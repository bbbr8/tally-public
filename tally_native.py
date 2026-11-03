"""Bounded, read-only native email/workbook imports with exact source coordinates.

No macros, external links, attachment execution or formula calculation. Quoted
mail boundaries are structural candidates, never verified speaker identities.
"""
import hashlib
from pathlib import Path
import posixpath
import re
from decimal import Decimal, InvalidOperation, localcontext, ROUND_HALF_UP, ROUND_HALF_EVEN
from email import policy
from email.parser import BytesParser
from email.utils import getaddresses, parsedate_to_datetime
import xml.etree.ElementTree as ET
from zipfile import ZipFile, BadZipFile

MAX_FILE = 16 * 1024 * 1024
MAX_XML = 64 * 1024 * 1024
NS = {'s': 'http://schemas.openxmlformats.org/spreadsheetml/2006/main',
      'r': 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'}


def read_bytes(path):
    with open(path, 'rb') as f:
        data = f.read(MAX_FILE + 1)
    if len(data) > MAX_FILE:
        raise ValueError('native file exceeds 16 MiB limit')
    return data


def mail_sections(body, tick=lambda: None):
    """Keep exact character spans, split recognizable reply/forward delimiters."""
    lines = body.splitlines(keepends=True)
    cuts = []; offset = 0
    for i, line in enumerate(lines):
        tick(); stripped = line.strip(); reason = None
        if re.match(r'^On\s.+\bwrote:\s*$', stripped):
            reason = 'on_wrote'
        elif re.match(r'^From:\s*\S', stripped, re.I):
            following = ''.join(lines[i:i+8])
            if re.search(r'^\s*(Sent|Date):\s*\S', following, re.M | re.I) and \
               re.search(r'^\s*(To|Subject):\s*\S', following, re.M | re.I):
                reason = 'header_block'
        elif re.match(r'^[- ]*(Original Message|Forwarded message)[- :]*$', stripped, re.I) or \
             re.match(r'^Begin forwarded message:\s*$', stripped, re.I):
            reason = 'forward_marker'
        elif stripped.startswith('>') and (i == 0 or not lines[i-1].strip().startswith('>')):
            reason = 'quote_prefix'
        if reason:
            cuts.append((offset, reason, line.rstrip('\r\n')))
        offset += len(line)
    out = []; start = 0; reason = 'outer_body'; header = None
    for end, next_reason, next_header in cuts + [(len(body), None, None)]:
        if end > start:
            out.append({'start': start, 'end': end, 'text': body[start:end],
                        'kind': 'outer' if reason == 'outer_body' else 'quoted',
                        'boundary': reason, 'header_raw': header,
                        'attribution': 'outer_message_context' if reason == 'outer_body' else 'quoted_header_unverified'})
        start, reason, header = end, next_reason, next_header
    return out


def load_eml(path, tick=lambda: None):
    data = read_bytes(path); msg = BytesParser(policy=policy.default).parsebytes(data)
    warnings = [str(x) for x in msg.defects]
    headers = {key: [str(v) for v in msg.get_all(key, [])]
               for key in ('From', 'To', 'Cc', 'Bcc', 'Date', 'Subject', 'Message-ID', 'In-Reply-To', 'References')}
    for key in ('From', 'Date', 'Subject', 'Message-ID'):
        if len(headers[key]) > 1:
            warnings.append('duplicate_header:' + key)
    def addresses(key):
        return [{'name': name, 'address': address} for name, address in getaddresses(headers[key])]
    attachments = []; candidates = []; part_count = [0]
    def walk(part, locator, inherited_attachment=False):
        tick(); part_count[0] += 1
        if part_count[0] > 5000 or locator.count('.') > 40:
            raise ValueError('email exceeds 5000 parts / 40 nesting levels')
        attached = inherited_attachment or part.get_content_disposition() == 'attachment' or part.get_filename() is not None
        if attached:
            # An attached message may itself be multipart; keep it out of body selection.
            payload = part.get_payload(decode=True)
            if payload is None:
                payload = part.as_bytes(policy=policy.default)
            attachments.append({'part': locator, 'filename': part.get_filename(),
                                'declared_type': part.get_content_type(), 'disposition': part.get_content_disposition(),
                                'size': len(payload), 'sha256': hashlib.sha256(payload).hexdigest()})
            return
        if part.is_multipart():
            for i, child in enumerate(part.iter_parts(), 1):
                walk(child, locator + '.' + str(i))
            return
        warnings.extend(str(x) for x in part.defects)
        if part.get_content_type() in ('text/plain', 'text/html'):
            payload = part.get_payload(decode=True) or b''
            charset = part.get_content_charset() or 'ascii'
            try:
                text = payload.decode(charset, errors='strict')
            except (UnicodeError, LookupError):
                text = payload.decode('utf-8', errors='replace')
                warnings.append('decode_fallback:' + locator + ':' + charset)
            candidates.append({'part': locator, 'format': part.get_content_type(), 'text': text})
    walk(msg, '1')
    plain = [x for x in candidates if x['format'] == 'text/plain']
    selected = (plain or candidates or [None])[0]
    if len(plain or candidates) > 1:
        warnings.append('multiple_body_parts: first selected; all available in body_parts')
    date_raw = headers['Date'][0] if headers['Date'] else None
    dt = None
    try:
        dt = parsedate_to_datetime(date_raw) if date_raw else None
    except (ValueError, TypeError, OverflowError):
        warnings.append('invalid_date')
    timezone_known = dt is not None and dt.utcoffset() is not None
    if dt is not None and not timezone_known:
        warnings.append('date_timezone_unknown')
    body = selected['text'] if selected else ''
    sections = mail_sections(body, tick) if selected and selected['format'] == 'text/plain' else []
    if selected and selected['format'] == 'text/html':
        warnings.append('html_body_unrendered: quote segmentation unavailable')
    return {'path': str(Path(path).resolve()), 'sha256': hashlib.sha256(data).hexdigest(),
            'headers': headers, 'from': addresses('From'), 'to': addresses('To'), 'cc': addresses('Cc'), 'bcc': addresses('Bcc'),
            'subject': headers['Subject'][0] if headers['Subject'] else None,
            'message_id': headers['Message-ID'][0] if headers['Message-ID'] else None,
            'date_raw': date_raw, 'date_iso': dt.isoformat() if dt else None,
            'timezone_known': timezone_known, 'body': body,
            'body_format': selected['format'] if selected else None,
            'body_part': selected['part'] if selected else None, 'body_parts': candidates,
            'sections': sections, 'attachments': attachments, 'warnings': warnings}


DATE_FORMATS = {14: 'mm-dd-yy', 15: 'd-mmm-yy', 16: 'd-mmm', 17: 'mmm-yy',
                18: 'h:mm AM/PM', 19: 'h:mm:ss AM/PM', 20: 'h:mm', 21: 'h:mm:ss',
                22: 'm/d/yy h:mm', 45: 'mm:ss', 46: '[h]:mm:ss', 47: 'mmss.0'}


def excel_calendar(serial, fmt, system):
    """Recognized date styles only. Raw serial remains the authoritative cell value."""
    from datetime import datetime, timedelta
    if not fmt or not isinstance(serial, Decimal):
        return None, 'numeric'
    clean = re.sub(r'"[^"]*"|\\.', '', fmt).lower().split(';')[0]
    if re.search(r'\[[hms]+\]', clean):
        return None, 'duration_serial'
    clean = re.sub(r'\[[^]]*\]', '', clean)
    if not re.search('[ymdhs]', clean):
        return None, 'numeric'
    try:
        if serial > Decimal('2958465.999999999'):
            return None, 'date_out_of_range'
        days = int(serial // 1); fraction = serial - days
        if serial < 0:
            return None, 'negative_date_serial'
        if system == '1900' and days == 60:
            return None, 'fictitious_1900_02_29'
        with localcontext() as ctx:
            ctx.prec = 40
            micros = int((fraction*Decimal(86400000000)).to_integral_value(rounding=ROUND_HALF_UP))
        if not re.search('[yd]', clean) and not re.search(r'm[^a-z]*[/\-]', clean):
            dt = datetime(1900, 1, 1) + timedelta(microseconds=micros)
            return dt.time().isoformat(), 'time_serial'
        epoch = datetime(1904, 1, 1) if system == '1904' else datetime(1899, 12, 30)
        adjusted = days+1 if system == '1900' and days < 60 else days
        return (epoch+timedelta(days=adjusted, microseconds=micros)).isoformat(), 'date_serial'
    except (OverflowError, ValueError):
        return None, 'date_out_of_range'


def load_xlsx(path, tick=lambda: None):
    data = read_bytes(path)
    import io
    with ZipFile(io.BytesIO(data)) as z:
        infos = z.infolist()
        if len(infos) > 2000 or sum(x.file_size for x in infos) > MAX_XML:
            raise ValueError('workbook exceeds 2000 entries / 64 MiB expanded limit')
        if len({x.filename for x in infos}) != len(infos):
            raise ValueError('duplicate workbook ZIP member')
        def xml(name):
            tick(); raw = z.read(name)
            if b'<!DOCTYPE' in raw.upper() or b'<!ENTITY' in raw.upper():
                raise ValueError('XML declarations with entities are unsupported')
            class NoDTD(ET.TreeBuilder):
                def doctype(self, name, pubid, system):
                    raise ValueError('XML document types are unsupported')
            return ET.fromstring(raw, parser=ET.XMLParser(target=NoDTD()))
        def rich(node):
            return ''.join(t.text or '' for t in node.findall('.//s:t', NS))
        strings = []
        if 'xl/sharedStrings.xml' in z.namelist():
            for si in xml('xl/sharedStrings.xml').findall('s:si', NS):
                tick(); strings.append(rich(si))
                if len(strings) > 100000: raise ValueError('workbook exceeds 100000 shared strings')
        book = xml('xl/workbook.xml')
        pr = book.find('s:workbookPr', NS)
        date_system = '1904' if pr is not None and pr.attrib.get('date1904') in ('1', 'true') else '1900'
        formats = dict(DATE_FORMATS); style_formats = [0]
        if 'xl/styles.xml' in z.namelist():
            styles = xml('xl/styles.xml')
            formats.update({int(x.attrib['numFmtId']): x.attrib['formatCode'] for x in styles.findall('s:numFmts/s:numFmt', NS)})
            style_formats = [int(x.attrib.get('numFmtId', '0')) for x in styles.findall('s:cellXfs/s:xf', NS)] or [0]
        rels = {r.attrib['Id']: r.attrib for r in xml('xl/_rels/workbook.xml.rels')}
        sheets = []; warnings = []; total_cells = 0
        for sheet in book.findall('s:sheets/s:sheet', NS):
            tick(); rel = rels[sheet.attrib['{' + NS['r'] + '}id']]
            if rel.get('TargetMode') == 'External':
                raise ValueError('external sheet relationship is unsupported')
            target = rel['Target']; target = target.lstrip('/') if target.startswith('/') else posixpath.normpath('xl/' + target)
            if not target.startswith('xl/') or '/..' in target or '\\' in target:
                raise ValueError('invalid sheet member path')
            root = xml(target); cells = {}
            for c in root.findall('s:sheetData/s:row/s:c', NS):
                tick(); total_cells += 1
                if total_cells > 100000:
                    raise ValueError('workbook exceeds 100000 cell limit')
                coord = c.attrib.get('r', '')
                if not re.fullmatch(r'[A-Z]{1,3}[1-9][0-9]{0,6}', coord) or coord in cells:
                    raise ValueError('invalid or duplicate cell coordinate: ' + coord)
                kind = c.attrib.get('t', 'n'); v = c.find('s:v', NS); f = c.find('s:f', NS)
                raw = v.text if v is not None else None; value = None
                if kind == 's' and raw is not None:
                    value = strings[int(raw)]
                elif kind == 'inlineStr':
                    value = rich(c)
                elif kind == 'b' and raw is not None:
                    if raw not in ('0', '1'): raise ValueError('invalid boolean cell: ' + coord)
                    value = raw == '1'
                elif kind == 'n' and raw is not None:
                    value = Decimal(raw)
                    if not value.is_finite(): raise ValueError('nonfinite numeric cell: ' + coord)
                else:
                    value = raw
                if f is not None and raw is None:
                    warnings.append('missing_formula_cache:' + sheet.attrib['name'] + '!' + coord)
                style_index = int(c.attrib.get('s', '0'))
                if not 0 <= style_index < len(style_formats):
                    raise ValueError('invalid cell style index: ' + coord)
                format_id = style_formats[style_index]; number_format = formats.get(format_id)
                date_iso, date_status = excel_calendar(value, number_format, date_system)
                if kind == 'd':
                    date_iso, date_status = raw, 'iso_date_literal'
                cells[coord] = {'number_format_id': format_id, 'number_format': number_format,
                                'date_iso': date_iso, 'date_status': date_status, 'coordinate': coord, 'kind': kind, 'value': value, 'raw': raw,
                                'style': c.attrib.get('s'), 'formula': f.text if f is not None else None,
                                'formula_attributes': dict(f.attrib) if f is not None else {},
                                'has_formula': f is not None,
                                'cache_status': ('missing' if raw is None else 'stored_unverified') if f is not None else 'literal'}
            sheets.append({'name': sheet.attrib['name'], 'state': sheet.attrib.get('state', 'visible'), 'cells': cells,
                           'merged_ranges': [m.attrib['ref'] for m in root.findall('s:mergeCells/s:mergeCell', NS)]})
        return {'path': str(Path(path).resolve()), 'sha256': hashlib.sha256(data).hexdigest(), 'sheets': sheets,
                'warnings': warnings, 'cell_count': total_cells,
                'date_system': date_system, 'calculation': 'stored values only; recognized date styles decoded beside raw serials; formulas never recalculated',
                'calc_properties': dict(book.find('s:calcPr', NS).attrib) if book.find('s:calcPr', NS) is not None else {}}


def money_parse(value, rounding='reject'):
    """Parse US monetary text/Decimal, disclose cent rounding; reject malformed grouping."""
    if rounding not in ('reject', 'half_up', 'half_even'):
        raise ValueError('rounding must be reject, half_up or half_even')
    raw = str(value)
    if isinstance(value, bool) or not isinstance(value, (str, Decimal)):
        raise ValueError('money_read needs monetary text or a decimal number')
    if len(raw) > 200:
        raise ValueError('monetary input exceeds 200 characters')
    text = raw.strip(); sign = 1
    if isinstance(value, str):
        if text.startswith('(') and text.endswith(')'):
            sign = -1; text = text[1:-1].strip()
            if text.startswith(('+', '-')): raise ValueError('conflicting money signs')
        else:
            if text.startswith('$'): text = text[1:].strip()
        if sign == 1 and text.startswith(('+', '-')):
            sign = -1 if text[0] == '-' else 1; text = text[1:].strip()
        if text.startswith('$'): text = text[1:].strip()
        # Scientific notation is accepted explicitly as a numeric representation,
        # useful for raw Excel cells; thousands separators still require groups of 3.
        if not re.fullmatch(r'(?:[0-9]+|[0-9]{1,3}(?:,[0-9]{3})+)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]{1,3})?', text):
            raise ValueError('invalid monetary text or thousands grouping')
        with localcontext() as ctx:
            ctx.prec = 240
            d = Decimal(text.replace(',', '')) * sign
    else:
        d = value
    if not d.is_finite() or abs(d) > Decimal('1e18') or (d and d.adjusted() < -100):
        raise ValueError('monetary value outside bounded finite range')
    with localcontext() as ctx:
        ctx.prec = 240
        cents = d * 100
        nearest = cents.to_integral_value(rounding=ROUND_HALF_UP if rounding != 'half_even' else ROUND_HALF_EVEN)
        rounded = nearest != cents
        if rounded and rounding == 'reject':
            raise ValueError('fractional cents require explicit half_up or half_even rounding')
        result = T.Money(int(nearest))
        delta = result.dec() - d
    return {'amount': result, 'raw': raw, 'decimal': str(d), 'rounded': rounded,
            'rounding': rounding, 'rounding_delta': str(delta)}


# Deferred import also lets standalone synthetic oracles use the native parsers.
import tally as T


def install(it):
    def eml(it_, node, path):
        p = T.resolve_path(it_, path)
        try:
            result = load_eml(p, lambda: it_.tick(node))
        except (OSError, ValueError, TypeError) as ex:
            raise it_.err('read_eml: ' + str(ex), node)
        base = p + '#sha256=' + result['sha256']
        for index, section in enumerate(result['sections']):
            cite = base + ':body:' + str(section['start']) + ':' + str(section['end'])
            section.update(source=cite)
            result['sections'][index] = T.wrap_deep(section, {cite})
        return T.wrap_deep(result, {base} | T.srcs(path))
    def xlsx(it_, node, path):
        p = T.resolve_path(it_, path)
        try:
            result = load_xlsx(p, lambda: it_.tick(node))
        except (OSError, ValueError, KeyError, IndexError, InvalidOperation, ET.ParseError, BadZipFile) as ex:
            raise it_.err('read_xlsx: ' + str(ex), node)
        base = p + '#sha256=' + result['sha256']
        for sheet in result['sheets']:
            for coord, cell in sheet['cells'].items():
                cell['source'] = base + ':' + sheet['name'] + '!' + coord
                sheet['cells'][coord] = T.wrap_deep(cell, {cell['source']} | T.srcs(path))
        for key in ('path', 'sha256', 'warnings', 'calculation', 'cell_count', 'calc_properties', 'date_system'):
            result[key] = T.wrap_deep(result[key], {base} | T.srcs(path))
        return result
    def rows(it_, node, book, sheet_name, start, end, mapping):
        name = T.strip(sheet_name); a = T.strip(start); b = T.strip(end); columns = T.strip(mapping)
        if not all(isinstance(x, Decimal) and x == x.to_integral_value() for x in (a, b)) or not 1 <= a <= b <= 1048576 or b-a >= 10000:
            raise it_.err('sheet_rows needs an explicit range of 1..10000 rows', node)
        if not isinstance(columns, dict) or not columns or len(columns) > 100:
            raise it_.err('sheet_rows needs 1..100 named columns', node)
        if any(not isinstance(k, str) or k == 'row' or not isinstance(T.strip(v), str) or not re.fullmatch('[A-Z]{1,3}', T.strip(v)) for k, v in columns.items()):
            raise it_.err('sheet_rows columns must map names to uppercase Excel columns; row is reserved', node)
        raw_book = T.strip(book)
        if not isinstance(raw_book, dict) or 'sheets' not in raw_book:
            raise it_.err('sheet_rows needs a read_xlsx workbook', node)
        matches = [s for s in T.strip(raw_book['sheets']) if T.strip(T.strip(s)['name']) == name]
        if len(matches) != 1: raise it_.err('sheet_rows requires one exact sheet name', node)
        sheet = T.strip(matches[0]); cells = T.strip(sheet['cells'])
        base = str(T.strip(raw_book['path'])) + '#sha256=' + str(T.strip(raw_book['sha256']))
        out = []
        for n in range(int(a), int(b)+1):
            it_.tick(node); row = {'row': Decimal(n)}
            for key, col in columns.items():
                coord = T.strip(col) + str(n)
                row[key] = cells.get(coord, T.wrap_deep({'coordinate': coord, 'value': None, 'raw': None,
                      'kind': 'absent', 'formula': None, 'has_formula': False, 'cache_status': 'absent',
                      'source': base + ':' + name + '!' + coord}, {base + ':' + name + '!' + coord}))
            out.append(row)
        return out
    def money(it_, node, value, rounding='reject'):
        try:
            r = money_parse(T.strip(value), T.strip(rounding))
        except (ValueError, InvalidOperation) as ex:
            raise it_.err('money_read: ' + str(ex), node)
        return T.wrap_deep(r, T.all_sources(value) | T.all_sources(rounding))
    def find_mail(it_, node, message, needle, scope='outer'):
        m = T.strip(message); text = T.strip(needle); selected = T.strip(scope)
        if not isinstance(m, dict) or T.strip(m.get('body_format')) != 'text/plain':
            raise it_.err('email_find needs a plain-text read_eml message', node)
        if not isinstance(text, str) or not 1 <= len(text) <= 200 or selected not in ('outer', 'quoted', 'all'):
            raise it_.err('email_find needs 1..200 characters and outer/quoted/all scope', node)
        result = []; searched = set(T.all_sources(needle) | T.all_sources(scope))
        for section in T.strip(m['sections']):
            it_.tick(node); section = T.strip(section); kind = T.strip(section['kind'])
            if selected != 'all' and kind != selected: continue
            searched.update(T.all_sources(section['text']))
            native = T.strip(section['text'])
            for match in re.finditer(re.escape(text), native, re.I):
                it_.tick(node); offset = int(T.strip(section['start']))
                result.append(T.wrap_deep({'text': native[match.start():match.end()],
                      'start': Decimal(offset+match.start()), 'end': Decimal(offset+match.end()),
                      'section_kind': kind, 'attribution': T.strip(section['attribution']),
                      'section_text': native}, T.all_sources(section['text']) | T.all_sources(needle) | T.all_sources(scope)))
        return T.wrap(result, searched)
    def budget(it_, node, records):
        raw = T.strip(records)
        if not isinstance(raw, list) or len(raw) > 2000:
            raise it_.err('budget_audit accepts at most 2000 explicitly mapped budget rows', node)
        fields = ('scheduled', 'change', 'revised', 'completed', 'deposits', 'total', 'balance')
        totals = {k: 0 for k in fields}; checks = []; ids = {}; duplicates = []; missing = []
        for index, record in enumerate(raw):
            it_.tick(node); row = T.strip(record)
            if not isinstance(row, dict) or any(k not in row for k in ('id',) + fields):
                raise it_.err('budget_audit rows need id, scheduled, change, revised, completed, deposits, total, balance', node)
            ident = T.strip(row['id'])
            if ident is None or ident == '': missing.append(Decimal(index))
            elif isinstance(ident, bool) or not isinstance(ident, (str, Decimal)):
                raise it_.err('budget_audit id must be a string, number or nil', node)
            elif (type(ident), ident) in ids:
                duplicates.append({'first': Decimal(ids[(type(ident), ident)]), 'repeat': Decimal(index), 'id': row['id']})
            else: ids[(type(ident), ident)] = index
            values = {}
            for key in fields:
                value = T.strip(row[key])
                if not isinstance(value, T.Money):
                    raise it_.err('budget_audit financial fields must be exact money; use money_read with explicit rounding', node)
                values[key] = value.cents; totals[key] += value.cents
            for rule, left, right in (('scheduled_plus_change', ('scheduled', 'change'), 'revised'),
                                      ('completed_plus_deposits', ('completed', 'deposits'), 'total'),
                                      ('revised_minus_total', ('revised',), 'balance')):
                calculated = sum(values[k] for k in left) - (values['total'] if rule == 'revised_minus_total' else 0)
                delta = calculated-values[right]
                inputs = [row[k] for k in left] + [row[right], row['id']]
                if rule == 'revised_minus_total': inputs.append(row['total'])
                cites = set().union(*(T.all_sources(x) for x in inputs))
                checks.append(T.wrap_deep({'row': Decimal(index), 'id': ident, 'rule': rule, 'ok': delta == 0,
                                          'calculated': T.Money(calculated), 'stored': T.Money(values[right]),
                                          'gap': T.Money(delta)}, cites))
        all_src = T.all_sources(records)
        failures = [x for x in checks if not T.strip(x['ok'])]
        return {'clean': T.wrap(bool(raw) and not (failures or duplicates or missing), all_src),
                'rows': T.wrap(Decimal(len(raw)), all_src), 'checks': checks, 'failures': failures,
                'duplicates': duplicates, 'missing_ids': missing,
                'totals': {k: T.wrap(T.Money(v), set().union(*(T.all_sources(T.strip(r)[k]) for r in raw))) for k, v in totals.items()}}
    for name, func, arity in [('read_eml', eml, (1, 1)), ('read_xlsx', xlsx, (1, 1)),
                              ('sheet_rows', rows, (5, 5)), ('money_read', money, (1, 2)),
                              ('email_find', find_mail, (2, 3)), ('budget_audit', budget, (1, 1))]:
        it.builtins.vars[name] = T.Builtin(name, func, arity)
