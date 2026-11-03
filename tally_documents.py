"""Read-only PDF surfaces and separately pinned OCR, with exact page locators.

PyMuPDF is optional. OCR is never substituted for the native text layer. Sparse
and image-bearing pages remain review candidates even when OCR confidence is high.
"""
import hashlib
import json
import math
import re
from pathlib import Path
from decimal import Decimal
import tally as T
from tally_exchange import no_duplicates

MAX_FILE = 64 * 1024 * 1024


def bounded(path, limit=MAX_FILE):
    with Path(path).open('rb') as f: data = f.read(limit + 1)
    if len(data) > limit: raise ValueError('file exceeds size bound')
    return data


def load_pdf(path, options=None, tick=lambda: None):
    try: import fitz
    except ImportError: raise ValueError('read_pdf requires optional PyMuPDF; no automatic installation')
    options = {} if options is None else options
    if not isinstance(options, dict) or set(options) - {'pages', 'ocr_path', 'ocr_sha256'}:
        raise ValueError('options: pages, ocr_path and ocr_sha256')
    data = bounded(path); sha = hashlib.sha256(data).hexdigest(); ocr = {}; side_hash = None; engine = None
    with fitz.open(stream=data, filetype='pdf') as doc:
        if doc.needs_pass: raise ValueError('encrypted PDF requires an unlocked copy')
        selected = options.get('pages', list(range(1, min(len(doc), 64) + 1)))
        if not isinstance(selected, list) or not 1 <= len(selected) <= 64: raise ValueError('select 1..64 pages')
        ps = []
        for p in selected:
            if isinstance(p, bool) or not isinstance(p, (int, Decimal)) or int(p) != p or not 1 <= p <= len(doc):
                raise ValueError('pages must be distinct valid one-based integers')
            ps.append(int(p))
        if len(set(ps)) != len(ps): raise ValueError('duplicate selected page')
        if ('ocr_path' in options) != ('ocr_sha256' in options): raise ValueError('OCR needs path AND expected sidecar hash')
        if 'ocr_path' in options:
            side = bounded(options['ocr_path'], 16 * 1024 * 1024); side_hash = hashlib.sha256(side).hexdigest()
            if not isinstance(options['ocr_sha256'], str) or not re.fullmatch('[0-9a-f]{64}', options['ocr_sha256']) or side_hash != options['ocr_sha256']:
                raise ValueError('OCR sidecar hash mismatch')
            raw = json.loads(side, object_pairs_hook=no_duplicates)
            if not isinstance(raw, dict) or raw.get('sha256') != sha or raw.get('error') is not None or not isinstance(raw.get('pages'), list) or len(raw['pages']) > 2000 or not isinstance(raw.get('engine'), str):
                raise ValueError('OCR PDF hash, error, engine or page envelope invalid')
            engine = raw['engine']
            for p in raw['pages']:
                if not isinstance(p, dict) or type(p.get('page')) is not int or not 1 <= p['page'] <= len(doc) or p['page'] in ocr:
                    raise ValueError('invalid/duplicate OCR page')
                if not isinstance(p.get('text'), str) or len(p['text']) > 1000000 or not isinstance(p.get('lines'), list) or len(p['lines']) > 20000:
                    raise ValueError('invalid/bounded OCR text and lines required')
                for line in p['lines']:
                    if not isinstance(line, dict) or not isinstance(line.get('text'), str) or len(line['text']) > 100000: raise ValueError('invalid OCR line')
                    bb = line.get('bbox'); conf = line.get('conf')
                    if not isinstance(bb, list) or len(bb) != 4 or any(type(x) not in (int, float) or not math.isfinite(x) or not 0 <= x <= 1 for x in bb) or bb[0]+bb[2] > 1.001 or bb[1]+bb[3] > 1.001:
                        raise ValueError('OCR boxes need normalized bottom-left xywh')
                    if type(conf) not in (int, float) or not math.isfinite(conf) or not 0 <= conf <= 1: raise ValueError('OCR confidence outside 0..1')
                    tick()
                if p['text'] != '\n'.join(l['text'] for l in p['lines']): raise ValueError('OCR text disagrees with line inventory')
                ocr[p['page']] = p
        pages = []; chars = 0
        for n in ps:
            tick(); page = doc[n-1]; text = page.get_text('text', sort=False); words = page.get_text('words', sort=False)
            chars += len(text)
            if chars > 2000000 or len(words) > 100000: raise ValueError('PDF text/word bound exceeded')
            imgs = len(page.get_images()); sparse = len(re.sub(r'\s', '', text)) < 80
            anchor = 'pdf:'+sha+'/page:'+str(n)
            surface = 'image_only' if not text.strip() else 'sparse_text_layer' if sparse else 'text_layer_present'
            o = ocr.get(n)
            pages.append({'page': Decimal(n), 'anchor': anchor, 'width': Decimal(str(page.rect.width)), 'height': Decimal(str(page.rect.height)),
                          'rotation': Decimal(page.rotation), 'native_text': text,
                          'words': [{'text': w[4], 'bbox': [Decimal(str(x)) for x in w[:4]]} for w in words],
                          'native_bbox_coordinates': 'page points top-left x0 y0 x1 y1', 'image_count': Decimal(imgs),
                          'surface': surface, 'ocr_text': o['text'] if o else None,
                          'ocr_lines': [{'text': l['text'], 'confidence': Decimal(str(l['conf'])), 'bbox': [Decimal(str(x)) for x in l['bbox']]} for l in o['lines']] if o else [],
                          'ocr_bbox_coordinates': 'normalized bottom-left xywh',
                          'review_required': bool(imgs or sparse or o), 'review_basis': 'OCR and image content require page review; text presence alone does not establish body coverage'})
        return {'schema': 'tally.pdf.v1', 'path': str(Path(path).resolve()), 'sha256': sha, 'page_count': Decimal(len(doc)),
                'selected_pages': pages, 'complete_page_selection': len(ps) == len(doc),
                'ocr_sha256': side_hash, 'ocr_engine': engine, 'analytical_tier': 'derived_extract',
                'extraction': 'PyMuPDF '+str(fitz.VersionBind), 'coverage': 'selected pages only; native text and OCR retained separately'}


def install(it):
    def read_pdf(it_, node, path, opts=None):
        path = T.strip(path)
        if not isinstance(path, str): raise it_.err('read_pdf path must be text', node)
        def plain(v):
            v = T.strip(v)
            return {k:plain(x) for k,x in v.items()} if isinstance(v,dict) else [plain(x) for x in v] if isinstance(v,list) else v
        try:
            options = plain(opts) if opts is not None else {}
            if isinstance(options, dict) and 'ocr_path' in options: options['ocr_path'] = T.resolve_path(it_, options['ocr_path'])
            d = load_pdf(T.resolve_path(it_, path), options, lambda: it_.tick(node))
            d['selected_pages'] = [T.wrap_deep(p, {p['anchor']}) for p in d['selected_pages']]
            return T.wrap(d, {'pdf:'+d['sha256']})
        except (ValueError, TypeError, OSError, RuntimeError, OverflowError, RecursionError) as e: raise it_.err('read_pdf: '+str(e), node)
    it.builtins.vars['read_pdf'] = T.Builtin('read_pdf', read_pdf, (1,2))
