#!/usr/bin/env python3
"""Zeta — a programming language whose rules are taken from the teachings of Jesus Christ.

A general-purpose language (functions, closures, if/while/for, lists, maps, exact numbers, exact money, dates)
whose built-in semantics are six teachings, each one a rule the interpreter enforces:

    witness    "In the mouth of two or three witnesses shall every word be established" (2 Cor 13:1)
               fact x = ... by "VENDOR_0014", "RECEIPT_0123"   ·   judge x   ·   established(x)
               A fact is ESTABLISHED by two witnesses from different source families. A value computed from
               facts is established only when every fact under it is.
    atonement  owe A -> B $AMT for "why" as d   ·   pay P on d $AMT   ·   forgive d   ·   ledger
               A payment by the debtor is PAID. A payment by anyone else is BORNE, and the language records
               who bore whose debt, forever. Paid, borne and forgiven are three kinds of settlement and never sum.
    fruits     "By their fruits ye shall know them" (Matt 7:16)
               x called "label"   ·   fruits NAME { "label" when <expr of v> ... }   ·   discern x with NAME
               A value is judged by what it does, not by what it is called.
    grace      grace { ... }  — a failing statement inside is forgiven and recorded, and the block goes on.
               confessions() returns every forgiven error with its line. Forgiven is not forgotten.
    parable    "the lot" meaning "the land behind it"  — a value with a surface and a depth.
               Arithmetic and printing use the surface; depth(x) reads what it meant.
    restore    forsake x   ·   restore x   ·   history("x")  — nothing bound is ever lost.
    the lost sheep  seek(items, total) — the one item (then the pair) whose removal makes the books close.

    zeta run FILE [--json]   ·   zeta check FILE   ·   zeta selftest   ·   zeta describe [--json]
    zeta repl   ·   zeta version

stdlib only.
"""
import json
import os
import re
import sys
from datetime import date, timedelta
from fractions import Fraction

VERSION = "0.2.0"


# ------------------------------------------------------------------ errors
class AtoneError(Exception):
    def __init__(self, code, message, line=0, col=0, hint=""):
        super().__init__(message)
        self.code, self.message, self.line, self.col, self.hint = code, message, line, col, hint

    def as_dict(self):
        return {"code": self.code, "message": self.message, "line": self.line, "col": self.col, "hint": self.hint}

    def __str__(self):
        s = f"{self.code} line {self.line}:{self.col}: {self.message}"
        return s + (f"\n  hint: {self.hint}" if self.hint else "")


ERRORS = {
    "A-E001": "unexpected character",
    "A-E002": "unexpected token",
    "A-E003": "undefined name",
    "A-E004": "type mismatch",
    "A-E005": "expect failed",
    "A-E006": "division by zero",
    "A-E007": "debt overpaid",
    "A-E008": "name was forsaken",
    "A-E010": "wrong number of arguments",
    "A-E011": "index or key missing",
    "A-E012": "unknown fruits classifier",
    "A-E013": "language is not a grafted parent",
    "A-E014": "parent language call failed",
}


# ------------------------------------------------------------------ values
class Money:
    """Exact dollars as a Fraction; prints $1,234.56."""
    __slots__ = ("d",)

    def __init__(self, d):
        self.d = Fraction(d)

    def __eq__(self, o):
        return isinstance(o, Money) and o.d == self.d

    def __hash__(self):
        return hash(("$", self.d))

    def __repr__(self):
        return fmt_money(self.d)


def fmt_money(d):
    neg = d < 0
    cents = abs(d) * 100
    if cents.denominator != 1:
        whole = abs(d)
        s = "$" + fmt_num(whole)
    else:
        c = int(cents)
        s = f"${c // 100:,}.{c % 100:02d}"
    return ("-" if neg else "") + s


def fmt_num(f):
    f = Fraction(f)
    if f.denominator == 1:
        return str(f.numerator)
    den = f.denominator
    for p in (2, 5):
        while den % p == 0:
            den //= p
    if den == 1:  # terminating decimal, print exactly
        sign = "-" if f < 0 else ""
        a = abs(f)
        k = 0
        while (a * 10 ** k).denominator != 1:
            k += 1
        n = int(a * 10 ** k)
        s = str(n).rjust(k + 1, "0")
        return f"{sign}{s[:-k]}.{s[-k:]}"
    return f"{f.numerator}/{f.denominator}"


class Rich:
    """A value carrying witnesses, a basis (the facts it was computed from), a label and a depth."""
    __slots__ = ("v", "wits", "basis", "label", "depth", "name")

    def __init__(self, v, wits=(), basis=(), label=None, depth=None, name=None):
        self.v, self.wits, self.basis, self.label, self.depth, self.name = v, tuple(wits), tuple(basis), label, depth, name

    def copy(self, **kw):
        r = Rich(self.v, self.wits, self.basis, self.label, self.depth, self.name)
        for k, val in kw.items():
            setattr(r, k, val)
        return r

    def carries_proof(self):
        return bool(self.wits or self.basis)


def un(x):
    return x.v if isinstance(x, Rich) else x


def family(src):
    """Source family of a witness: an uppercase record prefix or the first word."""
    s = str(src).strip()
    m = re.match(r"^([A-Za-z][A-Za-z\-]*?)[_ \-]?\d", s)
    if m and m.group(1).isupper():
        return m.group(1).upper().rstrip("-")
    return (re.split(r"[\s:]+", s, maxsplit=1)[0] or s).lower()


def established(x, seen=None):
    """(bool, reason). A fact needs two witnesses from distinct families; a computed value needs every basis."""
    if not isinstance(x, Rich):
        return False, "carries no witness"
    if x.basis:
        waiting = []
        for b in x.basis:
            ok, _ = established(b)
            if not ok:
                waiting.append(b.name or show(b))
        if waiting:
            return False, "computed from facts awaiting a second witness: " + ", ".join(waiting)
        return True, f"every one of {len(x.basis)} facts under it is established"
    fams = sorted({family(w) for w in x.wits})
    if len(fams) >= 2:
        return True, f"{len(x.wits)} witnesses from {len(fams)} families ({', '.join(fams)})"
    if x.wits:
        return False, (f"{len(x.wits)} witness{'es' if len(x.wits) > 1 else ''} from one family ({fams[0]}: "
                       f"{', '.join(x.wits)}); a witness from another family establishes it")
    return False, "carries no witness"


class Debt:
    _n = 0

    def __init__(self, debtor, creditor, amount, reason, name):
        Debt._n += 1
        self.id = Debt._n
        self.debtor, self.creditor, self.amount, self.reason, self.name = debtor, creditor, amount, reason, name
        self.events = []  # (kind, who, Fraction dollars, witnesses, line)

    def total(self, kind=None, who=None):
        return sum((e[2] for e in self.events if (kind is None or e[0] == kind) and (who is None or e[1] == who)),
                   Fraction(0))

    def outstanding(self):
        return self.amount - self.total()

    def bearers(self):
        out = {}
        for k, who, amt, _, _ in self.events:
            if k == "borne":
                out[who] = out.get(who, Fraction(0)) + amt
        return out


class Function:
    def __init__(self, name, params, body, env):
        self.name, self.params, self.body, self.env = name, params, body, env


class Builtin:
    def __init__(self, name, fn, arity=None):
        self.name, self.fn, self.arity = name, fn, arity


class Fruits:
    def __init__(self, name, rules, env):
        self.name, self.rules, self.env = name, rules, env


class QState:
    """A uniform superposition over a list of values; amplitudes a_i / sqrt(N) with a_i exact rationals."""

    def __init__(self, items, amps=None, iterations=0, marked=0):
        self.items = list(items)
        self.amps = list(amps) if amps is not None else [Fraction(1)] * len(self.items)
        self.iterations, self.marked = iterations, marked

    def probs(self):
        n = len(self.items)
        return [a * a / n for a in self.amps]


def show(x):
    if isinstance(x, Rich):
        return show(x.v)
    if x is None:
        return "nil"
    if x is True:
        return "true"
    if x is False:
        return "false"
    if isinstance(x, Fraction):
        return fmt_num(x)
    if isinstance(x, Money):
        return repr(x)
    if isinstance(x, date):
        return x.isoformat()
    if isinstance(x, str):
        return x
    if isinstance(x, list):
        return "[" + ", ".join(show_inner(i) for i in x) + "]"
    if isinstance(x, dict):
        return "{" + ", ".join(f"{show_inner(k)}: {show_inner(v)}" for k, v in x.items()) + "}"
    if isinstance(x, Debt):
        return f"<debt {x.name}: {x.debtor} -> {x.creditor} {fmt_money(x.amount)}>"
    if isinstance(x, (Function, Builtin)):
        return f"<fn {x.name}>"
    if isinstance(x, Fruits):
        return f"<fruits {x.name}>"
    if isinstance(x, QState):
        return f"<superposition of {len(x.items)}, {x.marked} marked, Grover x{x.iterations}>"
    return str(x)


def show_inner(x):
    return json.dumps(x) if isinstance(un(x), str) else show(x)


def to_json(x):
    x = un(x)
    if isinstance(x, Fraction):
        return fmt_num(x)
    if isinstance(x, (Money, date, Debt, Function, Builtin, Fruits, QState)):
        return show(x)
    if isinstance(x, list):
        return [to_json(i) for i in x]
    if isinstance(x, dict):
        return {show(k): to_json(v) for k, v in x.items()}
    return x


# ------------------------------------------------------------------ lexer
KEYWORDS = {"let", "fn", "return", "if", "else", "while", "for", "in", "print", "expect", "true", "false", "nil",
            "and", "or", "not", "fact", "by", "judge", "owe", "pay", "on", "forgive", "ledger", "as", "fruits",
            "when", "discern", "with", "called", "meaning", "grace", "forsake", "restore", "reveal"}
TOKEN_RX = re.compile(r"""
    (?P<ws>[ \t\r]+) | (?P<comment>\#[^\n]*) | (?P<nl>\n) |
    (?P<date>\d{4}-\d{2}-\d{2}(?![\d]))  |
    (?P<money>\$(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?) |
    (?P<num>\d+(?:\.\d+)?) |
    (?P<str>"(?:[^"\\\n]|\\.)*") |
    (?P<name>[A-Za-z_][A-Za-z0-9_]*) |
    (?P<op>->|==|!=|<=|>=|[-+*/%<>=(){}\[\],.:;])
""", re.X)


class Tok:
    __slots__ = ("kind", "val", "line", "col")

    def __init__(self, kind, val, line, col):
        self.kind, self.val, self.line, self.col = kind, val, line, col

    def __repr__(self):
        return f"{self.kind}:{self.val!r}@{self.line}"


def lex(src):
    toks, i, line, col0, depth = [], 0, 1, 0, 0
    while i < len(src):
        m = TOKEN_RX.match(src, i)
        if not m:
            raise AtoneError("A-E001", f"unexpected character {src[i]!r}", line, i - col0 + 1,
                             "strings use double quotes; money is written $1,234.56; comments start with #")
        k, v, col = m.lastgroup, m.group(), i - col0 + 1
        if k == "nl":
            if depth == 0:
                toks.append(Tok("nl", "\n", line, col))
            line, col0 = line + 1, m.end()
        elif k in ("ws", "comment"):
            pass
        elif k == "date":
            try:
                toks.append(Tok("date", date.fromisoformat(v), line, col))
            except ValueError:
                raise AtoneError("A-E001", f"{v} is not a calendar date", line, col, "write dates as YYYY-MM-DD")
        elif k == "money":
            toks.append(Tok("money", Money(Fraction(v[1:].replace(",", ""))), line, col))
        elif k == "num":
            toks.append(Tok("num", Fraction(v), line, col))
        elif k == "str":
            toks.append(Tok("str", json.loads(v), line, col))
        elif k == "name":
            toks.append(Tok("kw" if v in KEYWORDS else "name", v, line, col))
        else:
            if v in "([":
                depth += 1
            elif v in ")]":
                depth = max(0, depth - 1)
            toks.append(Tok("op", v, line, col))
        i = m.end()
    toks.append(Tok("nl", "\n", line, 1))
    toks.append(Tok("eof", None, line, 1))
    return toks


# ------------------------------------------------------------------ parser  (AST = tuples: (kind, line, ...))
BINARY = {"or": 2, "and": 3, "==": 5, "!=": 5, "<": 5, ">": 5, "<=": 5, ">=": 5, "+": 6, "-": 6, "*": 7, "/": 7,
          "%": 7}


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, o=0):
        return self.t[self.i + o]

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def at(self, kind, val=None):
        tok = self.peek()
        return tok.kind == kind and (val is None or tok.val == val)

    def eat(self, kind, val=None, hint=""):
        tok = self.peek()
        if not self.at(kind, val):
            want = repr(val) if val is not None else kind
            got = "end of line" if tok.kind == "nl" else ("end of file" if tok.kind == "eof" else repr(tok.val))
            raise AtoneError("A-E002", f"expected {want}, found {got}", tok.line, tok.col,
                             hint or "check the statement's shape with `zeta describe`")
        return self.next()

    def skip_nl(self):
        while self.at("nl") or self.at("op", ";"):
            self.next()

    def program(self):
        stmts = []
        self.skip_nl()
        while not self.at("eof"):
            stmts.append(self.statement())
            self.end_stmt()
        return stmts

    def end_stmt(self):
        if self.at("op", "}") or self.at("eof"):
            return
        prev = self.t[self.i - 1]
        if prev.kind == "op" and prev.val == "}":
            self.skip_nl()
            return
        if not (self.at("nl") or self.at("op", ";")):
            tok = self.peek()
            raise AtoneError("A-E002", f"expected end of statement, found {tok.val!r}", tok.line, tok.col,
                             "one statement per line, or separate them with ;")
        self.skip_nl()

    def block(self):
        self.eat("op", "{", hint="a block starts with {")
        self.skip_nl()
        body = []
        while not self.at("op", "}"):
            if self.at("eof"):
                tok = self.peek()
                raise AtoneError("A-E002", "block never closed", tok.line, tok.col, "add the closing }")
            body.append(self.statement())
            self.end_stmt()
        self.eat("op", "}")
        return body

    def names_list(self):
        out = [self.eat("name").val]
        while self.at("op", ","):
            self.next()
            out.append(self.eat("name").val)
        return out

    def statement(self):
        tok = self.peek()
        ln = tok.line
        if tok.kind == "kw":
            k = tok.val
            if k == "let":
                self.next()
                name = self.eat("name").val
                self.eat("op", "=")
                return ("let", ln, name, self.expr())
            if k == "fn" and self.peek(1).kind == "name":
                self.next()
                name = self.next().val
                params, body = self.fn_rest()
                return ("fndef", ln, name, params, body)
            if k == "return":
                self.next()
                if self.at("nl") or self.at("op", "}") or self.at("op", ";"):
                    return ("return", ln, None)
                return ("return", ln, self.expr())
            if k == "if":
                self.next()
                cond = self.expr()
                then = self.block()
                other = None
                if self.at("kw", "else"):
                    self.next()
                    other = [self.statement()] if self.at("kw", "if") else self.block()
                return ("if", ln, cond, then, other)
            if k == "while":
                self.next()
                return ("while", ln, self.expr(), self.block())
            if k == "for":
                self.next()
                var = self.eat("name").val
                self.eat("kw", "in")
                return ("for", ln, var, self.expr(), self.block())
            if k == "print":
                self.next()
                args = [self.expr()]
                while self.at("op", ","):
                    self.next()
                    args.append(self.expr())
                return ("print", ln, args)
            if k == "expect":
                self.next()
                return ("expect", ln, self.expr())
            if k == "fact":
                self.next()
                name = self.eat("name").val
                self.eat("op", "=")
                val = self.expr()
                self.eat("kw", "by", hint='a fact names its witnesses: fact x = $5.00 by "VENDOR_0014", "RECEIPT_0123"')
                wits = [self.expr()]
                while self.at("op", ","):
                    self.next()
                    wits.append(self.expr())
                return ("fact", ln, name, val, wits)
            if k == "judge":
                self.next()
                return ("judge", ln, self.expr())
            if k == "owe":
                self.next()
                debtor = self.expr()
                self.eat("op", "->", hint='owe "Debtor" -> "Creditor" $100.00 for "why" as d1')
                creditor = self.expr()
                amount = self.expr()
                reason = None
                if self.at("kw", "for"):
                    self.next()
                    reason = self.expr()
                self.eat("kw", "as", hint="name the debt: ... as d1")
                return ("owe", ln, debtor, creditor, amount, reason, self.eat("name").val)
            if k == "pay":
                self.next()
                payer = self.expr()
                self.eat("kw", "on", hint='pay "Payer" on d1 $100.00 [by "VENDOR_0007"]')
                debt = self.eat("name").val
                amount = self.expr()
                wits = []
                if self.at("kw", "by"):
                    self.next()
                    wits = [self.expr()]
                    while self.at("op", ","):
                        self.next()
                        wits.append(self.expr())
                return ("pay", ln, payer, debt, amount, wits)
            if k == "forgive":
                self.next()
                debt = self.eat("name").val
                amount = None
                if not (self.at("nl") or self.at("op", ";") or self.at("op", "}")):
                    amount = self.expr()
                return ("forgive", ln, debt, amount)
            if k == "ledger":
                self.next()
                return ("ledger", ln)
            if k == "fruits":
                self.next()
                name = self.eat("name").val
                self.eat("op", "{")
                self.skip_nl()
                rules = []
                while not self.at("op", "}"):
                    label = self.expr()
                    self.eat("kw", "when", hint='each fruit reads: "label" when <expression of v>')
                    rules.append((label, self.expr()))
                    self.end_stmt()
                self.eat("op", "}")
                return ("fruits", ln, name, rules)
            if k == "discern":
                self.next()
                x = self.expr()
                self.eat("kw", "with", hint="discern x with CLASSIFIER")
                return ("discern", ln, x, self.eat("name").val)
            if k == "grace":
                self.next()
                return ("grace", ln, self.block())
            if k == "forsake":
                self.next()
                return ("forsake", ln, self.names_list())
            if k == "restore":
                self.next()
                return ("restore", ln, self.names_list())
            if k == "reveal":
                self.next()
                return ("reveal", ln, self.expr())
        e = self.expr()
        if self.at("op", "="):
            self.next()
            if e[0] not in ("name", "index", "dot"):
                raise AtoneError("A-E002", "can only assign to a name, an index or a field", ln, tok.col)
            return ("assign", ln, e, self.expr())
        return ("exprstmt", ln, e)

    def fn_rest(self):
        self.eat("op", "(")
        params = []
        if not self.at("op", ")"):
            params = self.names_list()
        self.eat("op", ")")
        return params, self.block()

    # expressions — precedence: meaning/called (1) < or < and < not < compare < + - < * / % < unary < postfix
    def expr(self):
        left = self.binary(2)
        while self.at("kw", "meaning") or self.at("kw", "called"):
            op = self.next()
            right = self.binary(2)
            left = (op.val, op.line, left, right)
        return left

    def binary(self, minp):
        left = self.unary()
        while True:
            tok = self.peek()
            op = tok.val if tok.kind in ("op", "kw") else None
            p = BINARY.get(op)
            if p is None or p < minp:
                return left
            self.next()
            right = self.binary(p + 1)
            left = ("bin", tok.line, op, left, right)

    def unary(self):
        tok = self.peek()
        if self.at("op", "-"):
            self.next()
            return ("neg", tok.line, self.unary())
        if self.at("kw", "not"):
            self.next()
            return ("not", tok.line, self.binary(4))
        return self.postfix(self.primary())

    def postfix(self, e):
        while True:
            tok = self.peek()
            if self.at("op", "("):
                self.next()
                args = []
                if not self.at("op", ")"):
                    args.append(self.expr())
                    while self.at("op", ","):
                        self.next()
                        args.append(self.expr())
                self.eat("op", ")")
                e = ("call", tok.line, e, args)
            elif self.at("op", "["):
                self.next()
                idx = self.expr()
                self.eat("op", "]")
                e = ("index", tok.line, e, idx)
            elif self.at("op", "."):
                self.next()
                nt = self.peek()
                if nt.kind not in ("name", "kw"):
                    self.eat("name", hint="a field name follows the dot")
                e = ("dot", tok.line, e, self.next().val)
            else:
                return e

    def primary(self):
        tok = self.next()
        ln = tok.line
        if tok.kind in ("num", "money", "str", "date"):
            return ("lit", ln, tok.val)
        if tok.kind == "kw" and tok.val in ("true", "false", "nil"):
            return ("lit", ln, {"true": True, "false": False, "nil": None}[tok.val])
        if tok.kind == "name":
            return ("name", ln, tok.val, tok.col)
        if tok.kind == "kw" and tok.val == "fn":
            params, body = self.fn_rest()
            return ("lambda", ln, params, body)
        if tok.kind == "op" and tok.val == "(":
            e = self.expr()
            self.eat("op", ")")
            return e
        if tok.kind == "op" and tok.val == "[":
            items = []
            if not self.at("op", "]"):
                items.append(self.expr())
                while self.at("op", ","):
                    self.next()
                    if self.at("op", "]"):
                        break
                    items.append(self.expr())
            self.eat("op", "]")
            return ("list", ln, items)
        if tok.kind == "op" and tok.val == "{":
            pairs = []
            self.skip_nl()
            while not self.at("op", "}"):
                k = self.expr()
                self.eat("op", ":")
                pairs.append((k, self.expr()))
                self.skip_nl()
                if self.at("op", ","):
                    self.next()
                    self.skip_nl()
            self.eat("op", "}")
            return ("map", ln, pairs)
        got = "end of line" if tok.kind == "nl" else repr(tok.val)
        raise AtoneError("A-E002", f"expected a value, found {got}", tok.line, tok.col,
                         "values are numbers, $money, \"strings\", dates, [lists], {maps}, names or fn(...) {...}")


def parse(src):
    return Parser(lex(src)).program()


# ------------------------------------------------------------------ environment
class Env:
    def __init__(self, parent=None):
        self.vars, self.parent = {}, parent

    def find(self, name):
        e = self
        while e is not None:
            if name in e.vars:
                return e
            e = e.parent
        return None


class ReturnSignal(Exception):
    def __init__(self, value):
        self.value = value


# ------------------------------------------------------------------ interpreter
_ABILITY = {}


def load_ability(home):
    """The ability module beside a language file (ability.py in its folder), or None."""
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(home, "ability.py")
    if not os.path.isfile(path):
        return None
    if path not in _ABILITY:
        import importlib.util
        if here not in sys.path:
            sys.path.insert(0, here)
        spec = importlib.util.spec_from_file_location("zeta_ability_" + os.path.basename(home), path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _ABILITY[path] = mod
    return _ABILITY[path]


def install_ability(it):
    """Namesake ability: built-ins from ability.py beside the running language's own file, for that language alone."""
    here = os.path.dirname(os.path.abspath(__file__))
    if it.dialect is not None:
        home = os.path.join(os.path.dirname(here), str(it.dialect.get("lower", "")))
    elif type(it) is Interp:
        home = here
    else:
        return
    mod = load_ability(home)
    if mod is None:
        return

    def reg(name, arity, fn):
        def call(*args):
            try:
                return fn(*[un(a) for a in args])
            except (ValueError, TypeError, ArithmeticError) as e:
                raise AtoneError("A-E040", f"{name}: {e}", it.line, 0, mod.ABOUT["builtins"].get(name, ""))
        it.globals.vars[name] = Builtin(name, call, arity)
    mod.install(reg)


class Interp:
    def __init__(self, out=None, dialect=None):
        self.out = out if out is not None else sys.stdout
        self.dialect = dialect
        self.globals = Env()
        self.debts = []
        self.fruits = {}
        self.confessions = []
        self.tomb = {}       # name -> (value, line forsaken)
        self.history = {}    # name -> [(line, value)]
        self.expects = [0, 0]
        self.records = []    # structured output for --json
        self.line = 0
        install_builtins(self)
        install_ability(self)

    def emit(self, text, rec=None):
        print(text, file=self.out)
        if rec is not None:
            self.records.append(rec)

    def err(self, code, msg, hint=""):
        return AtoneError(code, msg, self.line, 0, hint)

    def run(self, src):
        prog = parse(src)
        self.block(prog, self.globals)
        return self

    def block(self, stmts, env):
        for s in stmts:
            self.stmt(s, env)

    def bind(self, env, name, val):
        env.vars[name] = val
        self.history.setdefault(name, []).append({"line": Fraction(self.line), "value": val})

    def stmt(self, s, env):
        kind = s[0]
        self.line = s[1]
        if kind == "let":
            self.bind(env, s[2], self.ev(s[3], env))
        elif kind == "assign":
            target, val = s[2], self.ev(s[3], env)
            if target[0] == "name":
                e = env.find(target[2])
                if e is None:
                    raise self.undefined(target[2], target[3])
                self.bind(e, target[2], val)
            elif target[0] == "index":
                coll, key = un(self.ev(target[2], env)), un(self.ev(target[3], env))
                if isinstance(coll, list):
                    coll[self.int_index(key, coll)] = val
                elif isinstance(coll, dict):
                    coll[key] = val
                else:
                    raise self.err("A-E004", f"cannot index-assign into {tname(coll)}")
            else:
                coll = un(self.ev(target[2], env))
                if not isinstance(coll, dict):
                    raise self.err("A-E004", f"cannot set a field on {tname(coll)}")
                coll[target[3]] = val
        elif kind == "fndef":
            self.bind(env, s[2], Function(s[2], s[3], s[4], env))
        elif kind == "return":
            raise ReturnSignal(self.ev(s[2], env) if s[2] is not None else None)
        elif kind == "if":
            if truthy(self.ev(s[2], env)):
                self.block(s[3], Env(env))
            elif s[4] is not None:
                self.block(s[4], Env(env))
        elif kind == "while":
            n = 0
            while truthy(self.ev(s[2], env)):
                n += 1
                if n > 1_000_000:
                    raise self.err("A-E004", "loop ran a million times", "check the loop's condition")
                self.block(s[3], Env(env))
        elif kind == "for":
            seq = un(self.ev(s[3], env))
            if isinstance(seq, dict):
                seq = list(seq.keys())
            if not isinstance(seq, (list, str)):
                raise self.err("A-E004", f"for needs a list, map or string, found {tname(seq)}")
            for item in list(seq):
                inner = Env(env)
                inner.vars[s[2]] = item
                self.block(s[4], inner)
        elif kind == "print":
            vals = [self.ev(a, env) for a in s[2]]
            self.emit(" ".join(show(v) for v in vals), {"print": [to_json(v) for v in vals]})
        elif kind == "expect":
            v = self.ev(s[2], env)
            self.expects[1] += 1
            if not truthy(v):
                raise self.err("A-E005", "expect failed: " + describe_expect(s[2], self, env),
                               "the program's own known answer did not hold")
            self.expects[0] += 1
        elif kind == "fact":
            v = self.ev(s[3], env)
            wits = []
            for w in s[4]:
                wv = un(self.ev(w, env))
                wits.extend(wv if isinstance(wv, list) else [wv])
            base = v if isinstance(v, Rich) else Rich(v)
            allw = []
            for w in list(base.wits) + [str(w) for w in wits]:
                if w not in allw:
                    allw.append(w)
            self.bind(env, s[2], base.copy(wits=tuple(allw), basis=(), name=s[2]))
        elif kind == "judge":
            v = self.ev(s[2], env)
            ok, why = established(v)
            name = src_text(s[2]) if s[2][0] == "name" or not (isinstance(v, Rich) and v.name) else v.name
            verdict = "ESTABLISHED" if ok else "AWAITS_SECOND_WITNESS"
            shown = v.name if isinstance(v, Rich) and isinstance(v.v, dict) and v.name else show(v)
            self.emit(f"judge {name} = {shown}: {verdict} — {why}",
                      {"judge": name, "value": to_json(v), "verdict": verdict, "why": why})
        elif kind == "owe":
            debtor, creditor = show(self.ev(s[2], env)), show(self.ev(s[3], env))
            amt = self.money(self.ev(s[4], env), "owe")
            reason = show(self.ev(s[5], env)) if s[5] is not None else ""
            d = Debt(debtor, creditor, amt, reason, s[6])
            self.debts.append(d)
            self.bind(env, s[6], d)
        elif kind == "pay":
            payer = show(self.ev(s[2], env))
            d = self.debt(s[3], env)
            raw = self.ev(s[4], env)
            amt = self.money(raw, "pay")
            wits = [str(un(self.ev(w, env))) for w in s[5]] + (list(raw.wits) if isinstance(raw, Rich) else [])
            if amt > d.outstanding():
                raise self.err("A-E007", f"{fmt_money(amt)} is more than the {fmt_money(d.outstanding())} "
                                         f"outstanding on {d.name}",
                               "an overpayment is a new debt the other way: owe it as its own line")
            kind2 = "paid" if payer == d.debtor else "borne"
            d.events.append((kind2, payer, amt, wits, self.line))
        elif kind == "forgive":
            d = self.debt(s[2], env)
            amt = self.money(self.ev(s[3], env), "forgive") if s[3] is not None else d.outstanding()
            if amt > d.outstanding():
                raise self.err("A-E007", f"cannot forgive {fmt_money(amt)}; {fmt_money(d.outstanding())} is outstanding")
            d.events.append(("forgiven", d.creditor, amt, [], self.line))
        elif kind == "ledger":
            self.print_ledger()
        elif kind == "fruits":
            self.fruits[s[2]] = Fruits(s[2], s[3], env)
            self.bind(env, s[2], self.fruits[s[2]])
        elif kind == "discern":
            r = self.know(self.ev(s[2], env), s[3])
            self.emit(f"discern {src_text(s[2])}: called {json.dumps(r['called'])}, fruits "
                      f"{json.dumps(r['fruits'])}: {r['verdict']}", {"discern": src_text(s[2]), **to_json(r)})
        elif kind == "grace":
            for inner in s[2]:
                try:
                    self.stmt(inner, env)
                except ReturnSignal:
                    raise
                except AtoneError as e:
                    self.confess(e.code, e.message, e.line or inner[1])
                except RecursionError:
                    self.confess("A-E004", "recursion too deep", inner[1])
        elif kind == "forsake":
            for name in s[2]:
                e = env.find(name)
                if e is None:
                    raise self.undefined(name, 0)
                self.tomb[name] = (e.vars.pop(name), self.line, e)
        elif kind == "restore":
            for name in s[2]:
                if name not in self.tomb:
                    raise self.err("A-E003", f"{name} was never forsaken", "restore brings back a forsaken name")
                val, _, e = self.tomb.pop(name)
                self.bind(e, name, val)
        elif kind == "reveal":
            v = self.ev(s[2], env)
            depth = show(v.depth) if isinstance(v, Rich) and v.depth is not None else "(no depth given)"
            label = f" · called {json.dumps(v.label)}" if isinstance(v, Rich) and v.label else ""
            self.emit(f"reveal {src_text(s[2])}: surface {show(v)} · meaning {depth}{label}",
                      {"reveal": src_text(s[2]), "surface": to_json(v), "meaning": depth})
        elif kind == "exprstmt":
            self.ev(s[2], env)
        else:
            raise self.err("A-E002", f"unknown statement {kind}")

    def confess(self, code, msg, line):
        self.confessions.append({"line": Fraction(line), "code": code, "error": msg})

    def undefined(self, name, col):
        if name in self.tomb:
            return AtoneError("A-E008", f"{name} was forsaken at line {self.tomb[name][1]}", self.line, col,
                              f"`restore {name}` brings it back with its history")
        known = [n for e in self._envs() for n in e.vars]
        near = [n for n in known if n.lower() == name.lower() or n.startswith(name[:3])][:3]
        return AtoneError("A-E003", f"{name} is not defined", self.line, col,
                          ("did you mean " + ", ".join(near) + "?") if near else "define it with let, fn or fact")

    def _envs(self):
        return [self.globals]

    def debt(self, name, env):
        e = env.find(name)
        d = e.vars[name] if e else None
        if not isinstance(d, Debt):
            raise self.err("A-E004", f"{name} is not a debt", "create one with: owe A -> B $AMT for \"why\" as NAME")
        return d

    def money(self, v, where):
        v = un(v)
        if not isinstance(v, Money):
            raise self.err("A-E004", f"{where} needs money, found {tname(v)}", "write money as $1,234.56")
        if v.d < 0:
            raise self.err("A-E004", f"{where} needs a positive amount, found {fmt_money(v.d)}",
                           "the direction lives in who owes whom")
        return v.d

    def print_ledger(self):
        if not self.debts:
            self.emit("ledger: no debts")
            return
        self.emit("ledger:")
        for d in self.debts:
            paid, borne, forg = d.total("paid"), d.total("borne"), d.total("forgiven")
            line = (f"  {d.name}: {d.debtor} owes {d.creditor} {fmt_money(d.amount)}"
                    + (f" for {d.reason}" if d.reason else "")
                    + f" · paid {fmt_money(paid)} · borne {fmt_money(borne)} · forgiven {fmt_money(forg)}"
                    + f" · outstanding {fmt_money(d.outstanding())}")
            self.emit(line, {"debt": d.name, "debtor": d.debtor, "creditor": d.creditor,
                             "amount": fmt_money(d.amount), "paid": fmt_money(paid), "borne": fmt_money(borne),
                             "forgiven": fmt_money(forg), "outstanding": fmt_money(d.outstanding()),
                             "bearers": {k: fmt_money(v) for k, v in d.bearers().items()}})
            for who, amt in d.bearers().items():
                self.emit(f"    {who} bore {fmt_money(amt)} of {d.debtor}'s debt to {d.creditor}")

    def know(self, x, fname):
        f = self.fruits.get(fname)
        if f is None:
            raise self.err("A-E012", f"no fruits classifier named {fname}", "declare one: fruits NAME { \"label\" when ... }")
        fruits = []
        for label_e, cond in f.rules:
            inner = Env(f.env)
            inner.vars["v"] = x
            if truthy(self.ev(cond, inner)):
                fruits.append(show(self.ev(label_e, inner)))
        called = x.label if isinstance(x, Rich) else None
        if not fruits:
            verdict = "NO_FRUIT_READ"
        elif called is None:
            verdict = "UNCALLED"
        elif called in fruits:
            verdict = "FRUITS_MATCH_NAME"
        else:
            verdict = "NAME_CONTRADICTED_BY_FRUITS"
        return {"called": called, "fruits": fruits, "verdict": verdict}

    def int_index(self, key, coll):
        if not (isinstance(key, Fraction) and key.denominator == 1):
            raise self.err("A-E004", f"a list index must be a whole number, found {show(key)}")
        k = int(key)
        if not -len(coll) <= k < len(coll):
            raise self.err("A-E011", f"index {k} is outside a list of {len(coll)}")
        return k

    # -------------------------------------------------------------- expressions
    def ev(self, e, env):
        kind = e[0]
        if kind == "lit":
            v = e[2]
            return list(v) if isinstance(v, list) else v
        if kind == "name":
            found = env.find(e[2])
            if found is None:
                raise self.undefined(e[2], e[3])
            return found.vars[e[2]]
        if kind == "bin":
            op = e[2]
            if op == "and":
                left = self.ev(e[3], env)
                return self.ev(e[4], env) if truthy(left) else left
            if op == "or":
                left = self.ev(e[3], env)
                return left if truthy(left) else self.ev(e[4], env)
            return self.binop(op, self.ev(e[3], env), self.ev(e[4], env))
        if kind == "neg":
            v = self.ev(e[2], env)
            return self.lift(lambda a: self.arith("-", Fraction(0) if not isinstance(a, Money) else Money(0), a), v)
        if kind == "not":
            return not truthy(self.ev(e[2], env))
        if kind == "called":
            v, label = self.ev(e[2], env), show(self.ev(e[3], env))
            return (v if isinstance(v, Rich) else Rich(v)).copy(label=label)
        if kind == "meaning":
            v, depth = self.ev(e[2], env), self.ev(e[3], env)
            return (v if isinstance(v, Rich) else Rich(v)).copy(depth=depth)
        if kind == "call":
            fnv = self.ev(e[2], env)
            args = [self.ev(a, env) for a in e[3]]
            return self.call(fnv, args, e[1])
        if kind == "index":
            coll, key = self.ev(e[2], env), un(self.ev(e[3], env))
            c = un(coll)
            if isinstance(c, list):
                return self.keep(coll, c[self.int_index(key, c)])
            if isinstance(c, str):
                return c[self.int_index(key, c)]
            if isinstance(c, dict):
                if key not in c:
                    raise self.err("A-E011", f"key {show_inner(key)} is not in the map",
                                   "keys(m) lists what is there; has(m, k) tests first")
                return self.keep(coll, c[key])
            raise self.err("A-E004", f"cannot index {tname(c)}")
        if kind == "dot":
            coll = self.ev(e[2], env)
            c = un(coll)
            if isinstance(c, dict) and e[3] in c:
                return self.keep(coll, c[e[3]])
            if isinstance(c, Debt) and e[3] in ("debtor", "creditor", "reason", "name"):
                return getattr(c, e[3])
            if isinstance(c, Debt) and e[3] == "amount":
                return Money(c.amount)
            raise self.err("A-E011", f"{tname(c)} has no field {e[3]}",
                           ("fields: " + ", ".join(map(str, c.keys()))) if isinstance(c, dict) else "")
        if kind == "list":
            return [self.ev(i, env) for i in e[2]]
        if kind == "map":
            return {un(self.ev(k, env)): self.ev(v, env) for k, v in e[2]}
        if kind == "lambda":
            return Function("fn", e[2], e[3], env)
        raise self.err("A-E002", f"unknown expression {kind}")

    def keep(self, parent, child):
        """A field read from a witnessed record keeps the record's witnesses."""
        if isinstance(parent, Rich) and parent.wits and not isinstance(child, Rich):
            return Rich(child, parent.wits, (), None, None, parent.name)
        return child

    def lift(self, fn, *vals):
        out = fn(*[un(v) for v in vals])
        proof = [v for v in vals if isinstance(v, Rich) and v.carries_proof()]
        if proof:
            return Rich(out, basis=tuple(proof))
        return out

    def binop(self, op, a, b):
        if op in ("==", "!="):
            r = values_equal(un(a), un(b))
            return r if op == "==" else not r
        if op in ("<", ">", "<=", ">="):
            x, y = un(a), un(b)
            x, y = (x.d, y.d) if isinstance(x, Money) and isinstance(y, Money) else (x, y)
            try:
                return {"<": x < y, ">": x > y, "<=": x <= y, ">=": x >= y}[op]
            except TypeError:
                raise self.err("A-E004", f"cannot compare {tname(un(a))} with {tname(un(b))}")
        return self.lift(lambda x, y: self.arith(op, x, y), a, b)

    def arith(self, op, x, y):
        tx, ty = type(x), type(y)
        if op == "+" and tx is str and ty is str:
            return x + y
        if op == "+" and tx is list and ty is list:
            return x + y
        if tx is Fraction and ty is Fraction:
            if op in "/%" and y == 0:
                raise self.err("A-E006", "division by zero")
            return {"+": x + y, "-": x - y, "*": x * y, "/": x / y if op == "/" else None,
                    "%": x % y if op == "%" else None}[op]
        if tx is Money and ty is Money:
            if op == "+":
                return Money(x.d + y.d)
            if op == "-":
                return Money(x.d - y.d)
            if op == "/":
                if y.d == 0:
                    raise self.err("A-E006", "division by zero")
                return x.d / y.d
        if tx is Money and ty is Fraction and op in "*/":
            if op == "/" and y == 0:
                raise self.err("A-E006", "division by zero")
            return Money(x.d * y if op == "*" else x.d / y)
        if tx is Fraction and ty is Money and op == "*":
            return Money(x * y.d)
        if tx is date and ty is date and op == "-":
            return Fraction((x - y).days)
        if tx is date and ty is Fraction and op in "+-" and y.denominator == 1:
            return x + timedelta(days=int(y) if op == "+" else -int(y))
        hint = ""
        if Money in (tx, ty) and Fraction in (tx, ty):
            hint = "money and plain numbers do not add; write the amount as $… or use money(x)"
        raise self.err("A-E004", f"cannot {op} {tname(x)} and {tname(y)}", hint)

    def call(self, fnv, args, line):
        f = un(fnv)
        if isinstance(f, Builtin):
            if f.arity is not None and len(args) not in (f.arity if isinstance(f.arity, tuple) else (f.arity,)):
                raise self.err("A-E010", f"{f.name} takes {f.arity} argument(s), given {len(args)}")
            return f.fn(*args)
        if isinstance(f, Function):
            if len(args) != len(f.params):
                raise self.err("A-E010", f"{f.name} takes {len(f.params)} argument(s), given {len(args)}")
            inner = Env(f.env)
            for p, a in zip(f.params, args):
                inner.vars[p] = a
            try:
                self.block(f.body, inner)
            except ReturnSignal as r:
                return r.value
            return None
        if isinstance(f, Fruits):
            if len(args) != 1:
                raise self.err("A-E010", f"fruits {f.name} takes one value")
            return self.know(args[0], f.name)
        raise self.err("A-E004", f"{tname(f)} is not a function")


def values_equal(x, y):
    if isinstance(x, Money) or isinstance(y, Money):
        return isinstance(x, Money) and isinstance(y, Money) and x.d == y.d
    if isinstance(x, list) and isinstance(y, list):
        return len(x) == len(y) and all(values_equal(un(a), un(b)) for a, b in zip(x, y))
    return type(x) is type(y) and x == y if not (isinstance(x, bool) or isinstance(y, bool)) else x is y


def truthy(v):
    v = un(v)
    if v is None or v is False:
        return False
    if isinstance(v, Fraction):
        return v != 0
    if isinstance(v, Money):
        return v.d != 0
    if isinstance(v, (str, list, dict)):
        return len(v) > 0
    return True


def tname(v):
    v = un(v)
    return {Fraction: "number", Money: "money", str: "string", list: "list", dict: "map", date: "date",
            bool: "bool", type(None): "nil", Debt: "debt", Function: "function", Builtin: "function",
            Fruits: "fruits", QState: "superposition"}.get(type(v), type(v).__name__)


def src_text(e):
    k = e[0]
    if k == "name":
        return e[2]
    if k == "lit":
        return show_inner(e[2])
    if k == "dot":
        return f"{src_text(e[2])}.{e[3]}"
    if k == "call":
        return f"{src_text(e[2])}({', '.join(src_text(a) for a in e[3])})"
    if k == "index":
        return f"{src_text(e[2])}[{src_text(e[3])}]"
    if k == "bin":
        return f"{src_text(e[3])} {e[2]} {src_text(e[4])}"
    if k == "neg":
        return f"-{src_text(e[2])}"
    if k in ("called", "meaning"):
        return src_text(e[2])
    return k


def describe_expect(e, interp, env):
    if e[0] == "bin" and e[2] in ("==", "!=", "<", ">", "<=", ">="):
        try:
            left, right = interp.ev(e[3], env), interp.ev(e[4], env)
            return f"{src_text(e)}  (left {show(left)}, right {show(right)})"
        except AtoneError:
            pass
    return src_text(e)


# ------------------------------------------------------------------ builtins
def install_builtins(it):
    g = it.globals.vars

    def B(name, arity=None):
        def deco(fn):
            g[name] = Builtin(name, fn, arity)
            return fn
        return deco

    def err(code, msg, hint=""):
        return AtoneError(code, msg, it.line, 0, hint)

    @B("len", 1)
    def _len(x):
        x = un(x)
        if isinstance(x, (str, list, dict)):
            return Fraction(len(x))
        raise err("A-E004", f"len needs a string, list or map, found {tname(x)}")

    @B("str", 1)
    def _str(x):
        return show(x)

    @B("num", 1)
    def _num(x):
        x = un(x)
        if isinstance(x, Money):
            return x.d
        try:
            return Fraction(str(x).replace(",", "").replace("$", ""))
        except (ValueError, ZeroDivisionError):
            raise err("A-E004", f"cannot read {show_inner(x)} as a number")

    @B("money", 1)
    def _money(x):
        x = un(x)
        if isinstance(x, Money):
            return x
        return Money(_num(x))

    @B("date", 1)
    def _date(x):
        try:
            return date.fromisoformat(show(x))
        except ValueError:
            raise err("A-E004", f"{show_inner(x)} is not a YYYY-MM-DD date")

    @B("contains", 2)
    def _contains(hay, needle):
        h, n = un(hay), un(needle)
        if isinstance(h, str):
            return show(n).lower() in h.lower()
        if isinstance(h, list):
            return any(values_equal(un(i), n) for i in h)
        if isinstance(h, dict):
            return n in h
        raise err("A-E004", f"contains needs a string, list or map, found {tname(h)}")

    @B("upper", 1)
    def _upper(x):
        return show(x).upper()

    @B("lower", 1)
    def _lower(x):
        return show(x).lower()

    @B("abs", 1)
    def _abs(x):
        return it.lift(lambda v: Money(abs(v.d)) if isinstance(v, Money) else abs(v), x)

    @B("sum", 1)
    def _sum(xs):
        items = un(xs)
        if not isinstance(items, list):
            raise err("A-E004", "sum needs a list")
        total = None
        for i in items:
            total = i if total is None else it.binop("+", total, i)
        return total if total is not None else Fraction(0)

    @B("keys", 1)
    def _keys(m):
        m = un(m)
        if not isinstance(m, dict):
            raise err("A-E004", "keys needs a map")
        return list(m.keys())

    @B("has", 2)
    def _has(m, k):
        m = un(m)
        return isinstance(m, dict) and un(k) in m

    @B("push", 2)
    def _push(xs, v):
        lst = un(xs)
        if not isinstance(lst, list):
            raise err("A-E004", "push needs a list")
        lst.append(v)
        return xs

    @B("range", (1, 2))
    def _range(a, b=None):
        lo, hi = (Fraction(0), un(a)) if b is None else (un(a), un(b))
        return [Fraction(i) for i in range(int(lo), int(hi))]

    @B("round", 1)
    def _round(x):
        """Round money to the cent (half away from zero) — the only place Zeta rounds, and only when asked."""
        v = un(x)
        d = v.d if isinstance(v, Money) else Fraction(v)
        c = abs(d) * 100
        r = int(c) + (1 if c - int(c) >= Fraction(1, 2) else 0)
        r = Fraction(r, 100) * (-1 if d < 0 else 1)
        return Money(r) if isinstance(v, Money) else r

    @B("value", 1)
    def _value(x):
        return un(x)

    @B("witnesses", 1)
    def _witnesses(x):
        if not isinstance(x, Rich):
            return []
        if x.basis:
            out = []
            for b in x.basis:
                out.extend(w for w in _witnesses(b) if w not in out)
            return out
        return list(x.wits)

    @B("witness", None)
    def _witness(x, *srcs):
        base = x if isinstance(x, Rich) else Rich(x)
        return base.copy(wits=tuple(base.wits) + tuple(show(s) for s in srcs), basis=())

    @B("established", 1)
    def _established(x):
        return established(x)[0]

    @B("family", 1)
    def _family(s):
        return family(show(s))

    @B("label", 1)
    def _label(x):
        return x.label if isinstance(x, Rich) else None

    @B("surface", 1)
    def _surface(x):
        return un(x)

    @B("depth", 1)
    def _depth(x):
        return x.depth if isinstance(x, Rich) else None

    @B("know", 2)
    def _know(x, f):
        name = un(f).name if isinstance(un(f), Fruits) else show(f)
        return it.know(x, name)

    @B("outstanding", 1)
    def _outstanding(d):
        d = un(d)
        if not isinstance(d, Debt):
            raise err("A-E004", "outstanding needs a debt")
        return Money(d.outstanding())

    @B("borne", 1)
    def _borne(d):
        d = un(d)
        if not isinstance(d, Debt):
            raise err("A-E004", "borne needs a debt")
        return Money(d.total("borne"))

    @B("paid", 1)
    def _paid(d):
        d = un(d)
        if not isinstance(d, Debt):
            raise err("A-E004", "paid needs a debt")
        return Money(d.total("paid"))

    @B("forgiven", 1)
    def _forgiven(d):
        d = un(d)
        if not isinstance(d, Debt):
            raise err("A-E004", "forgiven needs a debt")
        return Money(d.total("forgiven"))

    @B("bearers", 1)
    def _bearers(d):
        d = un(d)
        if not isinstance(d, Debt):
            raise err("A-E004", "bearers needs a debt")
        return {k: Money(v) for k, v in d.bearers().items()}

    @B("borne_by", 1)
    def _borne_by(who):
        w = show(who)
        return Money(sum((d.bearers().get(w, Fraction(0)) for d in it.debts), Fraction(0)))

    @B("debts", 0)
    def _debts():
        return list(it.debts)

    @B("confessions", 0)
    def _confessions():
        return [dict(c) for c in it.confessions]

    @B("history", 1)
    def _history(name):
        return [dict(h) for h in it.history.get(show(name), [])]

    @B("seek", 2)
    def _seek(items, target):
        """The lost sheep (Luke 15:4): which one item — failing that, which pair — leaves the rest summing to target."""
        xs = un(items)
        t = un(target)
        if not isinstance(xs, list):
            raise err("A-E004", "seek needs a list of amounts")
        vals = [un(x) for x in xs]
        total = sum((v.d if isinstance(v, Money) else v for v in vals), Fraction(0))
        tv = t.d if isinstance(t, Money) else t
        gap = total - tv
        singles = [[xs[i]] for i, v in enumerate(vals) if (v.d if isinstance(v, Money) else v) == gap]
        if singles:
            return singles
        out = []
        for i in range(len(vals)):
            for j in range(i + 1, len(vals)):
                a = vals[i].d if isinstance(vals[i], Money) else vals[i]
                b = vals[j].d if isinstance(vals[j], Money) else vals[j]
                if a + b == gap:
                    out.append([xs[i], xs[j]])
        return out

    # ---- quantum: superpose, amplify (exact Grover), probs, measure
    @B("superpose", 1)
    def _superpose(xs):
        items = un(xs)
        if not isinstance(items, list) or not items:
            raise err("A-E004", "superpose needs a non-empty list")
        return QState(items)

    @B("amplify", (2, 3))
    def _amplify(st, pred, k=None):
        q = un(st)
        if not isinstance(q, QState):
            raise err("A-E004", "amplify needs a superposition", "make one with superpose([...])")
        marked = [i for i, x in enumerate(q.items) if truthy(it.call(pred, [x], it.line))]
        n, m = len(q.items), len(marked)
        if k is None:
            import math
            k = 0 if m in (0, n) else int(math.floor(math.pi / (4 * math.asin(math.sqrt(m / n)))))
        else:
            k = int(un(k))
        a = list(q.amps)
        for _ in range(k):
            for i in marked:
                a[i] = -a[i]
            mean = sum(a, Fraction(0)) / n
            a = [2 * mean - x for x in a]
        return QState(q.items, a, q.iterations + k, m)

    @B("probs", 1)
    def _probs(st):
        q = un(st)
        if not isinstance(q, QState):
            raise err("A-E004", "probs needs a superposition")
        out = {}
        for x, p in zip(q.items, q.probs()):
            key = un(x)
            key = key if isinstance(key, (str, Fraction, bool)) or key is None else show(key)
            out[key] = out.get(key, Fraction(0)) + p
        return out

    @B("measure", (1, 2))
    def _measure(st, seed=None):
        import random as _r
        q = un(st)
        if not isinstance(q, QState):
            raise err("A-E004", "measure needs a superposition")
        rng = _r.Random(None if seed is None else show(seed))
        r, acc = Fraction(rng.random()), Fraction(0)
        for x, p in zip(q.items, q.probs()):
            acc += p
            if r < acc:
                return x
        return q.items[-1]

    # ---- graft: a dialect calls its parent languages through their own JSON interfaces
    def _need_parent(name):
        if it.dialect is None:
            raise err("A-E013", f"{name} is not grafted here", "parent calls work inside a vine branch (a dialect)")
        if name not in it.dialect["parents"]:
            raise err("A-E013", f"{name} is not a parent of {it.dialect['name']}",
                      "parents: " + ", ".join(it.dialect["parents"]))
        return it.dialect["bridges"].get(name, {})

    def _call(cmd, what, strict=False):
        import subprocess
        try:
            root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            p = subprocess.run([sys.executable, "-X", "utf8", *cmd], cwd=root,
                               capture_output=True, encoding="utf-8", timeout=180)
        except (OSError, subprocess.TimeoutExpired) as e:
            raise err("A-E014", f"{what}: {e}")
        if p.returncode not in ((0,) if strict else (0, 1)) or not p.stdout.strip():
            raise err("A-E014", f"{what} exited {p.returncode}: {(p.stderr or p.stdout).strip()[:200]}")
        try:
            return from_json(json.loads(p.stdout))
        except ValueError:
            return p.stdout.strip()

    @B("parents", 0)
    def _parents():
        return list(it.dialect["parents"]) if it.dialect else []

    @B("parent_describe", 1)
    def _parent_describe(name):
        n = show(name)
        br = _need_parent(n)
        return _call(br["describe_cmd"], f"{n} describe")

    @B("parent_run", 2)
    def _parent_run(name, source):
        import tempfile
        n = show(name)
        br = _need_parent(n)
        if not br.get("run"):
            raise err("A-E014", f"{n} has no JSON run interface", "use parent_describe, or graft a language that runs")
        ext = {"surd": ".surd", "tally": ".tly", "logos": ".logos", "zeta": ".zeta", "rico": ".rico",
               "warrant": ".wrt"}.get(n, ".txt")
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=ext, delete=False) as f:
            f.write(show(source))
            path = f.name
        try:
            return _call([path if a == "{file}" else a for a in br["run"]], f"{n} run")
        finally:
            os.unlink(path)

    @B("parent_example", 1)
    def _parent_example(name):
        n = show(name)
        br = _need_parent(n)
        if not (br.get("run") and br.get("example")):
            raise err("A-E014", f"{n} has no runnable example in this edition")
        return _call([br["example"] if a == "{file}" else a for a in br["run"]], f"{n} run {os.path.basename(br['example'])}", strict=True)

    @B("parent_bridge", 1)
    def _parent_bridge(name):
        return from_json(_need_parent(show(name)))

    @B("parent_eval", 2)
    def _parent_eval(name, expr):
        n = show(name)
        br = _need_parent(n)
        if not br.get("eval"):
            raise err("A-E014", f"{n} has no one-expression interface")
        return _call([show(expr) if a == "{expr}" else a for a in br["eval"]], f"{n} eval")

def from_json(x):
    if isinstance(x, bool) or x is None or isinstance(x, str):
        return x
    if isinstance(x, (int, float)):
        return Fraction(str(x))
    if isinstance(x, list):
        return [from_json(i) for i in x]
    if isinstance(x, dict):
        return {k: from_json(v) for k, v in x.items()}
    return str(x)


# ------------------------------------------------------------------ describe
DESCRIBE = {
    "language": "Zeta", "formerly": "Atone", "version": VERSION, "file_extension": ".zeta",
    "one_idea": "the teachings of Jesus Christ as language rules: witnesses establish, debts record who bore them, "
                "things are known by their fruits, errors are forgiven under grace and recorded",
    "statements": {
        "let x = e": "bind", "x = e": "rebind (history keeps every value)",
        "fn name(a, b) { ... }": "function; fn(a) { ... } is a closure value", "return e": "",
        "if c { } else { }": "", "while c { }": "", "for x in list { }": "",
        "print a, b": "", "expect e": "known-answer test; a false expect halts the run",
        "fact x = e by \"W1\", \"W2\"": "a value with witnesses (2 Cor 13:1)",
        "judge x": "ESTABLISHED (two witnesses, two families; or every fact under it established) or AWAITS_SECOND_WITNESS",
        "owe A -> B $AMT for \"why\" as d": "a debt", "pay P on d $AMT [by \"W\"]": "PAID if P is the debtor, BORNE if anyone else",
        "forgive d [$AMT]": "the creditor forgives (all outstanding if no amount)", "ledger": "every debt: paid · borne · forgiven · outstanding, and who bore what",
        "fruits NAME { \"label\" when <expr of v> ... }": "a classifier by deeds (Matt 7:16)",
        "discern x with NAME": "FRUITS_MATCH_NAME · NAME_CONTRADICTED_BY_FRUITS · UNCALLED · NO_FRUIT_READ",
        "grace { ... }": "each failing statement inside is forgiven, recorded, and the block goes on",
        "forsake x": "unbind, kept in the tomb", "restore x": "bring it back",
        "reveal x": "surface and meaning of a parable",
    },
    "operators": {"x called \"label\"": "what it is called", "a meaning b": "parable: surface a, depth b",
                  "+ - * / %": "exact; money stays money", "== != < > <= >=": "", "and or not": ""},
    "builtins": ["len", "str", "num", "money", "date", "contains", "upper", "lower", "abs", "sum", "keys", "has",
                 "push", "range", "round", "value", "witnesses", "witness", "established", "family", "label",
                 "surface", "depth", "know", "outstanding", "paid", "borne", "forgiven", "bearers", "borne_by",
                 "debts", "confessions", "history", "seek",
                 "superpose", "amplify", "probs", "measure", "parents", "parent_describe", "parent_run", "parent_eval",
                 "parent_example", "parent_bridge"],
    "quantum": "superpose(list) -> amplify(state, fn) runs exact Grover (amplitudes a/sqrt(N), a rational) -> "
               "probs(state) exact -> measure(state, seed)",
    "errors": ERRORS,
}


# ------------------------------------------------------------------ selftest
SELFTEST = [
    # (name, program, expected stdout lines or None, expected error code or None)
    ("exact arithmetic", "print 1/3 + 1/6, 1/3\nprint 0.1 + 0.2 == 0.3", ["0.5 1/3", "true"], None),
    ("money", "print $500.75 - $200.00\nprint $10.00 / 4\nprint -$5.5", ["$300.75", "$2.50", "-$5.50"], None),
    ("money and number refuse to add", "print $5.00 + 1", None, "A-E004"),
    ("dates", "print 2030-04-17 - 2030-03-01\nprint 2030-03-01 + 47", ["47", "2030-04-17"], None),
    ("closures", "fn adder(n) { return fn(x) { return x + n } }\nlet add5 = adder(5)\nprint add5(10)", ["15"], None),
    ("recursion", "fn f(n) { if n <= 1 { return 1 } return n * f(n - 1) }\nprint f(20)", ["2432902008176640000"], None),
    ("loops and lists", "let xs = []\nfor i in range(4) { push(xs, i * i) }\nprint xs, sum(xs)", ["[0, 1, 4, 9] 14"], None),
    ("maps and fields", 'let m = {"a": $1.00, "b": 2}\nm.c = "x"\nprint m.a, m["b"], len(m)', ["$1.00 2 3"], None),
    ("while", "let i = 0\nwhile i < 3 { i = i + 1 }\nprint i", ["3"], None),
    ("one family awaits a second witness",
     'fact w = $5.00 by "VENDOR_0014", "VENDOR_0015"\nprint established(w)\njudge w', ["false", None], None),
    ("two families establish",
     'fact w = $5.00 by "VENDOR_0014", "RECEIPT_0123"\nprint established(w)', ["true"], None),
    ("derived needs every basis",
     'fact a = $5.00 by "VENDOR_1", "RECEIPT_2"\nfact b = $1.00 by "VENDOR_3"\nlet c = a + b\nprint c, established(c), established(a + a)',
     ["$6.00 false true"], None),
    ("witnesses travel", 'fact a = $5.00 by "VENDOR_1", "RECEIPT_2"\nfact b = $1.00 by "DELIVERY_3"\nprint witnesses(a - b)',
     ['["VENDOR_1", "RECEIPT_2", "DELIVERY_3"]'], None),
    ("family", 'print family("RECEIPT_0012"), family("VENDOR_0014"), family("Owner notes")',
     ["RECEIPT VENDOR owner"], None),
    ("paid vs borne",
     'owe "Builder" -> "Vendor" $100.00 for "lumber" as d\npay "Builder" on d $30.00\npay "Owner" on d $50.00\n'
     'print paid(d), borne(d), outstanding(d), bearers(d), borne_by("Owner")',
     ['$30.00 $50.00 $20.00 {"Owner": $50.00} $50.00'], None),
    ("forgive", 'owe "A" -> "B" $10.00 as d\nforgive d $4.00\nprint forgiven(d), outstanding(d)', ["$4.00 $6.00"], None),
    ("overpay refused", 'owe "A" -> "B" $10.00 as d\npay "A" on d $11.00', None, "A-E007"),
    ("fruits contradict the name",
     'fruits use { "land" when contains(v.desc, "LAND")\n "lumber" when contains(v.desc, "LUMBER") }\n'
     'let w = {"desc": "PAYMENT FOR LAND"} called "construction"\nprint know(w, use).verdict, know(w, use).fruits',
     ['NAME_CONTRADICTED_BY_FRUITS ["land"]'], None),
    ("fruits match", 'fruits use { "land" when contains(v, "LAND") }\nprint know("DEMO LAND" called "land", use).verdict',
     ["FRUITS_MATCH_NAME"], None),
    ("grace forgives and records",
     'grace {\n  print 1\n  print 1 / 0\n  print 2\n}\nprint len(confessions()), confessions()[0].code',
     ["1", "2", "1 A-E006"], None),
    ("outside grace an error halts", "print 1 / 0", None, "A-E006"),
    ("parable", 'let p = "the lot" meaning "the land behind it"\nprint p, depth(p), surface(p) == "the lot"',
     ["the lot the land behind it true"], None),
    ("forsake and restore", "let x = 5\nx = 6\nforsake x\nrestore x\nprint x, len(history(\"x\"))", ["6 3"], None),
    ("forsaken names say so", "let x = 5\nforsake x\nprint x", None, "A-E008"),
    ("seek the lost sheep", "print seek([$10.00, $20.00, $7.00, $3.00], $33.00)", ["[[$7.00]]"], None),
    ("seek a pair", "print seek([$10.00, $20.00, $7.00, $3.00], $27.00)", ["[[$10.00, $3.00]]"], None),
    ("expect fails loudly", "expect 1 + 1 == 3", None, "A-E005"),
    ("undefined name has a hint", "print nmae", None, "A-E003"),
    ("parse error has a position", "let = 5", None, "A-E002"),
    ("exact Grover: 1 of 8 after 2 steps is 121/128",
     'let s = amplify(superpose(["a", "b", "c", "d", "e", "f", "g", "h"]), fn(x) { return x == "f" })\n'
     'print probs(s)["f"], probs(s)["a"]', ["0.9453125 0.0078125"], None),
    ("Grover: 1 of 4 is certain after 1 step", 'let s = amplify(superpose(["a", "b", "c", "d"]), fn(x) { return x == "c" })\n'
     'print measure(s, 7), probs(s)["c"]', ["c 1"], None),
    ("parent calls need a graft", 'print parent_describe("tally")', None, "A-E013"),
]

def run_capture(src):
    import io
    buf = io.StringIO()
    it = Interp(out=buf)
    try:
        it.run(src)
        return buf.getvalue().splitlines(), None, it
    except AtoneError as e:
        return buf.getvalue().splitlines(), e, it


def selftest():
    cases = SELFTEST
    ok = 0
    for name, prog, want, want_err in cases:
        lines, e, _ = run_capture(prog)
        good = True
        if want_err:
            good = e is not None and e.code == want_err and bool(e.hint or e.code in ("A-E005", "A-E006"))
        else:
            good = e is None and want is not None and len(lines) == len(want) and all(
                w is None or w == l for w, l in zip(want, lines))
        ok += good
        if not good:
            print(f"FAIL {name}: got {lines} {e.as_dict() if e else ''}")
    # every example program must run clean
    here = os.path.dirname(os.path.abspath(__file__))
    ex_dir = os.path.join(here, "examples")
    exs = sorted(f for f in os.listdir(ex_dir) if f.endswith(".zeta")) if os.path.isdir(ex_dir) else []
    for f in exs:
        with open(os.path.join(ex_dir, f), encoding="utf-8") as fh:
            lines, e, _ = run_capture(fh.read())
        good = e is None
        ok += good
        if not good:
            print(f"FAIL example {f}: {e}")
    total = len(cases) + len(exs)
    print(f"selftest {ok}/{total}")
    return ok == total


# ------------------------------------------------------------------ CLI
def run_program(path, as_json, dialect=None):
    import io
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    try:
        it = Interp(out=io.StringIO() if as_json else sys.stdout, dialect=dialect)
        it.run(src)
    except AtoneError as e:
        if as_json:
            print(json.dumps({"ok": False, "error": e.as_dict()}))
        else:
            print(str(e), file=sys.stderr)
        return 1
    if as_json:
        print(json.dumps({"ok": True, "records": it.records, "expects": it.expects,
                          "confessions": to_json(it.confessions)}, indent=2))
    else:
        tail = []
        if it.expects[1]:
            tail.append(f"expect {it.expects[0]}/{it.expects[1]}")
        if it.confessions:
            tail.append(f"grace: {len(it.confessions)} forgiven (confessions() lists them)")
        if tail:
            print("— " + " · ".join(tail))
    return 0


def dialect_main(dialect_path, argv):
    """Entry point for a vine branch: a Zeta dialect grafted on its parent languages."""
    with open(dialect_path, encoding="utf-8") as f:
        d = json.load(f)
    name = d["name"]
    if not argv or argv[0] in ("-h", "--help", "help"):
        print(f"{name} {d.get('version', '0.1.0')} — generation {d['generation']} branch of the Zeta vine, grafted on "
              f"{', '.join(d['parents'])}.\n  {d['lower']} run FILE [--json] · check FILE · selftest · describe [--json] · version")
        return 0
    cmd, rest = argv[0], argv[1:]
    if cmd == "version":
        print(f"{name} 0.1.0 (Zeta {VERSION})")
        return 0
    if cmd == "describe":
        out = {"language": name, "dialect_of": "Zeta", "zeta_version": VERSION, "atone_version": VERSION, **d, "zeta": DESCRIBE}
        ab = load_ability(os.path.dirname(os.path.abspath(dialect_path)))
        if ab is not None:
            out["ability"] = ab.ABOUT
        print(json.dumps(out, indent=None if "--json" in rest else 1))
        return 0
    if cmd == "check":
        with open(rest[0], encoding="utf-8") as fh:
            parse(fh.read())
        print(f"{rest[0]}: parses")
        return 0
    if cmd == "run":
        if not rest:
            print(f"usage: {d['lower']} run FILE", file=sys.stderr)
            return 2
        return run_program(rest[0], "--json" in rest, d)
    if cmd == "selftest":
        import io
        ok = total = 0
        for p in d["parents"]:
            total += 1
            buf = io.StringIO()
            try:
                Interp(out=buf, dialect=d).run(f'print len(str(parent_describe("{p}"))) > 0')
                good = buf.getvalue().strip() == "true"
            except AtoneError as e:
                good = False
                print(f"FAIL parent {p}: {e}")
            ok += good
        ex_dir = os.path.join(os.path.dirname(os.path.abspath(dialect_path)), "examples")
        for f in sorted(os.listdir(ex_dir)) if os.path.isdir(ex_dir) else []:
            total += 1
            buf = io.StringIO()
            try:
                with open(os.path.join(ex_dir, f), encoding="utf-8") as fh:
                    Interp(out=buf, dialect=d).run(fh.read())
                ok += 1
            except AtoneError as e:
                print(f"FAIL example {f}: {e}")
        print(f"selftest {ok}/{total}")
        return 0 if ok == total else 1
    print(f"{d['lower']}: unknown command {cmd!r} (run, check, selftest, describe, version)", file=sys.stderr)
    return 2


def main(argv):
    if not argv or argv[0] in ("-h", "--help", "help"):
        print(__doc__)
        return 0
    cmd, rest = argv[0], argv[1:]
    if cmd == "version":
        print(f"Zeta {VERSION}")
        return 0
    if cmd == "selftest":
        return 0 if selftest() else 1
    if cmd == "describe":
        ab = load_ability(os.path.dirname(os.path.abspath(__file__)))
        print(json.dumps(dict(DESCRIBE, ability=ab.ABOUT) if ab is not None else DESCRIBE, indent=None if "--json" in rest else 2))
        return 0
    if cmd in ("run", "check"):
        if not rest:
            print(f"usage: zeta {cmd} FILE", file=sys.stderr)
            return 2
        path = rest[0]
        with open(path, encoding="utf-8") as fh:
            src = fh.read()
        as_json = "--json" in rest
        try:
            if cmd == "check":
                parse(src)
                print(f"{path}: parses")
                return 0
            import io
            it = Interp(out=io.StringIO() if as_json else sys.stdout)
            it.run(src)
        except AtoneError as e:
            if as_json:
                print(json.dumps({"ok": False, "error": e.as_dict()}))
            else:
                print(str(e), file=sys.stderr)
            return 1
        if as_json:
            print(json.dumps({"ok": True, "records": it.records, "expects": it.expects,
                              "confessions": to_json(it.confessions)}, indent=2))
        else:
            tail = []
            if it.expects[1]:
                tail.append(f"expect {it.expects[0]}/{it.expects[1]}")
            if it.confessions:
                tail.append(f"grace: {len(it.confessions)} forgiven (confessions() lists them)")
            if tail:
                print("— " + " · ".join(tail))
        return 0
    if cmd == "repl":
        it = Interp()
        print(f"Zeta {VERSION} — ctrl-D ends")
        buf = []
        while True:
            try:
                line = input("... " if buf else "zeta> ")
            except EOFError:
                print()
                return 0
            buf.append(line)
            src = "\n".join(buf)
            if src.count("{") > src.count("}"):
                continue
            buf = []
            try:
                it.block(parse(src), it.globals)
            except AtoneError as e:
                print(e)
    print(f"zeta: unknown command {cmd!r} (run, check, selftest, describe, repl, version)", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    sys.exit(main(sys.argv[1:]))
