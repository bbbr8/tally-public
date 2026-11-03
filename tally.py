#!/usr/bin/env python3
"""Tally — a general-purpose programming language with exact money, dates and source tracking.

    tally FILE.tly            run a program
    tally test FILE.tly       run the program's `test "…" { … }` blocks
    tally check FILE.tly      static check: undefined names, redefinitions, unused lets, unreachable code
    tally eval 'EXPR' [--prelude FILE]   evaluate one expression
    tally describe [--json] [--verify]    the language reference (every built-in, verified examples)
    … --json                  run / test / check / eval print one JSON object (schema tally.<cmd>.v1)
    tally serve               a JSON-lines session for agents: one request object per line, one response per line
    tally doc FILE [--json]   a program's API without running it: functions, records, rules, facts, tests
    tally check FILE --strict also warn on top-level functions without a doc string or full types
    tally                     interactive prompt (REPL)
    tally --selftest          the interpreter's own tests
    tally ... --max-steps N   bound execution steps (shared across imports and inference)
    tally --help              commands and usage

The language in one screen:

    let x = 10                      # variables; numbers are exact decimals
    let pay = $55.00            # money: exact cents, never a float
    let day = @2040-02-13           # dates; day - @2040-02-03 == 10, day + 3 is a date
    fn double(n) { return n * 2 }   # functions, recursion, closures
    let sq = fn(n) => n * n         # function expressions
    for i in 1..5 { print(i) }      # ranges (end excluded), lists, maps, strings
    while x > 0 { x -= 1 }
    if x == 0 { print("zero") } else { print("not zero") }
    let m = {name: "Draw 3", amount: $123.45}
    print("{m.name}: {m.amount}")   # string interpolation
    try { throw "bad" } catch e { print(e) }
    let wire = $1,234.56 from "DOC_00164"      # a value that carries its source
    let total = wire + $10.00 from "fee note"
    print(sources(total))           # ["DOC_00164", "fee note"]
    import "lib.tly" as lib         # modules
    test "adds" { assert(1 + 1 == 2) }

Conditions must be true/false (no silent truthiness). Money only adds to money; money times a number
must land on whole cents or it is an error (use round_money). Every error names its line and column.
"""
import csv
import datetime as _dt
import json as _json
import os
import re
import sqlite3
import sys
from decimal import Decimal, getcontext, InvalidOperation, ROUND_HALF_EVEN

getcontext().prec = 50
if __name__ == "__main__":
    sys.modules["tally"] = sys.modules[__name__]  # tally_logic imports `tally`; it must be this module
sys.setrecursionlimit(20000)
VERSION = "0.28"


# ================================================================ errors
ERROR_CODES = [  # (code, pattern in the message) — first match wins; every error has a code an agent can branch on
    ("E_LIMIT", r"execution step limit"),
    ("E_QUANTUM", r"quantum:"),
    ("E_CONTRACT", r": (requires|ensures) .* (failed|could not be evaluated|is not true or false)"),
    ("E_MONEY", r"whole cents|money and number"),
    ("E_UNDEFINED", r"is not defined"),
    ("E_ARITY", r"takes .* argument|takes \d+\.\.\d+ values"),
    ("E_TYPE", r"must be |must return |cannot apply|cannot compare|expected (a|an) |is not a function|has no fields|"
               r"cannot index|cannot loop|a condition must be true or false"),
    ("E_ZERO", r"division by zero"),
    ("E_FIELD", r"has no field|no field or method|the map has no field|is not in the map"),
    ("E_INDEX", r"outside the list|a list index"),
    ("E_DUPLICATE", r"already defined|appears twice"),
    ("E_REQUEST", r"unknown op|request (?:is missing|op |code |pattern |name |path |max_steps |max_nodes )|not a JSON request|batch needs|rollback needs|a batch holds|checkpoint limit"),
    ("E_SYNTAX", r"expected|unexpected|unclosed|missing|unbalanced|not a real date|predicate starts with"),
    ("E_DATA", r"not present on this machine|unknown store|no store named|IS present|readonly|no such table"),
    ("E_LOGIC", r"have no order|did not settle|not bound by any condition|use query\(\)"),
    ("E_MATCH", r"no case matched"),
    ("E_IO", r"exists; set TALLY_ALLOW_OVERWRITE|No such file|no module at|import cycle"),
]


def error_code(msg):
    for code, pat in ERROR_CODES:
        if re.search(pat, msg):
            return code
    return "E_RUNTIME"


class TallyError(Exception):
    def __init__(self, msg, line=0, col=0, path="", hint=None):
        super().__init__(msg)
        self.msg, self.line, self.col, self.path, self.hint = msg, line, col, path, hint

    @property
    def code(self):
        return error_code(self.msg)

    def to_map(self):
        return {"code": self.code, "message": self.msg, "line": self.line, "col": self.col, "path": self.path,
                "hint": self.hint, "trace": [{"function": n, "called_at_line": l}
                                             for n, l in reversed(getattr(self, "trace", None) or [])]}

    def __str__(self):
        where = f"{self.path}:" if self.path else ""
        hint = f" (hint: {self.hint})" if self.hint else ""
        return f"{where}{self.line}:{self.col}: {self.msg}{hint}"


class LimitError(TallyError):
    """Execution exhaustion escapes language try/catch so it cannot be suppressed."""


class Budget:
    def __init__(self, limit=None):
        self.limit = limit
        self.steps = 0

    def tick(self, path="", node=None):
        self.steps += 1
        if self.limit is not None and self.steps > self.limit:
            raise LimitError(f"execution step limit {self.limit} exceeded", getattr(node, "line", 0),
                             getattr(node, "col", 0), path, "increase --max-steps for a trusted workload")


class Thrown(Exception):
    def __init__(self, value, line=0, col=0):
        super().__init__(repr(value))
        self.value, self.line, self.col = value, line, col


class ReturnSignal(Exception):
    def __init__(self, value):
        self.value = value


class BreakSignal(Exception):
    pass


class ContinueSignal(Exception):
    pass


# ================================================================ lexer
KEYWORDS = {"let", "fn", "return", "if", "else", "while", "for", "in", "break", "continue", "true", "false",
            "nil", "and", "or", "not", "try", "catch", "throw", "import", "as", "test", "from", "record",
            "match", "case", "fact", "rule", "when", "retract", "suppose", "then", "unless", "alias"}

TOKEN_RE = re.compile(r"""
  (?P<ws>[ \t\r]+)
| (?P<comment>\#[^\n]*)
| (?P<nl>\n)
| (?P<money>\$(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d{1,2})?(?![\d.]))
| (?P<date>@\d{4}-\d{2}-\d{2})
| (?P<number>\d[\d_]*(?:\.\d+)?)
| (?P<string>"(?:[^"\\]|\\.)*")
| (?P<ident>[A-Za-z_][A-Za-z0-9_]*)
| (?P<op>\|>|=>|->|\.\.|==|!=|<=|>=|\+=|-=|\*=|/=|[-+*/%<>=(){}\[\],.:;?])
""", re.X | re.S)


def scan_string(src, i, line, col, path):
    """end index of the string starting at src[i] == '"'. Quotes inside a {…} interpolation nest."""
    j, depth = i + 1, 0
    while j < len(src):
        c = src[j]
        if c == "\\":
            j += 2
            continue
        if c == '"' and depth == 0:
            return j + 1
        if c == '"':
            j = scan_string(src, j, line, col, path)
            continue
        if c == "{":
            depth += 1
        elif c == "}" and depth:
            depth -= 1
        j += 1
    raise TallyError("unclosed string", line, col, path)


class Tok:
    __slots__ = ("kind", "val", "line", "col")

    def __init__(self, kind, val, line, col):
        self.kind, self.val, self.line, self.col = kind, val, line, col

    def __repr__(self):
        return f"{self.kind}:{self.val!r}"


NO_NEWLINE_AFTER = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "=", "+=", "-=", "*=", "/=",
                    ",", ".", "..", "=>", "->", ":", "(", "[", "{", "and", "or", "not", "from", "|>"}
CONTINUES_NEXT_LINE = re.compile(r"[ \t\r]*(?:\n[ \t\r]*)*(?:\|>|\.[A-Za-z_])")


def lex(src, path=""):
    toks, i, line, line_start, stack = [], 0, 1, 0, []
    while i < len(src):
        if src.startswith('"""', i):
            j = src.find('"""', i + 3)
            if j < 0:
                raise TallyError("unclosed \"\"\" string", line, i - line_start + 1, path)
            body = src[i + 3:j]
            if body.startswith("\n"):
                body = body[1:]
            text = '"' + body.replace("\\", "\\\\").replace('"', '\\"') + '"'
            toks.append(Tok("string", text, line, i - line_start + 1))
            nl_count = src[i:j].count("\n")
            if nl_count:
                line += nl_count
                line_start = i + src[i:j].rfind("\n") + 1
            i = j + 3
            continue
        if src[i] == '"':
            j = scan_string(src, i, line, i - line_start + 1, path)
            text = src[i:j]
            toks.append(Tok("string", text, line, i - line_start + 1))
            nl_count = text.count("\n")
            if nl_count:
                line += nl_count
                line_start = i + text.rfind("\n") + 1
            i = j
            continue
        m = TOKEN_RE.match(src, i)
        if not m:
            raise TallyError(f"unexpected character {src[i]!r}", line, i - line_start + 1, path)
        kind, text = m.lastgroup, m.group()
        col = i - line_start + 1
        if kind == "nl":
            prev = toks[-1] if toks else None
            in_parens = bool(stack) and stack[-1] in "(["
            if not in_parens and prev is not None and prev.kind != "nl" and not (
                    prev.kind in ("op", "kw") and prev.val in NO_NEWLINE_AFTER) and \
                    not CONTINUES_NEXT_LINE.match(src, m.end()):
                toks.append(Tok("nl", "\n", line, col))
            line += 1
            line_start = m.end()
        elif kind in ("ws", "comment"):
            pass
        else:
            if kind == "ident" and text in KEYWORDS:
                kind = "kw"
            if kind == "op" and text in "([{":
                stack.append(text)
            elif kind == "op" and text in ")]}":
                if stack:
                    stack.pop()
            toks.append(Tok(kind, text, line, col))
        i = m.end()
    toks.append(Tok("nl", "\n", line, 0))
    toks.append(Tok("eof", "", line, 0))
    return toks


# ================================================================ AST
class N:
    """AST node: kind, fields, position."""
    __slots__ = ("k", "a", "line", "col")

    def __init__(self, k, a, tok):
        self.k, self.a = k, a
        self.line, self.col = (tok.line, tok.col) if tok is not None else (0, 0)

    def __repr__(self):
        return f"({self.k} {self.a})"


# ================================================================ parser
PREC = {"from": 1, "|>": 1.5, "or": 2, "and": 3, "==": 5, "!=": 5, "<": 5, "<=": 5, ">": 5, ">=": 5, "in": 5,
        "..": 6, "+": 7, "-": 7, "*": 8, "/": 8, "%": 8}


class Parser:
    def __init__(self, toks, path=""):
        self.t, self.i, self.path = toks, 0, path

    # --- token helpers
    def peek(self, k=0):
        return self.t[min(self.i + k, len(self.t) - 1)]

    def at(self, val, kind=None):
        tok = self.peek()
        return tok.val == val and (kind is None or tok.kind == kind) and tok.kind in ("op", "kw")

    def take(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, val):
        tok = self.peek()
        if tok.val != val or tok.kind not in ("op", "kw"):
            raise self.err(f"expected '{val}' but found {self.describe(tok)}", tok)
        return self.take()

    def expect_ident(self):
        tok = self.peek()
        if tok.kind != "ident":
            raise self.err(f"expected a name but found {self.describe(tok)}", tok)
        return self.take()

    def describe(self, tok):
        return "end of file" if tok.kind == "eof" else ("end of line" if tok.kind == "nl" else f"'{tok.val}'")

    def err(self, msg, tok):
        return TallyError(msg, tok.line, tok.col, self.path)

    def skip_nl(self):
        while self.peek().kind == "nl" or self.at(";"):
            self.take()

    def end_block_stmt(self):
        """a statement that ends with a block may be followed by another on the same line."""
        if self.peek().kind == "nl" or self.at(";"):
            self.take()

    def end_stmt(self):
        tok = self.peek()
        if tok.kind == "nl" or self.at(";"):
            self.take()
            return
        if self.at("}") or tok.kind == "eof":
            return
        raise self.err(f"expected end of statement but found {self.describe(tok)}", tok)

    # --- statements
    def program(self):
        stmts = []
        self.skip_nl()
        while self.peek().kind != "eof":
            stmts.append(self.statement())
            self.skip_nl()
        return stmts

    def block(self):
        self.expect("{")
        stmts = []
        self.skip_nl()
        while not self.at("}"):
            if self.peek().kind == "eof":
                raise self.err("missing '}'", self.peek())
            stmts.append(self.statement())
            self.skip_nl()
        self.expect("}")
        return stmts

    def statement(self):
        tok = self.peek()
        if tok.kind == "kw":
            v = tok.val
            if v == "let":
                self.take()
                name = self.expect_ident().val
                self.expect("=")
                e = self.expr()
                self.end_stmt()
                return N("let", (name, e), tok)
            if v == "fn" and self.peek(1).kind == "ident":
                self.take()
                name = self.expect_ident().val
                if self.at("."):
                    self.take()
                    meth = self.expect_ident().val
                    params, body, spec = self.fn_rest()
                    self.end_block_stmt()
                    return N("method", (name, meth, N("fn", (f"{name}.{meth}", params, body, spec), tok)), tok)
                params, body, spec = self.fn_rest()
                self.end_block_stmt()
                return N("let", (name, N("fn", (name, params, body, spec), tok)), tok)
            if v == "record":
                self.take()
                name = self.expect_ident().val
                self.expect("{")
                fields = []
                self.skip_nl()
                while not self.at("}"):
                    fname = self.expect_ident().val
                    default = None
                    if self.at("="):
                        self.take()
                        default = self.expr()
                    fields.append((fname, default))
                    self.skip_nl()
                    if self.at(","):
                        self.take()
                        self.skip_nl()
                self.expect("}")
                self.end_block_stmt()
                return N("record", (name, fields), tok)
            if v == "match":
                return self.match_stmt()
            if v == "fact":
                self.take()
                truth = True
                if self.at("not"):
                    self.take()
                    truth = False
                pred, args = self.fact_head()
                src = None
                if self.at("from"):
                    self.take()
                    src = self.expr(2)
                self.end_stmt()
                return N("fact", (pred, args, truth, src), tok)
            if v == "alias":
                self.take()
                ctok = self.peek()
                if ctok.kind != "string":
                    raise self.err('alias needs a name in quotes: alias "Alex Example" = "Example Company", …', ctok)
                self.take()
                self.expect("=")
                names = []
                while True:
                    ntok = self.peek()
                    if ntok.kind != "string":
                        raise self.err("alias: each other name goes in quotes", ntok)
                    self.take()
                    names.append(unquote(ntok.val, ntok, self.path))
                    if not self.at(","):
                        break
                    self.take()
                self.end_stmt()
                return N("alias", (unquote(ctok.val, ctok, self.path), names), tok)
            if v == "retract":
                self.take()
                pred, args = self.fact_head()
                self.end_stmt()
                return N("retract", (pred, args), tok)
            if v == "rule":
                return self.rule_stmt()
            if v == "suppose":
                self.take()
                body = self.block()
                self.skip_nl_before("then")
                self.expect("then")
                then = self.block()
                self.end_block_stmt()
                return N("suppose", (body, then), tok)
            if v == "if":
                return self.if_stmt()
            if v == "while":
                self.take()
                cond = self.expr()
                body = self.block()
                self.end_block_stmt()
                return N("while", (cond, body), tok)
            if v == "for":
                self.take()
                name = self.expect_ident().val
                name2 = None
                if self.at(","):
                    self.take()
                    name2 = self.expect_ident().val
                self.expect("in")
                it = self.expr()
                body = self.block()
                self.end_block_stmt()
                return N("for", (name, name2, it, body), tok)
            if v == "return":
                self.take()
                e = None
                if not (self.peek().kind in ("nl", "eof") or self.at("}") or self.at(";")):
                    e = self.expr()
                self.end_stmt()
                return N("return", (e,), tok)
            if v in ("break", "continue"):
                self.take()
                self.end_stmt()
                return N(v, (), tok)
            if v == "throw":
                self.take()
                e = self.expr()
                self.end_stmt()
                return N("throw", (e,), tok)
            if v == "try":
                self.take()
                body = self.block()
                self.skip_nl_before("catch")
                self.expect("catch")
                name = self.expect_ident().val
                handler = self.block()
                self.end_block_stmt()
                return N("try", (body, name, handler), tok)
            if v == "import":
                self.take()
                ptok = self.peek()
                if ptok.kind != "string":
                    raise self.err("import needs a file path in quotes", ptok)
                self.take()
                self.expect("as")
                name = self.expect_ident().val
                self.end_stmt()
                return N("import", (unquote(ptok.val, ptok, self.path), name), tok)
            if v == "test":
                self.take()
                ntok = self.peek()
                if ntok.kind != "string":
                    raise self.err("test needs a name in quotes", ntok)
                self.take()
                body = self.block()
                self.end_block_stmt()
                return N("test", (unquote(ntok.val, ntok, self.path), body), tok)
        e = self.expr()
        if self.peek().kind == "op" and self.peek().val in ("=", "+=", "-=", "*=", "/="):
            op = self.take()
            if e.k not in ("name", "index", "field"):
                raise self.err("can only assign to a name, an index or a field", op)
            rhs = self.expr()
            self.end_stmt()
            return N("assign", (e, op.val, rhs), op)
        self.end_stmt()
        return N("expr", (e,), tok)

    def fact_head(self):
        """Pred(arg, arg, …) — the predicate is a capitalised name; args are expressions (or, in rules, variables)."""
        ptok = self.expect_ident()
        if not ptok.val[:1].isupper():
            raise self.err(f"a predicate starts with a capital letter: {ptok.val}", ptok)
        self.expect("(")
        args = []
        while not self.at(")"):
            args.append(self.expr())
            if not self.at(")"):
                self.expect(",")
        self.expect(")")
        return ptok.val, args

    def rule_stmt(self):
        tok = self.expect("rule")
        name = self.expect_ident().val
        self.expect("{")
        self.skip_nl()
        self.expect("when")
        conds = []
        while True:
            self.skip_nl()
            if self.at("not"):
                ntok = self.take()
                pred, args = self.fact_head()
                conds.append({"kind": "neg", "pred": pred, "args": args, "line": ntok.line})
            elif self.at("let"):
                ltok = self.take()
                lname = self.expect_ident().val
                self.expect("=")
                e = self.expr(2)
                conds.append({"kind": "let", "name": lname, "expr": e, "line": ltok.line})
            elif self.peek().kind == "ident" and self.peek().val[:1].isupper() and self.peek(1).val == "(":
                pred, args = self.fact_head()
                conds.append({"kind": "pos", "pred": pred, "args": args, "line": self.peek().line})
            else:
                e = self.expr(2)
                conds.append({"kind": "guard", "expr": e, "line": e.line})
            self.skip_nl()
            if self.at(","):
                self.take()
                continue
            break
        self.skip_nl()
        self.expect("=>")
        concls = []
        while True:
            self.skip_nl()
            truth = True
            if self.at("not"):
                self.take()
                truth = False
            pred, args = self.fact_head()
            concls.append({"pred": pred, "args": args, "truth": truth})
            self.skip_nl()
            if self.at(","):
                self.take()
                continue
            break
        self.skip_nl()
        unless = []
        if self.at("unless"):
            self.take()
            while True:
                self.skip_nl()
                pred, args = self.fact_head()
                unless.append({"pred": pred, "args": args})
                self.skip_nl()
                if self.at(","):
                    self.take()
                    continue
                break
            self.skip_nl()
        self.expect("}")
        self.end_block_stmt()
        return N("rule", (name, conds, concls, unless), tok)

    def match_stmt(self):
        tok = self.expect("match")
        subject = self.expr()
        self.expect("{")
        arms = []
        self.skip_nl()
        while not self.at("}"):
            ctok = self.expect("case")
            pats = [self.pattern()]
            while self.at(","):
                self.take()
                pats.append(self.pattern())
            guard = None
            if self.at("if"):
                self.take()
                guard = self.expr()
            body = self.block()
            arms.append((pats, guard, body, ctok))
            self.skip_nl()
        self.expect("}")
        self.end_block_stmt()
        return N("match", (subject, arms), tok)

    def pattern(self):
        tok = self.peek()
        if tok.kind == "ident" and tok.val == "_":
            self.take()
            return N("pat_any", (), tok)
        if tok.kind == "ident" and self.peek(1).val != "(":
            self.take()
            return N("pat_bind", (tok.val,), tok)
        if tok.kind == "ident" and self.peek(1).val == "(":
            self.take()
            self.take()
            subs = []
            while not self.at(")"):
                subs.append(self.pattern())
                if not self.at(")"):
                    self.expect(",")
            self.expect(")")
            return N("pat_record", (tok.val, subs), tok)
        if tok.kind == "op" and tok.val == "[":
            self.take()
            subs, rest = [], None
            while not self.at("]"):
                if self.at(".."):
                    self.take()
                    rest = self.expect_ident().val
                    break
                subs.append(self.pattern())
                if not self.at("]"):
                    self.expect(",")
            self.expect("]")
            return N("pat_list", (subs, rest), tok)
        return N("pat_lit", (self.expr(6),), tok)

    def skip_nl_before(self, word):
        j = self.i
        while self.t[j].kind == "nl":
            j += 1
        if self.t[j].val == word:
            self.i = j

    def if_stmt(self):
        tok = self.expect("if")
        cond = self.expr()
        then = self.block()
        other = None
        self.skip_nl_before("else")
        if self.at("else"):
            self.take()
            if self.at("if"):
                other = [self.if_stmt()]
                return N("if", (cond, then, other), tok)
            other = self.block()
        self.end_block_stmt()
        return N("if", (cond, then, other), tok)

    def type_name_tok(self):
        tok = self.peek()
        if tok.kind not in ("ident", "kw"):
            raise self.err(f"expected a type name but found {self.describe(tok)}", tok)
        self.take()
        name = tok.val
        while self.at(".") and self.peek(1).kind == "ident":  # a record type from a module: cb.Party
            self.take()
            name += "." + self.take().val
        if self.at("?"):
            self.take()
            name += "?"
        return name

    def fn_rest(self):
        """(a, b: money, c: date = @2030-01-01) -> money { "doc" … }  — types, defaults, return type, doc string"""
        self.expect("(")
        params, spec = [], {"types": {}, "defaults": {}, "ret": None, "doc": None, "requires": [], "ensures": []}
        while not self.at(")"):
            name = self.expect_ident().val
            if name in params:
                raise self.err(f"parameter '{name}' appears twice", self.t[self.i - 1])
            params.append(name)
            if self.at(":"):
                self.take()
                spec["types"][name] = self.type_name_tok()
            if self.at("="):
                self.take()
                spec["defaults"][name] = self.expr()
            elif spec["defaults"]:
                raise self.err(f"parameter '{name}' needs a default: it follows a parameter that has one",
                               self.t[self.i - 1])
            if not self.at(")"):
                self.expect(",")
        self.expect(")")
        if self.at("->"):
            self.take()
            spec["ret"] = self.type_name_tok()
        # contracts: `requires COND` (checked on entry) / `ensures COND` (checked on return; `result` is the value)
        # each may sit on its own line, and so may the opening brace
        def skip_to_contract():
            j = self.i
            while self.t[j].kind == "nl":
                j += 1
            if (self.t[j].kind == "ident" and self.t[j].val in ("requires", "ensures")) or \
                    (self.t[j].kind == "op" and self.t[j].val == "{" and j > self.i):
                self.i = j
        skip_to_contract()
        while self.peek().kind == "ident" and self.peek().val in ("requires", "ensures"):
            which = self.take().val
            start = self.i
            cond = self.expr()
            text = join_tokens([t for t in self.t[start:self.i] if t.kind != "nl"])
            spec[which].append((cond, text))
            skip_to_contract()
        if self.at("=>"):
            tok = self.take()
            return params, [N("return", (self.expr(),), tok)], spec
        body = self.block()
        if body and body[0].k == "expr" and body[0].a[0].k == "lit" and isinstance(body[0].a[0].a[0], str):
            spec["doc"] = body[0].a[0].a[0]
        return params, body, spec

    # --- expressions (precedence climbing)
    def expr(self, min_prec=0):
        left = self.unary()
        while True:
            tok = self.peek()
            op = tok.val if tok.kind in ("op", "kw") else None
            if op not in PREC or PREC[op] < min_prec:
                break
            self.take()
            prec = PREC[op]
            right = self.expr(prec + 1)
            if op == "|>":
                if right.k not in ("call", "name", "field", "fn"):
                    raise self.err("the right side of |> must be a function or a call like f(x)", tok)
                left = N("pipe", (left, right), tok)
                continue
            left = N("bin", (op, left, right), tok)
        return left

    def unary(self):
        tok = self.peek()
        if tok.kind == "op" and tok.val == "-":
            self.take()
            return N("neg", (self.unary(),), tok)
        if tok.kind == "kw" and tok.val == "not":
            self.take()
            return N("not", (self.expr(4),), tok)
        return self.postfix(self.primary())

    def postfix(self, e):
        while True:
            tok = self.peek()
            if tok.kind == "op" and tok.val == "(":
                self.take()
                args, named = [], False
                while not self.at(")"):
                    nt = self.peek()
                    if nt.kind in ("ident", "kw") and self.peek(1).kind == "op" and self.peek(1).val == ":":
                        self.take()
                        self.take()
                        args.append(N("named", (nt.val, self.expr()), nt))
                        named = True
                    else:
                        if named:
                            raise self.err("a positional argument cannot follow a named one", nt)
                        args.append(self.expr())
                    if not self.at(")"):
                        self.expect(",")
                self.expect(")")
                e = N("call", (e, args), tok)
            elif tok.kind == "op" and tok.val == "[":
                self.take()
                lo = None if self.at(":") else self.expr()
                if self.at(":"):
                    self.take()
                    hi = None if self.at("]") else self.expr()
                    self.expect("]")
                    e = N("slice", (e, lo, hi), tok)
                else:
                    self.expect("]")
                    e = N("index", (e, lo), tok)
            elif tok.kind == "op" and tok.val == ".":
                self.take()
                ntok = self.peek()
                if ntok.kind == "kw":  # a keyword is fine as a field name: w.rule, m.fact
                    self.take()
                    name = ntok.val
                else:
                    name = self.expect_ident().val
                e = N("field", (e, name), tok)
            else:
                return e

    def primary(self):
        tok = self.take()
        k, v = tok.kind, tok.val
        if k == "number":
            return N("lit", (Decimal(v.replace("_", "")),), tok)
        if k == "money":
            return N("lit", (Money.parse(v),), tok)
        if k == "date":
            try:
                return N("lit", (_dt.date.fromisoformat(v[1:]),), tok)
            except ValueError:
                raise self.err(f"not a real date: {v}", tok)
        if k == "string":
            return self.string(tok)
        if k == "ident":
            return N("name", (v,), tok)
        if k == "kw":
            if v == "if":  # conditional expression: if C then A else B
                cond = self.expr()
                self.expect("then")
                a = self.expr()
                self.skip_nl_before("else")
                self.expect("else")
                b = self.expr()
                return N("cond", (cond, a, b), tok)
            if v == "true":
                return N("lit", (True,), tok)
            if v == "false":
                return N("lit", (False,), tok)
            if v == "nil":
                return N("lit", (None,), tok)
            if v == "fn":
                params, body, spec = self.fn_rest()
                return N("fn", ("<fn>", params, body, spec), tok)
        if k == "op" and v == "?":
            pred, args = self.fact_head()
            return N("goal", (pred, args), tok)
        if k == "op" and v == "(":
            e = self.expr()
            self.expect(")")
            return e
        if k == "op" and v == "[":
            items = []
            while not self.at("]"):
                items.append(self.expr())
                if not self.at("]"):
                    self.expect(",")
            self.expect("]")
            return N("list", (items,), tok)
        if k == "op" and v == "{":
            pairs = []
            self.skip_nl()
            while not self.at("}"):
                ktok = self.peek()
                if ktok.kind == "ident" or (ktok.kind == "kw" and self.peek(1).val == ":"):
                    self.take()
                    key = N("lit", (ktok.val,), ktok)
                else:
                    key = self.expr()
                self.expect(":")
                pairs.append((key, self.expr()))
                self.skip_nl()
                if not self.at("}"):
                    self.expect(",")
                    self.skip_nl()
            self.expect("}")
            return N("map", (pairs,), tok)
        raise self.err(f"unexpected {self.describe(tok)}", tok)

    def string(self, tok):
        raw = tok.val[1:-1]
        parts, buf, i = [], [], 0
        while i < len(raw):
            c = raw[i]
            if c == "\\" and i + 1 < len(raw):
                nxt = raw[i + 1]
                buf.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\", "{": "{", "}": "}"}.get(nxt, "\\" + nxt))
                i += 2
                continue
            if c == "{":
                depth, j = 1, i + 1
                while j < len(raw) and depth:
                    depth += {"{": 1, "}": -1}.get(raw[j], 0)
                    j += 1
                if depth:
                    raise self.err("unclosed '{' in string", tok)
                if buf:
                    parts.append("".join(buf))
                    buf = []
                try:
                    stoks = lex(raw[i + 1:j - 1], self.path)
                    # place the snippet's tokens where they sit in the file (errors inside {…} point at the file)
                    before = raw[:i + 1]
                    line_off = before.count("\n")
                    col0 = tok.col + 1 + (len(before) if not line_off else len(before) - before.rfind("\n") - 1)
                    for st in stoks:
                        if st.line == 1:
                            st.col = st.col + col0 - 1 if not line_off else st.col + col0 - 1
                        st.line = st.line + tok.line - 1 + line_off
                    sub = Parser(stoks, self.path)
                    e = sub.expr()
                    sub.skip_nl()
                    if sub.peek().kind != "eof":
                        raise TallyError("junk after expression", 0, 0)
                except TallyError as ex:
                    raise self.err(f"inside {{…}} in a string: {ex.msg} (write \\{{ for a literal brace)", tok)
                parts.append(e)
                i = j
                continue
            buf.append(c)
            i += 1
        if buf or not parts:
            parts.append("".join(buf))
        if len(parts) == 1 and isinstance(parts[0], str):
            return N("lit", (parts[0],), tok)
        return N("interp", (parts,), tok)


def unquote(s, tok, path):
    return s[1:-1].replace('\\"', '"').replace("\\\\", "\\")


def parse(src, path=""):
    return Parser(lex(src, path), path).program()


# ================================================================ values
class Money:
    """exact cents."""
    __slots__ = ("cents",)

    def __init__(self, cents):
        self.cents = int(cents)

    @staticmethod
    def parse(text):
        t = text.replace("$", "").replace(",", "")
        d = Decimal(t)
        return Money(int((d * 100).to_integral_value()))

    @staticmethod
    def from_decimal(d, where=None):
        c = d * 100
        if c != c.to_integral_value():
            raise TallyError(f"money must be whole cents, got ${d} (use round_money)", *(where or (0, 0)))
        return Money(int(c))

    def dec(self):
        return Decimal(self.cents) / 100

    def __eq__(self, o):
        return isinstance(o, Money) and o.cents == self.cents

    def __hash__(self):
        return hash(("money", self.cents))

    def __str__(self):
        sign = "-" if self.cents < 0 else ""
        c = abs(self.cents)
        return f"{sign}${c // 100:,}.{c % 100:02d}"


class Interval:
    """a value known only to lie in [lo, hi] (both money, or both numbers). Arithmetic is exact range arithmetic;
    a comparison is true or false when every value in the range agrees, otherwise MAYBE."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi

    def __eq__(self, o):
        return isinstance(o, Interval) and equal(self.lo, o.lo) and equal(self.hi, o.hi)

    def __hash__(self):
        return hash(("interval", show(self.lo), show(self.hi)))


class Maybe:
    """the result of a comparison some values in a range satisfy and some do not"""
    __slots__ = ()

    def __repr__(self):
        return "maybe"


MAYBE = Maybe()
EXT_BINOP = set()  # value classes with tally_binop(op, a, b, interp, node); modules register into this set


class Sourced:
    """a value with the record cites it came from. Operations union the cites."""
    __slots__ = ("v", "src")

    def __init__(self, v, src):
        self.v, self.src = v, frozenset(src)


def strip(x):
    return x.v if type(x) is Sourced else x


def srcs(*xs):
    out = None
    for x in xs:
        if type(x) is Sourced:
            out = x.src if out is None else out | x.src
    return out if out is not None else _EMPTY


_EMPTY = frozenset()


def all_sources(value, seen=None):
    """Collect sources through nested values, including cyclic mutable containers."""
    seen = set() if seen is None else seen
    out = set(srcs(value))
    value = strip(value)
    if id(value) in seen:
        return out
    seen.add(id(value))
    children = value if isinstance(value, list) else value.values() if isinstance(value, dict) else \
        value.vals.values() if isinstance(value, Record) else ()
    for child in children:
        out.update(all_sources(child, seen))
    return out


def wrap(v, s):
    if not s:
        return v
    if isinstance(v, Sourced):
        return Sourced(v.v, v.src | s)
    return Sourced(v, s)


class RecordType:
    def __init__(self, name, fields, defaults):
        self.name, self.fields, self.defaults, self.methods = name, fields, defaults, {}


class Record:
    __slots__ = ("type", "vals")

    def __init__(self, rtype, vals):
        self.type, self.vals = rtype, vals


class Function:
    def __init__(self, name, params, body, env, spec=None):
        self.name, self.params, self.body, self.env = name, params, body, env
        self.spec = spec or {"types": {}, "defaults": {}, "ret": None, "doc": None}
        self.spec.setdefault("requires", [])
        self.spec.setdefault("ensures", [])

    def required(self):
        return [p for p in self.params if p not in self.spec["defaults"]]

    def signature(self):
        parts = []
        for p in self.params:
            t = f": {self.spec['types'][p]}" if p in self.spec["types"] else ""
            d = f" = {show_src(self.spec['defaults'][p])}" if p in self.spec["defaults"] else ""
            parts.append(p + t + d)
        ret = f" -> {self.spec['ret']}" if self.spec["ret"] else ""
        con = "".join(f" requires {t}" for _, t in self.spec["requires"]) + \
            "".join(f" ensures {t}" for _, t in self.spec["ensures"])
        return f"{self.name}({', '.join(parts)}){ret}{con}"


class BoundMethod:
    def __init__(self, fn, obj):
        self.fn, self.obj = fn, obj


class Builtin:
    def __init__(self, name, fn, arity=None):
        self.name, self.fn, self.arity = name, fn, arity


class Env:
    __slots__ = ("vars", "parent")

    def __init__(self, parent=None):
        self.vars, self.parent = {}, parent

    def find(self, name):
        e = self
        while e is not None:
            if name in e.vars:
                return e
            e = e.parent
        return None


def type_name(x):
    x = strip(x)
    if x is None:
        return "nil"
    if isinstance(x, bool):
        return "bool"
    if isinstance(x, Decimal):
        return "number"
    if isinstance(x, Money):
        return "money"
    if isinstance(x, _dt.date):
        return "date"
    if isinstance(x, str):
        return "string"
    if isinstance(x, list):
        return "list"
    if isinstance(x, dict):
        return "map"
    if isinstance(x, (Function, Builtin)):
        return "function"
    if isinstance(x, Record):
        return x.type.name
    if isinstance(x, RecordType):
        return "record type"
    if type(x).__name__ == "Rng":
        return "rng"
    if isinstance(x, Interval):
        return "range"
    if isinstance(x, Maybe):
        return "maybe"
    if hasattr(x, "tally_type"):
        return x.tally_type  # extension values (qubit, register) name their own type
    return "unknown"


def join_tokens(toks):
    """source-like text from tokens: no space just inside brackets, before , or after a call's name"""
    out = ""
    prev = before = None
    for t in toks:
        v = t.val
        unary_prev = prev is not None and prev.kind == "op" and prev.val == "-" and (
            before is None or (before.kind == "op" and before.val not in ")]") or before.kind == "kw")
        tight = prev is None or (prev.kind == "op" and prev.val in "([.") or (t.kind == "op" and v in ")],.") or \
            (t.kind == "op" and v in "([" and prev is not None and (prev.kind in ("ident",) or prev.val in ")]")) or \
            unary_prev
        out += ("" if tight else " ") + v
        before, prev = prev, t
    return out


def names_in(node, out=None):
    out = set() if out is None else out
    if isinstance(node, N):
        if node.k == "name":
            out.add(node.a[0])
        for x in node.a:
            if isinstance(x, (N, list, tuple)):
                names_in(x, out)
    elif isinstance(node, (list, tuple)):
        for x in node:
            names_in(x, out)
    return out


def did_you_mean(name, env, extra=()):
    import difflib
    names = set(extra or ())
    while env is not None:
        names |= set(env.vars)
        env = env.parent
    close = difflib.get_close_matches(name, sorted(names), n=3, cutoff=0.6)
    return ("did you mean " + " or ".join(close) + "?") if close else None


TYPE_NAMES = {"number", "money", "date", "string", "bool", "list", "map", "function", "nil", "any"}


def type_ok(v, t):
    if t.endswith("?"):
        if strip(v) is None:
            return True
        t = t[:-1]
    if t == "any":
        return True
    return type_name(v) == t.split(".")[-1]


def show_src(node):
    """short source text of an expression node (for signatures)"""
    if node is None:
        return ""
    if node.k == "lit":
        return show(node.a[0], True)
    if node.k == "name":
        return node.a[0]
    return "…"


def show(x, nested=False):
    s = srcs(x)
    x = strip(x)
    if x is None:
        out = "nil"
    elif isinstance(x, bool):
        out = "true" if x else "false"
    elif isinstance(x, Decimal):
        out = fmt_num(x)
    elif isinstance(x, Money):
        out = str(x)
    elif isinstance(x, _dt.date):
        out = x.isoformat()
    elif isinstance(x, str):
        out = '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"' if nested else x
    elif isinstance(x, list):
        out = "[" + ", ".join(show(v, True) for v in x) + "]"
    elif isinstance(x, dict):
        out = "{" + ", ".join(f"{show(k, True)}: {show(v, True)}" for k, v in x.items()) + "}"
    elif isinstance(x, Interval):
        out = f"{show(x.lo)}..{show(x.hi)}"
    elif isinstance(x, Maybe):
        out = "maybe"
    elif isinstance(x, Record):
        out = x.type.name + "(" + ", ".join(f"{f}: {show(x.vals[f], True)}" for f in x.type.fields) + ")"
    elif isinstance(x, RecordType):
        out = f"<record {x.name}>"
    elif isinstance(x, Function):
        out = f"<fn {x.name}>"
    elif isinstance(x, Builtin):
        out = f"<builtin {x.name}>"
    elif hasattr(x, "tally_show"):
        out = x.tally_show()
    else:
        out = repr(x)
    return out


def fmt_num(d):
    if d == d.to_integral_value():
        return str(d.quantize(Decimal(1)))
    s = format(d.normalize(), "f")
    return s


def equal(a, b):
    a, b = strip(a), strip(b)
    if isinstance(a, bool) or isinstance(b, bool):
        return isinstance(a, bool) and isinstance(b, bool) and a == b
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(equal(x, y) for x, y in zip(a, b))
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(equal(a[k], b[k]) for k in a)
    if isinstance(a, Record) and isinstance(b, Record):
        return a.type is b.type and all(equal(a.vals[f], b.vals[f]) for f in a.type.fields)
    if type(a) is not type(b):
        return False
    if hasattr(a, "tally_eq"):
        return a.tally_eq(b)
    return a == b


def hashable_key(k, node):
    k = strip(k)
    if isinstance(k, (list, dict)):
        raise TallyError("a map key must be a string, number, money, date, bool or nil", node.line, node.col)
    return k


# ================================================================ interpreter
class Interp:
    def __init__(self, path="", out=None, budget=None):
        raw_limit = os.environ.get("TALLY_MAX_STEPS")
        if budget is None and raw_limit is not None and (not raw_limit.isdigit() or int(raw_limit) <= 0):
            raise TallyError("execution step limit must be a positive whole number", 0, 0, path)
        self.budget = budget if budget is not None else Budget(int(raw_limit) if raw_limit else None)
        self.path = path
        self.out = out or sys.stdout
        self.builtins = Env()
        self.globals = Env(self.builtins)
        self.tests = []
        self.modules = {}
        self.stack = []  # (function name, call line) for error traces
        self.pc = _EMPTY  # sources of the conditions that chose the branch now running (control-flow provenance)
        install_builtins(self)
        _tl.install(self)
        _td.install(self)
        _tx.install(self)
        _tm.install(self)
        _tr.install(self)
        _ta.install(self)
        _tq.install(self)
        _qsim.install(self)
        _tt.install(self)
        _ts.install(self)
        _rc.install(self)
        _nt.install(self)
        _ac.install(self)
        _qs.install(self)
        _ex.install(self)
        _pdf.install(self)
        _terms.install(self)
        _ap.install(self)
        _ob.install(self)
        _ql.install(self)

    def tick(self, node=None):
        self.budget.tick(self.path, node)


    def err(self, msg, node, hint=None):
        return TallyError(msg, node.line, node.col, self.path, hint)

    def run(self, src, path=None):
        if path:
            self.path = path
        prog = parse(src, self.path)
        return self.exec_block(prog, self.globals)

    def exec_block(self, stmts, env):
        last = None
        for s in stmts:
            last = self.exec(s, env)
        return last

    def truth(self, v, node):
        v = strip(v)
        if not isinstance(v, bool):
            if isinstance(v, Maybe):
                raise self.err("this comparison is undecided (maybe): a range, or a same-day order with no time",
                               node, hint="wrap it: necessarily(…) or possibly(…); inside a rule a maybe makes the "
                               "conclusion open")
            raise self.err(f"a condition must be true or false, got {type_name(v)} {show(v)}", node,
                           hint="to choose a value write: if C then A else B")
        return v

    def exec(self, s, env):
        self.tick(s)
        k, a = s.k, s.a
        if k == "expr":
            return self.eval(a[0], env)
        if k == "let":
            name, e = a
            if name in env.vars:
                raise self.err(f"'{name}' is already defined in this scope", s)
            env.vars[name] = self.eval(e, env) if not self.pc else wrap(self.eval(e, env), self.pc)
            return None
        if k == "assign":
            return self.assign(s, env)
        if k == "if":
            cond, then, other = a
            c = self.eval(cond, env)
            branch = then if self.truth(c, cond) else other
            if branch is None:
                return None
            if type(c) is not Sourced:
                return self.exec_block(branch, Env(env))
            saved, self.pc = self.pc, self.pc | c.src
            try:
                return self.exec_block(branch, Env(env))
            finally:
                self.pc = saved
        if k == "while":
            cond, body = a
            saved = self.pc
            try:
                while True:
                    c = self.eval(cond, env)
                    if type(c) is Sourced:
                        self.pc = self.pc | c.src
                    if not self.truth(c, cond):
                        break
                    try:
                        self.exec_block(body, Env(env))
                    except BreakSignal:
                        break
                    except ContinueSignal:
                        continue
            finally:
                self.pc = saved
            return None
        if k == "for":
            name, name2, it_node, body = a
            collection = self.eval(it_node, env)
            it = strip(collection)
            if isinstance(it, list):
                seq = [(Decimal(i), v) for i, v in enumerate(it)] if name2 else [(v, None) for v in it]
            elif isinstance(it, dict):
                seq = list(it.items()) if name2 else [(k2, None) for k2 in it]
            elif isinstance(it, str):
                seq = [(c, None) for c in it]
            else:
                raise self.err(f"cannot loop over {type_name(it)}", it_node)
            saved = self.pc
            self.pc |= srcs(collection)
            try:
                for x, y in seq:
                    self.tick(s)
                    inner = Env(env)
                    if name2:
                        inner.vars[name], inner.vars[name2] = wrap(x, srcs(collection)), wrap(y, srcs(collection))
                    else:
                        inner.vars[name] = wrap(x, srcs(collection))
                    try:
                        self.exec_block(body, inner)
                    except BreakSignal:
                        break
                    except ContinueSignal:
                        continue
            finally:
                self.pc = saved
            return None
        if k == "return":
            v = self.eval(a[0], env) if a[0] is not None else None
            raise ReturnSignal(wrap(v, self.pc) if self.pc and v is not None else v)
        if k == "break":
            raise BreakSignal()
        if k == "continue":
            raise ContinueSignal()
        if k == "throw":
            raise Thrown(self.eval(a[0], env), s.line, s.col)
        if k == "try":
            body, name, handler = a
            depth = len(self.stack)
            try:
                return self.exec_block(body, Env(env))
            except Thrown as t:
                val = t.value
            except LimitError:
                raise
            except TallyError as e:
                val = str(e)
            except RecursionError:
                val = "stack overflow (recursion too deep)"
            del self.stack[depth:]
            inner = Env(env)
            inner.vars[name] = val
            return self.exec_block(handler, inner)
        if k == "record":
            name, fields = a
            if name in env.vars:
                raise self.err(f"'{name}' is already defined in this scope", s)
            defaults = {f: self.eval(d, env) for f, d in fields if d is not None}
            env.vars[name] = RecordType(name, [f for f, _ in fields], defaults)
            return None
        if k == "method":
            tname, meth, fn_node = a
            found = env.find(tname)
            if found is None or not isinstance(strip(found.vars[tname]), RecordType):
                raise self.err(f"'{tname}' is not a record type", s)
            rt = strip(found.vars[tname])
            if fn_node.a[1][:1] != ["self"]:
                raise self.err(f"a method's first parameter must be 'self' (fn {tname}.{meth}(self, …))", s)
            rt.methods[meth] = Function(fn_node.a[0], fn_node.a[1], fn_node.a[2], env, fn_node.a[3])
            return None
        if k == "match":
            subject = self.eval(a[0], env)
            saved = self.pc
            if type(subject) is Sourced:
                self.pc = self.pc | subject.src  # which case runs depends on the subject
            try:
                for pats, guard, body, ctok in a[1]:
                    for pat in pats:
                        binds = {}
                        if self.match_pat(pat, subject, binds, env):
                            inner = Env(env)
                            inner.vars.update(binds)
                            if guard is not None:
                                g = self.eval(guard, inner)
                                if type(g) is Sourced:
                                    self.pc = self.pc | g.src
                                if not self.truth(g, guard):
                                    continue
                            return self.exec_block(body, inner)
                raise self.err(f"no case matched {show(subject, True)}", s)
            finally:
                self.pc = saved
        if k == "alias":
            canon, names = a
            self.kb.add_alias(canon, names)
            return None
        if k == "fact":
            pred, arg_nodes, truth, src_node = a
            raw_args = [self.eval(x, env) for x in arg_nodes]
            args = [self.kb.canon(x) for x in raw_args]
            src = set(self.pc) | {f"alias {strip(r)} = {strip(c)}" for r, c in zip(raw_args, args) if strip(r) != strip(c)}
            for v in args:
                src |= srcs(v)
            if src_node is not None:
                sv = strip(self.eval(src_node, env))
                src |= {strip(x) for x in sv} if isinstance(sv, list) else {sv}
            self.kb.add_base(_tl.Fact(pred, args, truth, src, s.line))
            return None
        if k == "retract":
            pred, arg_nodes = a
            return Decimal(self.kb.retract(pred, [self.kb.canon(self.eval(x, env)) for x in arg_nodes]))
        if k == "rule":
            name, conds, concls, unless = a
            if any(r.name == name for r in self.kb.rules):
                raise self.err(f"rule '{name}' is already defined", s)
            rule = _tl.Rule(name, conds, concls, env, s)
            rule.unless = unless
            self.kb.rules.append(rule)
            self.kb.stale = True
            return None
        if k == "suppose":
            snap = _tl.snapshot(self.kb)
            try:
                self.exec_block(a[0], Env(env))
                try:
                    _tl.infer(self, self.kb)
                except LimitError:
                    raise
                except TallyError as e:
                    if not e.line:
                        raise self.err(e.msg, s)
                    if not e.path:
                        e.path = self.path
                    raise
                return self.exec_block(a[1], Env(env))
            finally:
                _tl.restore(self.kb, snap)
        if k == "import":
            rel, name = a
            env.vars[name] = self.load_module(rel, s)
            return None
        if k == "test":
            self.tests.append((a[0], a[1], env, s))
            return None
        raise self.err(f"unknown statement {k}", s)

    def match_pat(self, pat, val, binds, env):
        k, a = pat.k, pat.a
        v = strip(val)
        if k == "pat_any":
            return True
        if k == "pat_bind":
            binds[a[0]] = val
            return True
        if k == "pat_lit":
            return equal(self.eval(a[0], env), val)
        if k == "pat_record":
            if not isinstance(v, Record) or v.type.name != a[0]:
                return False
            if len(a[1]) != len(v.type.fields):
                raise self.err(f"{a[0]} has {len(v.type.fields)} fields, pattern names {len(a[1])}", pat)
            return all(self.match_pat(p, v.vals[f], binds, env) for p, f in zip(a[1], v.type.fields))
        if k == "pat_list":
            subs, rest = a
            if not isinstance(v, list):
                return False
            if rest is None and len(v) != len(subs):
                return False
            if rest is not None and len(v) < len(subs):
                return False
            if not all(self.match_pat(p, x, binds, env) for p, x in zip(subs, v)):
                return False
            if rest is not None:
                binds[rest] = v[len(subs):]
            return True
        return False

    def load_module(self, rel, node):
        base = os.path.dirname(os.path.abspath(self.path)) if self.path else os.getcwd()
        p = os.path.normpath(os.path.join(base, rel))
        if p in self.modules:
            if self.modules[p] is None:
                raise self.err(f"import cycle through {rel}", node)
            return self.modules[p]
        if not os.path.exists(p):
            raise self.err(f"no module at {p}", node)
        self.modules[p] = None
        sub = Interp(p, self.out, budget=self.budget)
        sub.modules = self.modules
        with open(p, encoding="utf-8") as fh:
            sub.run(fh.read(), p)
        exported = dict(sub.globals.vars)
        self.modules[p] = exported
        return exported

    def assign(self, s, env):
        target, op, rhs = s.a
        val = self.eval(rhs, env)
        if op != "=":
            cur = self.eval(target, env)
            val = self.binop(op[0], cur, val, s)
        if self.pc:
            val = wrap(val, self.pc)
        if target.k == "name":
            e = env.find(target.a[0])
            if e is None:
                raise self.err(f"'{target.a[0]}' is not defined (use let)", target)
            e.vars[target.a[0]] = val
        elif target.k == "index":
            obj = strip(self.eval(target.a[0], env))
            key = self.eval(target.a[1], env)
            if isinstance(obj, list):
                obj[self.list_index(obj, key, target)] = val
            elif isinstance(obj, dict):
                obj[hashable_key(key, target)] = val
            else:
                raise self.err(f"cannot assign into {type_name(obj)}", target)
        else:
            obj = strip(self.eval(target.a[0], env))
            if isinstance(obj, Record):
                if target.a[1] not in obj.vals:
                    raise self.err(f"{obj.type.name} has no field '{target.a[1]}'", target)
                obj.vals[target.a[1]] = val
            elif isinstance(obj, dict):
                obj[target.a[1]] = val
            else:
                raise self.err(f"cannot set a field on {type_name(obj)}", target)
        return None

    def list_index(self, lst, key, node):
        key = strip(key)
        if not isinstance(key, Decimal) or key != key.to_integral_value():
            raise self.err("a list index must be a whole number", node)
        i = int(key)
        if i < 0:
            i += len(lst)
        if not 0 <= i < len(lst):
            raise self.err(f"index {int(key)} is outside the list (length {len(lst)})", node)
        return i

    def eval(self, e, env):
        self.tick(e)
        k, a = e.k, e.a
        if k == "lit":
            return a[0]
        if k == "name":
            name = a[0]
            start = env
            while env is not None:
                vs = env.vars
                if name in vs:
                    return vs[name]
                env = env.parent
            raise self.err(f"'{name}' is not defined", e, hint=did_you_mean(name, start))
        if k == "interp":
            out, s = [], set()
            for p in a[0]:
                if isinstance(p, str):
                    out.append(p)
                else:
                    v = self.eval(p, env)
                    s |= srcs(v)
                    out.append(show(v))
            return wrap("".join(out), s)
        if k == "list":
            return [self.eval(x, env) for x in a[0]]
        if k == "map":
            return {hashable_key(self.eval(kn, env), kn): self.eval(vn, env) for kn, vn in a[0]}
        if k == "fn":
            return Function(a[0], a[1], a[2], env, a[3] if len(a) > 3 else None)
        if k == "val":
            return a[0]
        if k == "cond":
            c = self.eval(a[0], env)
            pick = self.eval(a[1] if self.truth(c, a[0]) else a[2], env)
            return wrap(strip(pick), srcs(c, pick))
        if k == "named":
            return ("__named__", a[0], self.eval(a[1], env))
        if k == "pipe":
            v = self.eval(a[0], env)
            r = a[1]
            if r.k == "call":
                return self.eval(N("call", (r.a[0], [N("val", (v,), None)] + list(r.a[1])), r), env)
            return self.call(self.eval(r, env), [v], e)
        if k == "goal":
            args, qvars = [], []
            for x in a[1]:
                # a lowercase name is a variable unless the program bound it; a built-in function's name never pins
                # an argument (so ?Gap(a, gap) or ?Lag(x, lag) query, whatever built-ins exist)
                fe = env.find(x.a[0]) if x.k == "name" else None
                if x.k == "name" and (x.a[0] == "_" or (x.a[0][:1].islower() and (fe is None or fe is self.builtins))):
                    args.append(_tl.QVar(x.a[0]))
                    qvars.append(x.a[0])
                else:
                    args.append(self.kb.canon(self.eval(x, env)))
            g = {"pred": a[0], "args": args}
            if qvars:
                g["vars"] = qvars
            return g
        if k == "neg":
            v = self.eval(a[0], env)
            x = strip(v)
            if isinstance(x, Decimal):
                return wrap(-x, srcs(v))
            if isinstance(x, Money):
                return wrap(Money(-x.cents), srcs(v))
            raise self.err(f"cannot negate {type_name(x)}", e)
        if k == "not":
            v = self.eval(a[0], env)
            return wrap(not self.truth(v, a[0]), srcs(v))
        if k == "bin":
            op, ln, rn = a
            if op == "and":
                lv = self.eval(ln, env)
                if not self.truth(lv, ln):
                    return lv
                rv = self.eval(rn, env)
                self.truth(rv, rn)
                return wrap(strip(rv), srcs(lv, rv))
            if op == "or":
                lv = self.eval(ln, env)
                if self.truth(lv, ln):
                    return lv
                rv = self.eval(rn, env)
                self.truth(rv, rn)
                return wrap(strip(rv), srcs(lv, rv))
            if op == "from":
                v = self.eval(ln, env)
                src = strip(self.eval(rn, env))
                if isinstance(src, str):
                    src = [src]
                if not isinstance(src, list) or not all(isinstance(strip(x), str) for x in src):
                    raise self.err("`from` needs a source name in quotes (or a list of them)", rn)
                return wrap(strip(v), srcs(v) | {strip(x) for x in src})
            return self.binop(op, self.eval(ln, env), self.eval(rn, env), e)
        if k == "call":
            fn_node, arg_nodes = a
            if fn_node.k == "field":
                obj = self.eval(fn_node.a[0], env)
                o = strip(obj)
                if isinstance(o, dict) and fn_node.a[1] in o:
                    fn = o[fn_node.a[1]]
                    args = [self.eval(x, env) for x in arg_nodes]
                elif isinstance(o, Record) and fn_node.a[1] in o.type.methods:
                    fn = o.type.methods[fn_node.a[1]]
                    args = [obj] + [self.eval(x, env) for x in arg_nodes]
                elif isinstance(o, Record) and fn_node.a[1] in o.vals:
                    fn = o.vals[fn_node.a[1]]
                    args = [self.eval(x, env) for x in arg_nodes]
                else:  # method syntax: x.f(a) is f(x, a)
                    found = env.find(fn_node.a[1])
                    if found is None:
                        options = list(o.vals) + list(o.type.methods) if isinstance(o, Record) else (
                            list(o.keys()) if isinstance(o, dict) else [])
                        raise self.err(f"no function '{fn_node.a[1]}' for {type_name(o)}", fn_node,
                                       hint=did_you_mean(fn_node.a[1], env, options))
                    fn = found.vars[fn_node.a[1]]
                    args = [obj] + [self.eval(x, env) for x in arg_nodes]
            else:
                fn = self.eval(fn_node, env)
                args = [self.eval(x, env) for x in arg_nodes]
            if any(x.k == "named" for x in arg_nodes):
                return self.call_named(fn, args, arg_nodes, env, e)
            return self.call(fn, args, e)
        if k == "index":
            obj, key = self.eval(a[0], env), self.eval(a[1], env)
            o = strip(obj)
            if isinstance(o, list):
                return wrap(o[self.list_index(o, key, e)], srcs(obj, key))
            if isinstance(o, str):
                return wrap(o[self.list_index(list(o), key, e)], srcs(obj, key))
            if isinstance(o, dict):
                kk = hashable_key(key, e)
                if kk not in o:
                    raise self.err(f"key {show(kk, True)} is not in the map", e)
                return wrap(o[kk], srcs(obj, key))
            raise self.err(f"cannot index {type_name(o)}", e)
        if k == "slice":
            obj = self.eval(a[0], env)
            o = strip(obj)
            selection_sources = set(srcs(obj))
            def bound(n):
                value = self.eval(n, env)
                selection_sources.update(srcs(value))
                v = strip(value)
                if not isinstance(v, Decimal) or isinstance(v, bool) or v != v.to_integral_value():
                    raise self.err(f"a slice bound must be a whole number, got {type_name(v)} {show(v, True)}", n)
                return int(v)
            lo = 0 if a[1] is None else bound(a[1])
            hi = None if a[2] is None else bound(a[2])
            if isinstance(o, (list, str)):
                return wrap(o[lo:hi], selection_sources)
            raise self.err(f"cannot slice {type_name(o)}", e)
        if k == "field":
            carrier = self.eval(a[0], env)
            obj = strip(carrier)
            if isinstance(obj, dict):
                if a[1] not in obj:
                    raise self.err(f"the map has no field '{a[1]}'", e)
                return wrap(obj[a[1]], srcs(carrier))
            if isinstance(obj, Record):
                if a[1] in obj.vals:
                    return wrap(obj.vals[a[1]], srcs(carrier))
                if a[1] in obj.type.methods:
                    return BoundMethod(obj.type.methods[a[1]], carrier)
                raise self.err(f"{obj.type.name} has no field or method '{a[1]}'", e)
            if hasattr(obj, "tally_fields"):
                fs = obj.tally_fields()
                if a[1] not in fs:
                    raise self.err(f"a {type_name(obj)} has no field '{a[1]}'", e, hint="fields: " + ", ".join(fs))
                return fs[a[1]]
            raise self.err(f"{type_name(obj)} has no fields (did you mean .{a[1]}() ?)", e)
        raise self.err(f"unknown expression {k}", e)

    def contract(self, fn, which, cond, text, env, node):
        try:
            v = strip(self.eval(cond, env))
        except LimitError:
            raise
        except TallyError as ex:
            raise self.err(f"{fn.name}: {which} {text} could not be evaluated: {ex.msg}", node)
        if v is True:
            return
        names = sorted(n for n in names_in(cond) if env.find(n) is not None and n not in self.builtins.vars)
        vals = ", ".join(f"{n} = {show(env.find(n).vars[n], True)[:40]}" for n in names)
        what = "failed" if v is False else f"is not true or false (got {type_name(v)})"
        raise self.err(f"{fn.name}: {which} {text} {what}" + (f" ({vals})" if vals else ""), node)

    def call_named(self, fn, args, arg_nodes, env, node):
        """f(a, b, name: v) — named arguments fill the parameters by name; missing ones take their defaults."""
        positional = [v for v in args if not (isinstance(v, tuple) and len(v) == 3 and v[0] == "__named__")]
        named = {v[1]: v[2] for v in args if isinstance(v, tuple) and len(v) == 3 and v[0] == "__named__"}
        f = strip(fn)
        if isinstance(f, BoundMethod):
            positional = [f.obj] + positional
            f = f.fn
        if isinstance(f, Function):
            params = f.params
            defaults = {p: None for p in f.spec["defaults"]}
            label = f.signature()
        elif isinstance(f, Builtin):
            import inspect
            ps = list(inspect.signature(f.fn).parameters.values())[2:]
            params = [p.name for p in ps if p.kind != p.VAR_POSITIONAL]
            defaults = {p.name: p.default for p in ps if p.default is not p.empty}
            label = builtin_signature(f)
        elif isinstance(f, RecordType):
            given = {f.fields[i]: v for i, v in enumerate(positional)}
            for k2 in named:
                if k2 not in f.fields:
                    raise self.err(f"{f.name} has no field '{k2}'", node, hint=did_you_mean(k2, None, f.fields))
                if k2 in given:
                    raise self.err(f"field '{k2}' given twice", node)
            given.update(named)
            return self.call(f, [given], node)
        else:
            raise self.err(f"{type_name(f)} is not a function", node)
        filled = dict(zip(params, positional))
        for k2, v in named.items():
            if k2 not in params:
                raise self.err(f"no parameter '{k2}' — {label}", node, hint=did_you_mean(k2, None, params))
            if k2 in filled:
                raise self.err(f"parameter '{k2}' given twice — {label}", node)
            filled[k2] = v
        out = []
        for i, p in enumerate(params):
            if p in filled:
                out.append(filled[p])
            elif p in defaults:
                if isinstance(f, Function):
                    out.append(self.eval(f.spec["defaults"][p], f.env))
                else:
                    out.append(defaults[p])
            else:
                raise self.err(f"missing argument '{p}' — {label}", node)
        while out and isinstance(f, Builtin) and params and len(out) > len(positional) + len(named) \
                and params[len(out) - 1] not in filled:
            out.pop()  # let a built-in's own defaults apply for trailing parameters nobody named
        return self.call(f, out, node)

    def call(self, fn, args, node):
        self.tick(node)
        fn = strip(fn)
        if isinstance(fn, BoundMethod):
            return self.call(fn.fn, [fn.obj] + list(args), node)
        if isinstance(fn, RecordType):
            vals = {}
            if len(args) == 1 and isinstance(strip(args[0]), dict) and not any(
                    f not in strip(args[0]) and f not in fn.defaults for f in fn.fields):
                given = strip(args[0])
                extra = [k2 for k2 in given if k2 not in fn.fields]
                if extra:
                    raise self.err(f"{fn.name} has no field '{extra[0]}'", node)
                for f in fn.fields:
                    vals[f] = given[f] if f in given else fn.defaults[f]
                return Record(fn, vals)
            needed = [f for f in fn.fields if f not in fn.defaults]
            if len(args) < len(needed) or len(args) > len(fn.fields):
                raise self.err(f"{fn.name} takes {len(needed)}..{len(fn.fields)} values "
                               f"({', '.join(fn.fields)}), got {len(args)}", node)
            for i, f in enumerate(fn.fields):
                vals[f] = args[i] if i < len(args) else fn.defaults[f]
            return Record(fn, vals)
        if isinstance(fn, Builtin):
            if fn.arity is not None and len(args) not in (fn.arity if isinstance(fn.arity, tuple) else (fn.arity,)):
                raise self.err(f"{fn.name} takes {fn.arity} argument(s), got {len(args)}", node)
            try:
                return fn.fn(self, node, *args)
            except TallyError:
                raise
            except (Thrown, ReturnSignal):
                raise
            except Exception as ex:
                raise self.err(f"{fn.name}: {ex}", node)
        if isinstance(fn, Function):
            need = len(fn.required())
            if not need <= len(args) <= len(fn.params):
                count = f"{need}" if need == len(fn.params) else f"{need}..{len(fn.params)}"
                raise self.err(f"{fn.name} takes {count} argument(s), got {len(args)} — {fn.signature()}", node)
            env = Env(fn.env)
            types = fn.spec["types"]
            for i, p in enumerate(fn.params):
                v = args[i] if i < len(args) else self.eval(fn.spec["defaults"][p], fn.env)
                if p in types and not type_ok(v, types[p]):
                    raise self.err(f"{fn.name}: argument '{p}' must be {types[p]}, got {type_name(v)} "
                                   f"{show(v, True)[:40]} — {fn.signature()}", node)
                env.vars[p] = v
            for cond, text in fn.spec["requires"]:
                self.contract(fn, "requires", cond, text, env, node)
            self.stack.append((fn.name, node.line))
            try:
                self.exec_block(fn.body, env)
            except ReturnSignal as r:
                ret = fn.spec["ret"]
                if ret and not type_ok(r.value, ret):
                    raise self.err(f"{fn.name} must return {ret}, returned {type_name(r.value)} "
                                   f"{show(r.value, True)[:40]}", node)
                if fn.spec["ensures"]:
                    renv = Env(env)
                    renv.vars["result"] = r.value
                    for cond, text in fn.spec["ensures"]:
                        self.contract(fn, "ensures", cond, text, renv, node)
                return r.value
            except RecursionError:
                raise self.err("stack overflow (recursion too deep)", node)
            except TallyError as e:
                if not getattr(e, "trace", None):
                    e.trace = list(self.stack)
                raise
            except Thrown as t:
                if not getattr(t, "trace", None):
                    t.trace = list(self.stack)
                raise
            finally:
                self.stack.pop()
            ret = fn.spec["ret"]
            if ret and not type_ok(None, ret):
                raise self.err(f"{fn.name} must return {ret}, but ended without a return", node)
            return None
        raise self.err(f"{type_name(fn)} is not a function", node)

    def binop(self, op, lv, rv, node):
        a = lv.v if type(lv) is Sourced else lv
        b = rv.v if type(rv) is Sourced else rv
        ta_ = type(a)
        if ta_ in EXT_BINOP or type(b) in EXT_BINOP:  # extension values (time qubits) define their own operators
            h = a if ta_ in EXT_BINOP else b
            r = h.tally_binop(op, a, b, self, node)
            if r is not NotImplemented:
                return wrap(r, srcs(lv, rv))
        if ta_ is Interval or type(b) is Interval:
            return wrap(self.range_op(op, a, b, node), srcs(lv, rv))
        # fast path for sourced operands of one plain kind: compute on the values, union the sources once
        if ta_ is type(b) and (a is not lv or b is not rv):
            r = None
            if ta_ is Decimal:
                f = _NUM_FAST.get(op)
                if f is not None:
                    if op in ("/", "%") and b == 0:
                        raise self.err("division by zero", node)
                    r = f(a, b)
            elif ta_ is Money:
                if op in _CMP_FAST:
                    r = _CMP_FAST[op](a.cents, b.cents)
                elif op == "+":
                    r = Money(a.cents + b.cents)
                elif op == "-":
                    r = Money(a.cents - b.cents)
            elif (ta_ is _dt.date or ta_ is str) and op in _CMP_FAST:
                r = _CMP_FAST[op](a, b)
            if r is not None:
                return wrap(r, srcs(lv, rv))
        # fast path: two plain dates or two plain money values compared — the common case in rule guards
        tl = type(lv)
        if tl is type(rv) and op in _CMP_FAST:
            if tl is _dt.date:
                return _CMP_FAST[op](lv, rv)
            if tl is Money:
                return _CMP_FAST[op](lv.cents, rv.cents)
        # fast path: two plain decimals (no sources) — the common case in loops
        if type(lv) is Decimal and type(rv) is Decimal:
            f = _NUM_FAST.get(op)
            if f is not None:
                if op in ("/", "%") and rv == 0:
                    raise self.err("division by zero", node)
                return f(lv, rv)
        s = srcs(lv, rv)
        a, b = strip(lv), strip(rv)
        if op in ("==", "!="):
            r = equal(a, b)
            return wrap(r if op == "==" else not r, s)
        if op == "in":
            if isinstance(b, list):
                return wrap(any(equal(a, x) for x in b), s)
            if isinstance(b, dict):
                return wrap(a in b, s)
            if isinstance(b, str) and isinstance(a, str):
                return wrap(a in b, s)
            raise self.err(f"cannot test membership in {type_name(b)}", node)
        if op == "..":
            if isinstance(a, Decimal) and isinstance(b, Decimal):
                return [Decimal(i) for i in range(int(a), int(b))]
            if isinstance(a, _dt.date) and isinstance(b, _dt.date):
                return [a + _dt.timedelta(days=i) for i in range((b - a).days)]
            raise self.err("a range needs two whole numbers or two dates", node)
        ta, tb = type_name(a), type_name(b)
        if op in ("<", "<=", ">", ">="):
            if ta != tb or ta not in ("number", "money", "date", "string"):
                raise self.err(f"cannot compare {ta} with {tb}", node)
            x, y = (a.cents, b.cents) if ta == "money" else (a, b)
            r = {"<": x < y, "<=": x <= y, ">": x > y, ">=": x >= y}[op]
            return wrap(r, s)
        r = self.arith(op, a, b, ta, tb, node)
        return wrap(r, s)

    def range_op(self, op, a, b, node):
        def ends(x):
            return (x.lo, x.hi) if isinstance(x, Interval) else (x, x)
        (al, ah), (bl, bh) = ends(a), ends(b)
        def ar(o, x, y):
            return strip(self.binop(o, x, y, node))
        if op == "+":
            return Interval(ar("+", al, bl), ar("+", ah, bh))
        if op == "-":
            return Interval(ar("-", al, bh), ar("-", ah, bl))
        if op in ("*", "/"):
            if isinstance(a, Interval) and isinstance(b, Interval):
                raise self.err(f"'{op}' of two ranges is not supported (multiply a range by a number)", node)
            cands = [ar(op, x, y) for x in (al, ah) for y in (bl, bh)]
            lo = cands[0]
            hi = cands[0]
            for c in cands[1:]:
                if strip(self.binop("<", c, lo, node)):
                    lo = c
                if strip(self.binop(">", c, hi, node)):
                    hi = c
            return Interval(lo, hi)
        if op in ("<", "<=", ">", ">="):
            always = strip(self.binop(op, ah if op in ("<", "<=") else al, bl if op in ("<", "<=") else bh, node))
            never = not strip(self.binop(op, al if op in ("<", "<=") else ah, bh if op in ("<", "<=") else bl, node))
            return True if always else (False if never else MAYBE)
        if op in ("==", "!="):
            # equality is structural and always true/false: the same range (same ends), or a one-point range and its
            # value. Only the order comparisons can say maybe.
            same = equal(al, bl) and equal(ah, bh)
            return same if op == "==" else not same
        if op == "in":
            raise self.err("use contains_value(range, x) to test a value against a range", node)
        raise self.err(f"cannot apply '{op}' to a range", node)

    def arith(self, op, a, b, ta, tb, node):
        where = (node.line, node.col)
        if ta == tb == "number":
            if op in ("/", "%") and b == 0:
                raise self.err("division by zero", node)
            return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b, "/": lambda: a / b,
                    "%": lambda: a % b}[op]()
        if ta == tb == "money":
            if op == "+":
                return Money(a.cents + b.cents)
            if op == "-":
                return Money(a.cents - b.cents)
            if op == "/":
                if b.cents == 0:
                    raise self.err("division by zero money", node)
                return Decimal(a.cents) / Decimal(b.cents)
        if ta == "money" and tb == "number" and op in ("*", "/"):
            if op == "/" and b == 0:
                raise self.err("division by zero", node)
            return Money.from_decimal(a.dec() * b if op == "*" else a.dec() / b, where)
        if ta == "number" and tb == "money" and op == "*":
            return Money.from_decimal(b.dec() * a, where)
        if ta == "date" and tb == "number" and op in ("+", "-"):
            if b != b.to_integral_value():
                raise self.err("add whole days to a date", node)
            return a + _dt.timedelta(days=int(b) if op == "+" else -int(b))
        if ta == tb == "date" and op == "-":
            return Decimal((a - b).days)
        if ta == tb == "string" and op == "+":
            return a + b
        if ta == tb == "list" and op == "+":
            return a + b
        hint = ""
        if {ta, tb} == {"money", "number"} and op in ("+", "-"):
            hint = " (write the number as money, e.g. $10.00, or use money(x))"
        raise self.err(f"cannot apply '{op}' to {ta} and {tb}{hint}", node)


_CMP_FAST = {
    "<": lambda a, b: a < b, "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b,
    "==": lambda a, b: a == b, "!=": lambda a, b: a != b,
}

_NUM_FAST = {
    "+": lambda a, b: a + b, "-": lambda a, b: a - b, "*": lambda a, b: a * b, "/": lambda a, b: a / b,
    "%": lambda a, b: a % b, "<": lambda a, b: a < b, "<=": lambda a, b: a <= b, ">": lambda a, b: a > b,
    ">=": lambda a, b: a >= b, "==": lambda a, b: a == b, "!=": lambda a, b: a != b,
}


# ================================================================ standard library
def install_builtins(it):
    g = it.builtins.vars

    def bi(name, arity=None):
        def deco(f):
            g[name] = Builtin(name, f, arity)
            return f
        return deco

    def num(x, node, what="a number"):
        x = strip(x)
        if not isinstance(x, Decimal):
            raise it.err(f"expected {what}, got {type_name(x)}", node)
        return x

    def as_list(x, node):
        x = strip(x)
        if not isinstance(x, list):
            raise it.err(f"expected a list, got {type_name(x)}", node)
        return x

    @bi("print")
    def _print(it_, node, *args):
        it_.out.write(" ".join(show(a) for a in args) + "\n")

    @bi("len", 1)
    def _len(it_, node, x):
        s0 = srcs(x)
        x = strip(x)
        if isinstance(x, list):
            return wrap(Decimal(len(x)), s0 | srcs(*x))  # a count carries the records it counted
        if isinstance(x, (dict, str)):
            return wrap(Decimal(len(x)), s0)
        raise it.err(f"{type_name(x)} has no length", node)

    @bi("type", 1)
    def _type(it_, node, x):
        return type_name(x)

    @bi("str", 1)
    def _str(it_, node, x):
        return wrap(show(x), srcs(x))

    @bi("num", 1)
    def _num(it_, node, x):
        v = strip(x)
        try:
            if isinstance(v, Money):
                return wrap(v.dec(), srcs(x))
            if isinstance(v, str):
                return wrap(Decimal(v.replace(",", "").replace("$", "").strip()), srcs(x))
            if isinstance(v, Decimal):
                return x
        except InvalidOperation:
            pass
        raise it.err(f"cannot read {show(v, True)} as a number", node)

    @bi("money", 1)
    def _money(it_, node, x):
        v = strip(x)
        if isinstance(v, Money):
            return x
        if isinstance(v, str):
            try:
                return wrap(Money.parse(v.strip()), srcs(x))
            except InvalidOperation:
                raise it.err(f"cannot read {show(v, True)} as money", node)
        return wrap(Money.from_decimal(num(v, node), (node.line, node.col)), srcs(x))

    @bi("round_money", 1)
    def _round_money(it_, node, x):
        v = strip(x)
        d = v.dec() if isinstance(v, Money) else num(v, node)
        return wrap(Money(int((d * 100).quantize(Decimal(1), rounding=ROUND_HALF_EVEN))), srcs(x))

    @bi("round", (1, 2))
    def _round(it_, node, x, places=Decimal(0)):
        d = num(x, node)
        q = Decimal(1).scaleb(-int(strip(places)))
        return wrap(d.quantize(q, rounding=ROUND_HALF_EVEN), srcs(x))

    @bi("abs", 1)
    def _abs(it_, node, x):
        v = strip(x)
        if isinstance(v, Money):
            return wrap(Money(abs(v.cents)), srcs(x))
        return wrap(abs(num(v, node)), srcs(x))

    @bi("date", 1)
    def _date(it_, node, x):
        try:
            return wrap(_dt.date.fromisoformat(str(strip(x))[:10]), srcs(x))
        except ValueError:
            raise it.err(f"not a date: {show(strip(x), True)}", node)

    @bi("today", 0)
    def _today(it_, node):
        return _dt.date.today()

    @bi("weekday", 1)
    def _weekday(it_, node, d):
        return wrap(strip(d).strftime("%A"), srcs(d))

    @bi("sum", 1)
    def _sum(it_, node, xs):
        carrier = xs
        xs = as_list(xs, node)
        if not xs:
            return wrap(Decimal(0), srcs(carrier))
        total = wrap(xs[0], srcs(carrier))
        for x in xs[1:]:
            total = it_.binop("+", total, x, node)
        return total

    @bi("min", 1)
    def _min(it_, node, xs):
        support = all_sources(xs)
        xs = as_list(xs, node)
        if not xs:
            raise it.err("min of an empty list", node)
        best = xs[0]
        for x in xs[1:]:
            if strip(it_.binop("<", x, best, node)):
                best = x
        return wrap(best, support)

    @bi("max", 1)
    def _max(it_, node, xs):
        support = all_sources(xs)
        xs = as_list(xs, node)
        if not xs:
            raise it.err("max of an empty list", node)
        best = xs[0]
        for x in xs[1:]:
            if strip(it_.binop(">", x, best, node)):
                best = x
        return wrap(best, support)

    @bi("push", 2)
    def _push(it_, node, xs, v):
        as_list(xs, node).append(wrap(v, it_.pc) if it_.pc else v)
        return xs

    @bi("pop", 1)
    def _pop(it_, node, xs):
        lst = as_list(xs, node)
        if not lst:
            raise it.err("pop from an empty list", node)
        return lst.pop()

    @bi("keys", 1)
    def _keys(it_, node, m):
        m = strip(m)
        if not isinstance(m, dict):
            raise it.err(f"keys needs a map, got {type_name(m)}", node)
        return list(m.keys())

    @bi("values", 1)
    def _values(it_, node, m):
        return list(strip(m).values())

    @bi("has", 2)
    def _has(it_, node, m, k):
        return wrap(hashable_key(k, node) in strip(m), srcs(m, k))

    @bi("get", 3)
    def _get(it_, node, m, k, default):
        return wrap(strip(m).get(hashable_key(k, node), default), srcs(m, k))

    @bi("map", 2)
    def _map(it_, node, xs, f):
        return [it_.call(f, [x], node) for x in as_list(xs, node)]

    @bi("filter", 2)
    def _filter(it_, node, xs, f):
        out, support = [], set(srcs(xs, f))
        for x in as_list(xs, node):
            decision = it_.call(f, [x], node)
            support.update(srcs(decision))
            if it_.truth(decision, node):
                out.append(x)
        return wrap(out, support)

    @bi("reduce", 3)
    def _reduce(it_, node, xs, f, init):
        acc = init
        for x in as_list(xs, node):
            acc = it_.call(f, [acc, x], node)
        return acc

    @bi("sort", (1, 2))
    def _sort(it_, node, xs, key=None):
        import functools
        lst = list(as_list(xs, node))
        keys = [it_.call(key, [x], node) if key is not None else x for x in lst]  # each key computed once
        raw = [strip(k) for k in keys]
        # fast path: every key is one plain orderable kind -> native sort (stable, same order as the comparison path)
        kinds = {type(k) for k in raw}
        if len(kinds) == 1 and kinds <= {Decimal, str, _dt.date, Money}:
            nat = [k.cents for k in raw] if kinds == {Money} else raw
            order = sorted(range(len(lst)), key=nat.__getitem__)
            return [lst[i] for i in order]

        def cmp(i, j):
            if strip(it_.binop("<", keys[i], keys[j], node)):
                return -1
            if strip(it_.binop(">", keys[i], keys[j], node)):
                return 1
            return 0
        return [lst[i] for i in sorted(range(len(lst)), key=functools.cmp_to_key(cmp))]

    @bi("reverse", 1)
    def _reverse(it_, node, xs):
        return list(reversed(as_list(xs, node)))

    @bi("range", (1, 2))
    def _range(it_, node, a, b=None):
        if b is None:
            a, b = Decimal(0), a
        return [Decimal(i) for i in range(int(num(a, node)), int(num(b, node)))]

    @bi("join", 2)
    def _join(it_, node, xs, sep):
        lst = as_list(xs, node)
        return wrap(str(strip(sep)).join(show(x) for x in lst), srcs(*lst))

    @bi("split", 2)
    def _split(it_, node, s, sep):
        return [wrap(p, srcs(s)) for p in str(strip(s)).split(str(strip(sep)))]

    @bi("trim", 1)
    def _trim(it_, node, s):
        return wrap(str(strip(s)).strip(), srcs(s))

    @bi("upper", 1)
    def _upper(it_, node, s):
        return wrap(str(strip(s)).upper(), srcs(s))

    @bi("lower", 1)
    def _lower(it_, node, s):
        return wrap(str(strip(s)).lower(), srcs(s))

    @bi("contains", 2)
    def _contains(it_, node, s, part):
        return it_.binop("in", part, s, node)

    @bi("replace", 3)
    def _replace(it_, node, s, a, b):
        return wrap(str(strip(s)).replace(str(strip(a)), str(strip(b))), srcs(s))

    @bi("assert", (1, 2))
    def _assert(it_, node, cond, msg="assertion failed"):
        if not it_.truth(cond, node):
            raise Thrown(f"assert failed: {show(msg)}", node.line, node.col)

    @bi("error", 1)
    def _error(it_, node, msg):
        raise Thrown(msg, node.line, node.col)

    @bi("sources", 1)
    def _sources(it_, node, x):
        return sorted(all_sources(x))

    @bi("value", 1)
    def _value(it_, node, x):
        return strip(x)

    @bi("read_text", 1)
    def _read_text(it_, node, p):
        with open(resolve_path(it_, p), encoding="utf-8") as fh:
            return wrap(fh.read(), {f"file:{strip(p)}"})

    @bi("write_text", 2)
    def _write_text(it_, node, p, text):
        path = resolve_path(it_, p)
        if os.path.exists(path) and not os.environ.get("TALLY_ALLOW_OVERWRITE"):
            raise it.err(f"{path} exists; set TALLY_ALLOW_OVERWRITE=1 to replace it", node)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(show(text))
        return None

    @bi("read_csv", 1)
    def _read_csv(it_, node, p):
        path = resolve_path(it_, p)
        with open(path, newline="", encoding="utf-8") as fh:
            return [{k2: wrap(v, {f"{os.path.basename(path)} row {i + 2}"}) for k2, v in row.items()}
                    for i, row in enumerate(csv.DictReader(fh))]

    def quantified(it_, node, xs, f, want_any):
        # Keep short-circuit behavior; retain only inspected dependencies.
        evidence = srcs(xs, f)
        for x in as_list(xs, node):
            result = it_.call(f, [x], node)
            evidence |= srcs(x, result)
            truth = it_.truth(result, node)
            if truth == want_any:
                return wrap(want_any, evidence)
        return wrap(not want_any, evidence)

    @bi("any", 2)
    def _any(it_, node, xs, f):
        return quantified(it_, node, xs, f, True)

    @bi("all", 2)
    def _all(it_, node, xs, f):
        return quantified(it_, node, xs, f, False)

    @bi("find", 2)
    def _find(it_, node, xs, f):
        for x in as_list(xs, node):
            if it_.truth(it_.call(f, [x], node), node):
                return x
        return None

    @bi("index_of", 2)
    def _index_of(it_, node, xs, v):
        x = strip(xs)
        if isinstance(x, str):
            i = x.find(str(strip(v)))
            return Decimal(i)
        for i, y in enumerate(as_list(xs, node)):
            if equal(y, v):
                return Decimal(i)
        return Decimal(-1)

    @bi("unique", 1)
    def _unique(it_, node, xs):
        out = []
        for x in as_list(xs, node):
            if not any(equal(x, y) for y in out):
                out.append(x)
        return out

    @bi("zip", 2)
    def _zip(it_, node, a, b):
        return [[x, y] for x, y in zip(as_list(a, node), as_list(b, node))]

    @bi("flatten", 1)
    def _flatten(it_, node, xs):
        out = []
        for x in as_list(xs, node):
            x2 = strip(x)
            out.extend(x2 if isinstance(x2, list) else [x])
        return out

    @bi("group_by", 2)
    def _group_by(it_, node, xs, f):
        out = {}
        for x in as_list(xs, node):
            k2 = hashable_key(it_.call(f, [x], node), node)
            out.setdefault(k2, []).append(x)
        return out

    @bi("count_by", 2)
    def _count_by(it_, node, xs, f):
        out = {}
        for x in as_list(xs, node):
            k2 = hashable_key(it_.call(f, [x], node), node)
            out[k2] = out.get(k2, Decimal(0)) + 1
        return out

    @bi("sum_by", 2)
    def _sum_by(it_, node, xs, f):
        out = {}
        for x in as_list(xs, node):
            k2 = hashable_key(it_.call(f, [x], node), node)
            out[k2] = it_.binop("+", out[k2], x, node) if k2 in out else x
        return out

    @bi("starts_with", 2)
    def _starts(it_, node, s_, p):
        return str(strip(s_)).startswith(str(strip(p)))

    @bi("ends_with", 2)
    def _ends(it_, node, s_, p):
        return str(strip(s_)).endswith(str(strip(p)))

    @bi("chars", 1)
    def _chars(it_, node, s_):
        return [wrap(c, srcs(s_)) for c in str(strip(s_))]

    @bi("repeat", 2)
    def _repeat(it_, node, s_, n):
        return str(strip(s_)) * int(num(n, node))

    @bi("pad_left", (2, 3))
    def _pad_left(it_, node, s_, n, ch=" "):
        return wrap(show(s_).rjust(int(num(n, node)), str(strip(ch))), srcs(s_))

    @bi("pad_right", (2, 3))
    def _pad_right(it_, node, s_, n, ch=" "):
        return wrap(show(s_).ljust(int(num(n, node)), str(strip(ch))), srcs(s_))

    @bi("lines", 1)
    def _lines(it_, node, s_):
        return [wrap(l2, srcs(s_)) for l2 in str(strip(s_)).splitlines()]

    @bi("read_lines", 1)
    def _read_lines(it_, node, p):
        path = resolve_path(it_, p)
        with open(path, encoding="utf-8") as fh:
            return [wrap(l2.rstrip("\n"), {f"{os.path.basename(path)} line {i + 1}"})
                    for i, l2 in enumerate(fh)]

    @bi("json_parse", 1)
    def _json_parse(it_, node, s_):
        def conv(v):
            if isinstance(v, dict):
                return {k2: conv(x) for k2, x in v.items()}
            if isinstance(v, list):
                return [conv(x) for x in v]
            if isinstance(v, float):
                return Decimal(repr(v))
            if isinstance(v, int) and not isinstance(v, bool):
                return Decimal(v)
            return v
        try:
            return wrap_deep(conv(_json.loads(str(strip(s_)))), srcs(s_))
        except ValueError as ex:
            raise it.err(f"not valid JSON: {ex}", node)

    @bi("json", (1, 2))
    def _json_out(it_, node, x, pretty=False):
        return _json.dumps(to_json(x), indent=2 if strip(pretty) is True else None, ensure_ascii=False)

    @bi("read_json", 1)
    def _read_json(it_, node, p):
        path = resolve_path(it_, p)
        with open(path, encoding="utf-8") as fh:
            return _json_parse(it_, node, wrap(fh.read(), {f"file:{os.path.basename(path)}"}))

    @bi("write_csv", 2)
    def _write_csv(it_, node, p, rows):
        path = resolve_path(it_, p)
        if os.path.exists(path) and not os.environ.get("TALLY_ALLOW_OVERWRITE"):
            raise it.err(f"{path} exists; set TALLY_ALLOW_OVERWRITE=1 to replace it", node)
        rows = [strip(r) for r in as_list(rows, node)]
        cols = []
        for r in rows:
            for k2 in (r.keys() if isinstance(r, dict) else r.type.fields):
                if k2 not in cols:
                    cols.append(k2)
        with open(path, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(cols)
            for r in rows:
                d = r if isinstance(r, dict) else r.vals
                w.writerow([show(d.get(c)) if c in d else "" for c in cols])
        return Decimal(len(rows))

    @bi("table", (1, 2))
    def _table(it_, node, rows, cols=None):
        """print a list of maps/records as an aligned text table; money and numbers right-aligned."""
        rows = [strip(r) for r in as_list(rows, node)]
        if cols is None:
            cols = []
            for r in rows:
                for k2 in (r.keys() if isinstance(r, dict) else r.type.fields):
                    if k2 not in cols:
                        cols.append(k2)
        else:
            cols = [str(strip(c)) for c in as_list(cols, node)]
        cells = []
        for r in rows:
            d = r if isinstance(r, dict) else r.vals
            cells.append([show(d[c]) if c in d else "" for c in cols])
        right = [all(isinstance(strip((r if isinstance(r, dict) else r.vals).get(c)), (Decimal, Money))
                     for r in rows) for c in cols]
        widths = [max([len(c)] + [len(row[i]) for row in cells]) for i, c in enumerate(cols)]
        def fmt(row):
            return "  ".join(v.rjust(widths[i]) if right[i] else v.ljust(widths[i]) for i, v in enumerate(row))
        it_.out.write(fmt(cols) + "\n" + "  ".join("-" * w for w in widths) + "\n")
        for row in cells:
            it_.out.write(fmt(row) + "\n")
        return None

    @bi("fields", 1)
    def _fields(it_, node, r):
        r = strip(r)
        if isinstance(r, Record):
            return list(r.type.fields)
        if isinstance(r, dict):
            return list(r.keys())
        raise it.err(f"{type_name(r)} has no fields", node)

    @bi("to_map", 1)
    def _to_map(it_, node, r):
        r = strip(r)
        if isinstance(r, Record):
            return dict(r.vals)
        if isinstance(r, dict):
            return dict(r)
        raise it.err(f"cannot turn {type_name(r)} into a map", node)

    @bi("format", 2)
    def _format(it_, node, x, spec):
        """format(x, spec): "0.00" fixed places · "#,##0.00" thousands · "0%" percent · "<8" / ">8" / "^8" pad"""
        spec = str(strip(spec))
        v = strip(x)
        m = re.fullmatch(r"([<>^])(\d+)", spec)
        if m:
            w = int(m.group(2))
            t = show(v)
            return {"<": t.ljust(w), ">": t.rjust(w), "^": t.center(w)}[m.group(1)]
        if isinstance(v, Money):
            v = v.dec()
        if not isinstance(v, Decimal):
            raise it.err(f"format needs a number or money for spec {spec!r}, got {type_name(v)}", node)
        pct = spec.endswith("%")
        core = spec[:-1] if pct else spec
        if pct:
            v = v * 100
        places = len(core.split(".")[1]) if "." in core else 0
        q = v.quantize(Decimal(1).scaleb(-places), rounding=ROUND_HALF_EVEN)
        text = f"{q:,.{places}f}" if "," in core else f"{q:.{places}f}"
        return wrap(text + ("%" if pct else ""), srcs(x))

    @bi("read_jsonl", 1)
    def _read_jsonl(it_, node, p):
        path = resolve_path(it_, p)
        out = []
        with open(path, encoding="utf-8") as fh:
            for i, line in enumerate(fh):
                if line.strip():
                    out.append(_json_parse(it_, node, wrap(line, {f"{os.path.basename(path)} line {i + 1}"})))
        return out

    @bi("between", 2)
    def _between(it_, node, lo, hi):
        """a range value: everything from lo to hi (money or numbers); arithmetic on it is exact range arithmetic"""
        a, b = strip(lo), strip(hi)
        if type_name(a) != type_name(b) or type_name(a) not in ("money", "number"):
            raise it.err("between needs two money values or two numbers", node)
        if strip(it_.binop(">", a, b, node)):
            raise it.err(f"between: low end {show(a)} is above high end {show(b)}", node)
        return wrap(Interval(a, b), srcs(lo, hi))

    @bi("low", 1)
    def _low(it_, node, r):
        """the low end of a range (a plain value is its own low end)"""
        v = strip(r)
        return wrap(v.lo if isinstance(v, Interval) else v, srcs(r))

    @bi("high", 1)
    def _high(it_, node, r):
        """the high end of a range"""
        v = strip(r)
        return wrap(v.hi if isinstance(v, Interval) else v, srcs(r))

    @bi("width", 1)
    def _width(it_, node, r):
        """high minus low: how much is not known"""
        v = strip(r)
        if not isinstance(v, Interval):
            return Decimal(0) if not isinstance(v, Money) else Money(0)
        return wrap(strip(it_.binop("-", v.hi, v.lo, node)), srcs(r))

    @bi("necessarily", 1)
    def _necessarily(it_, node, c):
        """true only if the condition holds for every value in its ranges (maybe -> false)"""
        v = strip(c)
        return wrap(v is True, srcs(c))

    @bi("possibly", 1)
    def _possibly(it_, node, c):
        """true if the condition holds for at least one value in its ranges (maybe -> true)"""
        v = strip(c)
        return wrap(v is True or isinstance(v, Maybe), srcs(c))

    @bi("contains_value", 2)
    def _contains_value(it_, node, r, x):
        """true if x lies inside the range (ends included)"""
        v = strip(r)
        if not isinstance(v, Interval):
            raise it.err("contains_value needs a range", node)
        return strip(it_.binop("<=", v.lo, x, node)) and strip(it_.binop("<=", x, v.hi, node))

    @bi("help", (0, 1))
    def _help(it_, node, x=None):
        """help(f) — name, kind, signature and doc of a function, built-in or record type; help() lists built-ins"""
        if x is None:
            return sorted(it_.builtins.vars)
        return describe_value(strip(x))

    @bi("sql", (2, 3))
    def _sql(it_, node, db, query, params=None):
        """read-only SQLite. Each value carries `<db>:<table-or-query> rowid` as its source when the row has one."""
        path = resolve_path(it_, db)
        con = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
        try:
            cur = con.execute(str(strip(query)), [to_py(strip(x)) for x in (strip(params) or [])])
            cols = [c[0] for c in cur.description]
            rows = cur.fetchall()
        finally:
            con.close()
        name = os.path.basename(path)
        out = []
        for i, r in enumerate(rows):
            tag = {f"{name} row {i + 1}"}
            if "bates" in cols and r[cols.index("bates")]:
                tag = {str(r[cols.index("bates")])}
            out.append({c: wrap(from_py(v), tag) for c, v in zip(cols, r)})
        return out


def wrap_deep(v, s):
    if not s:
        return v
    if isinstance(v, dict):
        return {k2: wrap_deep(x, s) for k2, x in v.items()}
    if isinstance(v, list):
        return [wrap_deep(x, s) for x in v]
    return wrap(v, s)


def to_json(x):
    x = strip(x)
    if isinstance(x, Decimal):
        return int(x) if x == x.to_integral_value() else float(x)
    if isinstance(x, Money):
        return str(x)
    if isinstance(x, _dt.date):
        return x.isoformat()
    if isinstance(x, list):
        return [to_json(v) for v in x]
    if isinstance(x, dict):
        return {str(k2): to_json(v) for k2, v in x.items()}
    if isinstance(x, Record):
        return {f: to_json(x.vals[f]) for f in x.type.fields}
    if isinstance(x, Interval):
        return {"low": to_json(x.lo), "high": to_json(x.hi)}
    if isinstance(x, Maybe):
        return "maybe"
    if hasattr(x, "tally_fields"):
        return {k2: to_json(v) for k2, v in x.tally_fields().items()}
    if isinstance(x, (Function, Builtin, BoundMethod, RecordType)):
        return show(x)
    return x


def resolve_path(it, p):
    """a file path as a program means it: ~ expanded; a relative path is relative to the program's own folder (as
    `import` is), falling back to the working folder for the REPL, sessions and eval"""
    path = os.path.expanduser(str(strip(p)))
    if os.path.isabs(path):
        return path
    prog = getattr(it, "path", "") or ""
    if prog and not prog.startswith("<") and os.path.exists(prog):
        return os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(prog)), path))
    return os.path.abspath(path)


def builtin_signature(b):
    import inspect
    try:
        ps = list(inspect.signature(b.fn).parameters.values())[2:]
    except (TypeError, ValueError):
        return f"{b.name}(…)"
    parts = []
    for p in ps:
        if p.kind == p.VAR_POSITIONAL:
            parts.append("…" + p.name)
        elif p.default is not p.empty:
            parts.append(f"{p.name} = {show(p.default, True) if p.default is not None else 'nil'}")
        else:
            parts.append(p.name)
    return f"{b.name}({', '.join(parts)})"


def describe_value(x):
    if isinstance(x, Function):
        return {"name": x.name, "kind": "function", "signature": x.signature(), "doc": x.spec.get("doc"),
                "params": [{"name": p, "type": x.spec["types"].get(p), "has_default": p in x.spec["defaults"]}
                           for p in x.params], "returns": x.spec.get("ret"),
                "requires": [t for _, t in x.spec.get("requires", [])],
                "ensures": [t for _, t in x.spec.get("ensures", [])]}
    if isinstance(x, BoundMethod):
        return describe_value(x.fn)
    if isinstance(x, Builtin):
        import tally_docs as D
        out = {"name": x.name, "kind": "builtin", "signature": builtin_signature(x),
               "doc": (x.fn.__doc__ or "").strip() or None}
        if x.name in D.DOCS:
            e = D.entry(x.name)
            out.update({"doc": e["doc"], "group": e["group"], "example": e["example"], "result": e["result"]})
        return out
    if isinstance(x, RecordType):
        return {"name": x.name, "kind": "record type", "fields": list(x.fields),
                "defaults": {k: show(v, True) for k, v in x.defaults.items()},
                "methods": {k: m.signature() for k, m in x.methods.items()}}
    return {"name": None, "kind": type_name(x), "value": show(x, True)}


def to_py(x):
    if isinstance(x, Decimal):
        return int(x) if x == x.to_integral_value() else float(x)
    if isinstance(x, Money):
        return float(x.dec())
    if isinstance(x, _dt.date):
        return x.isoformat()
    return x


def from_py(v):
    if isinstance(v, bool):
        return v
    if isinstance(v, int):
        return Decimal(v)
    if isinstance(v, float):
        return Decimal(repr(v))
    return v


BUILTIN_NAMES = set()
_probe = Interp.__new__(Interp)
_probe.builtins = Env()
install_builtins(_probe)
import tally_logic as _tl  # noqa: E402
import tally_data as _td  # noqa: E402
import tally_experiments as _tx  # noqa: E402
import tally_math as _tm  # noqa: E402
import tally_reason as _tr  # noqa: E402
import tally_audit as _ta  # noqa: E402
import tally_qubit as _tq  # noqa: E402
import tally_quantum as _qsim  # noqa: E402
import tally_qtime as _tt  # noqa: E402
import tally_qsense as _ts  # noqa: E402
import tally_reconcile as _rc  # noqa: E402
import tally_native as _nt  # noqa: E402
import tally_documents as _pdf
import tally_terms as _terms
import tally_applications as _ap
import tally_obligations as _ob
import tally_qledger as _ql
import tally_accounting as _ac  # noqa: E402
import tally_qsearch as _qs  # noqa: E402
import tally_exchange as _ex  # noqa: E402

_tl.install(_probe)
_td.install(_probe)
_tx.install(_probe)
_tm.install(_probe)
_tr.install(_probe)
_tq.install(_probe)
_qsim.install(_probe)
_tt.install(_probe)
_ts.install(_probe)
_ta.install(_probe)
_rc.install(_probe)
_nt.install(_probe)
_ac.install(_probe)
_qs.install(_probe)
_ex.install(_probe)
_pdf.install(_probe)
_terms.install(_probe)
_ap.install(_probe)
_ob.install(_probe)
_ql.install(_probe)
BUILTIN_NAMES = set(_probe.builtins.vars)


# ================================================================ static check
class Checker:
    """`tally check FILE`: undefined names, redefinitions, assignment without let, unreachable code,
    unused let bindings, calls with the wrong number of arguments to functions defined in the file."""

    def __init__(self, path, strict=False):
        self.path = path
        self.strict = strict
        self.findings = []
        self.hoisted = set()  # top-level functions / records: a function body may call one defined further down
        self.fn_depth = 0

    def note(self, level, msg, node):
        self.findings.append((level, node.line, node.col, msg))

    def check(self, stmts):
        scope = {"__parent": None, "__names": {}}
        for st in stmts:
            if st.k == "let" and st.a[1].k == "fn":
                self.hoisted.add(st.a[0])
            elif st.k == "record":
                self.hoisted.add(st.a[0])
        for n in BUILTIN_NAMES:
            scope["__names"][n] = {"kind": "builtin", "used": True, "node": None}
        self.block(stmts, scope, in_fn=False, in_loop=False)
        if self.strict:  # an AI reading this program's API needs a doc line and full types on every top-level function
            for st in stmts:
                if st.k == "let" and st.a[1].k == "fn":
                    spec = st.a[1].a[3] if len(st.a[1].a) > 3 else {"types": {}, "ret": None, "doc": None}
                    if not spec.get("doc"):
                        self.note("warn", f"function '{st.a[0]}' has no doc string", st)
                    untyped = [p for p in st.a[1].a[1] if p not in spec.get("types", {})]
                    if untyped or not spec.get("ret"):
                        what = (f"parameters {untyped} have no type" if untyped else "") + \
                            (" and " if untyped and not spec.get("ret") else "") + \
                            ("no return type" if not spec.get("ret") else "")
                        self.note("warn", f"function '{st.a[0]}': {what}", st)
        # top-level names are not reported as unused: a module exports them
        return sorted(self.findings, key=lambda f: (f[1], f[2]))

    def new_scope(self, parent):
        return {"__parent": parent, "__names": {}}

    def lookup(self, scope, name):
        while scope is not None:
            if name in scope["__names"]:
                return scope["__names"][name]
            scope = scope["__parent"]
        return None

    def define(self, scope, name, node, kind="let", arity=None):
        if name in scope["__names"] and scope["__names"][name]["kind"] != "builtin":
            self.note("error", f"'{name}' is already defined in this scope", node)
        elif name in BUILTIN_NAMES and kind in ("let", "param") and node is not None:
            self.note("warn", f"'{name}' hides the built-in {name}() in this scope", node)
        scope["__names"][name] = {"kind": kind, "used": False, "node": node, "arity": arity}

    def unused(self, scope):
        for name, info in scope["__names"].items():
            if info["kind"] in ("let", "param") and not info["used"] and info["node"] is not None \
                    and not name.startswith("_"):
                self.note("warn", f"'{name}' is defined but never used", info["node"])

    def block(self, stmts, scope, in_fn, in_loop):
        dead = False
        for s in stmts:
            if dead:
                self.note("warn", "unreachable code", s)
                dead = False
            self.stmt(s, scope, in_fn, in_loop)
            if s.k in ("return", "break", "continue", "throw"):
                dead = True

    def stmt(self, s, scope, in_fn, in_loop):
        k, a = s.k, s.a
        if k == "let":
            arity = None
            if a[1].k == "fn":
                spec = a[1].a[3] if len(a[1].a) > 3 else {"defaults": {}}
                arity = (len([p for p in a[1].a[1] if p not in spec["defaults"]]), len(a[1].a[1]))
            if a[1].k == "fn":
                self.define(scope, a[0], s, "let", arity)  # defined first so the body may recurse
                self.expr(a[1], scope)
            else:
                self.expr(a[1], scope)
                self.define(scope, a[0], s, "let", arity)
        elif k == "record":
            for _, d in a[1]:
                if d is not None:
                    self.expr(d, scope)
            self.define(scope, a[0], s, "record")
        elif k == "method":
            info = self.lookup(scope, a[0])
            if info is None:
                self.note("error", f"'{a[0]}' is not defined", s)
            else:
                info["used"] = True
            self.expr(a[2], scope)
        elif k == "assign":
            t = a[0]
            if t.k == "name":
                info = self.lookup(scope, t.a[0])
                if info is None:
                    self.note("error", f"'{t.a[0]}' is not defined (use let)", t)
                else:
                    info["used"] = True
            else:
                self.expr(t, scope)
            self.expr(a[2], scope)
        elif k == "expr":
            self.expr(a[0], scope)
        elif k == "if":
            self.expr(a[0], scope)
            self.block(a[1], self.new_scope(scope), in_fn, in_loop)
            if a[2] is not None:
                self.block(a[2], self.new_scope(scope), in_fn, in_loop)
        elif k == "while":
            self.expr(a[0], scope)
            self.block(a[1], self.new_scope(scope), in_fn, True)
        elif k == "for":
            self.expr(a[2], scope)
            inner = self.new_scope(scope)
            self.define(inner, a[0], s, "param")
            inner["__names"][a[0]]["used"] = True
            if a[1]:
                self.define(inner, a[1], s, "param")
                inner["__names"][a[1]]["used"] = True
            self.block(a[3], inner, in_fn, True)
        elif k == "return":
            if not in_fn:
                self.note("error", "return outside a function", s)
            if a[0] is not None:
                self.expr(a[0], scope)
        elif k in ("break", "continue"):
            if not in_loop:
                self.note("error", f"{k} outside a loop", s)
        elif k == "throw":
            self.expr(a[0], scope)
        elif k == "try":
            self.block(a[0], self.new_scope(scope), in_fn, in_loop)
            inner = self.new_scope(scope)
            self.define(inner, a[1], s, "param")
            inner["__names"][a[1]]["used"] = True
            self.block(a[2], inner, in_fn, in_loop)
        elif k == "import":
            self.define(scope, a[1], s, "module")
        elif k == "test":
            self.block(a[1], self.new_scope(scope), False, False)
        elif k == "fact":
            for x in a[1]:
                self.expr(x, scope)
            if a[3] is not None:
                self.expr(a[3], scope)
        elif k == "retract":
            for x in a[1]:
                self.expr(x, scope)
        elif k == "alias":
            pass
        elif k == "rule":
            inner = self.new_scope(scope)
            for c in a[1]:
                if c["kind"] in ("pos", "neg"):
                    for x in c["args"]:
                        if x.k == "name" and (x.a[0][:1].islower() or x.a[0] == "_"):
                            inner["__names"][x.a[0]] = {"kind": "param", "used": True, "node": x}
                        else:
                            self.expr(x, inner)
            for c in a[1]:
                if c["kind"] == "let":
                    self.expr(c["expr"], inner)
                    inner["__names"][c["name"]] = {"kind": "param", "used": True, "node": s}
                elif c["kind"] == "guard":
                    self.expr(c["expr"], inner)
            for c in a[3]:
                for x in c["args"]:
                    if x.k == "name" and (x.a[0][:1].islower() or x.a[0] == "_"):
                        if x.a[0] != "_" and x.a[0] not in inner["__names"]:
                            inner["__names"][x.a[0]] = {"kind": "param", "used": True, "node": x}
                    else:
                        self.expr(x, inner)
            for c in a[2]:
                for x in c["args"]:
                    if not (x.k == "name" and x.a[0][:1].islower()):
                        self.expr(x, inner)
                    elif x.a[0] not in inner["__names"]:
                        self.note("error", f"rule {a[0]}: '{x.a[0]}' in the conclusion is not bound by a condition", x)
        elif k == "suppose":
            self.block(a[0], self.new_scope(scope), in_fn, in_loop)
            self.block(a[1], self.new_scope(scope), in_fn, in_loop)
        elif k == "match":
            self.expr(a[0], scope)
            for pats, guard, body, ctok in a[1]:
                inner = self.new_scope(scope)
                for p in pats:
                    self.pattern(p, inner, scope)
                if guard is not None:
                    self.expr(guard, inner)
                self.block(body, inner, in_fn, in_loop)

    def pattern(self, p, inner, scope):
        if p.k == "pat_bind":
            inner["__names"][p.a[0]] = {"kind": "param", "used": True, "node": p}
        elif p.k == "pat_lit":
            self.expr(p.a[0], scope)
        elif p.k == "pat_record":
            if self.lookup(scope, p.a[0]) is None:
                self.note("error", f"'{p.a[0]}' is not defined", p)
            for q in p.a[1]:
                self.pattern(q, inner, scope)
        elif p.k == "pat_list":
            for q in p.a[0]:
                self.pattern(q, inner, scope)
            if p.a[1]:
                inner["__names"][p.a[1]] = {"kind": "param", "used": True, "node": p}

    def expr(self, e, scope):
        k, a = e.k, e.a
        if k == "name":
            info = self.lookup(scope, a[0])
            if info is None:
                if not (self.fn_depth and a[0] in self.hoisted):
                    self.note("error", f"'{a[0]}' is not defined", e)
            else:
                info["used"] = True
        elif k == "fn":
            spec = a[3] if len(a) > 3 else {"types": {}, "defaults": {}}
            for d in spec["defaults"].values():
                self.expr(d, scope)
            for p, t in spec["types"].items():
                base = t.rstrip("?").split(".")[0]
                if base not in TYPE_NAMES and self.lookup(scope, base) is None and not (
                        self.fn_depth == 0 and base in self.hoisted):
                    self.note("error", f"unknown type '{t}' for parameter '{p}' (types: "
                                       f"{', '.join(sorted(TYPE_NAMES))}, or a record name)", e)
            inner = self.new_scope(scope)
            self.fn_depth += 1
            for p in a[1]:
                self.define(inner, p, e, "param")
            for cond, _ in spec.get("requires", []):
                self.expr(cond, inner)
            if spec.get("ensures"):
                rs = self.new_scope(inner)
                rs["__names"]["result"] = {"kind": "param", "used": True, "node": None}
                for cond, _ in spec["ensures"]:
                    self.expr(cond, rs)
            self.block(a[2], inner, True, False)
            self.unused(inner)
            self.fn_depth -= 1
        elif k == "pipe":
            self.expr(a[0], scope)
            r = a[1]
            if r.k == "call":
                self.expr(N("call", (r.a[0], [N("val", (None,), None)] + list(r.a[1])), r), scope)
            else:
                self.expr(r, scope)
        elif k == "named":
            self.expr(a[1], scope)
        elif k == "cond":
            for x in a:
                self.expr(x, scope)
        elif k == "call":
            fn_node, args = a
            if fn_node.k == "name" and not any(x.k == "named" for x in args):
                info = self.lookup(scope, fn_node.a[0])
                ar = info.get("arity") if info is not None else None
                if ar is not None and not ar[0] <= len(args) <= ar[1]:
                    count = f"{ar[0]}" if ar[0] == ar[1] else f"{ar[0]}..{ar[1]}"
                    self.note("error", f"{fn_node.a[0]} takes {count} argument(s), got {len(args)}", e)
            if fn_node.k == "field":
                self.expr(fn_node.a[0], scope)  # method syntax may resolve at run time
            else:
                self.expr(fn_node, scope)
            for x in args:
                self.expr(x, scope)
        elif k == "interp":
            for p in a[0]:
                if not isinstance(p, str):
                    self.expr(p, scope)
        elif k == "list":
            for x in a[0]:
                self.expr(x, scope)
        elif k == "map":
            for kn, vn in a[0]:
                self.expr(kn, scope)
                self.expr(vn, scope)
        elif k == "bin":
            self.expr(a[1], scope)
            self.expr(a[2], scope)
        elif k in ("neg", "not"):
            self.expr(a[0], scope)
        elif k == "index":
            self.expr(a[0], scope)
            self.expr(a[1], scope)
        elif k == "slice":
            self.expr(a[0], scope)
            if a[1] is not None:
                self.expr(a[1], scope)
            if a[2] is not None:
                self.expr(a[2], scope)
        elif k == "field":
            self.expr(a[0], scope)
        elif k == "goal":
            for x in a[1]:
                if x.k == "name" and (x.a[0] == "_" or (x.a[0][:1].islower() and self.lookup(scope, x.a[0]) is None)):
                    continue  # an unbound lowercase name in ?P(...) is a query variable
                self.expr(x, scope)


def check_file(path, out=None, strict=False):
    out = out or sys.stdout
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    try:
        stmts = parse(src, path)
    except TallyError as e:
        out.write(f"error: {e}\n")
        return False
    findings = Checker(path, strict).check(stmts)
    for level, line, col, msg in findings:
        out.write(f"{path}:{line}:{col}: {level}: {msg}\n")
    errors = sum(1 for f in findings if f[0] == "error")
    out.write(f"{errors} error(s), {len(findings) - errors} warning(s)\n")
    return errors == 0


# ================================================================ reference (AI-facing)
KEYWORD_FORMS = [
    {"form": "let NAME = EXPR", "doc": "define a variable (once per scope)"},
    {"form": "NAME = EXPR / NAME += EXPR", "doc": "reassign a defined variable, list item or field"},
    {"form": "fn NAME(a: type, b: type = default) -> type { \"doc\" … }", "doc": "function; types, defaults, "
     "return type and a first-line doc string are optional and checked at call time"},
    {"form": "fn(x) => EXPR", "doc": "function expression"},
    {"form": "fn NAME(a: type) -> type requires COND ensures COND { … }", "doc": "contracts: requires is checked "
     "on entry, ensures on return (`result` is the returned value); a failure is E_CONTRACT with the values"},
    {"form": "f(a, name: value)", "doc": "named arguments (functions, built-ins, record constructors); defaults "
     "fill the rest"},
    {"form": "x |> f(a) |> g", "doc": "pipeline: x |> f(a) is f(x, a); a line may start with |>"},
    {"form": "if C then A else B", "doc": "conditional expression (a value); C must be true or false"},
    {"form": "between(lo, hi)  ·  r < x  ·  necessarily(c) / possibly(c)", "doc": "range values: + - and × number "
     "are exact; < <= > >= give true, false or maybe (maybe cannot drive an if); == and != are structural (same ends)"},
    {"form": "record NAME { field, field = default }", "doc": "record type; construct with NAME(…) or NAME({…})"},
    {"form": "fn NAME.method(self, …) { … }", "doc": "method on a record type"},
    {"form": "if C { … } else if C { … } else { … }", "doc": "conditions must be true/false"},
    {"form": "while C { … } / for x in LIST { … } / for i, v in LIST / for k, v in MAP", "doc": "loops; break, continue"},
    {"form": "match V { case PATTERN if GUARD { … } case _ { … } }", "doc": "patterns: literals, names, _, "
     "[first, ..rest], Record(a, b)"},
    {"form": "try { … } catch e { … } / throw V", "doc": "errors; a caught interpreter error is its message text"},
    {"form": "import \"path.tly\" as M", "doc": "module; M.name for its top-level names"},
    {"form": "test \"name\" { assert(…) }", "doc": "a test block; run with `tally test FILE`"},
    {"form": "VALUE from \"source\"", "doc": "attach a record cite; results built from it carry it, and so does anything set, pushed or returned inside a branch (if / while / match) that a sourced value chose"},
    {"form": "fact P(a, b) from \"source\" / fact not P(…) from …", "doc": "assert a fact (or its explicit "
     "falsity); a second source adds; true + false from different sources becomes `conflicted`"},
    {"form": "rule NAME { when P(x), not Q(x), let y = EXPR, GUARD => R(x, y) unless D(x) }",
     "doc": "forward-chaining rule; lowercase names are variables, _ matches anything"},
    {"form": "?P(a, x, _)", "doc": "a fact pattern for holds/query/explain/…; unbound lowercase names are variables"},
    {"form": "retract P(…)", "doc": "remove a base fact"},
    {"form": 'alias "Alex Example" = "Example Company", "ExampleCo"', "doc": "one party under several names: "
     "facts, rule patterns, goals and queries use the first name; each renamed fact carries the alias as a source"},
    {"form": "suppose { … } then { … }", "doc": "what-if: change facts/rules, re-infer, run the then-block, restore"},
]
LITERALS = [
    {"literal": "42, 1.5", "type": "number", "doc": "exact decimals (50 digits); 0.1 + 0.2 == 0.3"},
    {"literal": "$1,234.56", "type": "money", "doc": "exact cents; adds only to money; × number must stay in whole cents"},
    {"literal": "@2040-02-13", "type": "date", "doc": "date - date = days; date + n = date; @a..@b = days"},
    {"literal": "\"text {expr}\" / \"\"\"multi-line\"\"\"", "type": "string", "doc": "interpolation; \\{ for a brace"},
    {"literal": "[1, 2]", "type": "list", "doc": "xs[0], xs[-1], xs[1:3]"},
    {"literal": "{name: \"x\", amount: $1.00}", "type": "map", "doc": "m.name, m[\"name\"]; keys may be words"},
    {"literal": "true, false, nil", "type": "bool / nil", "doc": "no truthiness: conditions need a bool"},
]


def reference(verify=False):
    """the whole language as data. With verify=True every example is run and its result compared."""
    import tally_docs as D
    it = Interp("<describe>")
    names = sorted(it.builtins.vars)
    builtins_, missing, failures = [], [], []
    for n in names:
        b = it.builtins.vars[n]
        if n not in D.DOCS:
            missing.append(n)
            continue
        e = D.entry(n)
        row = {"name": n, "signature": builtin_signature(b), **e}
        if verify:
            row["verified"] = verify_example(D.PRELUDE, e)
            if row["verified"] is not True:
                failures.append({"name": n, "problem": row["verified"]})
        builtins_.append(row)
    extra = sorted(set(D.DOCS) - set(names))
    return {"language": "Tally", "version": VERSION, "groups": D.GROUPS, "keyword_forms": KEYWORD_FORMS,
            "literals": LITERALS, "types": sorted(TYPE_NAMES), "error_codes": [c for c, _ in ERROR_CODES] + ["E_RUNTIME"],
            "builtins": builtins_, "undocumented": missing, "documented_but_missing": extra,
            "example_failures": failures}


def verify_example(prelude, e):
    import io
    if e["data"] and not os.path.isfile(os.environ.get("TALLY_BANK_DB", "")):
        return "skipped: data not on this machine"
    lines = e["example"].split("\n")
    it = Interp("<example>", io.StringIO())
    try:
        it.run(prelude + "\n" + "\n".join(lines[:-1]))
        v = it.eval(Parser(lex(lines[-1]), "<example>").expr(), it.globals)
    except (TallyError, Thrown) as ex:
        return f"raised {ex}"
    got = show(v, True)
    return True if got == e["result"] else f"result {got} != documented {e['result']}"


# ================================================================ drivers
def run_file(path, out=None):
    it = Interp(path, out)
    with open(path, encoding="utf-8") as fh:
        it.run(fh.read(), path)
    return it


# ---------------------------------------------------------------- structured (JSON) results for agents
def file_sha(path):
    import hashlib
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def interpreter_pin():
    here = os.path.dirname(os.path.abspath(__file__))
    files = ["tally.py", "tally_logic.py", "tally_data.py", "tally_docs.py", "tally_experiments.py", "tally_math.py", "tally_reason.py", "tally_audit.py", "tally_qubit.py", "tally_quantum.py", "tally_qtime.py", "tally_qsense.py", "tally_reconcile.py", "tally_native.py", "tally_accounting.py", "tally_qsearch.py", "tally_exchange.py", "tally_documents.py", "tally_obligations.py", "tally_qledger.py", "tally_applications.py", "tally_terms.py"]

    return {"version": VERSION, "sha256": {f: file_sha(os.path.join(here, f)) for f in files
                                          if os.path.exists(os.path.join(here, f))}}


def thrown_map(t):
    return {"code": "E_THROWN", "message": show(t.value), "value": to_json(t.value), "line": t.line, "col": t.col,
            "hint": None, "trace": [{"function": n, "called_at_line": l}
                                    for n, l in reversed(getattr(t, "trace", None) or [])]}


def reasoning_state(it):
    kb = it.kb
    return {"base_facts": len(kb.base), "derived_facts": len(kb.derived), "rules": [r.name for r in kb.rules],
            "open": [dict(o) for o in kb.open], "defeated": [dict(d) for d in kb.defeated],
            "conflicted": sorted(kb.conflicted)}


def run_json(path, budget=None):
    import io
    import time
    out = io.StringIO()
    t0 = time.time()
    res = {"schema": "tally.run.v1", "ok": True, "file": path, "inputs": {path: file_sha(path)},
           "interpreter": interpreter_pin(), "error": None}
    it = Interp(path, out, budget=budget)
    try:
        with open(path, encoding="utf-8") as fh:
            it.run(fh.read(), path)
    except TallyError as e:
        res["ok"], res["error"] = False, e.to_map()
    except Thrown as t:
        res["ok"], res["error"] = False, thrown_map(t)
    except (BreakSignal, ContinueSignal, ReturnSignal):
        res["ok"], res["error"] = False, {"code": "E_SYNTAX", "message": "break/continue/return outside a loop "
                                          "or function", "line": 0, "col": 0, "hint": None, "trace": []}
    for p in it.modules:
        if os.path.exists(p):
            res["inputs"][p] = file_sha(p)
    res["output"] = out.getvalue()
    res["reasoning"] = reasoning_state(it)
    res["seconds"] = round(time.time() - t0, 3)
    return res


def tests_json(path, budget=None):
    import io
    out = io.StringIO()
    res = {"schema": "tally.test.v1", "ok": False, "file": path, "inputs": {path: file_sha(path)},
           "interpreter": interpreter_pin(), "tests": [], "passed": 0, "total": 0, "error": None}
    it = Interp(path, out, budget=budget)
    try:
        with open(path, encoding="utf-8") as fh:
            it.run(fh.read(), path)
    except TallyError as e:
        res["error"] = e.to_map()
        return res
    except Thrown as t:
        res["error"] = thrown_map(t)
        return res
    for name, body, env, node in it.tests:
        row = {"name": name, "ok": True, "line": node.line, "error": None}
        try:
            it.exec_block(body, Env(env))
        except Thrown as t:
            row["ok"], row["error"] = False, thrown_map(t)
        except TallyError as e:
            row["ok"], row["error"] = False, e.to_map()
        res["tests"].append(row)
    res["total"] = len(res["tests"])
    res["passed"] = sum(1 for r in res["tests"] if r["ok"])
    res["ok"] = res["passed"] == res["total"]
    res["output"] = out.getvalue()
    return res


def program_api(path):
    """the public surface of a program, read without running it: functions, records, rules, facts, tests, imports"""
    with open(path, encoding="utf-8") as fh:
        stmts = parse(fh.read(), path)

    def pat(c):
        args = ", ".join(show_src(x) if x.k != "name" else x.a[0] for x in c["args"])
        return ("not " if c.get("kind") == "neg" or c.get("truth") is False else "") + f"{c['pred']}({args})"
    api = {"schema": "tally.doc.v1", "file": path, "inputs": {path: file_sha(path)}, "functions": [], "records": [],
           "methods": [], "rules": [], "facts": [], "tests": [], "imports": []}
    for st in stmts:
        if st.k == "let" and st.a[1].k == "fn":
            f = Function(st.a[0], st.a[1].a[1], st.a[1].a[2], None, st.a[1].a[3] if len(st.a[1].a) > 3 else None)
            d = describe_value(f)
            d["line"] = st.line
            api["functions"].append(d)
        elif st.k == "method":
            f = Function(st.a[2].a[0], st.a[2].a[1], st.a[2].a[2], None, st.a[2].a[3] if len(st.a[2].a) > 3 else None)
            api["methods"].append(dict(describe_value(f), record=st.a[0], line=st.line))
        elif st.k == "record":
            api["records"].append({"name": st.a[0], "fields": [f for f, _ in st.a[1]],
                                   "defaults": {f: show_src(d) for f, d in st.a[1] if d is not None}, "line": st.line})
        elif st.k == "rule":
            conds = [pat(c) if c["kind"] in ("pos", "neg") else ("let " + c["name"] + " = …" if c["kind"] == "let"
                                                                  else "guard") for c in st.a[1]]
            api["rules"].append({"name": st.a[0], "when": conds, "then": [pat(c) for c in st.a[2]],
                                 "unless": [pat(u) for u in st.a[3]], "line": st.line})
        elif st.k == "fact":
            api["facts"].append({"fact": ("not " if not st.a[2] else "") + st.a[0], "line": st.line})
        elif st.k == "test":
            api["tests"].append({"name": st.a[0], "line": st.line})
        elif st.k == "import":
            api["imports"].append({"path": st.a[0], "as": st.a[1]})
    preds = {}
    for f in api["facts"]:
        preds[f["fact"].replace("not ", "")] = preds.get(f["fact"].replace("not ", ""), 0) + 1
    api["facts"] = [{"predicate": k, "count": v} for k, v in sorted(preds.items())]
    return api


def check_json(path, strict=False):
    res = {"schema": "tally.check.v1", "ok": False, "file": path, "inputs": {path: file_sha(path)},
           "interpreter": interpreter_pin(), "findings": [], "errors": 0, "warnings": 0}
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    try:
        stmts = parse(src, path)
    except TallyError as e:
        res["findings"] = [dict(e.to_map(), level="error")]
        res["errors"] = 1
        return res
    for level, line, col, msg in Checker(path, strict).check(stmts):
        res["findings"].append({"level": level, "line": line, "col": col, "message": msg,
                                "code": error_code(msg) if level == "error" else "W_" + (
                                    "UNUSED" if "never used" in msg else "SHADOW" if "hides the built-in" in msg
                                    else "UNREACHABLE" if "unreachable" in msg else "UNDOCUMENTED" if "no doc" in msg
                                    else "UNTYPED" if "no type" in msg or "no return type" in msg else "OTHER")})
    res["errors"] = sum(1 for f in res["findings"] if f["level"] == "error")
    res["warnings"] = len(res["findings"]) - res["errors"]
    res["ok"] = res["errors"] == 0
    return res


def eval_json(expr_src, prelude_path=None):
    """evaluate one expression (after an optional prelude file); the value as JSON, its type and sources"""
    import io
    out = io.StringIO()
    res = {"schema": "tally.eval.v1", "ok": True, "expr": expr_src, "interpreter": interpreter_pin(), "error": None}
    it = Interp(prelude_path or "<eval>", out)
    try:
        if prelude_path:
            with open(prelude_path, encoding="utf-8") as fh:
                it.run(fh.read(), prelude_path)
            res["inputs"] = {prelude_path: file_sha(prelude_path)}
        p = Parser(lex(expr_src, "<eval>"), "<eval>")
        e = p.expr()
        p.skip_nl()
        if p.peek().kind != "eof":
            raise p.err("one expression expected (use `tally run` for statements)", p.peek())
        v = it.eval(e, it.globals)
        res.update({"value": to_json(v), "display": show(v, True), "type": type_name(v), "sources": sorted(all_sources(v))})
    except TallyError as ex:
        res["ok"], res["error"] = False, ex.to_map()
    except Thrown as t:
        res["ok"], res["error"] = False, thrown_map(t)
    res["output"] = out.getvalue()
    return res


# ---------------------------------------------------------------- JSON-lines session (`tally serve`)
SERVE_OPS = {
    "exec": "run statements in the session (facts, rules, functions persist); returns output and the last "
            "expression's value",
    "eval": "evaluate one expression: value, display, type, sources",
    "proof_graph": "ground pattern -> structured proof graph; optional max_nodes bounds traversal",
    "impact": "sources: [names] -> reversible combined source-withdrawal analysis",
    "query": "pattern like 'Paid(\"Customer\", m, t)' -> list of bindings (runs infer first)",
    "explain": "pattern -> the derivation text (runs infer first)",
    "status": "pattern -> true|false|conflicted|defeated|open|unknown (runs infer first)",
    "help": "name -> signature and doc of a built-in, function or record type",
    "check": "static check of code (not run)",
    "run_file": "path -> like `tally run --json`",
    "test_file": "path -> like `tally test --json`",
    "describe": "the language reference",
    "reset": "start a fresh session",
    "batch": "requests: [...], atomic: true -> run them in order; if atomic and one fails, the session is rolled "
             "back to before the batch",
    "checkpoint": "-> {checkpoint: n}: a point you can roll back to",
    "rollback": "to: n -> restore the saved in-memory state at checkpoint n, without replaying requests",
    "history": "successful state-changing requests in the current memory snapshot",
    "ops": "this list",
}


class Session:
    STATEFUL = ("exec", "eval")  # failed requests restore a snapshot of memory state

    def __init__(self, max_steps=1_000_000):
        if isinstance(max_steps, bool) or not isinstance(max_steps, int) or max_steps <= 0:
            raise ValueError("max_steps must be a positive whole number")
        self.max_steps = max_steps
        self.next_checkpoint = 0
        self.reset()

    def reset(self):
        import io
        self.out = io.StringIO()
        self.it = Interp("<session>", self.out, budget=Budget(self.max_steps))
        self.history = []
        self.checkpoints = {}

    def capture(self):
        """Copy values, closures and rules as one object graph, preserving builtin bindings."""
        import copy
        state = {"globals": self.it.globals, "kb": self.it.kb, "modules": self.it.modules,
                 "tests": self.it.tests, "pc": self.it.pc, "stack": self.it.stack,
                 "path": self.it.path, "history": self.history}
        return copy.deepcopy(state, {id(self.it.builtins): self.it.builtins})

    def restore_state(self, saved):
        import copy
        state = copy.deepcopy(saved, {id(self.it.builtins): self.it.builtins})
        for key in ("globals", "kb", "modules", "tests", "pc", "stack", "path"):
            setattr(self.it, key, state[key])
        self.history = state["history"]

    def rebuild(self, n):
        # Retained method name for existing Python callers; execution is never replayed.
        if isinstance(n, bool) or n not in self.checkpoints:
            raise TallyError("rollback needs to: an existing checkpoint", 0, 0, "<session>")
        self.restore_state(self.checkpoints[n])
        self.checkpoints = {k: v for k, v in self.checkpoints.items() if k <= n}
        self.out.seek(0)
        self.out.truncate()

    def handle(self, req, record=True, nested=False):
        op = req.get("op")
        rid = req.get("id")
        base = {"id": rid, "op": op, "ok": True, "error": None}
        self.out.seek(0)
        self.out.truncate()
        before = None
        try:
            if not isinstance(op, str):
                raise TallyError("request op must be a string", 0, 0, "<session>")
            for key in ("code", "pattern", "name", "path"):
                if key in req and not isinstance(req[key], str):
                    raise TallyError(f"request {key} must be a string", 0, 0, "<session>")
            if not nested:
                limit = req.get("max_steps", self.max_steps)
                if isinstance(limit, bool) or not isinstance(limit, int) or not 1 <= limit <= self.max_steps:
                    raise TallyError(f"request max_steps must be a whole number from 1 to {self.max_steps}",
                                     0, 0, "<session>")
                self.it.budget = Budget(limit)
            if op in self.STATEFUL:
                before = self.capture()
            if op == "batch":
                reqs = req.get("requests")
                if not isinstance(reqs, list):
                    raise TallyError("batch needs requests: [...]", 0, 0, "<session>")
                saved = self.capture()
                saved_checkpoints = dict(self.checkpoints)
                results = []
                for sub in reqs:
                    if not isinstance(sub, dict) or sub.get("op") not in ("exec", "eval", "query", "explain", "status", "proof_graph", "impact", "help", "check"):
                        results.append({"id": sub.get("id") if isinstance(sub, dict) else None, "ok": False,
                                        "error": {"code": "E_REQUEST", "message": "a batch holds exec/eval/query/"
                                                  "explain/status/proof_graph/impact/help/check requests", "line": 0, "col": 0,
                                                  "hint": None, "trace": []}})
                    else:
                        results.append(self.handle(sub, nested=True))
                    if req.get("atomic") and not results[-1]["ok"]:
                        break
                failed = [r for r in results if not r["ok"]]
                base["value"] = results
                base["rolled_back"] = False
                if failed and req.get("atomic"):
                    self.restore_state(saved)
                    self.checkpoints = saved_checkpoints
                    base["rolled_back"] = True
                    base["ok"] = False
                    base["error"] = dict(failed[0]["error"], message="batch rolled back: " + failed[0]["error"]["message"])
                elif failed:
                    base["ok"] = False
                    base["error"] = failed[0]["error"]
                base["output"] = ""
                return base
            if op == "checkpoint":
                if len(self.checkpoints) >= 64:
                    raise TallyError("checkpoint limit 64 reached; reset or roll back before saving more", 0, 0)
                token = self.next_checkpoint
                self.next_checkpoint += 1
                self.checkpoints[token] = self.capture()
                base["value"] = {"checkpoint": token}
                base["output"] = ""
                return base
            if op == "rollback":
                to = req.get("to")
                if isinstance(to, bool) or not isinstance(to, int) or to not in self.checkpoints:
                    raise TallyError("rollback needs to: an existing checkpoint", 0, 0, "<session>")
                self.rebuild(to)
                base["value"] = {"checkpoint": to}
                base["output"] = ""
                return base
            if op == "history":
                base["value"] = [dict(h) for h in self.history]
                base["output"] = ""
                return base
            if op == "exec":
                v = None
                stmts = parse(req.get("code", ""), "<session>")
                last = None
                for st in stmts:
                    last = self.it.exec(st, self.it.globals)
                if stmts and stmts[-1].k == "expr":
                    v = last
                    base.update({"value": to_json(v), "display": show(v, True), "type": type_name(v),
                                 "sources": sorted(all_sources(v))})
            elif op == "eval":
                p = Parser(lex(req.get("code", ""), "<session>"), "<session>")
                e = p.expr()
                p.skip_nl()
                if p.peek().kind != "eof":
                    raise p.err("one expression expected (use op exec for statements)", p.peek())
                v = self.it.eval(e, self.it.globals)
                base.update({"value": to_json(v), "display": show(v, True), "type": type_name(v),
                             "sources": sorted(all_sources(v))})
            elif op == "impact":
                v = _ta.impact(self.it, req.get("sources", []))
                base["value"] = to_json(v)
            elif op == "proof_graph":
                pat = req.get("pattern", "").strip().lstrip("?")
                # Require a single ground pattern; trailing code is rejected.
                parser = Parser(lex("?" + pat, "<session>"), "<session>")
                expr = parser.expr()
                parser.skip_nl()
                if parser.peek().kind != "eof":
                    raise parser.err("one ground pattern expected", parser.peek())
                q = self.it.eval(expr, self.it.globals)
                pred, args = _ta.goal(q, expr, self.it)
                size = req.get("max_nodes", 5000)
                if isinstance(size, bool) or not isinstance(size, int) or not 1 <= size <= 100000:
                    raise TallyError("request max_nodes must be a whole number from 1 to 100000", 0, 0)
                base["value"] = _ta.proof_graph(self.it, pred, args, size)
            elif op in ("query", "explain", "status"):
                pat = req.get("pattern", "").strip()
                if pat.startswith("?"):
                    pat = pat[1:]
                fn = {"query": "query", "explain": "explain", "status": "status"}[op]
                self.it.exec(parse("infer()", "<session>")[0], self.it.globals)
                v = self.it.eval(Parser(lex(f"{fn}(?{pat})", "<session>"), "<session>").expr(), self.it.globals)
                base.update({"value": to_json(v), "display": show(v, True) if op != "explain" else strip(v)})
                if op == "query":
                    base["sources"] = [sorted(srcs(b)) for b in strip(v)]
            elif op == "help":
                name = req.get("name", "")
                found = self.it.globals.find(name)
                if found is None:
                    raise TallyError(f"'{name}' is not defined", 0, 0, "<session>",
                                     did_you_mean(name, self.it.globals))
                base["value"] = describe_value(strip(found.vars[name]))
            elif op == "check":
                stmts = parse(req.get("code", ""), "<session>")
                ck = Checker("<session>")
                # names the session already defined count as defined
                fs = ck.check(stmts)
                known = set()
                e = self.it.globals
                while e is not None:
                    known |= set(e.vars)
                    e = e.parent
                fs = [f for f in fs if not (f[0] == "error" and re.match(r"'(\w+)' is not defined", f[3])
                                            and re.match(r"'(\w+)'", f[3]).group(1) in known)]
                base["findings"] = [{"level": l, "line": a, "col": b, "message": m,
                                     "code": error_code(m) if l == "error" else "W"} for l, a, b, m in fs]
                base["ok"] = not any(f["level"] == "error" for f in base["findings"])
            elif op == "run_file":
                base["value"] = run_json(req["path"], budget=self.it.budget)
                base["ok"] = base["value"]["ok"]
                base["error"] = base["value"]["error"]
            elif op == "test_file":
                base["value"] = tests_json(req["path"], budget=self.it.budget)
                base["ok"] = base["value"]["ok"]
                base["error"] = base["value"]["error"] or next(
                    (t["error"] for t in base["value"]["tests"] if not t["ok"]), None)
            elif op == "describe":
                base["value"] = reference(verify=False)
            elif op == "reset":
                self.reset()
            elif op == "ops":
                base["value"] = SERVE_OPS
            else:
                raise TallyError(f"unknown op '{op}' (ops: {', '.join(SERVE_OPS)})", 0, 0, "<session>")
        except TallyError as ex:
            base["ok"], base["error"] = False, ex.to_map()
        except Thrown as t:
            base["ok"], base["error"] = False, thrown_map(t)
        except (BreakSignal, ContinueSignal, ReturnSignal):
            base["ok"], base["error"] = False, {"code": "E_SYNTAX", "message": "break/continue/return outside "
                                                "a loop or function", "line": 0, "col": 0, "hint": None, "trace": []}
        except KeyError as ex:
            base["ok"], base["error"] = False, {"code": "E_REQUEST", "message": f"request is missing {ex}",
                                                "line": 0, "col": 0, "hint": None, "trace": []}
        except RecursionError:
            base["ok"], base["error"] = False, {"code": "E_RUNTIME", "message": "stack overflow", "line": 0,
                                                "col": 0, "hint": None, "trace": []}
        if before is not None and not base["ok"]:
            self.restore_state(before)
            base["rolled_back"] = True
        base["output"] = self.out.getvalue()
        base["steps"] = self.it.budget.steps
        if record and base["ok"] and op in self.STATEFUL:
            self.history.append({k: req[k] for k in ("op", "code", "id") if k in req})
        return base


def serve(inp=None, outp=None):
    import json as _j
    inp = inp or sys.stdin
    outp = outp or sys.stdout
    sess = Session(max_steps=int(os.environ.get("TALLY_MAX_STEPS", "1000000")))
    outp.write(_j.dumps({"id": None, "op": "hello", "ok": True, "tally": VERSION, "ops": list(SERVE_OPS)}) + "\n")
    outp.flush()
    for line in inp:
        line = line.strip()
        if not line:
            continue
        try:
            req = _j.loads(line)
            if not isinstance(req, dict):
                raise ValueError("a request is a JSON object")
        except ValueError as ex:
            resp = {"id": None, "ok": False, "error": {"code": "E_REQUEST", "message": f"not a JSON request: {ex}",
                                                       "line": 0, "col": 0, "hint": None, "trace": []}}
        else:
            resp = sess.handle(req)
        outp.write(_j.dumps(resp, ensure_ascii=False, default=str) + "\n")
        outp.flush()


def run_tests(path, out=None):
    out = out or sys.stdout
    it = Interp(path, out)
    try:
        with open(path, encoding="utf-8") as fh:
            it.run(fh.read(), path)
    except TallyError as e:
        out.write(f"error before any test ran: {e}\n0/0 tests passed\n")
        return False
    except Thrown as t:
        out.write(f"uncaught before any test ran: {show(t.value)} at {t.line}:{t.col}\n0/0 tests passed\n")
        return False
    passed = 0
    for name, body, env, node in it.tests:
        try:
            it.exec_block(body, Env(env))
            passed += 1
            out.write(f"  pass  {name}\n")
        except Thrown as t:
            out.write(f"  FAIL  {name}  ({t.line}:{t.col}) {show(t.value)}\n")
        except TallyError as e:
            out.write(f"  FAIL  {name}  {e}\n")
    out.write(f"{passed}/{len(it.tests)} tests passed\n")
    return passed == len(it.tests)


def repl():
    it = Interp("<repl>")
    print(f"Tally {VERSION} — exact money, dates, sources. Ctrl-D to quit.")
    buf = []
    while True:
        try:
            line = input("... " if buf else ">>> ")
        except EOFError:
            print()
            return
        buf.append(line)
        src = "\n".join(buf)
        if src.count("{") > src.count("}") or src.count("(") > src.count(")") or \
                src.count("[") > src.count("]"):
            continue
        buf = []
        try:
            prog = parse(src, "<repl>")
            for s in prog:
                v = it.exec(s, it.globals)
                if s.k == "expr" and v is not None:
                    print(show(v, True) + (f"   from {sorted(srcs(v))}" if srcs(v) else ""))
        except TallyError as e:
            print(f"error: {e}")
        except Thrown as t:
            print(f"uncaught: {show(t.value)} ({t.line}:{t.col})")
        except (BreakSignal, ContinueSignal, ReturnSignal):
            print("error: break/continue/return outside a loop or function")


def trace_text(e):
    tr = getattr(e, "trace", None) or []
    return "".join(f"  in {name} (called at line {line})\n" for name, line in reversed(tr))


def _main(argv):
    if "--max-steps" in argv:
        pos = argv.index("--max-steps")
        if pos + 1 >= len(argv) or not argv[pos + 1].isdigit() or int(argv[pos + 1]) <= 0:
            err = TallyError("execution step limit must be a positive whole number", 0, 0)
            if "--json" in argv:
                print(_json.dumps({"ok": False, "error": err.to_map()}))
            else:
                sys.stderr.write(str(err) + "\n")
            return 2
        os.environ["TALLY_MAX_STEPS"] = argv[pos + 1]
        argv = argv[:pos] + argv[pos + 2:]
    if not argv:
        repl()
        return 0
    if argv[0] == "--selftest":
        from tally_selftest import selftest
        return selftest()
    if argv[0] == "--version":
        print(f"Tally {VERSION}")
        return 0
    if argv[0] == "describe":
        import json as _j
        ref = reference(verify="--verify" in argv)
        if "--json" in argv:
            print(_j.dumps(ref, indent=1, ensure_ascii=False))
        else:
            for g in ref["groups"]:
                print(f"\n## {g}")
                for b in ref["builtins"]:
                    if b["group"] == g:
                        mark = "" if b.get("verified", True) is True else f"   !! {b['verified']}"
                        print(f"  {b['signature']:44} {b['doc']}{mark}")
            if ref["undocumented"]:
                print("\nUNDOCUMENTED:", ", ".join(ref["undocumented"]))
        return 0 if not (ref["undocumented"] or ref["example_failures"]) else 1
    if argv[0] == "serve":
        serve()
        return 0
    as_json = "--json" in argv
    argv = [a for a in argv if a != "--json"]
    if as_json:
        import json as _j
        cmd = argv[0]
        if cmd == "test":
            r = tests_json(argv[1])
        elif cmd == "check":
            r = check_json(argv[1], "--strict" in argv)
        elif cmd == "doc":
            r = dict(program_api(argv[1]), ok=True)
        elif cmd == "eval":
            pre = argv[argv.index("--prelude") + 1] if "--prelude" in argv else None
            r = eval_json(argv[1], pre)
        else:
            r = run_json(argv[1] if cmd == "run" else cmd)
        print(_j.dumps(r, indent=1, ensure_ascii=False, default=str))
        return 0 if r["ok"] else 1
    try:
        if argv[0] == "test":
            return 0 if run_tests(argv[1]) else 1
        if argv[0] == "check":
            strict = "--strict" in argv
            return 0 if all(check_file(p, strict=strict) for p in argv[1:] if p != "--strict") else 1
        if argv[0] == "doc":
            api = program_api(argv[1])
            for f in api["functions"]:
                print(f"fn {f['signature']}" + (f"\n     {f['doc']}" if f["doc"] else ""))
            for m in api["methods"]:
                print(f"fn {m['record']}.{m['signature'].split('.', 1)[-1]}")
            for r in api["records"]:
                print(f"record {r['name']} {{ {', '.join(r['fields'])} }}")
            for r in api["rules"]:
                print(f"rule {r['name']}: {', '.join(r['when'])} => {', '.join(r['then'])}"
                      + (f" unless {', '.join(r['unless'])}" if r["unless"] else ""))
            print(f"tests: {len(api['tests'])}   imports: {[i['path'] for i in api['imports']]}")
            return 0
        if argv[0] == "eval":
            r = eval_json(argv[1], argv[argv.index("--prelude") + 1] if "--prelude" in argv else None)
            if not r["ok"]:
                sys.stderr.write(f"error: {r['error']['message']}\n")
                return 2
            print(r["display"] + (f"   from {r['sources']}" if r["sources"] else ""))
            return 0
        run_file(argv[1] if argv[0] == "run" else argv[0])
        return 0
    except TallyError as e:
        sys.stderr.write(f"error: {e}\n" + trace_text(e))
        return 2
    except Thrown as t:
        sys.stderr.write(f"uncaught: {show(t.value)} at {t.line}:{t.col}\n" + trace_text(t))
        return 1
    except (BreakSignal, ContinueSignal):
        sys.stderr.write("error: break/continue outside a loop\n")
        return 2
    except ReturnSignal:
        return 0


HELP = """Tally 0.22 — exact calculations and inspectable reasoning

  tally FILE.tly                  execute a program
  tally run FILE.tly --json       output, reasoning state and interpreter fingerprints
  tally eval 'EXPR' --json        evaluate one expression
  tally test FILE.tly --json      execute test blocks
  tally check FILE.tly --strict   inspect names, arity and declarations
  tally doc FILE.tly --json       inspect a program's API without running it
  tally describe --verify         verify the built-in reference examples
  tally serve                    persistent JSON-lines session
  tally --selftest                portable synthetic checks (no private stores)
  tally --version

Add --max-steps N to bound execution (positive whole number).
JSON-line sessions default to 1,000,000 steps per request. Imports and rule
inference share the budget. File I/O and individual Python built-ins are not
wall-time or memory sandboxed.

New: qstate/qcircuit/qmeasure/qsample CPU quantum simulation; qasm OpenQASM 3 export.
Classical register models accept sampling controls; best_check supports per-record costs.
Audits: proof_graph(?Goal(...)) and impact(["source-A", "source-B"]).
Session checkpoints save memory state; restore never replays reads or writes.
External file writes are not undone by rollback.
"""


def main(argv):
    if argv and argv[0] in ("--help", "-h", "help"):
        print(HELP)
        return 0
    if argv and argv[0] in ("run", "eval", "test", "check", "doc") and (len(argv) < 2 or argv[1].startswith("--")):
        error = TallyError(f"request is missing input for {argv[0]}", 0, 0)
        if "--json" in argv:
            print(_json.dumps({"ok": False, "error": error.to_map()}))
        else:
            sys.stderr.write(str(error) + "\n")
        return 2
    try:
        return _main(argv)
    except IndexError:
        payload = TallyError("request is missing a command argument", 0, 0).to_map()
    except (OSError, UnicodeError) as ex:
        error = TallyError(str(ex), 0, 0)
        payload = error.to_map()
        payload["code"] = "E_IO"
    except LimitError as ex:
        payload = ex.to_map()
    if "--json" in argv:
        print(_json.dumps({"ok": False, "error": payload}))
    else:
        sys.stderr.write(f"error: {payload['message']}\n")
    return 2


if __name__ == "__main__":
    # Shared exchange interface; ordinary execution does not load this module.
    if len(__import__("sys").argv) > 1 and __import__("sys").argv[1] in ("--contract", "--validate-exchange"):
        import os as _suite_os, runpy as _suite_runpy
        from pathlib import Path as _SuitePath
        _suite_root = _suite_os.environ.get("TALLY_LANGUAGE_ROOT")
        _suite_candidates = [_SuitePath(_suite_root) / "tools/language_suite/contract.py"] if _suite_root else []
        _suite_path = next((candidate for candidate in _suite_candidates if candidate.is_file()), None)
        if _suite_path is None:
            print('{"ok":false,"error":{"code":"E_EXCHANGE_CONFIG","message":"Set TALLY_LANGUAGE_ROOT to your installation containing tools/language_suite/contract.py"}}')
            raise SystemExit(2)
        _suite_runpy.run_path(str(_suite_path))["cli"]('tally', __file__, __import__("sys").argv[1:])
    sys.exit(main(sys.argv[1:]))
