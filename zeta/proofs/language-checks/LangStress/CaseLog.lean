import LangStress.Tokens
/-!
# CaseLog — reference semantics (stratum-free Datalog with four-valued answers)

Ground atoms are `pred*16 + a0*4 + a1`. Every constant is a constant, whatever its spelling.
Closure: least set of atoms holding the visible facts and closed under every ground rule instance.
Best tier: the weakest-input tier of the best proof (min over proofs of max over inputs).
Family sets: every set of source families some proof of the atom rests on.
Truth: TRUE / FALSE / BOTH / NEITHER from the closure of `p` and `not_p`.
-/
namespace LangStress.CaseLog

structure Lit where
  p : Nat
  a0 : Nat
  a1 : Nat

structure Rule where
  head : Lit
  body : List Lit

def aid (p a0 a1 : Nat) : Nat := p * 16 + a0 * 4 + a1

/-- value of a term under an assignment `σ` (3 variables); wildcard = none -/
def tval (σ : List Nat) (t : Nat) : Option Nat :=
  if t < 100 then some t else if t == 199 then none else some (σ.getD (t - 100) 0)

def tmatch (σ : List Nat) (t v : Nat) : Bool :=
  match tval σ t with
  | none => true
  | some x => x == v

structure Ctx where
  K : Nat
  ar : List Nat   -- arity of p mod NP
  NP : Nat

def arity (c : Ctx) (p : Nat) : Nat := c.ar.getD (p % c.NP) 1

/-- the ground atoms a literal can match under σ -/
def lmatch (c : Ctx) (σ : List Nat) (l : Lit) : List Nat :=
  let a1s := if arity c l.p == 2 then List.range c.K else [0]
  (List.range c.K).flatMap fun a0 =>
    a1s.filterMap fun a1 =>
      if tmatch σ l.a0 a0 && (arity c l.p == 1 || tmatch σ l.a1 a1) then some (aid l.p a0 a1) else none

def builtinOk (σ : List Nat) (l : Lit) : Bool :=
  match tval σ l.a0, tval σ l.a1 with
  | some x, some y => if l.p == 200 then x == y else x != y
  | _, _ => false

def assignments (K : Nat) : List (List Nat) :=
  (List.range K).flatMap fun x => (List.range K).flatMap fun y => (List.range K).map fun z => [x, y, z]

def headAtom (σ : List Nat) (l : Lit) : Nat :=
  aid l.p ((tval σ l.a0).getD 0) ((tval σ l.a1).getD 0)

/-- one round: fire every ground rule instance whose body holds in `d` -/
def step (c : Ctx) (rs : List Rule) (d : Nat) : Nat :=
  rs.foldl (fun acc r =>
    (assignments c.K).foldl (fun acc σ =>
      if r.body.all (fun l => if l.p ≥ 200 then builtinOk σ l else (lmatch c σ l).any (d.testBit ·))
      then acc ||| (1 <<< headAtom σ r.head) else acc) acc) d

def fix (c : Ctx) (rs : List Rule) : Nat → Nat → Nat
  | 0, d => d
  | n + 1, d => let d' := step c rs d; if d' == d then d else fix c rs n d'

def closure (c : Ctx) (rs : List Rule) (base : Nat) : Nat := fix c rs 200 base

/-- best tier per atom (3 = no proof) -/
def tierStep (c : Ctx) (rs : List Rule) (d : Nat) (tr : Array Nat) : Array Nat :=
  rs.foldl (fun tr r =>
    (assignments c.K).foldl (fun tr σ =>
      if r.body.all (fun l => if l.p ≥ 200 then builtinOk σ l else (lmatch c σ l).any (d.testBit ·)) then
        let cand := r.body.foldl (fun m l =>
          if l.p ≥ 200 then m else
            Nat.max m (((lmatch c σ l).filter (d.testBit ·)).foldl (fun b a => Nat.min b (tr.getD a 3)) 3)) 0
        let h := headAtom σ r.head
        if cand < tr.getD h 3 then tr.set! h cand else tr
      else tr) tr) tr

def tierFix (c : Ctx) (rs : List Rule) (d : Nat) : Nat → Array Nat → Array Nat
  | 0, tr => tr
  | n + 1, tr => let tr' := tierStep c rs d tr; if tr' == tr then tr else tierFix c rs d n tr'

/-- sets of family masks (bit `m` set = some proof rests exactly on families `m`) -/
def combine (A B : Nat) : Nat :=
  (List.range 8).foldl (fun acc x => if A.testBit x then
    (List.range 8).foldl (fun acc y => if B.testBit y then acc ||| (1 <<< (x ||| y)) else acc) acc else acc) 0

def famStep (c : Ctx) (rs : List Rule) (d : Nat) (fs : Array Nat) : Array Nat :=
  rs.foldl (fun fs r =>
    (assignments c.K).foldl (fun fs σ =>
      if r.body.all (fun l => if l.p ≥ 200 then builtinOk σ l else (lmatch c σ l).any (d.testBit ·)) then
        let s := r.body.foldl (fun acc l =>
          if l.p ≥ 200 then acc else
            combine acc (((lmatch c σ l).filter (d.testBit ·)).foldl (fun u a => u ||| fs.getD a 0) 0)) 1
        let h := headAtom σ r.head
        fs.set! h (fs.getD h 0 ||| s)
      else fs) fs) fs

def famFix (c : Ctx) (rs : List Rule) (d : Nat) : Nat → Array Nat → Array Nat
  | 0, fs => fs
  | n + 1, fs => let fs' := famStep c rs d fs; if fs' == fs then fs else famFix c rs d n fs'

def truth (pos neg : Bool) : Nat := if pos && neg then 3 else if pos then 1 else if neg then 2 else 0

def readLits (r : Rd) : Nat → List Lit × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (p, r) := r.nat
    let (a0, r) := r.nat
    let (a1, r) := r.nat
    let (rest, r) := readLits r k
    (⟨p, a0, a1⟩ :: rest, r)

def readRules (r : Rd) : Nat → List Rule × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (hs, r) := readLits r 1
    let (nb, r) := r.nat
    let (body, r) := readLits r nb
    let (rest, r) := readRules r k
    (⟨hs.headD ⟨0, 0, 0⟩, body⟩ :: rest, r)

structure Used where
  kind : Nat
  atom : Nat
  tier : Nat
  fam : Nat

structure Der where
  atom : Nat
  ok : Bool        -- every value is a declared constant
  tier : Nat
  fam : Nat
  used : List Used

def readUsed (r : Rd) : Nat → List Used × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (xs, r) := r.nats 6
    let (rest, r) := readUsed r k
    (⟨xs.getD 0 0, aid (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0), xs.getD 4 0, xs.getD 5 0⟩ :: rest, r)

def readDers (r : Rd) : Nat → List Der × Rd
  | 0 => ([], r)
  | k + 1 =>
    let (xs, r) := r.nats 5
    let (nu, r) := r.nat
    let (us, r) := readUsed r nu
    let (rest, r) := readDers r k
    (⟨aid (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0), xs.getD 1 0 < 9, xs.getD 3 0, xs.getD 4 0, us⟩ :: rest, r)

/-- does the list of inputs instantiate this rule body, literal by literal, under σ -/
def bodyMatch (c : Ctx) (σ : List Nat) : List Lit → List Used → Bool
  | [], us => us.isEmpty
  | l :: ls, us =>
    if l.p ≥ 200 then builtinOk σ l && bodyMatch c σ ls us
    else match us with
      | [] => false
      | u :: rest => (lmatch c σ l).contains u.atom && bodyMatch c σ ls rest

def check (line : String) : String × List String := Id.run do
  let r := Rd.ofLine line
  let (_, r) := r.word
  let (seed, r) := r.nat
  let (NP, r) := r.nat
  let (K, r) := r.nat
  let (ar, r) := r.nats NP
  let (view, r) := r.nat
  let (group, r) := r.nat
  let (on, r) := r.nat
  let (nf, r) := r.nat
  let (fl, r) := r.nats (7 * nf)
  let (nr, r) := r.nat
  let (rs, r) := readRules r nr
  let (nq, r) := r.nat
  let (qs, r) := readLits r nq
  let (_, r) := r.word
  let (nd, r) := r.nat
  let (ders, r) := readDers r nd
  let (_, r) := r.word
  let (tl, r) := r.nats nq
  let (_, r) := r.word
  let (moved, _) := r.nat
  let c : Ctx := { K, ar, NP }
  -- visible facts
  let facts := (List.range nf).map fun i => (fl.drop (7 * i)).take 7
  let vis := facts.filter fun f =>
    view == 0 || f.getD 5 0 == 0 || ((f.getD 5 0 &&& group) != 0 && f.getD 6 0 ≤ on)
  let atomOf := fun (f : List Nat) => aid (f.getD 0 0) (f.getD 1 0) (f.getD 2 0)
  let base := vis.foldl (fun b f => b ||| (1 <<< atomOf f)) 0
  let cl := closure c rs base
  let tr0 := vis.foldl (fun tr f => let a := atomOf f; tr.set! a (Nat.min (tr.getD a 3) (f.getD 3 3))) (Array.replicate 128 3)
  let tr := tierFix c rs cl 300 tr0
  let mut bad : List String := []
  -- closure agreement: recorded facts ∪ CaseLog's derived entries
  let pyset := ders.foldl (fun b d => if d.ok then b ||| (1 <<< d.atom) else b) base
  if ders.any (fun d => !d.ok) then
    bad := bad ++ [s!"C_NONCONSTANT seed={seed} (a derived value is not a declared constant)"]
  if pyset != cl then
    let extra := (List.range 128).filter fun a => pyset.testBit a && !cl.testBit a
    let missing := (List.range 128).filter fun a => cl.testBit a && !pyset.testBit a
    bad := bad ++ [s!"C_CLOSURE seed={seed} caselog_extra={extra} caselog_missing={missing}"]
  for (d, i) in ders.zipIdx do
    let a := d.atom
    if d.ok && cl.testBit a then
      -- (1) the tier is the best any proof reaches
      let best := tr.getD a 3
      if d.tier < best then bad := bad ++ [s!"C_TIER_UNSOUND seed={seed} atom={a} caselog=F{d.tier} best=F{best}"]
      else if d.tier > best then bad := bad ++ [s!"C_TIER_NONOPTIMAL seed={seed} atom={a} caselog=F{d.tier} best=F{best}"]
      -- (2) the reported proof is a real one: every input exists as stated, none is the fact itself,
      --     derived inputs were settled earlier, and the inputs instantiate a rule with this head
      let inputsOk := d.used.all fun u =>
        u.atom != a &&
        (if u.kind == 0 then vis.any (fun f => atomOf f == u.atom && f.getD 3 3 == u.tier && (1 <<< f.getD 4 0) == u.fam)
         else (ders.take i).any (fun e => e.atom == u.atom && e.tier == u.tier && e.fam == u.fam))
      let ruleOk := rs.any fun rl => (assignments K).any fun σ => headAtom σ rl.head == a && bodyMatch c σ rl.body d.used
      let wantTier := if d.used.isEmpty then 2 else d.used.foldl (fun m u => Nat.max m u.tier) 0
      let wantFam := d.used.foldl (fun m u => m ||| u.fam) 0
      if !inputsOk then bad := bad ++ [s!"C_PROOF_INPUT seed={seed} atom={a} (an input of the reported proof does not exist as stated, or is circular)"]
      if !ruleOk then bad := bad ++ [s!"C_PROOF_RULE seed={seed} atom={a} (the reported inputs instantiate no rule with this head)"]
      if wantTier != d.tier || wantFam != d.fam then
        bad := bad ++ [s!"C_PROOF_SUM seed={seed} atom={a} tier={d.tier} want={wantTier} families={d.fam} want={wantFam}"]
  if moved == 1 then bad := bad ++ [s!"C_ORDER_DEPENDENT seed={seed} (reordering the statements changed a tier, family set, anchor or answer)"]
  -- query truth
  for (q, i) in qs.zipIdx do
    let pos := (assignments K).any fun σ => (lmatch c σ q).any (cl.testBit ·)
    let neg := (assignments K).any fun σ => (lmatch c σ { q with p := q.p + NP }).any (cl.testBit ·)
    let w := truth pos neg
    let g := tl.getD i 9
    if w != g then bad := bad ++ [s!"C_TRUTH seed={seed} query={i} lean={w} caselog={g}"]
  return (s!"C {seed}", bad)

end LangStress.CaseLog

namespace LangStress.CaseLog
/-- the four-valued answer moves only up the knowledge order when support is added:
    NEITHER → TRUE/FALSE → BOTH, never back, and never TRUE ↔ FALSE directly -/
def kle (a b : Nat) : Bool := a == b || a == 0 || b == 3

theorem truth_knowledge_mono : ∀ p n p' n' : Bool, (p → p') → (n → n') →
    kle (truth p n) (truth p' n') = true := by
  intro p n p' n'; cases p <;> cases n <;> cases p' <;> cases n' <;> decide

theorem truth_both_iff : ∀ p n : Bool, truth p n = 3 ↔ (p = true ∧ n = true) := by
  intro p n; cases p <;> cases n <;> decide

theorem truth_neither_iff : ∀ p n : Bool, truth p n = 0 ↔ (p = false ∧ n = false) := by
  intro p n; cases p <;> cases n <;> decide
end LangStress.CaseLog
