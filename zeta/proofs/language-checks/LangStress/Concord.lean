import LangStress.Tokens
/-!
# Concord — reference semantics and its laws

Scale AGAINST < OPEN < LEANS < STANDS, plus CONFLICT, which poisons any composition.
`all_of` = weakest input, `any_of` = strongest input.
The laws below are proved for every input, not sampled.
-/
namespace LangStress.Concord

inductive St | against | open_ | leans | stands | conflict
  deriving DecidableEq, Repr, Inhabited

def St.rank : St → Nat
  | .against => 0 | .open_ => 1 | .leans => 2 | .stands => 3 | .conflict => 4

def allOf2 : St → St → St
  | .conflict, _ => .conflict
  | _, .conflict => .conflict
  | a, b => if a.rank ≤ b.rank then a else b

def anyOf2 : St → St → St
  | .conflict, _ => .conflict
  | _, .conflict => .conflict
  | a, b => if a.rank ≤ b.rank then b else a

-- no Mathlib: each law is proved by splitting on the five states and deciding each instance

theorem allOf_comm : ∀ a b : St, allOf2 a b = allOf2 b a := by intro a b ; cases a <;> cases b <;> decide
theorem anyOf_comm : ∀ a b : St, anyOf2 a b = anyOf2 b a := by intro a b ; cases a <;> cases b <;> decide
theorem allOf_assoc : ∀ a b c : St, allOf2 (allOf2 a b) c = allOf2 a (allOf2 b c) := by intro a b c ; cases a <;> cases b <;> cases c <;> decide
theorem anyOf_assoc : ∀ a b c : St, anyOf2 (anyOf2 a b) c = anyOf2 a (anyOf2 b c) := by intro a b c ; cases a <;> cases b <;> cases c <;> decide
theorem allOf_idem : ∀ a : St, allOf2 a a = a := by intro a ; cases a <;> decide
theorem anyOf_idem : ∀ a : St, anyOf2 a a = a := by intro a ; cases a <;> decide
theorem conflict_poisons_all : ∀ a : St, allOf2 a .conflict = .conflict ∧ allOf2 .conflict a = .conflict := by intro a ; cases a <;> decide
theorem conflict_poisons_any : ∀ a : St, anyOf2 a .conflict = .conflict ∧ anyOf2 .conflict a = .conflict := by intro a ; cases a <;> decide
/-- an all_of never sits above the any_of of the same two inputs -/
theorem all_le_any : ∀ a b : St, (allOf2 a b).rank ≤ (anyOf2 a b).rank := by intro a b ; cases a <;> cases b <;> decide
/-- raising one input never lowers a composition (CONFLICT aside) -/
theorem allOf_mono : ∀ a a' b : St, a ≠ .conflict → a' ≠ .conflict → b ≠ .conflict →
    a.rank ≤ a'.rank → (allOf2 a b).rank ≤ (allOf2 a' b).rank := by intro a a' b ; cases a <;> cases a' <;> cases b <;> decide
theorem anyOf_mono : ∀ a a' b : St, a ≠ .conflict → a' ≠ .conflict → b ≠ .conflict →
    a.rank ≤ a'.rank → (anyOf2 a b).rank ≤ (anyOf2 a' b).rank := by intro a a' b ; cases a <;> cases a' <;> cases b <;> decide
/-- an all_of can only reach STANDS when every input stands -/
theorem allOf_stands : ∀ a b : St, allOf2 a b = .stands ↔ (a = .stands ∧ b = .stands) := by intro a b ; cases a <;> cases b <;> decide

def ofNat : Nat → St
  | 0 => .against | 1 => .open_ | 2 => .leans | 3 => .stands | _ => .conflict

/-- evaluate a prefix-coded tree: 0 s = leaf, 1 n … = all_of of n, 2 n … = any_of of n -/
partial def evalTree (r : Rd) : St × Rd :=
  let (k, r) := r.nat
  if k == 0 then
    let (s, r) := r.nat
    (ofNat s, r)
  else
    let (n, r) := r.nat
    let rec go (i : Nat) (acc : Option St) (r : Rd) : Option St × Rd :=
      if i == 0 then (acc, r) else
        let (s, r) := evalTree r
        let acc := some (match acc with
          | none => s
          | some a => if k == 1 then allOf2 a s else anyOf2 a s)
        go (i - 1) acc r
    let (acc, r) := go n none r
    (acc.getD .conflict, r)

def check (line : String) : String × List String :=
  let r := Rd.ofLine line
  let (_, r) := r.word
  let (seed, r) := r.nat
  let (want, r) := evalTree r
  let (_, r) := r.word
  let (got, _) := r.nat
  if want.rank == got then (s!"K {seed}", []) else
    (s!"K {seed}", [s!"K_COMPOSE seed={seed} lean={want.rank} concord={got}"])

end LangStress.Concord
