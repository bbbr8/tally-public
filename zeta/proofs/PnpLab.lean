/-
PnpLab.lean — machine-checked statements behind the P vs NP lab (Lean 4 core, no Mathlib).

Nothing here is a theorem about P vs NP.  Each theorem is a small exact fact the lab's code relies on,
checked by Lean's kernel instead of by a test.
-/
import Std.Tactic.BVDecide

namespace PnpLab

/-! ## 1. Arithmetization (arith.py): a clause as a polynomial -/

def b2i (b : Bool) : Int := if b then 1 else 0

/-- The polynomial `arith.py` uses for a clause `a ∨ b ∨ c`. -/
def clausePoly (a b c : Int) : Int := 1 - (1 - a) * (1 - b) * (1 - c)

/-- On 0/1 inputs the polynomial is exactly OR. -/
theorem clause_is_or : ∀ a b c : Bool, clausePoly (b2i a) (b2i b) (b2i c) = b2i (a || b || c) := by decide

/-- A negated literal is `1 - x`. -/
theorem neg_literal : ∀ a : Bool, 1 - b2i a = b2i (!a) := by decide

/-- The expansion, for every integer (so for every field element the verifier may pick). -/
theorem clause_expand (a b c : Int) :
    clausePoly a b c = a + b + c - a * b - a * c - b * c + a * b * c := by
  unfold clausePoly; grind

/-! ## 2. The sum over the cube, and the one-round identity of the sum-check protocol -/

/-- Sum of `f` over all 0/1 assignments to `n` variables. -/
def sumCube : (n : Nat) → (List Bool → Int) → Int
  | 0, f => f []
  | n + 1, f => sumCube n (fun xs => f (false :: xs)) + sumCube n (fun xs => f (true :: xs))

/-- What the verifier checks each round: the two halves add up to the whole. -/
theorem round_identity (n : Nat) (f : List Bool → Int) :
    sumCube (n + 1) f = sumCube n (fun xs => f (false :: xs)) + sumCube n (fun xs => f (true :: xs)) := rfl

/-- Summing a 0/1-valued function counts where it is 1: two variables, the clause `x ∨ y` has 3 solutions. -/
theorem count_example : sumCube 2 (fun xs => match xs with
    | [x, y] => b2i (x || y)
    | _ => 0) = 3 := by decide

/-! ## 3. Why a false count is caught: a nonzero low-degree polynomial has few roots (miniature, field of 7 elements) -/

/-- Over the integers mod 7, a quadratic that is not identically zero vanishes at no more than 2 of the 7 points.
The sum-check verifier's error bound is this fact at scale: degree / field size. -/
theorem quadratic_few_roots : ∀ a b c : Fin 7, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ((List.finRange 7).filter (fun x => a * x * x + b * x + c = 0)).length ≤ 2 := by decide

/-! ## 4. Pigeonhole: 3 pigeons do not fit in 2 holes; 4 do not fit in 3 -/

/-- `p i j` : pigeon `i` sits in hole `j`.  Every assignment breaks a clause. -/
theorem php_3_2 : ∀ p00 p01 p10 p11 p20 p21 : Bool,
    ((p00 || p01) && (p10 || p11) && (p20 || p21) &&
     (!p00 || !p10) && (!p00 || !p20) && (!p10 || !p20) &&
     (!p01 || !p11) && (!p01 || !p21) && (!p11 || !p21)) = false := by decide

theorem php_4_3 (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : Bool) :
    ((a0 || a1 || a2) && (b0 || b1 || b2) && (c0 || c1 || c2) && (d0 || d1 || d2) &&
     (!a0 || !b0) && (!a0 || !c0) && (!a0 || !d0) && (!b0 || !c0) && (!b0 || !d0) && (!c0 || !d0) &&
     (!a1 || !b1) && (!a1 || !c1) && (!a1 || !d1) && (!b1 || !c1) && (!b1 || !d1) && (!c1 || !d1) &&
     (!a2 || !b2) && (!a2 || !c2) && (!a2 || !d2) && (!b2 || !c2) && (!b2 || !d2) && (!c2 || !d2)) = false := by
  bv_decide

/-! ## 5. A machine-checked lower bound: XOR of two variables needs 4 leaves -/

/-- De Morgan formulas over two variables: literals (possibly negated), AND, OR. -/
inductive F where
  | lit (second : Bool) (neg : Bool) : F
  | and (a b : F) : F
  | or (a b : F) : F

/-- Number of leaves (literal occurrences): the size measure used in loop 2. -/
def F.leaves : F → Nat
  | .lit _ _ => 1
  | .and a b => a.leaves + b.leaves
  | .or a b => a.leaves + b.leaves

/-- Truth table as 4 bits: bit `2*y + x` is the value at inputs `x`, `y`. -/
def F.tt : F → BitVec 4
  | .lit false false => 0b1010#4
  | .lit false true => 0b0101#4
  | .lit true false => 0b1100#4
  | .lit true true => 0b0011#4
  | .and a b => a.tt &&& b.tt
  | .or a b => a.tt ||| b.tt

def R1 : List (BitVec 4) := [0b1010#4, 0b0101#4, 0b1100#4, 0b0011#4]
def comb (A B : List (BitVec 4)) : List (BitVec 4) :=
  A.flatMap fun a => B.flatMap fun b => [a &&& b, a ||| b]
def R2 : List (BitVec 4) := comb R1 R1
def R3 : List (BitVec 4) := comb R1 R2 ++ comb R2 R1

theorem leaves_pos (f : F) : 1 ≤ f.leaves := by
  induction f with
  | lit _ _ => simp [F.leaves]
  | and a b iha ihb => simp [F.leaves]; omega
  | or a b iha ihb => simp [F.leaves]; omega

theorem mem_comb {A B : List (BitVec 4)} {a b : BitVec 4} (ha : a ∈ A) (hb : b ∈ B) :
    (a &&& b) ∈ comb A B ∧ (a ||| b) ∈ comb A B := by
  constructor <;> (simp only [comb, List.mem_flatMap]; exact ⟨a, ha, b, hb, by simp⟩)

theorem tt1 (f : F) (h : f.leaves = 1) : f.tt ∈ R1 := by
  cases f with
  | lit s n => cases s <;> cases n <;> decide
  | and a b => have := leaves_pos a; have := leaves_pos b; simp [F.leaves] at h; omega
  | or a b => have := leaves_pos a; have := leaves_pos b; simp [F.leaves] at h; omega

theorem tt2 (f : F) (h : f.leaves = 2) : f.tt ∈ R2 := by
  cases f with
  | lit s n => simp [F.leaves] at h
  | and a b =>
    have ha := leaves_pos a; have hb := leaves_pos b; simp [F.leaves] at h
    exact (mem_comb (tt1 a (by omega)) (tt1 b (by omega))).1
  | or a b =>
    have ha := leaves_pos a; have hb := leaves_pos b; simp [F.leaves] at h
    exact (mem_comb (tt1 a (by omega)) (tt1 b (by omega))).2

theorem tt3 (f : F) (h : f.leaves = 3) : f.tt ∈ R3 := by
  cases f with
  | lit s n => simp [F.leaves] at h
  | and a b =>
    have ha := leaves_pos a; have hb := leaves_pos b; simp [F.leaves] at h
    by_cases h1 : a.leaves = 1
    · exact List.mem_append_left _ (mem_comb (tt1 a h1) (tt2 b (by omega))).1
    · exact List.mem_append_right _ (mem_comb (tt2 a (by omega)) (tt1 b (by omega))).1
  | or a b =>
    have ha := leaves_pos a; have hb := leaves_pos b; simp [F.leaves] at h
    by_cases h1 : a.leaves = 1
    · exact List.mem_append_left _ (mem_comb (tt1 a h1) (tt2 b (by omega))).2
    · exact List.mem_append_right _ (mem_comb (tt2 a (by omega)) (tt1 b (by omega))).2

/-- The truth table of `x XOR y`. -/
def xorTT : BitVec 4 := 0b0110#4

set_option maxRecDepth 100000 in
/-- No formula with 3 or fewer leaves computes XOR.  (Loop 2 found the exact size 4 by exhaustive search;
this is the lower half of that statement, proved for every formula rather than enumerated.) -/
theorem xor_needs_four_leaves (f : F) (h : f.leaves ≤ 3) : f.tt ≠ xorTT := by
  have hp := leaves_pos f
  have h1 : xorTT ∉ R1 := by decide
  have h2 : xorTT ∉ R2 := by decide
  have h3 : xorTT ∉ R3 := by decide
  intro e
  by_cases c1 : f.leaves = 1
  · exact h1 (e ▸ tt1 f c1)
  · by_cases c2 : f.leaves = 2
    · exact h2 (e ▸ tt2 f c2)
    · exact h3 (e ▸ tt3 f (by omega))

/-- And 4 leaves are enough: `(x ∧ ¬y) ∨ (¬x ∧ y)`. -/
theorem xor_has_four_leaves :
    ∃ f : F, f.leaves = 4 ∧ f.tt = xorTT :=
  ⟨.or (.and (.lit false false) (.lit true true)) (.and (.lit false true) (.lit true false)), by decide, by decide⟩

end PnpLab

#print axioms PnpLab.clause_is_or
#print axioms PnpLab.clause_expand
#print axioms PnpLab.round_identity
#print axioms PnpLab.count_example
#print axioms PnpLab.quadratic_few_roots
#print axioms PnpLab.php_3_2
#print axioms PnpLab.php_4_3
#print axioms PnpLab.xor_needs_four_leaves
#print axioms PnpLab.xor_has_four_leaves
