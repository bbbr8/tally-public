/-
Parity.lean — every De Morgan formula for the parity of four variables has at least 16 leaves.

Shape of the proof (the same as `xor_needs_four_leaves` in lean/PnpLab.lean, scaled up):
  1. Lean evaluates three finite checks on the size table (literals, closure under AND/OR, maximum).
  2. From the checks alone, by induction on formulas:  s (truth table of f) ≤ leaves f,  for EVERY formula f.
  3. The table's entry for parity is 16, so a formula for parity has at least 16 leaves.
The table came from the lab's search, but step 2 never assumes it is correct.

Trust: Lean's kernel, plus `native_decide` (Lean's compiler evaluates the three checks as compiled code).
This is a theorem about one function on four variables.  It is not a statement about P vs NP.
-/
import PnpFormal.Table

namespace PnpFormal

/-! ## The three checks, evaluated by Lean -/

theorem lits_ok : checkLits = true := by native_decide
theorem closed_ok : checkClosed = true := by native_decide
theorem max_ok : checkMax = true := by native_decide

theorem allBelow_spec : ∀ (n : Nat) (p : Nat → Bool), allBelow n p = true → ∀ i, i < n → p i = true := by
  intro n
  induction n with
  | zero => intro p _ i hi; omega
  | succ k ih =>
    intro p h i hi
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases e : i = k
    · subst e; exact h.1
    · exact ih p h.2 i (by omega)

theorem s_le_16 (t : Nat) (ht : t < 65536) : s t ≤ 16 := by
  have := allBelow_spec 65536 _ max_ok t ht
  simpa using this

/-- Closure in the ordered form the check was run in. -/
theorem closed_ordered (x y : Nat) (hx : x < 65536) (hy : y < 65536) (hxy : s x ≤ s y) (hs : s x + s y ≤ 15) :
    s (x &&& y) ≤ s x + s y ∧ s (x ||| y) ≤ s x + s y := by
  have h1 := allBelow_spec 65536 _ closed_ok x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 with h1 | h1
  · omega
  · have h2 := allBelow_spec 65536 _ h1 y hy
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
    rcases h2 with (h2 | h2) | h2
    · omega
    · omega
    · exact h2

/-- Closure for any order of the two arguments. -/
theorem closed (x y : Nat) (hx : x < 65536) (hy : y < 65536) (hs : s x + s y ≤ 15) :
    s (x &&& y) ≤ s x + s y ∧ s (x ||| y) ≤ s x + s y := by
  by_cases hxy : s x ≤ s y
  · exact closed_ordered x y hx hy hxy hs
  · have h := closed_ordered y x hy hx (by omega) (by omega)
    rw [Nat.and_comm, Nat.or_comm] at h
    constructor <;> omega

/-! ## Formulas over four variables -/

/-- De Morgan formulas: literals (a variable or its negation), AND, OR. -/
inductive F where
  | lit (v : Fin 4) (neg : Bool) : F
  | and (a b : F) : F
  | or (a b : F) : F

/-- Number of leaves. -/
def F.leaves : F → Nat
  | .lit _ _ => 1
  | .and a b => a.leaves + b.leaves
  | .or a b => a.leaves + b.leaves

/-- Truth table of a literal: bit `i` of the result is the literal's value on input number `i`. -/
def litTT (v : Fin 4) (neg : Bool) : Nat :=
  match v, neg with
  | 0, false => 0xAAAA | 0, true => 0x5555
  | 1, false => 0xCCCC | 1, true => 0x3333
  | 2, false => 0xF0F0 | 2, true => 0x0F0F
  | 3, false => 0xFF00 | 3, true => 0x00FF

/-- Truth table of a formula as a 16-bit number. -/
def F.tt : F → Nat
  | .lit v n => litTT v n
  | .and a b => a.tt &&& b.tt
  | .or a b => a.tt ||| b.tt

theorem litTT_lt (v : Fin 4) (n : Bool) : litTT v n < 65536 := by
  revert v n; decide

theorem litTT_size (v : Fin 4) (n : Bool) : s (litTT v n) ≤ 1 := by
  have h := lits_ok
  simp only [checkLits, litTables, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  match v, n with
  | 0, false => exact h0 | 0, true => exact h1
  | 1, false => exact h2 | 1, true => exact h3
  | 2, false => exact h4 | 2, true => exact h5
  | 3, false => exact h6 | 3, true => exact h7

theorem tt_lt (f : F) : f.tt < 65536 := by
  induction f with
  | lit v n => exact litTT_lt v n
  | and a b iha ihb => exact Nat.lt_of_le_of_lt Nat.and_le_left iha
  | or a b iha ihb => exact Nat.or_lt_two_pow (n := 16) iha ihb

theorem leaves_pos (f : F) : 1 ≤ f.leaves := by
  induction f with
  | lit _ _ => simp [F.leaves]
  | and a b iha ihb => simp [F.leaves]; omega
  | or a b iha ihb => simp [F.leaves]; omega

/-- **The table is a lower bound for every formula.**  Whatever formula computes a function, it has at least
as many leaves as the table says. -/
theorem size_le_leaves (f : F) : s f.tt ≤ f.leaves := by
  induction f with
  | lit v n => simpa [F.tt, F.leaves] using litTT_size v n
  | and a b iha ihb =>
    simp only [F.tt, F.leaves]
    by_cases h : a.leaves + b.leaves ≤ 15
    · have := (closed a.tt b.tt (tt_lt a) (tt_lt b) (by omega)).1
      omega
    · have := s_le_16 (a.tt &&& b.tt) (tt_lt (.and a b))
      omega
  | or a b iha ihb =>
    simp only [F.tt, F.leaves]
    by_cases h : a.leaves + b.leaves ≤ 15
    · have := (closed a.tt b.tt (tt_lt a) (tt_lt b) (by omega)).2
      omega
    · have := s_le_16 (a.tt ||| b.tt) (tt_lt (.or a b))
      omega

/-! ## Parity of four variables -/

/-- Truth table of `x0 XOR x1 XOR x2 XOR x3`. -/
def parityTT : Nat := 0x6996

theorem parity_entry : s parityTT = 16 := by native_decide

/-- **Every formula for 4-variable parity has at least 16 leaves.** -/
theorem parity_needs_16_leaves (f : F) (h : f.tt = parityTT) : 16 ≤ f.leaves := by
  have h1 := size_le_leaves f
  rw [h, parity_entry] at h1
  exact h1

def x (i : Fin 4) : F := .lit i false
def nx (i : Fin 4) : F := .lit i true
def xor2 (i j : Fin 4) : F := .or (.and (x i) (nx j)) (.and (nx i) (x j))
def xnor2 (i j : Fin 4) : F := .or (.and (x i) (x j)) (.and (nx i) (nx j))
/-- `(x0 ⊕ x1) ⊕ (x2 ⊕ x3)` written with AND, OR and negated literals: 16 leaves. -/
def parityFormula : F := .or (.and (xor2 0 1) (xnor2 2 3)) (.and (xnor2 0 1) (xor2 2 3))

/-- And 16 leaves are enough, so the exact size is 16. -/
theorem parity_has_16_leaves : parityFormula.leaves = 16 ∧ parityFormula.tt = parityTT := by
  constructor <;> decide

/-- The table marks 114 functions with 16; by `size_le_leaves` every one of them needs at least 16 leaves. -/
theorem hardest_count : countAt 16 = 114 := by native_decide

theorem any_marked_16_needs_16 (f : F) (h : s f.tt = 16) : 16 ≤ f.leaves := by
  have := size_le_leaves f; omega

end PnpFormal

#print axioms PnpFormal.size_le_leaves
#print axioms PnpFormal.parity_needs_16_leaves
#print axioms PnpFormal.parity_has_16_leaves
#print axioms PnpFormal.hardest_count
