/-
Exact.lean — the size table is exact for every function of four variables.

Parity.lean proved the table is a LOWER bound for every formula.  Here Lean checks that every entry is also
ACHIEVED: the table carries, for each function of size 2 or more, two smaller functions that combine to it with
sizes adding up, and from those Lean builds an actual formula of exactly that size.

Result: for each of the 65,534 non-constant functions, the minimum number of leaves is exactly the table entry;
the largest is 16 and exactly 114 functions need it.  (The two constants need 2 leaves.)

Trust: Lean's kernel, plus `native_decide` for the finite checks.  Not a statement about P vs NP.
-/
import PnpFormal.Parity

namespace PnpFormal

theorem ones_ok : checkOnes = true := by native_decide
theorem build_ok : checkBuild = true := by native_decide

/-- The literal whose truth table is `t` (for the eight literal tables). -/
def litOf (t : Nat) : F :=
  if t = 0xAAAA then .lit 0 false else if t = 0x5555 then .lit 0 true else
  if t = 0xCCCC then .lit 1 false else if t = 0x3333 then .lit 1 true else
  if t = 0xF0F0 then .lit 2 false else if t = 0x0F0F then .lit 2 true else
  if t = 0xFF00 then .lit 3 false else .lit 3 true

theorem litOf_ok (t : Nat) (h : t ∈ litTables) : (litOf t).tt = t ∧ (litOf t).leaves = 1 := by
  simp only [litTables, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem ones_spec (t : Nat) (ht : t < 65536) (h1 : s t = 1) : t ∈ litTables := by
  have h := allBelow_spec 65536 _ ones_ok t ht
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h1 h
  · simpa using h

theorem build_spec (t : Nat) (ht : t < 65536) (h2 : 2 ≤ s t) :
    wx t < 65536 ∧ wy t < 65536 ∧ 1 ≤ s (wx t) ∧ 1 ≤ s (wy t) ∧ s (wx t) + s (wy t) = s t ∧
    (wor t = true → wx t ||| wy t = t) ∧ (wor t = false → wx t &&& wy t = t) := by
  have h := allBelow_spec 65536 _ build_ok t ht
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
    refine ⟨a, b, c, d, e, ?_, ?_⟩
    · intro hw; rw [hw] at f; simpa using f
    · intro hw; rw [hw] at f; simpa using f

/-- Build a formula for `t` by following the table's constructions (`fuel` bounds the depth). -/
def build : Nat → Nat → F
  | 0, _ => .lit 0 false
  | fuel + 1, t =>
    if s t ≤ 1 then litOf t
    else if wor t then .or (build fuel (wx t)) (build fuel (wy t))
    else .and (build fuel (wx t)) (build fuel (wy t))

theorem build_correct : ∀ (fuel t : Nat), t < 65536 → 1 ≤ s t → s t ≤ fuel →
    (build fuel t).tt = t ∧ (build fuel t).leaves = s t := by
  intro fuel
  induction fuel with
  | zero => intro t _ h1 h0; omega
  | succ k ih =>
    intro t ht h1 hk
    by_cases hs : s t ≤ 1
    · have e : s t = 1 := by omega
      have h := litOf_ok t (ones_spec t ht e)
      simp only [build, hs, if_true]
      rw [e]; exact h
    · obtain ⟨hx, hy, sx, sy, hsum, hor, hand⟩ := build_spec t ht (by omega)
      have ihx := ih (wx t) hx sx (by omega)
      have ihy := ih (wy t) hy sy (by omega)
      cases hw : wor t
      · have := hand hw
        simp [build, hs, hw, F.tt, F.leaves, ihx.1, ihx.2, ihy.1, ihy.2, this, hsum]
      · have := hor hw
        simp [build, hs, hw, F.tt, F.leaves, ihx.1, ihx.2, ihy.1, ihy.2, this, hsum]

/-- **The table is exact.**  For every non-constant function of four variables: some formula has exactly
`s t` leaves, and no formula has fewer. -/
theorem table_exact (t : Nat) (ht : t < 65536) (h1 : 1 ≤ s t) :
    (∃ f : F, f.tt = t ∧ f.leaves = s t) ∧ (∀ f : F, f.tt = t → s t ≤ f.leaves) :=
  ⟨⟨build (s t) t, build_correct (s t) t ht h1 (Nat.le_refl _)⟩, fun f h => h ▸ size_le_leaves f⟩

/-- Every non-constant function of four variables has a formula with at most 16 leaves. -/
theorem every_function_fits_in_16 (t : Nat) (ht : t < 65536) (h1 : 1 ≤ s t) : ∃ f : F, f.tt = t ∧ f.leaves ≤ 16 := by
  obtain ⟨f, hf, hl⟩ := (table_exact t ht h1).1
  exact ⟨f, hf, by have := s_le_16 t ht; omega⟩

/-- The size distribution found by loop 2, re-counted by Lean. -/
theorem size_histogram :
    [countAt 0, countAt 1, countAt 2, countAt 3, countAt 4, countAt 5, countAt 6, countAt 7, countAt 8,
     countAt 9, countAt 10, countAt 11, countAt 12, countAt 13, countAt 14, countAt 15, countAt 16]
    = [2, 8, 48, 256, 940, 2048, 5248, 8672, 11768, 10592, 11536, 5472, 6304, 960, 1472, 96, 114] := by native_decide

/-- The two entries of 0 are the constants; a constant needs 2 leaves, and 2 are enough. -/
theorem constant_needs_two (f : F) (h : f.tt = 0 ∨ f.tt = 65535) : 2 ≤ f.leaves := by
  cases f with
  | lit v n =>
    exfalso
    have : litTT v n ≠ 0 ∧ litTT v n ≠ 65535 := by revert v n; decide
    simp only [F.tt] at h
    rcases h with h | h
    · exact this.1 h
    · exact this.2 h
  | and a b => have := leaves_pos a; have := leaves_pos b; simp [F.leaves]; omega
  | or a b => have := leaves_pos a; have := leaves_pos b; simp [F.leaves]; omega

theorem constants_have_two :
    (F.and (x 0) (nx 0)).tt = 0 ∧ (F.and (x 0) (nx 0)).leaves = 2 ∧
    (F.or (x 0) (nx 0)).tt = 65535 ∧ (F.or (x 0) (nx 0)).leaves = 2 := by decide

end PnpFormal

#print axioms PnpFormal.table_exact
#print axioms PnpFormal.every_function_fits_in_16
#print axioms PnpFormal.size_histogram
#print axioms PnpFormal.constant_needs_two
#print axioms PnpFormal.constants_have_two
