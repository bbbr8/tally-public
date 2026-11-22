/-
Facts.lean — named consequences of `table_exact`: the exact formula sizes the lab quotes.
Each is "some formula has exactly this many leaves, and no formula has fewer".
-/
import PnpFormal.Exact

namespace PnpFormal

/-- Exact size statement for one truth table. -/
def ExactSize (t k : Nat) : Prop :=
  (∃ f : F, f.tt = t ∧ f.leaves = k) ∧ (∀ f : F, f.tt = t → k ≤ f.leaves)

theorem exact_of_entry (t k : Nat) (ht : t < 65536) (hk : 1 ≤ k) (h : s t = k) : ExactSize t k := by
  subst h; exact table_exact t ht hk

/-- `x0 XOR x1` : exactly 4 leaves. -/
theorem xor2_exact : ExactSize 0x6666 4 := exact_of_entry _ _ (by decide) (by decide) (by native_decide)

/-- `x0 XOR x1 XOR x2` : exactly 10 leaves.  (Khrapchenko's bound gives only 9; the lab's first test expected 9 and was wrong.) -/
theorem parity3_exact : ExactSize 0x9696 10 := exact_of_entry _ _ (by decide) (by decide) (by native_decide)

/-- Majority of `x0, x1, x2` : exactly 5 leaves. -/
theorem majority3_exact : ExactSize 0xE8E8 5 := exact_of_entry _ _ (by decide) (by decide) (by native_decide)

/-- `x0 XOR x1 XOR x2 XOR x3` : exactly 16 leaves. -/
theorem parity4_exact : ExactSize 0x6996 16 := exact_of_entry _ _ (by decide) (by decide) (by native_decide)

/-- No function of four variables needs more than 16 leaves, and exactly 114 need 16. -/
theorem largest_is_16 : (∀ t, t < 65536 → s t ≤ 16) ∧ countAt 16 = 114 := ⟨s_le_16, hardest_count⟩

end PnpFormal

#print axioms PnpFormal.xor2_exact
#print axioms PnpFormal.parity3_exact
#print axioms PnpFormal.majority3_exact
#print axioms PnpFormal.parity4_exact
#print axioms PnpFormal.largest_is_16
