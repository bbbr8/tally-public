import LangStress.Spectra

namespace LangStress.Spectra

/-- The LIBR owner and other-origin slots partition the four traceable balances. -/
theorem libr_partition (mask : Nat) (v : Vec) :
    (libOfOwnerLast mask v).getD 5 0 + (libOfOwnerLast mask v).getD 6 0 =
    v.getD 0 0 + v.getD 1 0 + v.getD 2 0 + v.getD 3 0 := by
  simp [libOfOwnerLast, List.range_succ, zero, Array.set!, Array.getD, isOwner]
  split <;> split <;> grind

/-- When the four traceable balances are nonnegative, both aggregated holdings are nonnegative. -/
theorem libr_nonnegative (mask : Nat) (v : Vec)
    (h : ∀ i, i < 4 → 0 ≤ v.getD i 0) :
    0 ≤ (libOfOwnerLast mask v).getD 5 0 ∧ 0 ≤ (libOfOwnerLast mask v).getD 6 0 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp [libOfOwnerLast, List.range_succ, zero, Array.set!, Array.getD, isOwner] at *
  split <;> split <;> grind

/-- The overdraft stays in its separate slot for every owner mask. -/
theorem libr_preserves_overdraft (mask : Nat) (v : Vec) :
    (libOfOwnerLast mask v).getD 4 0 = v.getD 4 0 := by
  simp [libOfOwnerLast, zero, Array.set!, Array.getD]

#print axioms libr_partition
#print axioms libr_nonnegative
#print axioms libr_preserves_overdraft

end LangStress.Spectra
