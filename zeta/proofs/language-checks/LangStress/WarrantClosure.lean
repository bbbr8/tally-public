import LangStress.Warrant

namespace LangStress.Warrant

/-- Every set bit of the first mask is set in the second. -/
def Included (smaller larger : Nat) : Prop :=
  ∀ bit, smaller.testBit bit = true → larger.testBit bit = true

theorem sub_iff_included (a b : Nat) : sub a b = true ↔ Included a b := by
  unfold sub
  rw [beq_iff_eq]
  constructor
  · intro h bit ha
    have he := congrArg (fun mask : Nat => mask.testBit bit) h
    simpa [Nat.testBit_and, ha] using he
  · intro h
    apply Nat.eq_of_testBit_eq
    intro bit
    rw [Nat.testBit_and, Bool.eq_iff_iff, Bool.and_eq_true]
    exact ⟨And.left, fun ha => ⟨ha, h bit ha⟩⟩

private def enabled (j : Just) (s d : Nat) : Bool :=
  sub j.u s && j.ants.all (fun a => d.testBit a)

private theorem enabled_mono {j : Just} {s s' d d' : Nat}
    (hs : Included s s') (hd : Included d d') :
    enabled j s d = true → enabled j s' d' = true := by
  simp only [enabled, Bool.and_eq_true, sub_iff_included, List.all_eq_true]
  intro ⟨hu, ha⟩
  exact ⟨fun bit hb => hs bit (hu bit hb), fun a mem => hd a (ha a mem)⟩

private def addRule (s d acc : Nat) (j : Just) : Nat :=
  if enabled j s d then acc ||| (1 <<< j.t) else acc

private theorem addRule_mono {s s' d d' a a' : Nat} (j : Just)
    (hs : Included s s') (hd : Included d d') (ha : Included a a') :
    Included (addRule s d a j) (addRule s' d' a' j) := by
  intro bit hb
  by_cases small : enabled j s d = true
  · have large := enabled_mono hs hd small
    simp only [addRule, small, large, ite_true, Nat.testBit_or, Bool.or_eq_true] at hb ⊢
    exact hb.elim (fun h => Or.inl (ha bit h)) Or.inr
  · simp only [addRule, small] at hb
    by_cases large : enabled j s' d' = true
    · simp only [addRule, large, ite_true, Nat.testBit_or, Bool.or_eq_true]
      exact Or.inl (ha bit hb)
    · simpa [addRule, large] using ha bit hb

theorem step_mono (js : List Just) {s s' d d' : Nat}
    (hs : Included s s') (hd : Included d d') :
    Included (step js s d) (step js s' d') := by
  have fold : ∀ (rules : List Just) (a a' : Nat), Included a a' →
      Included (rules.foldl (addRule s d) a) (rules.foldl (addRule s' d') a') := by
    intro rules
    induction rules with
    | nil => intro a a' h; exact h
    | cons j rest ih =>
      intro a a' h
      exact ih _ _ (addRule_mono j hs hd h)
  exact fold js d d' hd

theorem iter_mono (js : List Just) {s s' : Nat} (hs : Included s s') (rounds : Nat)
    {d d' : Nat} (hd : Included d d') :
    Included (iter js s rounds d) (iter js s' rounds d') := by
  induction rounds generalizing d d' with
  | zero => exact hd
  | succ n ih => exact ih (step_mono js hs hd)

/-- With the same rules and round bound, enlarging the premise mask preserves closure. -/
theorem closure_mono (N : Nat) (js : List Just) {s s' : Nat} (h : sub s s' = true) :
    Included (closure N js s) (closure N js s') := by
  have hs := (sub_iff_included s s').mp h
  exact iter_mono js hs (N + 1) hs

theorem holds_mono (N : Nat) (js : List Just) {s s' n : Nat} (h : sub s s' = true) :
    holds N js s n = true → holds N js s' n = true :=
  closure_mono N js h n

#print axioms closure_mono
#print axioms holds_mono

end LangStress.Warrant
