/-
RootBound.lean — why the sum-check verifier catches a false count.

In each round the prover sends a polynomial g of degree at most d.  If it is not the true one, the difference
g - g_true is a nonzero polynomial of degree at most d, and the verifier is fooled only if its random challenge
is a root of that difference.  So the per-round error is (number of roots) / (field size), and the whole bound
rests on one fact:

    a polynomial of degree d whose leading coefficient is nonzero mod p has at most d roots mod p.

This file proves that fact from scratch (Lean 4 core, no Mathlib), for any modulus p with Euclid's property
(p divides a product only if it divides a factor — true exactly when p is prime), and then discharges
Euclid's property for p = 7 so that one instance is unconditional for every degree.

Polynomials are coefficient lists, lowest degree first.  Not a statement about P vs NP.
-/
namespace PnpFormal.Poly

/-- Value of the polynomial with coefficients `cs` (lowest degree first) at `x`. -/
def eval (x : Int) : List Int → Int
  | [] => 0
  | c :: cs => c + x * eval x cs

/-- Leading (highest-degree) coefficient; 0 for the empty list. -/
def lead : List Int → Int
  | [] => 0
  | [c] => c
  | _ :: c' :: cs => lead (c' :: cs)

/-- Quotient on dividing by `(x - r)`: one coefficient shorter. -/
def quot (r : Int) : List Int → List Int
  | [] => []
  | [_] => []
  | _ :: c' :: cs => eval r (c' :: cs) :: quot r (c' :: cs)

theorem quot_length (r : Int) : ∀ cs : List Int, (quot r cs).length = cs.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: c' :: cs => by
    have ih := quot_length r (c' :: cs)
    simp only [quot, List.length_cons] at ih ⊢
    omega

/-- The factor theorem: `p(x) = (x - r) * q(x) + p(r)`. -/
theorem eval_quot (x r : Int) : ∀ cs : List Int, eval x cs = (x - r) * eval x (quot r cs) + eval r cs
  | [] => by simp [eval, quot]
  | [c] => by simp [eval, quot]
  | c :: c' :: cs => by
    have ih := eval_quot x r (c' :: cs)
    simp only [quot, eval] at ih ⊢
    rw [ih]
    grind

/-- Dividing by `(x - r)` keeps the leading coefficient (for degree at least 1). -/
theorem lead_quot (r : Int) : ∀ cs : List Int, 2 ≤ cs.length → lead (quot r cs) = lead cs
  | [] => by simp
  | [_] => by simp
  | [c, c'] => by simp [quot, lead, eval]
  | c :: c' :: c'' :: cs => by
    intro _
    have ih := lead_quot r (c' :: c'' :: cs) (by simp)
    simp only [quot, lead] at ih ⊢
    exact ih

/-- **Root bound.**  Let `p` have Euclid's property.  If the leading coefficient of `cs` is not divisible by `p`,
then any list of roots mod `p` that are pairwise different mod `p` is no longer than the degree. -/
theorem roots_le_degree (p : Int) (hE : ∀ a b : Int, p ∣ a * b → p ∣ a ∨ p ∣ b) :
    ∀ (rs : List Int) (cs : List Int), ¬ p ∣ lead cs →
      rs.Pairwise (fun a b => ¬ p ∣ (a - b)) → (∀ r ∈ rs, p ∣ eval r cs) → rs.length + 1 ≤ cs.length := by
  intro rs
  induction rs with
  | nil =>
    intro cs hl _ _
    cases cs with
    | nil => exact absurd (Int.dvd_zero p) hl
    | cons c cs => simp
  | cons r rs ih =>
    intro cs hl hpw hroots
    have hr : p ∣ eval r cs := hroots r (List.mem_cons_self ..)
    -- a constant polynomial with a root would have leading coefficient divisible by p
    have hlen : 2 ≤ cs.length := by
      match cs, hl, hr with
      | [], hl, _ => exact absurd (Int.dvd_zero p) hl
      | [c], hl, hr => simp [eval, lead] at hl hr; exact absurd hr hl
      | _ :: _ :: _, _, _ => simp
    have hpw' := List.pairwise_cons.mp hpw
    -- every later root is a root of the quotient
    have hq : ∀ s ∈ rs, p ∣ eval s (quot r cs) := by
      intro s hs
      have hsroot : p ∣ eval s cs := hroots s (List.mem_cons_of_mem _ hs)
      rw [eval_quot s r cs] at hsroot
      have hprod : p ∣ (s - r) * eval s (quot r cs) := by
        have := Int.dvd_sub hsroot hr
        rwa [Int.add_sub_cancel] at this
      rcases hE _ _ hprod with h | h
      · exfalso
        apply hpw'.1 s hs
        have : r - s = -(s - r) := by omega
        rw [this]
        exact Int.dvd_neg.mpr h
      · exact h
    have := ih (quot r cs) (by rw [lead_quot r cs hlen]; exact hl) hpw'.2 hq
    rw [quot_length] at this
    simp only [List.length_cons]
    omega

/-! ## One unconditional instance: p = 7 -/

/-- Euclid's property for 7. -/
theorem euclid_seven : ∀ a b : Int, (7 : Int) ∣ a * b → (7 : Int) ∣ a ∨ (7 : Int) ∣ b := by
  intro a b h
  have hm : (a % 7) * (b % 7) % 7 = 0 := by
    rw [← Int.mul_emod]; exact Int.emod_eq_zero_of_dvd h
  have ha0 : 0 ≤ a % 7 := Int.emod_nonneg a (by decide)
  have ha1 : a % 7 < 7 := Int.emod_lt_of_pos a (by decide)
  have hb0 : 0 ≤ b % 7 := Int.emod_nonneg b (by decide)
  have hb1 : b % 7 < 7 := Int.emod_lt_of_pos b (by decide)
  by_cases hA : a % 7 = 0
  · exact Or.inl (Int.dvd_of_emod_eq_zero hA)
  · by_cases hB : b % 7 = 0
    · exact Or.inr (Int.dvd_of_emod_eq_zero hB)
    · exfalso
      generalize a % 7 = x at *
      generalize b % 7 = y at *
      have hx : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
      have hy : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by omega
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm

/-- Mod 7, with no assumption left: a polynomial whose leading coefficient is not a multiple of 7 has at most
`degree` roots that differ mod 7.  (lean/PnpLab.lean checked this for quadratics by enumeration; this is every degree.) -/
theorem roots_le_degree_mod7 (rs cs : List Int) (hl : ¬ (7 : Int) ∣ lead cs)
    (hpw : rs.Pairwise (fun a b => ¬ (7 : Int) ∣ (a - b))) (hroots : ∀ r ∈ rs, (7 : Int) ∣ eval r cs) :
    rs.length + 1 ≤ cs.length :=
  roots_le_degree 7 euclid_seven rs cs hl hpw hroots

end PnpFormal.Poly

#print axioms PnpFormal.Poly.eval_quot
#print axioms PnpFormal.Poly.roots_le_degree
#print axioms PnpFormal.Poly.euclid_seven
#print axioms PnpFormal.Poly.roots_le_degree_mod7
