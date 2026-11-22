/-
Field.lean — the two moduli used by arith.py are prime, so the root bound holds for them with no assumption.

  2^31 - 1 = 2147483647            (numpy / GPU prover)
  2^61 - 1 = 2305843009213693951   (pure-Python prover, v2 and v3)

Chain: trial division up to the square root (run compiled, `native_decide`)  ->  only divisors are 1 and p
       ->  Euclid's property (through gcd)  ->  `Poly.roots_le_degree`.

Consequence for the sum-check protocol: if the polynomial a prover sends in a round differs from the true one,
their difference has degree at most d, so at most d of the p possible challenges fail to expose it.
Not a statement about P vs NP.
-/
import PnpFormal.PrimeCheck
import PnpFormal.RootBound

namespace PnpFormal

theorem noDiv_spec (p : Nat) : ∀ B : Nat, noDiv p B = true → ∀ d, 2 ≤ d → d ≤ B → p % d ≠ 0 := by
  intro B
  induction B with
  | zero => intro _ d h2 hB; omega
  | succ k ih =>
    cases k with
    | zero => intro _ d h2 hB; omega
    | succ j =>
      intro h d h2 hB
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      by_cases e : d = j + 2
      · subst e; exact h.1
      · exact ih h.2 d h2 (by omega)

/-- If trial division finds nothing up to `B` and `(B+1)^2 > p`, the only divisors of `p` are 1 and `p`. -/
theorem prime_of_check (p B : Nat) (hp : 2 ≤ p) (hB : p < (B + 1) * (B + 1)) (h : noDiv p B = true) :
    ∀ m, m ∣ p → m = 1 ∨ m = p := by
  intro m hm
  obtain ⟨k, hk⟩ := hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  have hm0 : m ≠ 0 := by intro e; subst e; simp at hk; omega
  have hk0 : k ≠ 0 := by intro e; subst e; simp at hk; omega
  have hk1 : k ≠ 1 := by intro e; subst e; simp at hk; exact hmp hk.symm
  have small : ∀ d e : Nat, 2 ≤ d → d ≤ e → p = d * e → False := by
    intro d e hd hde hp'
    have hsq : d * d ≤ p := by rw [hp']; exact Nat.mul_le_mul_left d hde
    have hdB : d ≤ B := by
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_not_le
      intro hc
      exact absurd (Nat.lt_of_lt_of_le hB (Nat.le_trans (Nat.mul_le_mul hc hc) hsq)) (Nat.lt_irrefl _)
    exact noDiv_spec p B h d hd hdB (by rw [hp']; exact Nat.mul_mod_right d e)
  by_cases hle : m ≤ k
  · exact small m k (by omega) hle hk
  · exact small k m (by omega) (by omega) (by rw [hk, Nat.mul_comm])

/-- Euclid's property for a number whose only divisors are 1 and itself. -/
theorem euclid_nat (p : Nat) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (a b : Nat) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    have hg : Nat.gcd p a = 1 := by
      rcases hpr _ (Nat.gcd_dvd_left p a) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ Nat.gcd_dvd_right p a) ha
    exact Nat.Coprime.dvd_of_dvd_mul_left hg h

theorem euclid_int (p : Nat) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (a b : Int) (h : (p : Int) ∣ a * b) :
    (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  have h' : p ∣ a.natAbs * b.natAbs := by
    have := Int.ofNat_dvd_left.mp h
    rwa [Int.natAbs_mul] at this
  rcases euclid_nat p hpr _ _ h' with h1 | h1
  · exact Or.inl (Int.ofNat_dvd_left.mpr h1)
  · exact Or.inr (Int.ofNat_dvd_left.mpr h1)

/-! ## The two moduli -/

def P31 : Nat := 2147483647
def P61 : Nat := 2305843009213693951

theorem p31_check : noDiv P31 46340 = true := by native_decide
theorem p61_check : noDiv P61 1518500249 = true := by native_decide

/-- 2^31 - 1 is prime. -/
theorem p31_prime : ∀ m, m ∣ P31 → m = 1 ∨ m = P31 :=
  prime_of_check P31 46340 (by decide) (by decide) p31_check

/-- 2^61 - 1 is prime. -/
theorem p61_prime : ∀ m, m ∣ P61 → m = 1 ∨ m = P61 :=
  prime_of_check P61 1518500249 (by decide) (by decide) p61_check

/-- **Root bound in the lab's 61-bit field, no assumptions.**  A polynomial whose leading coefficient is not a
multiple of `2^61 - 1` has at most `degree` roots that differ mod `2^61 - 1`. -/
theorem roots_le_degree_p61 (rs cs : List Int) (hl : ¬ (P61 : Int) ∣ Poly.lead cs)
    (hpw : rs.Pairwise (fun a b => ¬ (P61 : Int) ∣ (a - b))) (hroots : ∀ r ∈ rs, (P61 : Int) ∣ Poly.eval r cs) :
    rs.length + 1 ≤ cs.length :=
  Poly.roots_le_degree (P61 : Int) (euclid_int P61 p61_prime) rs cs hl hpw hroots

/-- The same in the 31-bit field. -/
theorem roots_le_degree_p31 (rs cs : List Int) (hl : ¬ (P31 : Int) ∣ Poly.lead cs)
    (hpw : rs.Pairwise (fun a b => ¬ (P31 : Int) ∣ (a - b))) (hroots : ∀ r ∈ rs, (P31 : Int) ∣ Poly.eval r cs) :
    rs.length + 1 ≤ cs.length :=
  Poly.roots_le_degree (P31 : Int) (euclid_int P31 p31_prime) rs cs hl hpw hroots

end PnpFormal

#print axioms PnpFormal.p61_prime
#print axioms PnpFormal.roots_le_degree_p61
#print axioms PnpFormal.roots_le_degree_p31
