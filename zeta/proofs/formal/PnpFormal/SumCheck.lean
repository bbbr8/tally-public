/-
SumCheck.lean — soundness of the sum-check protocol, all rounds.

Setting (the protocol in arith.py).  There are n rounds.  Before round i the verifier holds a claim c and the
challenges so far (`pre`).  The prover sends a polynomial g of degree at most `deg i`; the verifier checks
g(0) + g(1) = c, draws a challenge r, and the claim becomes g(r).  After the last round the verifier compares
the claim with the true value, which it computes itself.

What is proved (soundness; completeness is the theorem after it).  Fix any prover `G` (a function from the challenges seen so far to the polynomial it sends).
`countAcc` counts the challenge vectors on which the verifier accepts.  If the opening claim is false, then

      (number of accepting challenge vectors) * p  ≤  (deg 0 + … + deg (n-1)) * p ^ n ,

that is, the verifier accepts on at most a (sum of degrees)/p fraction of its random choices.

The truth is described abstractly by `T` (the true partial sum after each prefix of challenges; at a full
prefix it is the value the verifier computes) and `S` (the honest prover's polynomial), tied together by three
consistency conditions.  An honest prover exists exactly when such T, S exist; `demo_*` at the end gives one
concrete instance and checks an actual cheating prover against the bound.

Polynomials are coefficient lists, lowest degree first, as in RootBound.lean.  arith.py sends the same polynomial
as its values at 0..d; that is a change of representation only.  The bound is for truly random challenges; arith.py
derives its challenges from a hash, which this theorem does not model.

Lean 4 core, no Mathlib.  Not a statement about P vs NP.
-/
import PnpFormal.RootBound
import PnpFormal.Field

namespace PnpFormal.SumCheck
open PnpFormal.Poly

/-! ## 1. Polynomial facts beyond RootBound -/

/-- If every coefficient is divisible by `p`, every value is. -/
theorem dvd_eval_of_all (p x : Int) : ∀ cs : List Int, (∀ c ∈ cs, p ∣ c) → p ∣ eval x cs
  | [], _ => by simp [eval]
  | c :: cs, h => by
    have h1 : p ∣ c := h c (List.mem_cons_self ..)
    have h2 : p ∣ eval x cs := dvd_eval_of_all p x cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [eval]
    exact Int.dvd_add h1 (Int.dvd_mul_of_dvd_right h2)

theorem lead_append (a : Int) : ∀ cs : List Int, lead (cs ++ [a]) = a
  | [] => rfl
  | [_] => rfl
  | _ :: c' :: cs => by
    have ih := lead_append a (c' :: cs)
    simpa [lead] using ih

/-- Dropping a top coefficient that is divisible by `p` does not change values mod `p`. -/
theorem eval_append_dvd (p x a : Int) (ha : p ∣ a) : ∀ cs : List Int, p ∣ (eval x (cs ++ [a]) - eval x cs)
  | [] => by simpa [eval] using ha
  | c :: cs => by
    have ih := eval_append_dvd p x a ha cs
    have e : eval x ((c :: cs) ++ [a]) - eval x (c :: cs) = x * (eval x (cs ++ [a]) - eval x cs) := by
      simp only [List.cons_append, eval]; grind
    rw [e]; exact Int.dvd_mul_of_dvd_right ih

theorem exists_concat : ∀ cs : List Int, cs ≠ [] → ∃ init last, cs = init ++ [last]
  | [], h => absurd rfl h
  | [c], _ => ⟨[], c, rfl⟩
  | c :: c' :: cs, _ => by
    obtain ⟨init, last, h⟩ := exists_concat (c' :: cs) (by simp)
    exact ⟨c :: init, last, by rw [List.cons_append, ← h]⟩

/-- **Root bound for any polynomial that is not zero mod `p`** (some coefficient is not divisible by `p`):
pairwise different roots mod `p` number at most `length - 1`. -/
theorem roots_le_of_exists (p : Int) (hE : ∀ a b : Int, p ∣ a * b → p ∣ a ∨ p ∣ b) :
    ∀ (n : Nat) (cs : List Int), cs.length = n → (∃ c, c ∈ cs ∧ ¬ p ∣ c) →
      ∀ rs : List Int, rs.Pairwise (fun a b => ¬ p ∣ (a - b)) → (∀ r ∈ rs, p ∣ eval r cs) →
        rs.length + 1 ≤ cs.length := by
  intro n
  induction n with
  | zero =>
    intro cs hlen hex
    obtain ⟨c, hc, _⟩ := hex
    cases cs with
    | nil => simp at hc
    | cons a as => simp at hlen
  | succ k ih =>
    intro cs hlen hex rs hpw hroots
    by_cases hl : p ∣ lead cs
    · have hne : cs ≠ [] := by intro e; subst e; simp at hlen
      obtain ⟨init, last, hcs⟩ := exists_concat cs hne
      subst hcs
      rw [lead_append] at hl
      have hlen' : init.length = k := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
      obtain ⟨c, hc, hnd⟩ := hex
      have hc' : c ∈ init := by
        rcases List.mem_append.mp hc with h | h
        · exact h
        · have e : c = last := by simpa using h
          rw [e] at hnd; exact absurd hl hnd
      have hroots' : ∀ r ∈ rs, p ∣ eval r init := by
        intro r hr
        have h1 := hroots r hr
        have h2 := eval_append_dvd p r last hl init
        have h3 := Int.dvd_sub h1 h2
        have e : eval r (init ++ [last]) - (eval r (init ++ [last]) - eval r init) = eval r init := by omega
        rwa [e] at h3
      have h4 := ih init hlen' ⟨c, hc', hnd⟩ rs hpw hroots'
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · exact roots_le_degree p hE rs cs hl hpw hroots

/-- Coefficientwise difference of two polynomials. -/
def sub : List Int → List Int → List Int
  | [], bs => bs.map (fun b => -b)
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a - b) :: sub as bs

theorem eval_neg (x : Int) : ∀ bs : List Int, eval x (bs.map (fun b => -b)) = - eval x bs
  | [] => by simp [eval]
  | b :: bs => by
    have ih := eval_neg x bs
    simp only [List.map_cons, eval, ih]; grind

theorem eval_sub (x : Int) : ∀ as bs : List Int, eval x (sub as bs) = eval x as - eval x bs
  | [], bs => by simp [sub, eval, eval_neg]
  | a :: as, [] => by simp [sub, eval]
  | a :: as, b :: bs => by
    have ih := eval_sub x as bs
    simp only [sub, eval, ih]; grind

theorem sub_length : ∀ (as bs : List Int) (n : Nat), as.length ≤ n → bs.length ≤ n → (sub as bs).length ≤ n
  | [], bs, n, _, hb => by simpa [sub] using hb
  | a :: as, [], n, ha, _ => by simpa [sub] using ha
  | a :: as, b :: bs, n, ha, hb => by
    cases n with
    | zero => simp at ha
    | succ m =>
      have ih := sub_length as bs m (by simpa using ha) (by simpa using hb)
      simp only [sub, List.length_cons]; omega

/-! ## 2. Counting over the challenges 0, 1, …, n-1 -/

/-- `f 0 + f 1 + … + f (n-1)`. -/
def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- How many `r < n` are bad. -/
def countRange (bad : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countRange bad n + (if bad n then 1 else 0)

/-- The bad `r < n`, largest first. -/
def listRange (bad : Nat → Bool) : Nat → List Nat
  | 0 => []
  | n + 1 => if bad n then n :: listRange bad n else listRange bad n

theorem listRange_length (bad : Nat → Bool) : ∀ n, (listRange bad n).length = countRange bad n
  | 0 => rfl
  | n + 1 => by
    have ih := listRange_length bad n
    by_cases hb : bad n = true <;> simp [listRange, countRange, hb, ih]

theorem listRange_mem (bad : Nat → Bool) : ∀ (n b : Nat), b ∈ listRange bad n → b < n ∧ bad b = true
  | 0, b, h => by simp [listRange] at h
  | n + 1, b, h => by
    by_cases hb : bad n = true
    · have e : listRange bad (n + 1) = n :: listRange bad n := by simp [listRange, hb]
      rw [e] at h
      rcases List.mem_cons.mp h with e' | h'
      · exact ⟨by omega, by rw [e']; exact hb⟩
      · have := listRange_mem bad n b h'; exact ⟨by omega, this.2⟩
    · have e : listRange bad (n + 1) = listRange bad n := by simp [listRange, hb]
      rw [e] at h
      have := listRange_mem bad n b h; exact ⟨by omega, this.2⟩

theorem sumRange_le (f : Nat → Nat) (M : Nat) : ∀ n, (∀ r, r < n → f r ≤ M) → sumRange f n ≤ n * M
  | 0, _ => by simp [sumRange]
  | n + 1, h => by
    have ih := sumRange_le f M n (fun r hr => h r (by omega))
    have hn := h n (by omega)
    simp only [sumRange, Nat.add_mul, Nat.one_mul]
    omega

theorem sumRange_mul (f : Nat → Nat) (c : Nat) : ∀ n, sumRange (fun r => f r * c) n = sumRange f n * c
  | 0 => by simp [sumRange]
  | n + 1 => by
    have ih := sumRange_mul f c n
    simp only [sumRange, ih, Nat.add_mul]

theorem sumRange_const (f : Nat → Nat) (M : Nat) : ∀ n, (∀ r, r < n → f r = M) → sumRange f n = n * M
  | 0, _ => by simp [sumRange]
  | n + 1, h => by
    have ih := sumRange_const f M n (fun r hr => h r (by omega))
    have hn := h n (by omega)
    simp only [sumRange, ih, hn, Nat.add_mul, Nat.one_mul]

/-- Split a sum by a bad/good test: bad terms are at most `M`, good terms at most `m`. -/
theorem sumRange_split (f : Nat → Nat) (bad : Nat → Bool) (M m : Nat) :
    ∀ n, (∀ r, r < n → bad r = true → f r ≤ M) → (∀ r, r < n → bad r = false → f r ≤ m) →
      sumRange f n ≤ countRange bad n * M + n * m
  | 0, _, _ => by simp [sumRange]
  | n + 1, hb, hg => by
    have ih := sumRange_split f bad M m n (fun r hr => hb r (by omega)) (fun r hr => hg r (by omega))
    by_cases h : bad n = true
    · have h1 := hb n (by omega) h
      have e : countRange bad (n + 1) = countRange bad n + 1 := by simp [countRange, h]
      rw [e]
      simp only [sumRange, Nat.add_mul, Nat.one_mul]
      omega
    · have h' : bad n = false := by simpa using h
      have h1 := hg n (by omega) h'
      have e : countRange bad (n + 1) = countRange bad n := by simp [countRange, h']
      rw [e]
      simp only [sumRange, Nat.add_mul, Nat.one_mul]
      omega

/-- Two different residues below `p` are not congruent mod `p`. -/
theorem not_dvd_cast_sub (p a b : Nat) (hab : b < a) (hap : a < p) : ¬ (p : Int) ∣ ((a : Int) - (b : Int)) := by
  intro h
  have h0 := Int.emod_eq_zero_of_dvd h
  have h1 : ((a : Int) - (b : Int)) % (p : Int) = (a : Int) - (b : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  omega

theorem pairwise_listRange (p : Nat) (bad : Nat → Bool) : ∀ n, n ≤ p →
    ((listRange bad n).map (fun r : Nat => (r : Int))).Pairwise (fun a b => ¬ (p : Int) ∣ (a - b))
  | 0, _ => by simp [listRange]
  | n + 1, hn => by
    have ih := pairwise_listRange p bad n (by omega)
    by_cases hb : bad n = true
    · have e : listRange bad (n + 1) = n :: listRange bad n := by simp [listRange, hb]
      rw [e, List.map_cons]
      refine List.pairwise_cons.mpr ⟨?_, ih⟩
      intro a' ha'
      obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp ha'
      exact not_dvd_cast_sub p n b (listRange_mem bad n b hbm).1 (by omega)
    · have e : listRange bad (n + 1) = listRange bad n := by simp [listRange, hb]
      rw [e]; exact ih

/-- **How many challenges are roots.**  If a polynomial is not zero mod `p`, fewer than `length` of the residues
`0..p-1` are roots of it mod `p`. -/
theorem bad_count_lt (p : Nat) (hE : ∀ a b : Int, (p : Int) ∣ a * b → (p : Int) ∣ a ∨ (p : Int) ∣ b)
    (cs : List Int) (hex : ∃ c, c ∈ cs ∧ ¬ (p : Int) ∣ c) :
    countRange (fun r => decide (eval (r : Int) cs % (p : Int) = 0)) p + 1 ≤ cs.length := by
  have hpw := pairwise_listRange p (fun r => decide (eval (r : Int) cs % (p : Int) = 0)) p (Nat.le_refl p)
  have hroots : ∀ r ∈ (listRange (fun r => decide (eval (r : Int) cs % (p : Int) = 0)) p).map (fun r : Nat => (r : Int)),
      (p : Int) ∣ eval r cs := by
    intro r hr
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hr
    have h := (listRange_mem _ p b hbm).2
    exact Int.dvd_of_emod_eq_zero (by simpa using h)
  have h := roots_le_of_exists (p : Int) hE cs.length cs rfl hex _ hpw hroots
  rw [List.length_map, listRange_length] at h
  exact h

/-! ## 3. The protocol -/

section Protocol

variable (p : Nat) (T : List Int → Int) (G : List Int → List Int) (deg : Nat → Nat)

/-- Number of challenge vectors in `{0..p-1}^k` on which the verifier accepts, from the state
(`pre` = challenges so far, `c` = current claim), against prover `G`.
Round: the prover sends `G pre`; the verifier checks the degree bound and `g(0) + g(1) = c` (mod `p`);
for each challenge `r` the claim becomes `g(r)`.  With no rounds left the claim is compared with `T pre`. -/
def countAcc : Nat → List Int → Int → Nat
  | 0, pre, c => if (c - T pre) % (p : Int) = 0 then 1 else 0
  | k + 1, pre, c =>
    if (G pre).length ≤ deg pre.length + 1 ∧ (eval 0 (G pre) + eval 1 (G pre) - c) % (p : Int) = 0 then
      sumRange (fun r => countAcc k (pre ++ [(r : Int)]) (eval (r : Int) (G pre))) p
    else 0

/-- `deg i + deg (i+1) + … + deg (i+k-1)`. -/
def degSum : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i => deg i + degSum k (i + 1)

/-- There are only `p ^ k` challenge vectors. -/
theorem countAcc_le : ∀ (k : Nat) (pre : List Int) (c : Int), countAcc p T G deg k pre c ≤ p ^ k
  | 0, pre, c => by
    simp only [countAcc]; split <;> simp
  | k + 1, pre, c => by
    simp only [countAcc]
    split
    · have h := sumRange_le (fun r => countAcc p T G deg k (pre ++ [(r : Int)]) (eval (r : Int) (G pre))) (p ^ k) p
        (fun r _ => countAcc_le k _ _)
      have e : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [e]; exact h
    · exact Nat.zero_le _

/-- **Soundness of sum-check.**  `S` is the honest prover and `T` the truth, consistent with each other for the
`n` rounds.  From any state whose claim is false, against any prover `G`, the verifier accepts on at most
`(sum of the remaining degree bounds) / p` of the remaining challenge vectors. -/
theorem soundness (hE : ∀ a b : Int, (p : Int) ∣ a * b → (p : Int) ∣ a ∨ (p : Int) ∣ b)
    (S : List Int → List Int) (n : Nat)
    (hS1 : ∀ pre : List Int, pre.length < n → (S pre).length ≤ deg pre.length + 1)
    (hS2 : ∀ pre : List Int, pre.length < n → (p : Int) ∣ (eval 0 (S pre) + eval 1 (S pre) - T pre))
    (hS3 : ∀ (pre : List Int) (r : Nat), pre.length < n →
      (p : Int) ∣ (T (pre ++ [(r : Int)]) - eval (r : Int) (S pre))) :
    ∀ (k : Nat) (pre : List Int) (c : Int), pre.length + k = n → ¬ (p : Int) ∣ (c - T pre) →
      countAcc p T G deg k pre c * p ≤ degSum deg k pre.length * p ^ k := by
  intro k
  induction k with
  | zero =>
    intro pre c _ hc
    have h : (c - T pre) % (p : Int) ≠ 0 := fun h => hc (Int.dvd_of_emod_eq_zero h)
    simp [countAcc, h]
  | succ k ih =>
    intro pre c hlen hc
    simp only [countAcc]
    split
    · rename_i hcond
      obtain ⟨hGlen, hGsum⟩ := hcond
      have hGsum' : (p : Int) ∣ (eval 0 (G pre) + eval 1 (G pre) - c) := Int.dvd_of_emod_eq_zero hGsum
      have hpre : pre.length < n := by omega
      -- the prover's polynomial differs from the honest one: their difference is not zero mod p
      have hex : ∃ c', c' ∈ sub (G pre) (S pre) ∧ ¬ (p : Int) ∣ c' := by
        apply Classical.byContradiction
        intro hno
        have hall : ∀ c' ∈ sub (G pre) (S pre), (p : Int) ∣ c' := by
          intro c' hc'
          apply Classical.byContradiction
          intro hn
          exact hno ⟨c', hc', hn⟩
        have h0 := dvd_eval_of_all (p : Int) 0 _ hall
        have h1 := dvd_eval_of_all (p : Int) 1 _ hall
        rw [eval_sub] at h0 h1
        have h2 := hS2 pre hpre
        apply hc
        have e : c - T pre = (eval 0 (G pre) - eval 0 (S pre)) + (eval 1 (G pre) - eval 1 (S pre))
            - (eval 0 (G pre) + eval 1 (G pre) - c) + (eval 0 (S pre) + eval 1 (S pre) - T pre) := by omega
        rw [e]
        exact Int.dvd_add (Int.dvd_sub (Int.dvd_add h0 h1) hGsum') h2
      have hDlen : (sub (G pre) (S pre)).length ≤ deg pre.length + 1 := sub_length _ _ _ hGlen (hS1 pre hpre)
      have hbad := bad_count_lt p hE (sub (G pre) (S pre)) hex
      have hbad' : countRange (fun r => decide (eval (r : Int) (sub (G pre) (S pre)) % (p : Int) = 0)) p
          ≤ deg pre.length := by omega
      -- bad challenges: at most p^k suffixes each;  good challenges: the claim stays false, use the induction hypothesis
      have hsplit := sumRange_split
        (fun r => countAcc p T G deg k (pre ++ [(r : Int)]) (eval (r : Int) (G pre)) * p)
        (fun r => decide (eval (r : Int) (sub (G pre) (S pre)) % (p : Int) = 0))
        (p ^ k * p) (degSum deg k (pre.length + 1) * p ^ k) p
        (fun r _ _ => Nat.mul_le_mul_right p (countAcc_le p T G deg k _ _))
        (by
          intro r _ hbr
          have hnd : ¬ (p : Int) ∣ eval (r : Int) (sub (G pre) (S pre)) := by
            intro h
            have h' := Int.emod_eq_zero_of_dvd h
            simp [h'] at hbr
          rw [eval_sub] at hnd
          have h3 := hS3 pre r hpre
          have hc' : ¬ (p : Int) ∣ (eval (r : Int) (G pre) - T (pre ++ [(r : Int)])) := by
            intro h
            apply hnd
            have e : eval (r : Int) (G pre) - eval (r : Int) (S pre)
                = (eval (r : Int) (G pre) - T (pre ++ [(r : Int)])) + (T (pre ++ [(r : Int)]) - eval (r : Int) (S pre)) := by
              omega
            rw [e]; exact Int.dvd_add h h3
          have h4 := ih (pre ++ [(r : Int)]) (eval (r : Int) (G pre))
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hc'
          simpa using h4)
      rw [sumRange_mul] at hsplit
      have e1 : p * (degSum deg k (pre.length + 1) * p ^ k) = degSum deg k (pre.length + 1) * (p ^ k * p) := by
        rw [Nat.mul_comm p, Nat.mul_assoc]
      rw [e1] at hsplit
      have e2 : countRange (fun r => decide (eval (r : Int) (sub (G pre) (S pre)) % (p : Int) = 0)) p * (p ^ k * p)
          ≤ deg pre.length * (p ^ k * p) := Nat.mul_le_mul_right _ hbad'
      simp only [degSum, Nat.pow_succ, Nat.add_mul]
      exact Nat.le_trans hsplit (Nat.add_le_add_right e2 _)
    · simp

/-- **Completeness of sum-check.**  The honest prover `S`, starting from a true claim, is accepted on every one of
the `p ^ k` remaining challenge vectors. -/
theorem completeness (S : List Int → List Int) (n : Nat)
    (hS1 : ∀ pre : List Int, pre.length < n → (S pre).length ≤ deg pre.length + 1)
    (hS2 : ∀ pre : List Int, pre.length < n → (p : Int) ∣ (eval 0 (S pre) + eval 1 (S pre) - T pre))
    (hS3 : ∀ (pre : List Int) (r : Nat), pre.length < n →
      (p : Int) ∣ (T (pre ++ [(r : Int)]) - eval (r : Int) (S pre))) :
    ∀ (k : Nat) (pre : List Int) (c : Int), pre.length + k = n → (p : Int) ∣ (c - T pre) →
      countAcc p T S deg k pre c = p ^ k := by
  intro k
  induction k with
  | zero =>
    intro pre c _ hc
    have h : (c - T pre) % (p : Int) = 0 := Int.emod_eq_zero_of_dvd hc
    simp [countAcc, h]
  | succ k ih =>
    intro pre c hlen hc
    have hpre : pre.length < n := by omega
    have h2 := hS2 pre hpre
    have hsum : (eval 0 (S pre) + eval 1 (S pre) - c) % (p : Int) = 0 := by
      apply Int.emod_eq_zero_of_dvd
      have e : eval 0 (S pre) + eval 1 (S pre) - c = (eval 0 (S pre) + eval 1 (S pre) - T pre) - (c - T pre) := by omega
      rw [e]; exact Int.dvd_sub h2 hc
    have hcond : (S pre).length ≤ deg pre.length + 1 ∧ (eval 0 (S pre) + eval 1 (S pre) - c) % (p : Int) = 0 :=
      ⟨hS1 pre hpre, hsum⟩
    have hall : ∀ r, r < p → countAcc p T S deg k (pre ++ [(r : Int)]) (eval (r : Int) (S pre)) = p ^ k := by
      intro r _
      apply ih
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · have h3 := hS3 pre r hpre
        have e : eval (r : Int) (S pre) - T (pre ++ [(r : Int)]) = -(T (pre ++ [(r : Int)]) - eval (r : Int) (S pre)) := by omega
        rw [e]; exact Int.dvd_neg.mpr h3
    simp only [countAcc]
    split
    · rw [sumRange_const _ (p ^ k) p hall, Nat.pow_succ]
      exact Nat.mul_comm _ _
    · rename_i hno
      exact absurd hcond hno

end Protocol

/-! ## 4. The lab's field, with no assumption left -/

/-- **Sum-check soundness over the 61-bit field used by arith.py.**  From the opening state (`pre = []`), a false
claim is accepted on at most `(deg 0 + … + deg (n-1)) / (2^61 - 1)` of the challenge vectors. -/
theorem soundness_p61 (T : List Int → Int) (G : List Int → List Int) (deg : Nat → Nat)
    (S : List Int → List Int) (n : Nat)
    (hS1 : ∀ pre : List Int, pre.length < n → (S pre).length ≤ deg pre.length + 1)
    (hS2 : ∀ pre : List Int, pre.length < n → (P61 : Int) ∣ (eval 0 (S pre) + eval 1 (S pre) - T pre))
    (hS3 : ∀ (pre : List Int) (r : Nat), pre.length < n →
      (P61 : Int) ∣ (T (pre ++ [(r : Int)]) - eval (r : Int) (S pre)))
    (c : Int) (hc : ¬ (P61 : Int) ∣ (c - T [])) :
    countAcc P61 T G deg n [] c * P61 ≤ degSum deg n 0 * P61 ^ n :=
  soundness P61 T G deg (euclid_int P61 p61_prime) S n hS1 hS2 hS3 n [] c (by simp) hc

/-- The same bound with any ceiling `D` on the sum of the degree bounds. -/
theorem soundness_p61_le (T : List Int → Int) (G : List Int → List Int) (deg : Nat → Nat)
    (S : List Int → List Int) (n : Nat)
    (hS1 : ∀ pre : List Int, pre.length < n → (S pre).length ≤ deg pre.length + 1)
    (hS2 : ∀ pre : List Int, pre.length < n → (P61 : Int) ∣ (eval 0 (S pre) + eval 1 (S pre) - T pre))
    (hS3 : ∀ (pre : List Int) (r : Nat), pre.length < n →
      (P61 : Int) ∣ (T (pre ++ [(r : Int)]) - eval (r : Int) (S pre)))
    (c : Int) (hc : ¬ (P61 : Int) ∣ (c - T [])) (D : Nat) (hD : degSum deg n 0 ≤ D) :
    countAcc P61 T G deg n [] c * P61 ≤ D * P61 ^ n :=
  Nat.le_trans (soundness_p61 T G deg S n hS1 hS2 hS3 c hc) (Nat.mul_le_mul_right _ hD)

/-- The lab's largest proofs: at most 256 clauses of 3 literals, so the degree bounds sum to at most 3 * 256 = 768,
and 768 / (2^61 - 1) is below 2^-51.  With `soundness_p61_le`: a false count survives on fewer than one challenge
vector in 2^51. -/
theorem lab_error_bound : 768 * 2 ^ 51 < P61 := by decide

/-! ## 5. A concrete instance: P(x, y) = x*y + 1, two rounds

True count over 0/1 inputs: 1 + 1 + 1 + 2 = 5.  Honest round polynomials: s₁(X) = X + 2, s₂(Y) = r*Y + 1. -/

def demoT : List Int → Int
  | [] => 5
  | [r] => r + 2
  | [r, t] => r * t + 1
  | _ => 0

def demoS : List Int → List Int
  | [] => [2, 1]
  | [r] => [1, r]
  | _ => []

/-- For this polynomial the hypotheses of `soundness` hold, so the bound is not vacuous:
any prover claiming a count other than 5 is accepted on at most `2 * p` of the `p * p` challenge pairs. -/
theorem demo_sound (p : Nat) (hE : ∀ a b : Int, (p : Int) ∣ a * b → (p : Int) ∣ a ∨ (p : Int) ∣ b)
    (G : List Int → List Int) (c : Int) (hc : ¬ (p : Int) ∣ (c - 5)) :
    countAcc p demoT G (fun _ => 1) 2 [] c * p ≤ 2 * p ^ 2 := by
  have h := soundness p demoT G (fun _ => 1) hE demoS 2
    (by
      intro pre hpre
      match pre, hpre with
      | [], _ => simp [demoS]
      | [_], _ => simp [demoS]
      | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega))
    (by
      intro pre hpre
      match pre, hpre with
      | [], _ => simp [demoS, demoT, eval]
      | [r], _ =>
        have e : eval 0 (demoS [r]) + eval 1 (demoS [r]) - demoT [r] = 0 := by
          simp only [demoS, demoT, eval]; omega
        rw [e]; exact Int.dvd_zero _
      | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega))
    (by
      intro pre r hpre
      match pre, hpre with
      | [], _ =>
        have e : demoT ([] ++ [(r : Int)]) - eval (r : Int) (demoS []) = 0 := by
          simp only [List.nil_append, demoS, demoT, eval]; omega
        rw [e]; exact Int.dvd_zero _
      | [r0], _ =>
        have e : demoT ([r0] ++ [(r : Int)]) - eval (r : Int) (demoS [r0]) = 0 := by
          simp only [List.cons_append, List.nil_append, demoS, demoT, eval]; grind
        rw [e]; exact Int.dvd_zero _
      | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega))
    2 [] c (by simp) (by simpa [demoT] using hc)
  simpa [degSum] using h

/-- The honest prover (claim 5) is accepted on all 49 challenge pairs mod 7. -/
theorem demo_honest : countAcc 7 demoT demoS (fun _ => 1) 2 [] 5 = 49 := by decide

/-- A cheating prover claiming 6: round 1 sends `2 + 2X` (sums to 6); round 2 sends `1 + 2rY`. -/
def demoCheat : List Int → List Int
  | [] => [2, 2]
  | [r] => [1, 2 * r]
  | _ => []

/-- It is accepted on exactly 13 of the 49 challenge pairs mod 7; the theorem allows at most 2 * 7 = 14. -/
theorem demo_cheat : countAcc 7 demoT demoCheat (fun _ => 1) 2 [] 6 = 13 := by decide

end PnpFormal.SumCheck

#print axioms PnpFormal.SumCheck.roots_le_of_exists
#print axioms PnpFormal.SumCheck.soundness
#print axioms PnpFormal.SumCheck.completeness
#print axioms PnpFormal.SumCheck.soundness_p61
#print axioms PnpFormal.SumCheck.soundness_p61_le
#print axioms PnpFormal.SumCheck.lab_error_bound
#print axioms PnpFormal.SumCheck.demo_sound
#print axioms PnpFormal.SumCheck.demo_honest
#print axioms PnpFormal.SumCheck.demo_cheat
