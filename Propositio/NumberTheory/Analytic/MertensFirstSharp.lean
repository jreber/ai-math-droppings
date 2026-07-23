import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Propositio.NumberTheory.Analytic.MertensLogPrimeLower
import Propositio.NumberTheory.Analytic.MertensLogPrimeUpper
import Propositio.NumberTheory.Analytic.ChebyshevThetaLower

/-!
# Sharp Mertens' first theorem: `Σ_{p ≤ n} (log p)/p = log n + O(1)`

mathlib has no Mertens-type estimate for `Σ_{p ≤ x} (log p)/p`.  The companion files
`MertensLogPrimeLower` / `MertensLogPrimeUpper` prove the **order** form
`(1/4) log n ≤ mertensSum n ≤ log n + log 4`.  This file upgrades the *lower* half to the
**sharp (bounded-error)** form, giving the two-sided bound

`|Σ_{p ≤ n} (log p)/p − log n| ≤ C`  (here `C = 9`, `N = 1`).

## Proof outline

We refine the classical `log(n!)` two-ways argument, controlling *all* errors to `O(n)`:

1. **Refined Legendre.**  `vₚ(n!)·(p−1) ≤ n`, i.e. `vₚ(n!) ≤ n/(p−1)`, and the algebraic
   split `1/(p−1) = 1/p + 1/(p(p−1))` give termwise
   `vₚ(n!)·log p ≤ n·(log p/p) + n·(log p/(p(p−1)))`.  Summing,
   `log(n!) ≤ n·mertensSum n + n·T(n)` where `T(n) = Σ_{p ≤ n} log p/(p(p−1))`
   (`log_factorial_le_refined`).
2. **Convergent tail.**  `T(n) ≤ 2·Σ_{2 ≤ k ≤ n} (log k)/k²`, and the latter sum is bounded
   by an absolute constant via `log k ≤ 2√k` (`ChebyshevThetaLower.log_le_two_sqrt`) plus the
   telescoping bound `(log k)/k² ≤ 4(1/√(k−1) − 1/√k)`.  Hence `T(n) ≤ 8` (`tailT_le`).
3. **Stirling.**  `n·log n − n ≤ log(n!)` (`Stirling.le_log_factorial_stirling`, dropping the
   nonnegative tails).
4. **Combine and divide by `n > 0`:** `mertensSum n ≥ log n − 9` (`mertensSum_ge_log_sub`).
5. The matching upper bound is `MertensLogPrimeUpper.mertensSum_le`, and together they give the
   two-sided sharp estimate `mertensSum_sub_log_le`.
-/

open Real Finset

namespace MertensFirstSharp

/-! ## Step 1: the convergent tail `Σ_{2 ≤ k ≤ n} (log k)/k²` -/

/-- **The crux per-step inequality.**  For `k = n+1 ≥ 2`,
`(log k)/k² ≤ 4·(1/√(k−1) − 1/√k)`, the comparison that makes the tail telescope.
The proof reduces, with `a = √n`, `b = √(n+1)`, to the elementary `a² + ab ≤ 2b²`. -/
lemma crux (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ 2
      ≤ 4 / Real.sqrt (n : ℝ) - 4 / Real.sqrt ((n : ℝ) + 1) := by
  set m : ℝ := (n : ℝ) with hm_def
  have hm1 : (1 : ℝ) ≤ m := by rw [hm_def]; exact_mod_cast hn
  have hm0 : 0 < m := by linarith
  set a : ℝ := Real.sqrt m with ha_def
  set b : ℝ := Real.sqrt (m + 1) with hb_def
  have ha2 : a ^ 2 = m := by rw [ha_def, Real.sq_sqrt hm0.le]
  have hb2 : b ^ 2 = m + 1 := by rw [hb_def, Real.sq_sqrt (by linarith)]
  have ha0 : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.mpr hm0
  have hb0 : 0 < b := by rw [hb_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := by rw [ha_def, hb_def]; exact Real.sqrt_le_sqrt (by linarith)
  have hb2eq : b ^ 2 = a ^ 2 + 1 := by rw [hb2, ha2]
  have hab2 : a * b ≤ b ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hab hb0.le]
  -- The key polynomial inequality `0 ≤ 4b³ − 4ab² − 2a`.
  have hX : 0 ≤ 4 * b ^ 3 - 4 * a * b ^ 2 - 2 * a := by
    have hsum_pos : 0 < a + b := by linarith
    have hRpos : 0 ≤ 2 * a ^ 2 + 4 - 2 * a * b := by nlinarith [hab2, hb2eq]
    have e1 : (a + b) * (4 * b ^ 3 - 4 * a * b ^ 2 - 2 * a) = 2 * a ^ 2 + 4 - 2 * a * b := by
      linear_combination (4 * b ^ 2 + 4) * hb2eq
    have hmul : 0 ≤ (a + b) * (4 * b ^ 3 - 4 * a * b ^ 2 - 2 * a) := by rw [e1]; exact hRpos
    exact (mul_nonneg_iff_of_pos_left hsum_pos).mp hmul
  have hlog : Real.log (m + 1) ≤ 2 * b := by
    rw [hb_def]; exact ChebyshevThetaLower.log_le_two_sqrt (by linarith)
  have hm1sq : (m + 1) ^ 2 = b ^ 4 := by rw [← hb2]; ring
  -- `2b/(m+1)² ≤ 4/a − 4/b`.
  have key : 2 * b / (m + 1) ^ 2 ≤ 4 / a - 4 / b := by
    have hdiff : 4 / a - 4 / b - 2 * b / (m + 1) ^ 2
        = (4 * b ^ 3 - 4 * a * b ^ 2 - 2 * a) / (a * b ^ 3) := by
      rw [hm1sq]; field_simp
    have hnn : 0 ≤ (4 * b ^ 3 - 4 * a * b ^ 2 - 2 * a) / (a * b ^ 3) :=
      div_nonneg hX (mul_nonneg ha0.le (pow_nonneg hb0.le 3))
    linarith [hdiff, hnn]
  have step1 : Real.log (m + 1) / (m + 1) ^ 2 ≤ 2 * b / (m + 1) ^ 2 :=
    (div_le_div_iff_of_pos_right (pow_pos (by linarith : (0 : ℝ) < m + 1) 2)).mpr hlog
  exact le_trans step1 key

/-- The telescoping invariant: `Σ_{2 ≤ k ≤ n} (log k)/k² ≤ 4 − 4/√n` for `n ≥ 1`. -/
lemma tail_invariant : ∀ n : ℕ, 1 ≤ n →
    ∑ k ∈ Finset.Icc 2 n, Real.log k / (k : ℝ) ^ 2 ≤ 4 - 4 / Real.sqrt n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, Nat.cast_one, Real.sqrt_one]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
    have hc := crux n hn
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, hc]

/-- **The tail is bounded by an absolute constant:** `Σ_{2 ≤ k ≤ n} (log k)/k² ≤ 4`. -/
lemma tail_bound (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 n, Real.log k / (k : ℝ) ^ 2 ≤ 4 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]; norm_num
  · have hinv := tail_invariant n h
    have hpos : 0 ≤ 4 / Real.sqrt n := by positivity
    linarith

/-- The Mertens-style prime tail `T(n) = Σ_{p ≤ n} log p/(p(p−1))`. -/
noncomputable def tailT (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))

/-- **The prime tail is bounded by an absolute constant:** `T(n) ≤ 8`. -/
lemma tailT_le (n : ℕ) : tailT n ≤ 8 := by
  unfold tailT
  calc ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 2 * (Real.log p / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hpp := hp.2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hppos : (0 : ℝ) < (p : ℝ) := by linarith
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
        have hc : (0 : ℝ) < (p : ℝ) ^ 2 / 2 := by nlinarith [mul_pos hppos hppos]
        have hc1 : Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ Real.log p / ((p : ℝ) ^ 2 / 2) := by
          apply div_le_div_of_nonneg_left hlogp hc
          nlinarith [mul_nonneg hppos.le (show (0 : ℝ) ≤ (p : ℝ) - 2 by linarith)]
        have hc2 : Real.log p / ((p : ℝ) ^ 2 / 2) = 2 * (Real.log p / (p : ℝ) ^ 2) := by
          field_simp
        rw [hc2] at hc1; exact hc1
    _ ≤ ∑ k ∈ Finset.Icc 2 n, 2 * (Real.log k / (k : ℝ) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_range] at hp
          rw [Finset.mem_Icc]
          exact ⟨hp.2.two_le, by omega⟩
        · intro k hk _
          rw [Finset.mem_Icc] at hk
          have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have hlk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
          positivity
    _ = 2 * ∑ k ∈ Finset.Icc 2 n, Real.log k / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * 4 := by linarith [mul_le_mul_of_nonneg_left (tail_bound n) (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 8 := by norm_num

/-! ## Step 2: the refined Legendre upper bound on `log(n!)` -/

/-- **Refined termwise Legendre bound.**  For a prime `p`,
`vₚ(n!)·log p ≤ n·(log p/p) + n·(log p/(p(p−1)))`. -/
lemma term_refined (n p : ℕ) (hpp : p.Prime) :
    ((Nat.factorial n).factorization p : ℝ) * Real.log p
      ≤ (n : ℝ) * (Real.log p / (p : ℝ))
        + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  -- `vₚ(n!)·(p−1) ≤ n`.
  have hvp_nat : (Nat.factorial n).factorization p ≤ n / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hpp n
  have hp1posN : 0 < p - 1 := by have := hpp.two_le; omega
  have hmul_nat : (Nat.factorial n).factorization p * (p - 1) ≤ n :=
    (Nat.le_div_iff_mul_le hp1posN).mp hvp_nat
  have hvpnn : (0 : ℝ) ≤ ((Nat.factorial n).factorization p : ℝ) := by positivity
  have hcast : ((Nat.factorial n).factorization p : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
    have h : (((Nat.factorial n).factorization p * (p - 1) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
      exact_mod_cast hmul_nat
    rw [Nat.cast_mul, Nat.cast_sub hpp.one_lt.le, Nat.cast_one] at h
    linarith [h]
  -- `vₚ(n!)·log p ≤ n·(log p/(p−1))`.
  have hle1 : ((Nat.factorial n).factorization p : ℝ) * Real.log p
      ≤ (n : ℝ) * (Real.log p / ((p : ℝ) - 1)) := by
    rw [show (n : ℝ) * (Real.log p / ((p : ℝ) - 1)) = (n : ℝ) * Real.log p / ((p : ℝ) - 1) by ring,
        le_div_iff₀ hp1pos]
    nlinarith [mul_le_mul_of_nonneg_right hcast hlogp]
  -- The algebraic split `1/(p−1) = 1/p + 1/(p(p−1))`.
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1pos
  have hid : (n : ℝ) * (Real.log p / ((p : ℝ) - 1))
      = (n : ℝ) * (Real.log p / (p : ℝ))
        + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    field_simp; ring
  linarith [hle1, hid]

/-- **Refined upper bound:** `log(n!) ≤ n·mertensSum n + n·T(n)`. -/
theorem log_factorial_le_refined (n : ℕ) :
    Real.log (Nat.factorial n)
      ≤ (n : ℝ) * MertensLogPrimeLower.mertensSum n + (n : ℝ) * tailT n := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ p ∈ (Nat.factorial n).factorization.support,
          ((Nat.factorial n).factorization p : ℝ) * Real.log p
      ≤ ∑ p ∈ (Nat.factorial n).factorization.support,
          ((n : ℝ) * (Real.log p / (p : ℝ))
            + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
        exact term_refined n p hp.1
    _ ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
          ((n : ℝ) * (Real.log p / (p : ℝ))
            + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (MertensLogPrimeLower.support_subset n)
        intro p hp _
        rw [Finset.mem_filter] at hp
        have hpp : p.Prime := hp.2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hppos : (0 : ℝ) < (p : ℝ) := by linarith
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        apply add_nonneg
        · exact mul_nonneg hnn (div_nonneg hlogp hppos.le)
        · exact mul_nonneg hnn
            (div_nonneg hlogp (mul_nonneg hppos.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)))
    _ = (n : ℝ) * MertensLogPrimeLower.mertensSum n + (n : ℝ) * tailT n := by
        unfold MertensLogPrimeLower.mertensSum tailT
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Step 3: the sharp lower bound, and the two-sided theorem -/

/-- **Sharp Mertens lower bound.**  With `C = 9`, `N = 1`,
`log n − 9 ≤ Σ_{p ≤ n} (log p)/p` for all `n ≥ 1` — strictly sharper than the order-form
`(1/4) log n` bound, since the gap to `log n` is now an absolute constant. -/
theorem mertensSum_ge_log_sub :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log n - C ≤ MertensLogPrimeLower.mertensSum n := by
  refine ⟨9, 1, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hstir := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hstir' : (n : ℝ) * Real.log n - (n : ℝ) ≤ Real.log (Nat.factorial n) := by
    linarith [hstir, hlogn_nn, hlog2pi]
  have hrefined := log_factorial_le_refined n
  have htail := tailT_le n
  have hnt : (n : ℝ) * tailT n ≤ 8 * (n : ℝ) := by nlinarith [htail, hnpos]
  have hcomb : (n : ℝ) * (Real.log n - 9)
      ≤ (n : ℝ) * MertensLogPrimeLower.mertensSum n := by
    have expand : (n : ℝ) * (Real.log n - 9) = (n : ℝ) * Real.log n - 9 * (n : ℝ) := by ring
    rw [expand]
    linarith [hstir', hrefined, hnt]
  exact le_of_mul_le_mul_left hcomb hnpos

/-- **Sharp Mertens' first theorem (two-sided, bounded-error form).**  There is an absolute
constant `C` and threshold `N` with `|Σ_{p ≤ n} (log p)/p − log n| ≤ C` for all `n ≥ N`. -/
theorem mertensSum_sub_log_le :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |MertensLogPrimeLower.mertensSum n - Real.log n| ≤ C := by
  obtain ⟨Cl, Nl, hl⟩ := mertensSum_ge_log_sub
  obtain ⟨Cu, Nu, hu⟩ := MertensLogPrimeUpper.mertensSum_le
  refine ⟨max Cl Cu, max Nl Nu, ?_⟩
  intro n hn
  have hn_l : Nl ≤ n := le_trans (le_max_left _ _) hn
  have hn_u : Nu ≤ n := le_trans (le_max_right _ _) hn
  have h1 := hl n hn_l
  have h2 := hu n hn_u
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hl' : -Cl ≤ MertensLogPrimeLower.mertensSum n - Real.log n := by linarith
    have : -(max Cl Cu) ≤ -Cl := neg_le_neg (le_max_left _ _)
    linarith
  · have hu' : MertensLogPrimeLower.mertensSum n - Real.log n ≤ Cu := by linarith
    linarith [le_max_right Cl Cu]

end MertensFirstSharp
