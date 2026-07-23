import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Propositio.NumberTheory.Analytic.MertensLogPrimeLower
import Propositio.NumberTheory.Analytic.MertensFirstSharp

/-!
# Mertens' second theorem (upper bound): `Σ_{p ≤ n} 1/p ≤ log log n + O(1)`

The companion file `MertensReciprocalLower` proves the lower half
`Σ_{p ≤ n} 1/p ≥ log log n − 1`.  This file proves the matching **upper** half,
completing the two-sided Mertens' second theorem with an explicit constant.

## Proof outline (discrete Abel summation)

Write `S(n) = Σ_{p ≤ n} 1/p = Σ_{k < n+1} w k · a k` where `a k = (log k)/k · [k prime]`
(so that `Σ_{k < m+1} a k = mertensSum m`, the engine) and `w k = (log k)⁻¹`.
Summation by parts (`Finset.sum_range_by_parts`) gives

`S(n) = w n · A(n) + Σ_{k < n}(w k − w (k+1)) · A(k)`,   `A(k) = mertensSum k`.

Using the **sharp** Mertens' first theorem `A(k) ≤ log k + C₀` (uniform for `k ≥ 2`,
from `MertensFirstSharp.mertensSum_sub_log_le`) and `w k − w (k+1) ≥ 0`:

* `w n · A(n) ≤ 1 + C₀/log 2`;
* the correction telescopes: `Σ (w k − w (k+1)) = w 2 − w n ≤ 1/log 2`, contributing `C₀/log 2`;
* the main part obeys the **per-step** bound
  `(w k − w (k+1))·log k = 1 − log k/log(k+1) ≤ log log (k+1) − log log k` (one application of
  `log x ≤ x − 1`), telescoping to `log log n − log log 2`.

Hence `S(n) ≤ log log n + C` with `C = 1 + 2·C₀/log 2 − log log 2`.
-/

open Real Finset

namespace MertensReciprocalUpper

open MertensLogPrimeLower (mertensSum)

/-- Prime-indicator increments: `Σ_{k < m+1} a k = mertensSum m`. -/
noncomputable def a (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

/-- Abel weights `w k = (log k)⁻¹`, decreasing for `k ≥ 2`. -/
noncomputable def w (k : ℕ) : ℝ := (Real.log k)⁻¹

/-- `mertensSum` as an indicator sum over `range (k+1)`. -/
lemma A_eq (k : ℕ) : mertensSum k = ∑ i ∈ Finset.range (k + 1), a i := by
  unfold MertensLogPrimeLower.mertensSum a
  rw [Finset.sum_filter]

lemma A_zero : mertensSum 0 = 0 := by
  unfold MertensLogPrimeLower.mertensSum
  rw [show (Finset.range 1).filter Nat.Prime = ∅ from by decide, Finset.sum_empty]

lemma A_one : mertensSum 1 = 0 := by
  unfold MertensLogPrimeLower.mertensSum
  rw [show (Finset.range 2).filter Nat.Prime = ∅ from by decide, Finset.sum_empty]

/-- The summand `(log p)/p` is nonnegative on primes. -/
lemma term_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log p / p :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg p)

lemma A_nonneg (k : ℕ) : 0 ≤ mertensSum k := by
  unfold MertensLogPrimeLower.mertensSum
  apply Finset.sum_nonneg
  intro p hp
  rw [Finset.mem_filter] at hp
  exact term_nonneg hp.2

lemma A_mono {k m : ℕ} (h : k ≤ m) : mertensSum k ≤ mertensSum m := by
  unfold MertensLogPrimeLower.mertensSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.filter_subset_filter
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro p hp _
    rw [Finset.mem_filter] at hp
    exact term_nonneg hp.2

/-- **Uniform** sharp Mertens' first upper bound: `mertensSum k ≤ log k + C₀` for all `k ≥ 2`,
with `C₀ ≥ 0`.  Small `k` are absorbed by monotonicity. -/
lemma A_uniform :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ k : ℕ, 2 ≤ k → mertensSum k ≤ Real.log k + C₀ := by
  obtain ⟨C', N', hN'⟩ := MertensFirstSharp.mertensSum_sub_log_le
  refine ⟨max (max C' (mertensSum N' - Real.log 2)) 0, le_max_right _ _, ?_⟩
  intro k hk
  by_cases hkN : N' ≤ k
  · have hub : mertensSum k - Real.log k ≤ C' := (abs_le.mp (hN' k hkN)).2
    have hle : C' ≤ max (max C' (mertensSum N' - Real.log 2)) 0 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · have hkN' : k < N' := Nat.lt_of_not_le hkN
    have hmono : mertensSum k ≤ mertensSum N' := A_mono (le_of_lt hkN')
    have hlog2 : Real.log 2 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    have hle : (mertensSum N' - Real.log 2) ≤ max (max C' (mertensSum N' - Real.log 2)) 0 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith

/-- Telescoping over `Finset.Ico m n`. -/
lemma tele_add (g : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (g (i + 1) - g i) = g n - g m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
    rw [Finset.sum_Ico_succ_top hp, ih]; ring

/-- `w k * a k = if k prime then 1/k else 0`: the bridge from the `(log p)/p` engine to `1/p`. -/
lemma w_mul_a (i : ℕ) : w i * a i = if i.Prime then (1 : ℝ) / (i : ℝ) else 0 := by
  unfold w a
  by_cases hp : i.Prime
  · rw [if_pos hp, if_pos hp]
    have hlog : Real.log (i : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hlog, one_mul, one_div]
  · rw [if_neg hp, if_neg hp, mul_zero]

/-- **The per-step Abel inequality.**  For `i ≥ 2`,
`(w i − w (i+1))·log i = 1 − log i/log (i+1) ≤ log log (i+1) − log log i`. -/
lemma step {i : ℕ} (hi : 2 ≤ i) :
    (w i - w (i + 1)) * Real.log i
      ≤ Real.log (Real.log (i + 1)) - Real.log (Real.log i) := by
  have hiR : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have e : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hLpos : 0 < Real.log (i : ℝ) := Real.log_pos (by linarith)
  have hMpos : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
  have hkey := Real.log_le_sub_one_of_pos (div_pos hLpos hMpos)
  rw [Real.log_div hLpos.ne' hMpos.ne'] at hkey
  simp only [w]
  rw [e]
  set L := Real.log (i : ℝ) with hL
  set M := Real.log ((i : ℝ) + 1) with hM
  -- hkey : Real.log L - Real.log M ≤ L / M - 1
  -- goal  : (L⁻¹ - M⁻¹) * L ≤ Real.log M - Real.log L
  have hLne : L ≠ 0 := hLpos.ne'
  have hLHS : (L⁻¹ - M⁻¹) * L = 1 - L / M := by
    rw [sub_mul, inv_mul_cancel₀ hLne]; ring
  rw [hLHS]
  linarith [hkey]

/-- **Mertens' second theorem (upper bound).**  There are constants `C`, `N` such that
`Σ_{p ≤ n, p prime} 1/p ≤ log (log n) + C` for all `n ≥ N`. -/
theorem sum_reciprocal_primes_le :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p
        ≤ Real.log (Real.log n) + C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := A_uniform
  refine ⟨1 + 2 * (C₀ * (Real.log 2)⁻¹) - Real.log (Real.log 2), 2, ?_⟩
  intro n hn
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlognpos : 0 < Real.log n := Real.log_pos (by linarith)
  -- Rewrite the target as `Σ w·a`.
  have hSeq : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p
      = ∑ i ∈ Finset.range (n + 1), w i * a i := by
    rw [Finset.sum_filter]
    exact (Finset.sum_congr rfl (fun i _ => (w_mul_a i).symm))
  -- Abel summation by parts.
  have habel := Finset.sum_range_by_parts w a (n + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, ← A_eq] at habel
  -- habel : Σ w·a = w n * mertensSum n - Σ_{i<n} (w (i+1) - w i) * mertensSum i
  -- Flip the correction sum into the nonnegative form.
  have hflip : ∑ i ∈ Finset.range n, (w (i + 1) - w i) * mertensSum i
      = - ∑ i ∈ Finset.range n, (w i - w (i + 1)) * mertensSum i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- Bound on `w n * mertensSum n`.
  have hP1 : w n * mertensSum n ≤ 1 + C₀ * (Real.log 2)⁻¹ := by
    have hMn := hC₀ n hn
    have hwn : w n = (Real.log n)⁻¹ := rfl
    have hwnpos : 0 < w n := by rw [hwn]; exact inv_pos.mpr hlognpos
    have h1 : w n * mertensSum n ≤ w n * (Real.log n + C₀) :=
      mul_le_mul_of_nonneg_left hMn hwnpos.le
    have h2 : w n * (Real.log n + C₀) = 1 + C₀ * (Real.log n)⁻¹ := by
      rw [hwn, mul_add, inv_mul_cancel₀ hlognpos.ne']; ring
    have h3 : C₀ * (Real.log n)⁻¹ ≤ C₀ * (Real.log 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ hlog2pos (Real.log_le_log (by norm_num) hnR)) hC₀0
    linarith [h1, h2, h3]
  -- Bound on the nonnegative correction sum.
  have hSumBound : ∑ i ∈ Finset.range n, (w i - w (i + 1)) * mertensSum i
      ≤ (Real.log (Real.log n) - Real.log (Real.log 2)) + C₀ * (Real.log 2)⁻¹ := by
    -- drop the vanishing `i = 0, 1` terms
    have hdrop : ∑ i ∈ Finset.range n, (w i - w (i + 1)) * mertensSum i
        = ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * mertensSum i := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro i hi
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_range]; exact hi.2
      · intro i hi hni
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Ico] at hni
        have hi2 : i < 2 := by omega
        interval_cases i
        · rw [A_zero, mul_zero]
        · rw [A_one, mul_zero]
    rw [hdrop]
    -- termwise: replace `mertensSum i` by `log i + C₀`
    have hbound1 : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * mertensSum i
        ≤ ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * (Real.log i + C₀) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi2 : 2 ≤ i := hi.1
      have hiR2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
      have hLpos : 0 < Real.log (i : ℝ) := Real.log_pos (by linarith)
      have hle : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by linarith)
        push_cast; linarith
      have hwnn : 0 ≤ w i - w (i + 1) := by
        have : w (i + 1) ≤ w i := by simp only [w]; exact inv_anti₀ hLpos hle
        linarith
      exact mul_le_mul_of_nonneg_left (hC₀ i hi2) hwnn
    refine hbound1.trans ?_
    -- split into main + telescoping correction
    have hsplit : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * (Real.log i + C₀)
        = (∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * Real.log i)
          + C₀ * ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit]
    -- main part
    have hmain : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * Real.log i
        ≤ Real.log (Real.log n) - Real.log (Real.log 2) := by
      have h1 : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) * Real.log i
          ≤ ∑ i ∈ Finset.Ico 2 n,
              (Real.log (Real.log (i + 1)) - Real.log (Real.log i)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        exact step hi.1
      have h2 : ∑ i ∈ Finset.Ico 2 n,
            (Real.log (Real.log (i + 1)) - Real.log (Real.log i))
          = Real.log (Real.log n) - Real.log (Real.log 2) := by
        have ht := tele_add (fun k => Real.log (Real.log k)) hn
        simp only [Nat.cast_add, Nat.cast_one] at ht
        rw [ht]; norm_num
      linarith [h1, h2]
    -- telescoping correction part
    have htele2 : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1)) = w 2 - w n := by
      have hba : ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1))
          = - ∑ i ∈ Finset.Ico 2 n, (w (i + 1) - w i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hba, tele_add w hn]; ring
    have hw2 : w 2 = (Real.log 2)⁻¹ := by simp only [w]; norm_num
    have hwn0 : 0 ≤ w n := by
      simp only [w]; exact inv_nonneg.mpr hlognpos.le
    have hC0bound : C₀ * ∑ i ∈ Finset.Ico 2 n, (w i - w (i + 1))
        ≤ C₀ * (Real.log 2)⁻¹ := by
      rw [htele2, hw2]
      have hle2 : (Real.log 2)⁻¹ - w n ≤ (Real.log 2)⁻¹ := by linarith
      exact mul_le_mul_of_nonneg_left hle2 hC₀0
    linarith [hmain, hC0bound]
  -- combine
  rw [hSeq, habel, hflip]
  linarith [hP1, hSumBound]

end MertensReciprocalUpper
