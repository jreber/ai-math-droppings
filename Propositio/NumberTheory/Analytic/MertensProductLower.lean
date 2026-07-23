import Propositio.NumberTheory.Analytic.MertensReciprocalUpper
import Propositio.NumberTheory.Analytic.MertensProductUpper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mertens' third theorem (lower bound): `∏_{p ≤ n}(1 - 1/p) ≥ c / log n`

The companion file `MertensProductUpper.lean` proves the upper half
`∏_{p ≤ n}(1 - 1/p) ≤ 1 / log n`.  Here we prove the lower half: there is an absolute
constant `c > 0` with `∏_{p ≤ n}(1 - 1/p) ≥ c / log n` for all large `n`.  Together they
give the two-sided Mertens' third theorem `∏_{p ≤ n}(1 - 1/p) ≍ 1 / log n`.

## Proof outline

Write `P = ∏_{p ≤ n}(1 - 1/p) > 0`.  Then `log P = Σ_{p ≤ n} log(1 - 1/p)`, so it suffices
to upper-bound `-log P = Σ_{p ≤ n} -log(1 - 1/p)`.

1. **Pointwise.**  For a prime `p` (so `x = 1/p ≤ 1/2`),
   `-log(1 - 1/p) ≤ 1/(p-1) = 1/p + 1/(p(p-1))`.  This comes from
   `Real.log_le_sub_one_of_pos` applied to `(1 - 1/p)⁻¹`.
2. **Sum and split.**  `Σ -log(1-1/p) ≤ Σ 1/p + Σ 1/(p(p-1))`.
3. **Mertens 2nd (upper).**  `Σ_{p ≤ n} 1/p ≤ log log n + C` is today's
   `MertensReciprocalUpper.sum_reciprocal_primes_le`.
4. **Correction.**  `Σ_{p ≤ n} 1/(p(p-1)) ≤ Σ_{k=2}^n 1/(k(k-1)) = 1 - 1/n ≤ 1` (telescoping).
5. **Combine and exponentiate.**  `-log P ≤ log log n + C + 1`, so
   `P ≥ exp(-(C+1)) / log n`.  Take `c = exp(-(C+1)) > 0`.
-/

open Real Finset

namespace MertensProductLower

/-- **Pointwise log bound.**  For `p ≥ 2`,
`-log(1 - 1/p) ≤ 1/p + 1/(p(p-1))`.  (Here `1/(p-1) = 1/p + 1/(p(p-1))`.) -/
lemma neg_log_one_sub_inv_le {p : ℕ} (hp : 2 ≤ p) :
    -Real.log (1 - (1 : ℝ) / p) ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  -- `1 - 1/p ≥ 1/2 > 0`.
  have hfacpos : (0 : ℝ) < 1 - (1 : ℝ) / p := by
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  have hne : (1 - (1 : ℝ) / p) ≠ 0 := hfacpos.ne'
  -- `log((1-1/p)⁻¹) ≤ (1-1/p)⁻¹ - 1`.
  have hkey := Real.log_le_sub_one_of_pos (inv_pos.mpr hfacpos)
  rw [Real.log_inv] at hkey
  -- `(1-1/p)⁻¹ - 1 = 1/p + 1/(p(p-1))`.
  have hfac_eq : (1 : ℝ) - 1 / p = ((p : ℝ) - 1) / p := by
    field_simp
  have heq : (1 - (1 : ℝ) / p)⁻¹ - 1 = 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hfac_eq, inv_div]
    field_simp
    ring
  linarith [hkey, heq.le]

/-- **Telescoping correction sum.**  For `m ≥ 1`,
`Σ_{k=2}^{m} 1/(k(k-1)) = 1 - 1/m`. -/
lemma sum_correction_eq (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 2 (m + 1), 1 / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ p + 1), ih]
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) + 1 ≠ 0 := by linarith
    have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
    have hsub : ((p : ℝ) + 1) - 1 = (p : ℝ) := by ring
    rw [hcast, hsub]
    field_simp
    ring

/-- **Mertens' third theorem, lower bound (with explicit threshold).**
There is an absolute constant `c > 0` and a threshold `N` such that for all `n ≥ N`,
`c / log n ≤ ∏_{p ≤ n, p prime}(1 - 1/p)`.  The product index set matches
`MertensProductUpper.prod_one_sub_inv_le` verbatim, so the two compose into the two-sided
Mertens' third theorem. -/
theorem prod_one_sub_inv_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c / Real.log n ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  obtain ⟨C, N₁, hEng⟩ := MertensReciprocalUpper.sum_reciprocal_primes_le
  refine ⟨Real.exp (-(C + 1)), Real.exp_pos _, max N₁ 2, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left N₁ 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N₁ 2).trans hn
  -- The prime index set.
  set S := (Finset.range (n + 1)).filter Nat.Prime with hS
  -- Membership facts.
  have hmem : ∀ p ∈ S, p.Prime ∧ 2 ≤ p ∧ p < n + 1 := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2, hp.2.two_le, hp.1⟩
  -- Each factor `1 - 1/p > 0`.
  have hfacpos : ∀ p ∈ S, (0 : ℝ) < 1 - (1 : ℝ) / p := by
    intro p hp
    obtain ⟨_, hp2, _⟩ := hmem p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  set P : ℝ := ∏ p ∈ S, (1 - (1 : ℝ) / p) with hP
  have hPpos : (0 : ℝ) < P := Finset.prod_pos hfacpos
  -- `log P = Σ log(1-1/p)`.
  have hlogP : Real.log P = ∑ p ∈ S, Real.log (1 - (1 : ℝ) / p) := by
    rw [hP, Real.log_prod]
    intro p hp; exact (hfacpos p hp).ne'
  -- Pointwise: `-(1/p + 1/(p(p-1))) ≤ log(1-1/p)`.
  have hpoint : ∀ p ∈ S,
      -(1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.log (1 - (1 : ℝ) / p) := by
    intro p hp
    obtain ⟨_, hp2, _⟩ := hmem p hp
    have := neg_log_one_sub_inv_le hp2
    linarith
  -- Sum the pointwise bound: `-Σ(1/p + corr) ≤ log P`.
  have hsum_ge :
      ∑ p ∈ S, -(1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.log P := by
    rw [hlogP]; exact Finset.sum_le_sum hpoint
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum_ge
  -- First sum bound (Mertens 2nd upper, today).
  have h1 : ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log n) + C := hEng n hn1
  -- Correction bound `≤ 1` via telescoping.
  have hsub : S ⊆ Finset.Ico 2 (n + 1) := by
    intro p hp
    obtain ⟨_, hp2, hpn⟩ := hmem p hp
    rw [Finset.mem_Ico]; exact ⟨hp2, hpn⟩
  have hnonneg : ∀ k ∈ Finset.Ico 2 (n + 1), k ∉ S →
      0 ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    intro k hk _
    rw [Finset.mem_Ico] at hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    positivity
  have h2 : ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ k ∈ Finset.Ico 2 (n + 1), 1 / ((k : ℝ) * ((k : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      _ = 1 - 1 / (n : ℝ) := sum_correction_eq n (by omega)
      _ ≤ 1 := by
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
          linarith
  -- Combine: `-log P ≤ log log n + C + 1`.
  have hcomb : -Real.log P ≤ Real.log (Real.log n) + C + 1 := by
    have : -((∑ p ∈ S, (1 : ℝ) / p) + ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ Real.log P := hsum_ge
    linarith
  -- `log n > 0`.
  have hlogn_pos : (0 : ℝ) < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- `P = exp(log P) ≥ exp(-(log log n + C + 1))`.
  have hPexp : Real.exp (-(Real.log (Real.log n) + C + 1)) ≤ P := by
    rw [← Real.exp_log hPpos]
    apply Real.exp_le_exp.mpr
    linarith [hcomb]
  -- `exp(-(log log n + C + 1)) = exp(-(C+1)) / log n`.
  have hexp_eq :
      Real.exp (-(Real.log (Real.log n) + C + 1)) = Real.exp (-(C + 1)) / Real.log n := by
    rw [show -(Real.log (Real.log n) + C + 1) = -(C + 1) - Real.log (Real.log n) by ring,
        Real.exp_sub, Real.exp_log hlogn_pos]
  -- Conclude.
  rw [← hexp_eq]
  exact hPexp

end MertensProductLower
