import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2TwoAdic
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic

/-!
# The integer linear form `Dₙ·Iₙ = (Dₙ·cₙ)·log2 + uₙ`

Assembling the diagonal `log 2` construction into an honest **integer linear form**.  From
`DiagonalIntegralLog2.I_eq_rat_add_log`,

  `Iₙ = cₙ·log 2 + ∑_{k≠n} cₖ·(2^(k−n) − 1)/(k − n)`,   `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`.

Multiplying by `Dₙ = lcmUpto n = lcm(1..n)` turns the rational sum into an **integer**:

* each `(k − n)` with `k ∈ [0,2n]`, `k ≠ n`, has `|k − n| ≤ n`, so `|k − n| ∣ Dₙ` (`dvd_lcmUpto`);
* the fractional power `2^(k−n)` for `k < n` is integral after multiplying `cₖ`, because
  `2^(n−k) ∣ cₖ` (`two_pow_dvd_coeff`, the 2-adic miracle).

Hence `Dₙ·Iₙ = (Dₙ·cₙ)·log 2 + uₙ` with `uₙ ∈ ℤ` and the `log 2` coefficient `Dₙ·cₙ ∈ ℤ` — the
exact shape `IrrMeasureCombination.irrationality_measure_le` consumes (`θ = log 2`, `aₙ = Dₙ·cₙ`,
`bₙ = −uₙ`).  The remaining inputs for a full effective measure are the size bound
(`Dₙ·Iₙ → 0`, from `LcmGrowthBound` + `I_le`) and the non-vanishing/determinant condition.
-/

namespace DiagonalIntegralLog2

open Polynomial LcmGrowthBound

/-- Integer coefficient `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`. -/
noncomputable def intCoeff (n k : ℕ) : ℤ := ((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n).coeff k

theorem intCoeff_cast (n k : ℕ) :
    (((X - 1 : ℝ[X]) ^ n * (2 - X) ^ n).coeff k) = (intCoeff n k : ℝ) := by
  rw [intCoeff]; exact coeff_eq_intCast n k

/-- **Per-term integrality.**  For `k ∈ [0,2n]`, `k ≠ n`, the rational term
`cₖ·(2^(k−n) − 1)/(k − n)` (in the exact `ℝ`-coefficient shape of `I_eq_rat_add_log`)
becomes an integer after multiplying by `Dₙ = lcmUpto n`. -/
theorem D_mul_term_int (n k : ℕ) (hk : k < 2 * n + 1) (hkn : k ≠ n) :
    ∃ z : ℤ, (lcmUpto n : ℝ) *
        ((((X - 1 : ℝ[X]) ^ n * (2 - X) ^ n).coeff k) * ((2 : ℝ) ^ ((k : ℤ) - n) - 1)
          / ((k : ℤ) - n)) = (z : ℝ) := by
  rw [intCoeff_cast]
  rcases lt_or_gt_of_ne hkn with hlt | hgt
  · -- k < n : let m = n - k ≥ 1, m ≤ n.  2^(k−n) = (2^m)⁻¹, and 2^m ∣ cₖ.
    set m : ℕ := n - k with hm
    have hm1 : 1 ≤ m := by omega
    have hmn : m ≤ n := by omega
    obtain ⟨D', hD'⟩ := dvd_lcmUpto hm1 hmn
    obtain ⟨c', hc'⟩ := two_pow_dvd_coeff n k
    have hexp : n - k = m := rfl
    rw [hexp] at hc'
    refine ⟨D' * c' * (2 ^ m - 1), ?_⟩
    have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hzp : (2 : ℝ) ^ ((k : ℤ) - n) = ((2 : ℝ) ^ m)⁻¹ := by
      rw [show (k : ℤ) - n = -(m : ℤ) by omega, zpow_neg, zpow_natCast]
    have hcR : (intCoeff n k : ℝ) = (2 : ℝ) ^ m * (c' : ℝ) := by
      rw [intCoeff, hc']; push_cast; ring
    have hDR : (lcmUpto n : ℝ) = (m : ℝ) * (D' : ℝ) := by rw [hD']; push_cast; ring
    have hval : (k : ℝ) - n = -(m : ℝ) := by rw [hm, Nat.cast_sub hlt.le]; ring
    rw [hzp, hcR, hDR]
    push_cast
    rw [hval]
    field_simp
    ring
  · -- k > n : let d = k - n ≥ 1, d ≤ n.  2^(k−n) = 2^d ∈ ℤ.
    set d : ℕ := k - n with hd
    have hd1 : 1 ≤ d := by omega
    have hdn : d ≤ n := by omega
    obtain ⟨D', hD'⟩ := dvd_lcmUpto hd1 hdn
    refine ⟨D' * intCoeff n k * (2 ^ d - 1), ?_⟩
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hzp : (2 : ℝ) ^ ((k : ℤ) - n) = (2 : ℝ) ^ d := by
      rw [show (k : ℤ) - n = (d : ℤ) by omega, zpow_natCast]
    have hDR : (lcmUpto n : ℝ) = (d : ℝ) * (D' : ℝ) := by rw [hD']; push_cast; ring
    have hval : (k : ℝ) - n = (d : ℝ) := by rw [hd, Nat.cast_sub hgt.le]
    rw [hzp, hDR]
    push_cast
    rw [hval]
    field_simp

/-- **The integer linear form.**  `Dₙ·Iₙ = (Dₙ·cₙ)·log 2 + uₙ` with `uₙ ∈ ℤ` and `log 2`
coefficient `Dₙ·cₙ ∈ ℤ`. -/
theorem D_mul_I_int_form (n : ℕ) :
    ∃ u : ℤ, (lcmUpto n : ℝ) * I n
      = ((lcmUpto n : ℤ) * intCoeff n n : ℝ) * Real.log 2 + (u : ℝ) := by
  classical
  set S := (Finset.range (2 * n + 1)).erase n with hS
  have hmem : ∀ k ∈ S, k < 2 * n + 1 ∧ k ≠ n := by
    intro k hk
    rw [hS, Finset.mem_erase, Finset.mem_range] at hk
    exact ⟨hk.2, hk.1⟩
  -- per-term integer witness function
  let zfun : ℕ → ℤ := fun k =>
    if h : k < 2 * n + 1 ∧ k ≠ n then (D_mul_term_int n k h.1 h.2).choose else 0
  have hzspec : ∀ k ∈ S, (lcmUpto n : ℝ) *
      ((((X - 1 : ℝ[X]) ^ n * (2 - X) ^ n).coeff k) * ((2 : ℝ) ^ ((k : ℤ) - n) - 1)
        / ((k : ℤ) - n)) = (zfun k : ℝ) := by
    intro k hk
    have h := hmem k hk
    simp only [zfun, dif_pos h]
    exact (D_mul_term_int n k h.1 h.2).choose_spec
  refine ⟨∑ k ∈ S, zfun k, ?_⟩
  rw [I_eq_rat_add_log, mul_add]
  congr 1
  · -- log 2 coefficient
    rw [intCoeff_cast]; push_cast; ring
  · -- rational sum × D = ∑ integer witnesses
    rw [Finset.mul_sum, Int.cast_sum]
    exact Finset.sum_congr rfl hzspec

end DiagonalIntegralLog2
