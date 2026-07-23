import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# The diagonal Legendre integral for `log 2` — analytic bounds

Towards a formalized effective irrationality measure of `log 2` (the single-log warm-up for the
`log₂3` construction that closes the Collatz `PowGap` wall — see `IrrMeasureCombination` and
`docs/sessions/2026-06-21-evening-8af4c65.md`).

The Alladi–Robinson diagonal integral is `Iₙ = ∫₀¹ xⁿ(1−x)ⁿ/(1+x)ⁿ⁺¹ dx`.  Its integrand is
`g(x)ⁿ/(1+x)` with `g(x) = x(1−x)/(1+x)`, and the calculus maximum of `g` on `[0,1]` is
`3−2√2 = (√2−1)²`, attained at `x = √2−1` (the discriminant of `x²−(1−c)x+c` with `c=3−2√2` is
exactly `0`).  This file proves the pointwise bounds that drive `0 < Iₙ ≤ (3−2√2)ⁿ·log2`.
-/

namespace DiagonalIntegralLog2

open Real

/-- `g(x) = x(1−x)/(1+x)`, the base of the diagonal integrand. -/
noncomputable def g (x : ℝ) : ℝ := x * (1 - x) / (1 + x)

/-- **Nonnegativity** of `g` on `[0,1]`. -/
theorem g_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ g x := by
  unfold g
  apply div_nonneg
  · nlinarith
  · linarith

/-- **The maximum bound.**  `g(x) = x(1−x)/(1+x) ≤ 3 − 2√2` on `[0,1]`.  Equality at `x = √2−1`.
The proof clears `1+x>0` and reduces to the perfect square `(x − (√2−1))² ≥ 0`. -/
theorem g_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : g x ≤ 3 - 2 * Real.sqrt 2 := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  unfold g
  rw [div_le_iff₀ h1x]
  nlinarith [sq_nonneg (x - (Real.sqrt 2 - 1)), Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg 2]

/-- The full diagonal integrand `f n x = xⁿ(1−x)ⁿ/(1+x)ⁿ⁺¹`. -/
noncomputable def f (n : ℕ) (x : ℝ) : ℝ := x ^ n * (1 - x) ^ n / (1 + x) ^ (n + 1)

/-- `f n x = g(x)ⁿ / (1+x)`. -/
theorem f_eq_g_pow (n : ℕ) {x : ℝ} (hx : 0 < 1 + x) : f n x = g x ^ n / (1 + x) := by
  unfold f g
  rw [div_pow, mul_pow, div_div, ← pow_succ]

/-- **Nonnegativity** of the integrand on `[0,1]`. -/
theorem f_nonneg (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ f n x := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  rw [f_eq_g_pow n h1x]
  exact div_nonneg (pow_nonneg (g_nonneg hx0 hx1) n) (le_of_lt h1x)

/-- **Pointwise upper bound** driving the integral estimate:
`f n x ≤ (3−2√2)ⁿ / (1+x)` on `[0,1]`. -/
theorem f_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    f n x ≤ (3 - 2 * Real.sqrt 2) ^ n / (1 + x) := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  rw [f_eq_g_pow n h1x]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (g_nonneg hx0 hx1) (g_le hx0 hx1) n) (le_of_lt h1x)

/-! ## The integral and its bound -/

/-- The Alladi–Robinson diagonal integral `Iₙ = ∫₀¹ xⁿ(1−x)ⁿ/(1+x)ⁿ⁺¹ dx`. -/
noncomputable def I (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, f n x

theorem f_continuousOn (n : ℕ) : ContinuousOn (f n) (Set.uIcc 0 1) := by
  unfold f
  apply ContinuousOn.div
  · exact (((continuous_id.pow n)).mul ((continuous_const.sub continuous_id).pow n)).continuousOn
  · exact ((continuous_const.add continuous_id).pow (n + 1)).continuousOn
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have : (0:ℝ) < 1 + x := by linarith [hx.1]
    positivity

theorem bound_continuousOn (n : ℕ) :
    ContinuousOn (fun x => (3 - 2 * Real.sqrt 2) ^ n / (1 + x)) (Set.uIcc 0 1) := by
  apply ContinuousOn.div continuousOn_const ((continuous_const.add continuous_id).continuousOn)
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  simp only [Set.mem_Icc] at hx
  have : (0:ℝ) < 1 + x := by linarith [hx.1]
  exact ne_of_gt this

/-- **Positivity** `0 < Iₙ`. -/
theorem I_pos (n : ℕ) : 0 < I n := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on ((f_continuousOn n).intervalIntegrable)
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    unfold f
    apply div_pos
    · exact mul_pos (pow_pos hx.1 n) (pow_pos (by linarith [hx.2]) n)
    · exact pow_pos (by linarith [hx.1]) (n + 1)
  · norm_num

/-- **The integral upper bound** `0 < Iₙ ≤ (3−2√2)ⁿ·log 2`.  Via the pointwise bound `f_le` and
`∫₀¹ (1+x)⁻¹ dx = log 2`. -/
theorem I_le (n : ℕ) : I n ≤ (3 - 2 * Real.sqrt 2) ^ n * Real.log 2 := by
  have hmono : I n ≤ ∫ x in (0:ℝ)..1, (3 - 2 * Real.sqrt 2) ^ n / (1 + x) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      ((f_continuousOn n).intervalIntegrable) ((bound_continuousOn n).intervalIntegrable)
    intro x hx
    simp only [Set.mem_Icc] at hx
    exact f_le n hx.1 hx.2
  have heval : (∫ x in (0:ℝ)..1, (3 - 2 * Real.sqrt 2) ^ n / (1 + x))
      = (3 - 2 * Real.sqrt 2) ^ n * Real.log 2 := by
    have hrw : ∀ x : ℝ, (3 - 2 * Real.sqrt 2) ^ n / (1 + x)
        = (3 - 2 * Real.sqrt 2) ^ n * (1 + x)⁻¹ := fun x => by rw [div_eq_mul_inv]
    simp_rw [hrw]
    rw [intervalIntegral.integral_const_mul]
    have hlog : (∫ x in (0:ℝ)..1, (1 + x)⁻¹) = Real.log 2 := by
      have hshift : (∫ x in (0:ℝ)..1, (1 + x)⁻¹) = ∫ x in (0:ℝ)..1, (x + 1)⁻¹ := by
        simp_rw [add_comm]
      rw [hshift, intervalIntegral.integral_comp_add_right (fun x => x⁻¹) 1,
        integral_inv_of_pos (by norm_num) (by norm_num)]
      norm_num
    rw [hlog]
  rw [I] at hmono ⊢
  rw [heval] at hmono
  exact hmono

/-! ## Substituted form (entry point to the integer linear form)

Substituting `t = 1 + x` turns the diagonal integral into `∫₁² (t−1)ⁿ(2−t)ⁿ/tⁿ⁺¹ dt`, whose
integrand is `(integer polynomial of degree 2n in t) / tⁿ⁺¹`.  Term-by-term integration against
`tᵏ` (`∫₁² tᵏ = (2ᵏ⁺¹−1)/(k+1)` for `k≠−1`, `= log 2` for `k=−1`) then exhibits the integer
linear form `dₙ·Iₙ = uₙ + vₙ·log2` with `dₙ = lcm(1..n)` clearing the denominators (the
remaining multi-session crux). -/
theorem I_eq_sub (n : ℕ) :
    I n = ∫ t in (1:ℝ)..2, (t - 1) ^ n * (2 - t) ^ n / t ^ (n + 1) := by
  rw [I]
  have hpt : ∀ x : ℝ, f n x
      = (fun t => (t - 1) ^ n * (2 - t) ^ n / t ^ (n + 1)) (x + 1) := by
    intro x
    simp only
    unfold f
    rw [show x + 1 - 1 = x from by ring, show 2 - (x + 1) = 1 - x from by ring,
      show x + 1 = 1 + x from by ring]
  rw [intervalIntegral.integral_congr (g := fun x => (fun t => (t - 1) ^ n * (2 - t) ^ n
        / t ^ (n + 1)) (x + 1)) (fun x _ => hpt x)]
  rw [intervalIntegral.integral_comp_add_right
      (fun t => (t - 1) ^ n * (2 - t) ^ n / t ^ (n + 1)) 1]
  norm_num

/-- **Term-by-term decomposition.**  Expanding the integer polynomial `(X−1)ⁿ(2−X)ⁿ` and
dividing by `tⁿ⁺¹`, the diagonal integral is a finite ℤ-linear combination of the elementary
integrals `∫₁² t^(k−n−1)`:

  `Iₙ = ∑_{k=0}^{2n} cₖ · ∫₁² t^(k−n−1) dt`,  `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`.

For `k ≠ n` the elementary integral is the rational `(2^(k−n) − 1)/(k−n)` (denominator `|k−n| ≤ n`,
cleared by `lcm(1..n)`); for `k = n` it is `log 2`.  This is the structural heart of the integer
linear form `dₙ·Iₙ = uₙ + vₙ·log2` (`vₙ = cₙ`); the remaining work is evaluating the elementary
integrals and the `lcm`-clearing of the rational part. -/
theorem I_eq_sum (n : ℕ) :
    I n = ∑ k ∈ Finset.range (2 * n + 1),
      (((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff k)
        * ∫ t in (1:ℝ)..2, t ^ ((k : ℤ) - (n + 1)) := by
  have h1 : ((Polynomial.X - 1 : Polynomial ℝ)).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (Polynomial.X : Polynomial ℝ) 1
  have h2 : ((2 - Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (2 : Polynomial ℝ) Polynomial.X
  have hp1 : ((Polynomial.X - 1) ^ n : Polynomial ℝ).natDegree ≤ n := by
    refine Polynomial.natDegree_pow_le.trans ?_
    calc n * ((Polynomial.X - 1 : Polynomial ℝ)).natDegree ≤ n * 1 := Nat.mul_le_mul (le_refl n) h1
      _ = n := mul_one n
  have hp2 : ((2 - Polynomial.X) ^ n : Polynomial ℝ).natDegree ≤ n := by
    refine Polynomial.natDegree_pow_le.trans ?_
    calc n * ((2 - Polynomial.X : Polynomial ℝ)).natDegree ≤ n * 1 := Nat.mul_le_mul (le_refl n) h2
      _ = n := mul_one n
  have hdeg : ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).natDegree
      < 2 * n + 1 := by
    have hm := Polynomial.natDegree_mul_le (p := ((Polynomial.X - 1) ^ n : Polynomial ℝ))
      (q := ((2 - Polynomial.X) ^ n : Polynomial ℝ))
    omega
  have hnum : ∀ t : ℝ, (t - 1) ^ n * (2 - t) ^ n
      = ∑ k ∈ Finset.range (2 * n + 1),
          ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff k * t ^ k := by
    intro t
    have hev : ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).eval t
        = (t - 1) ^ n * (2 - t) ^ n := by
      simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_ofNat, Polynomial.eval_one]
    rw [← hev, Polynomial.eval_eq_sum_range' hdeg]
  rw [I_eq_sub]
  rw [intervalIntegral.integral_congr (g := fun t => ∑ k ∈ Finset.range (2 * n + 1),
      ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff k
        * t ^ ((k : ℤ) - (n + 1))) ?_]
  · rw [intervalIntegral.integral_finset_sum]
    · exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
    · exact fun k _ => (intervalIntegral.intervalIntegrable_zpow (Or.inr (by norm_num))).const_mul _
  · intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by linarith [ht.1]
    simp only []
    rw [hnum t, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_div_assoc]
    congr 1
    rw [← zpow_natCast t k, ← zpow_natCast t (n + 1), ← zpow_sub₀ (ne_of_gt htpos)]
    norm_num

/-- The elementary integral `∫₁² tᵐ = (2^(m+1) − 1)/(m+1)` for `m ≠ −1`. -/
theorem integral_zpow_one_two {m : ℤ} (hm : m ≠ -1) :
    (∫ t in (1:ℝ)..2, t ^ m) = (2 ^ (m + 1) - 1) / (m + 1) := by
  rw [integral_zpow (Or.inr ⟨hm, by norm_num⟩)]
  simp [one_zpow]

/-- The elementary integral `∫₁² t⁻¹ = log 2` (the single source of the logarithm). -/
theorem integral_negone_one_two : (∫ t in (1:ℝ)..2, t ^ (-1 : ℤ)) = Real.log 2 := by
  simp_rw [zpow_neg_one]
  rw [integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

/-- **The log isolated.**  Evaluating the elementary integrals in `I_eq_sum` (`log 2` only from
the `k = n` term, rationals elsewhere):

  `Iₙ = cₙ·log 2 + ∑_{k≠n} cₖ·(2^(k−n) − 1)/(k − n)`,  `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ)`.

The `log 2` coefficient is exactly `cₙ` (the central coefficient).  What remains for the full
integer linear form is the integrality of `cₖ` and the `lcm(1..n)`-clearing of the rational sum. -/
theorem I_eq_rat_add_log (n : ℕ) :
    I n = (((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff n) * Real.log 2
      + ∑ k ∈ (Finset.range (2 * n + 1)).erase n,
          (((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff k)
            * ((2 : ℝ) ^ ((k : ℤ) - n) - 1) / ((k : ℤ) - n) := by
  rw [I_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : n < 2 * n + 1))]
  congr 1
  · -- k = n term: cₙ · ∫₁² t^(n−(n+1)) = cₙ · ∫₁² t⁻¹ = cₙ · log 2
    rw [show ((n : ℤ) - (n + 1)) = -1 by ring, integral_negone_one_two]
  · -- k ≠ n terms: cₖ · ∫₁² t^(k−(n+1)) = cₖ · (2^(k−n)−1)/(k−n)
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkne : k ≠ n := Finset.ne_of_mem_erase hk
    have hkn : (k : ℤ) - (n + 1) ≠ -1 := by
      have : (k : ℤ) ≠ n := by exact_mod_cast hkne
      omega
    rw [integral_zpow_one_two hkn, show (k : ℤ) - (n + 1) + 1 = (k : ℤ) - n by ring]
    push_cast
    ring

/-- **Integrality of the coefficients.**  `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ)` is an integer (the
real polynomial is the `ℤ[X]→ℝ[X]` image of the integer polynomial). -/
theorem coeff_eq_intCast (n k : ℕ) :
    ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ).coeff k
      = (((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℤ).coeff k : ℝ) := by
  have hmap : ((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℝ)
      = (((Polynomial.X - 1) ^ n * (2 - Polynomial.X) ^ n : Polynomial ℤ)).map
          (Int.castRingHom ℝ) := by
    simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_ofNat, Polynomial.map_one]
  rw [hmap, Polynomial.coeff_map]
  simp

end DiagonalIntegralLog2
