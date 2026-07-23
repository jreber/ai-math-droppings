import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# The weighted two-pole diagonal integral `Jₙ` and its recurrence

`Jₙ = ∫₀¹ xⁿ(1−x)ⁿ / [(1+x)ⁿ⁺¹(2+x)ⁿ⁺¹] dx` — the natural two-pole analogue of the log2
diagonal Legendre integral. By exact partial fractions `Jₙ = Pₙ + α₁(n)·log(4/3)` (a SINGLE
logarithm, because the integrand decays like `1/x²` at `∞` so its simple-residue sum vanishes).

This file proves the crux: the **integral recurrence**
`(n+2)Jₙ₊₂ = 7(2n+3)Jₙ₊₁ − (n+1)Jₙ` (a generalized central-Delannoy recurrence, roots `(2±√3)²`),
the exact analogue of the log2 `(n+2)Iₙ₊₂ = 3(2n+3)Iₙ₊₁ − (n+1)Iₙ`, with the `3` replaced by `7`.

Method (creative telescoping / Gosper, verbatim from `DiagonalIntegralLog2IntegralRec.lean`):
the certificate `Gₙ(x) = (4x²+4x−2)·xⁿ⁺¹(1−x)ⁿ⁺¹ / [(1+x)ⁿ⁺²(2+x)ⁿ⁺²]` satisfies
* **pointwise** `G'ₙ(x) = −(n+1)hₙ + 7(2n+3)hₙ₊₁ − (n+2)hₙ₊₂`, where `hₘ(x)=xᵐ(1−x)ᵐ/[(1+x)ᵐ⁺¹(2+x)ᵐ⁺¹]`;
* **boundary** `Gₙ(0)=Gₙ(1)=0` (the factor `xⁿ⁺¹(1−x)ⁿ⁺¹` vanishes at both endpoints).

FTC then gives `0 = Gₙ(1)−Gₙ(0) = ∫₀¹ G'ₙ = −(n+1)Jₙ + 7(2n+3)Jₙ₊₁ − (n+2)Jₙ₊₂`.

The certificate `W(x)=4x²+4x−2` was derived by solving the order-`n` Gosper equation; the key
algebraic miracle is `−v²+14uv−u² = −4(2x²+2x−1)²` and `u'v−uv' = −2(2x²+2x−1)`
(`u=x(1−x)`, `v=(1+x)(2+x)`), so `W = (−v²+14uv−u²)/(u'v−uv') = 2(2x²+2x−1) = 4x²+4x−2`.
All identities verified by exact arithmetic in `experiments/twolog_*.clj`.
-/

namespace WeightedDiagonalLog43

open MeasureTheory intervalIntegral Set

/-- The two-pole diagonal integrand `hₘ(x) = xᵐ(1−x)ᵐ / [(1+x)ᵐ⁺¹(2+x)ᵐ⁺¹]`. -/
noncomputable def hJ (m : ℕ) (x : ℝ) : ℝ :=
  x ^ m * (1 - x) ^ m / ((1 + x) ^ (m + 1) * (2 + x) ^ (m + 1))

/-- `Jₘ = ∫₀¹ hₘ`. -/
noncomputable def J (m : ℕ) : ℝ := ∫ x in (0:ℝ)..1, hJ m x

theorem hJ_continuousOn (m : ℕ) : ContinuousOn (hJ m) (uIcc 0 1) := by
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply ContinuousOn.div
  · exact ((continuous_id.pow m).mul ((continuous_const.sub continuous_id).pow m)).continuousOn
  · exact (((continuous_const.add continuous_id).pow (m + 1)).mul
      ((continuous_const.add continuous_id).pow (m + 1))).continuousOn
  · intro x hx
    simp only [mem_Icc] at hx
    have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0:ℝ) < 2 + x := by linarith [hx.1]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt h1)) (pow_ne_zero _ (ne_of_gt h2))

theorem hJ_intervalIntegrable (m : ℕ) : IntervalIntegrable (hJ m) volume 0 1 :=
  (hJ_continuousOn m).intervalIntegrable

/-- The Gosper certificate `Gₙ(x) = (4x²+4x−2)·xⁿ⁺¹(1−x)ⁿ⁺¹ / [(1+x)ⁿ⁺²(2+x)ⁿ⁺²]`. -/
noncomputable def Gcert (n : ℕ) (x : ℝ) : ℝ :=
  (4 * x ^ 2 + 4 * x - 2) * x ^ (n + 1) * (1 - x) ^ (n + 1)
    / ((1 + x) ^ (n + 2) * (2 + x) ^ (n + 2))

/-- **Pointwise certificate derivative.**
`G'ₙ(x) = −(n+1)hₙ + 7(2n+3)hₙ₊₁ − (n+2)hₙ₊₂` for `x` with `1+x>0`, `2+x>0`. -/
theorem hasDerivAt_Gcert (n : ℕ) {x : ℝ} (h1 : 0 < 1 + x) (h2 : 0 < 2 + x) :
    HasDerivAt (Gcert n)
      (-((n:ℝ) + 1) * hJ n x + 7 * (2 * (n:ℝ) + 3) * hJ (n + 1) x
        - ((n:ℝ) + 2) * hJ (n + 2) x) x := by
  have hden : ((1 + x) ^ (n + 2) * (2 + x) ^ (n + 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ne_of_gt h1)) (pow_ne_zero _ (ne_of_gt h2))
  -- numerator factors
  have hW : HasDerivAt (fun s : ℝ => 4 * s ^ 2 + 4 * s - 2) (4 * (2 * x ^ 1) + 4 * 1) x := by
    have hp : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (4 * (2 * x ^ 1)) x :=
      (hasDerivAt_pow 2 x).const_mul 4
    have hq : HasDerivAt (fun s : ℝ => 4 * s) (4 * 1) x := (hasDerivAt_id x).const_mul 4
    exact (hp.add hq).sub_const 2
  have hxp : HasDerivAt (fun s : ℝ => s ^ (n + 1)) ((↑(n + 1)) * x ^ n) x := by
    simpa using hasDerivAt_pow (n + 1) x
  have h1x0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
  have h1x : HasDerivAt (fun s : ℝ => (1 - s) ^ (n + 1)) ((↑(n + 1)) * (1 - x) ^ n * (-1)) x := by
    simpa using h1x0.pow (n + 1)
  -- denominator factors
  have h1px0 : HasDerivAt (fun s : ℝ => 1 + s) 1 x := by
    simpa using (hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)
  have h1px : HasDerivAt (fun s : ℝ => (1 + s) ^ (n + 2)) ((↑(n + 2)) * (1 + x) ^ (n + 1) * 1) x := by
    simpa using h1px0.pow (n + 2)
  have h2px0 : HasDerivAt (fun s : ℝ => 2 + s) 1 x := by
    simpa using (hasDerivAt_const x (2:ℝ)).add (hasDerivAt_id x)
  have h2px : HasDerivAt (fun s : ℝ => (2 + s) ^ (n + 2)) ((↑(n + 2)) * (2 + x) ^ (n + 1) * 1) x := by
    simpa using h2px0.pow (n + 2)
  -- assemble N = ((W·x^(n+1))·(1−x)^(n+1)),  D = (1+x)^(n+2)·(2+x)^(n+2)
  have hN := (hW.mul hxp).mul h1x
  have hD := h1px.mul h2px
  have hG := hN.div hD hden
  convert hG using 1
  simp only [hJ, Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem Gcert_zero (n : ℕ) : Gcert n 0 = 0 := by
  simp only [Gcert]
  rw [show (0:ℝ) ^ (n + 1) = 0 from zero_pow (Nat.succ_ne_zero n)]
  ring

theorem Gcert_one (n : ℕ) : Gcert n 1 = 0 := by
  simp only [Gcert]
  rw [show (1:ℝ) - 1 = 0 by ring, zero_pow (Nat.succ_ne_zero n)]
  ring

/-- **The integral recurrence.** `(n+2)Jₙ₊₂ = 7(2n+3)Jₙ₊₁ − (n+1)Jₙ`
(generalized central Delannoy, the log2 recurrence with `3 → 7`). -/
theorem J_recurrence (n : ℕ) :
    ((n:ℝ) + 2) * J (n + 2) = 7 * (2 * (n:ℝ) + 3) * J (n + 1) - ((n:ℝ) + 1) * J n := by
  have hA := (hJ_intervalIntegrable n).const_mul (-((n:ℝ) + 1))
  have hB := (hJ_intervalIntegrable (n + 1)).const_mul (7 * (2 * (n:ℝ) + 3))
  have hC := (hJ_intervalIntegrable (n + 2)).const_mul (((n:ℝ) + 2))
  have hderiv : ∀ y ∈ uIcc (0:ℝ) 1, HasDerivAt (Gcert n)
      (-((n:ℝ) + 1) * hJ n y + 7 * (2 * (n:ℝ) + 3) * hJ (n + 1) y
        - ((n:ℝ) + 2) * hJ (n + 2) y) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
    simp only [mem_Icc] at hy
    exact hasDerivAt_Gcert n (by linarith [hy.1] : (0:ℝ) < 1 + y) (by linarith [hy.1] : (0:ℝ) < 2 + y)
  have hF'int : IntervalIntegrable
      (fun y => -((n:ℝ) + 1) * hJ n y + 7 * (2 * (n:ℝ) + 3) * hJ (n + 1) y
        - ((n:ℝ) + 2) * hJ (n + 2) y) volume 0 1 := (hA.add hB).sub hC
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hF'int
  rw [Gcert_one, Gcert_zero, sub_zero] at hFTC
  rw [integral_sub (hA.add hB) hC, integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  -- hFTC : -(n+1)·Jₙ + 7(2n+3)·Jₙ₊₁ − (n+2)·Jₙ₊₂ = 0   (after folding the J definitions)
  simp only [J]
  linarith [hFTC]

/-- **The kernel bound** `x(1−x) ≤ (7−4√3)·(1+x)(2+x)` on `[0,1]` (cleared form of
`max_{[0,1]} x(1−x)/[(1+x)(2+x)] = 7−4√3 = (2−√3)²`).  The geometric decay rate `ρ = 7−4√3` of
`Jₙ`.  Proof: the difference is the perfect square `(8−4√3)·(x − (√3−1)/2)² ≥ 0`. -/
theorem kernel_bound {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    x * (1 - x) ≤ (7 - 4 * Real.sqrt 3) * ((1 + x) * (2 + x)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith [sq_nonneg (2 * x - Real.sqrt 3 + 1), sq_nonneg (Real.sqrt 3 - 2), h3, h3nn,
    mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - x)]

/-- **Positivity** `0 < Jₙ` — the integrand is positive on `(0,1)`. (Needed for the irrationality
argument: `lcm(1..n)·Jₙ` is a *nonzero* integer combination of `1, log(4/3)`.) -/
theorem J_pos (n : ℕ) : 0 < J n := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on ((hJ_continuousOn n).intervalIntegrable)
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    unfold hJ
    apply div_pos
    · exact mul_pos (pow_pos hx.1 n) (pow_pos (by linarith [hx.2]) n)
    · exact mul_pos (pow_pos (by linarith [hx.1]) (n + 1)) (pow_pos (by linarith [hx.1]) (n + 1))
  · norm_num

/-- **Base case** `J₀ = log(4/3)` — grounds the single-log decomposition `Jₙ = Pₙ + α₁(n)·log(4/3)`
(`P₀ = 0`, `α₁(0) = 1`).  Via FTC with antiderivative `log(1+x) − log(2+x)` of
`1/((1+x)(2+x)) = 1/(1+x) − 1/(2+x)`. -/
theorem J_zero : J 0 = Real.log (4 / 3) := by
  have key : (∫ x in (0:ℝ)..1, hJ 0 x)
      = (fun y : ℝ => Real.log (1 + y) - Real.log (2 + y)) 1
        - (fun y : ℝ => Real.log (1 + y) - Real.log (2 + y)) 0 := by
    refine integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Real.log (1 + y) - Real.log (2 + y))
      (f' := hJ 0) ?_ ?_
    · intro x hx
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      simp only [mem_Icc] at hx
      have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
      have h2 : (0:ℝ) < 2 + x := by linarith [hx.1]
      have had1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)
      have had2 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
        simpa using (hasDerivAt_const x (2:ℝ)).add (hasDerivAt_id x)
      have d1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
        simpa using had1.log h1.ne'
      have d2 : HasDerivAt (fun y : ℝ => Real.log (2 + y)) (1 / (2 + x)) x := by
        simpa using had2.log h2.ne'
      convert d1.sub d2 using 1
      simp only [hJ, pow_zero, pow_one, one_mul, Nat.zero_add]
      field_simp
      ring
    · exact hJ_intervalIntegrable 0
  rw [J, key]
  simp only []
  rw [show (1:ℝ) + 1 = 2 by norm_num, show (2:ℝ) + 1 = 3 by norm_num,
    show (1:ℝ) + 0 = 1 by norm_num, show (2:ℝ) + 0 = 2 by norm_num, Real.log_one]
  rw [show (4:ℝ) / 3 = 2 ^ 2 / 3 by norm_num, Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  push_cast; ring

/-- **Second base case** `J₁ = 7·log(4/3) − 2` (so `α₁(1) = 7`, `P₁ = −2`).  Via FTC with
antiderivative `7log(1+x) + 2(1+x)⁻¹ − 7log(2+x) + 6(2+x)⁻¹` of the partial fraction
`x(1−x)/[(1+x)²(2+x)²] = 7/(1+x) − 2/(1+x)² − 7/(2+x) − 6/(2+x)²`. -/
theorem J_one : J 1 = 7 * Real.log (4 / 3) - 2 := by
  set F : ℝ → ℝ := fun y => 7 * Real.log (1 + y) + 2 * (1 + y)⁻¹
    - 7 * Real.log (2 + y) + 6 * (2 + y)⁻¹ with hF
  have key : (∫ x in (0:ℝ)..1, hJ 1 x) = F 1 - F 0 := by
    refine integral_eq_sub_of_hasDerivAt (f := F) (f' := hJ 1) ?_ ?_
    · intro x hx
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      simp only [mem_Icc] at hx
      have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
      have h2 : (0:ℝ) < 2 + x := by linarith [hx.1]
      have had1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)
      have had2 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
        simpa using (hasDerivAt_const x (2:ℝ)).add (hasDerivAt_id x)
      have dlog1 : HasDerivAt (fun y : ℝ => 7 * Real.log (1 + y)) (7 * (1 / (1 + x))) x :=
        (had1.log h1.ne').const_mul 7
      have dinv1 : HasDerivAt (fun y : ℝ => 2 * (1 + y)⁻¹) (2 * (-1 / (1 + x) ^ 2)) x :=
        (had1.inv h1.ne').const_mul 2
      have dlog2 : HasDerivAt (fun y : ℝ => 7 * Real.log (2 + y)) (7 * (1 / (2 + x))) x :=
        (had2.log h2.ne').const_mul 7
      have dinv2 : HasDerivAt (fun y : ℝ => 6 * (2 + y)⁻¹) (6 * (-1 / (2 + x) ^ 2)) x :=
        (had2.inv h2.ne').const_mul 6
      have hD := ((dlog1.add dinv1).sub dlog2).add dinv2
      rw [hF]
      convert hD using 1
      simp only [hJ, pow_one]
      field_simp
      ring
    · exact hJ_intervalIntegrable 1
  rw [J, key, hF]
  simp only [add_zero]
  rw [show (1:ℝ) + 1 = 2 by norm_num, show (2:ℝ) + 1 = 3 by norm_num, Real.log_one]
  rw [show (4:ℝ) / 3 = 2 ^ 2 / 3 by norm_num, Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  norm_num
  ring

/-- **Geometric upper bound** `Jₙ ≤ ρⁿ·log(4/3)`, `ρ = 7−4√3 ≈ 0.0718`.  Via the pointwise
factorization `hₙ(x) = g(x)ⁿ·h₀(x)` with `g(x) = x(1−x)/[(1+x)(2+x)] ∈ [0,ρ]` (`kernel_bound`),
then `∫₀¹ h₀ = J₀ = log(4/3)`.  Combined with `lcm(1..n)·ρⁿ → 0` (`e·ρ≈0.195<1`) this is the
`hsmall` decay for the unconditional measure of `log(4/3)`. -/
theorem J_le (n : ℕ) : J n ≤ (7 - 4 * Real.sqrt 3) ^ n * Real.log (4 / 3) := by
  set ρ : ℝ := 7 - 4 * Real.sqrt 3 with hρ
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) 1, hJ n x ≤ ρ ^ n * hJ 0 x := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    have h2 : (0:ℝ) < 2 + x := by linarith [hx.1]
    have hden0 : (0:ℝ) < (1 + x) * (2 + x) := mul_pos h1 h2
    have hJ0nn : 0 ≤ hJ 0 x := by
      simp only [hJ, pow_zero, pow_one, one_mul, Nat.zero_add]
      positivity
    have hg0 : 0 ≤ x * (1 - x) / ((1 + x) * (2 + x)) :=
      div_nonneg (mul_nonneg hx.1 (by linarith [hx.2])) (le_of_lt hden0)
    have hgρ : x * (1 - x) / ((1 + x) * (2 + x)) ≤ ρ :=
      (div_le_iff₀ hden0).mpr (kernel_bound hx.1 hx.2)
    have hfac : hJ n x = (x * (1 - x) / ((1 + x) * (2 + x))) ^ n * hJ 0 x := by
      simp only [hJ, pow_zero, pow_one, one_mul, Nat.zero_add, div_pow, mul_pow]
      rw [pow_succ (1 + x) n, pow_succ (2 + x) n]
      field_simp
    rw [hfac]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg0 hgρ n) hJ0nn
  have hint : IntervalIntegrable (fun x => ρ ^ n * hJ 0 x) volume 0 1 :=
    (hJ_intervalIntegrable 0).const_mul _
  calc J n = ∫ x in (0:ℝ)..1, hJ n x := rfl
    _ ≤ ∫ x in (0:ℝ)..1, ρ ^ n * hJ 0 x :=
        intervalIntegral.integral_mono_on (by norm_num) (hJ_intervalIntegrable n) hint hbound
    _ = ρ ^ n * ∫ x in (0:ℝ)..1, hJ 0 x := intervalIntegral.integral_const_mul _ _
    _ = ρ ^ n * J 0 := rfl
    _ = ρ ^ n * Real.log (4 / 3) := by rw [J_zero]

end WeightedDiagonalLog43
