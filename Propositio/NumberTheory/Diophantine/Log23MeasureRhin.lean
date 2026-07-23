import Propositio.NumberTheory.Diophantine.LinIndepMeasure3DMain
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination
import Mathlib.Tactic

/-!
# Toward `μ(log₂3)` — the Rhin construction scaffold (the Collatz `PowGap` prize)

This file scaffolds the remaining prize of the twolog program: an **effective irrationality
measure of `log₂3`**, which closes the Collatz `PowGap` / sub-threshold Baker wall *without* Baker's
theorem (see `CollatzPowGapBaker.powGap_of_irrMeasure`).

## Status of the program (2026-06-23)

* `μ(log 2)` — DONE, unconditional, axiom-clean (`DiagonalIntegralLog2.log2_measure_unconditional`).
* `μ(log 4/3)` — DONE, unconditional, axiom-clean (`WeightedDiagonalLog43.log43_measure_unconditional`).
* `μ(log₂3)` — OPEN. The 3-D linear-independence engine (`LinIndepMeasure3D`) is built; the missing
  piece is a construction whose Nesterenko **budget converges**.

## Why naive constructions fail, and what Rhin's fixes (the recipe)

Single *diagonal* integrals do NOT close `μ(log₂3)`:
* the **symmetric** weighted diagonal collapses to a single log (`log 4/3`) by residue-sum-zero;
* an **asymmetric** single diagonal `∫₀¹ xⁿ(1−x)ⁿ/((1+x)ⁿ⁺¹(2+x)ⁿ)` is genuinely 3-D (residue sum
  `±1`) and lcm-clearing survives, but its Nesterenko **budget diverges**: the constant-column `2×2`
  cofactors grow like `Q^{1.5n}` while values decay like `ρⁿ`, with `Q²ρ ≈ 184 ≫ 1` (verified `n≤6`).

Rhin's construction (Rhin 1987; Zudilin, *An essay…*, arXiv:math/0404523; Zeilberger–Zudilin,
arXiv:1912.10381) fixes this with TWO ingredients:

1. **A single contour integral** `Iₖ = ∫_{Γ_{1,a}} (z−1)^{n₀}(z−a₁)^{n₁}⋯(z−a_k)^{n_k} / z^{m+1} dz`
   whose **log-coefficient is independent of the evaluation point `a`**.  Substituting `a = a₁` then
   `a = a₂` yields *simultaneous* approximations to `log a₁, log a₂` from **one holonomic family** —
   so the consecutive-form `2×2` minors collapse to a single small **Casoratian** (the perfect-system
   property), exactly what makes the budget converge.
2. **A transfinite-diameter-optimized numerator** `Hₙ(z)` (Zudilin eq. (23)) replacing the plain
   `(z−1)ⁿ(z−aᵢ)ⁿ`; the optimized fractional exponents push the integrand max down so that
   effectively `Q²ρ < 1`.  Without it one gets `μ ≤ 11.10`; with it `μ ≤ 8.616`.

The discrete shadow is an **order-3 Almkvist–Zeilberger recurrence** (indicial polynomial published;
full coefficients in `oSALIKHOV2.txt`), the natural successor to `aRes_recurrence`.

## Formalization roadmap (conjecture card `conj-2026-06-23-R04`)

1. Define the integer forms `(aₙ, bₙ, cₙ)` (coords of `aₙ + bₙ log2 + cₙ log3`) via the order-3
   recurrence (concrete, WZ-certifiable like `JαZ_rec`).
2. Prove the recurrence by its AZ/WZ certificate.
3. Bound the rates: heights `≤ B·Qⁿ`, value `|aₙ + bₙ log2 + cₙ log3| ≤ A·ρⁿ`.
4. Discharge the 3-D `budget` via the perfect-system Casoratian smallness (the `select` hypothesis of
   `LinIndepMeasure3D.linindep_measure_3d`).
5. Feed `linindep_measure_3d` and apply **`log23_measure_of_3d_bound`** (proved below) to land the
   `|log₂3 − p/q|` measure.

This file proves step 5 — the **construction-independent top connector** — axiom-clean now, so the
remaining work is exactly the construction (steps 1–4).
-/

namespace Log23MeasureRhin

open Real

/-- **Top connector (construction-independent): a 3-D linear-independence measure of `(1, log2, log3)`
gives an effective irrationality measure of `log₂3`.**

Given the conclusion of `LinIndepMeasure3D.linindep_measure_3d` specialized to `u = log 2`,
`v = log 3` with exponent `μ` — i.e. a `C > 0` with
`C / (max(|q|,|s|,|t|))^μ ≤ |q + s·log2 + t·log3|` for every nonzero integer triple — we obtain a
`C' > 0` with
`C' / (q · max(|p|,q)^μ) ≤ |log₂3 − p/q|` for all `p` and `q ≥ 1`.

Proof: instantiate the hypothesis at the triple `(0, −p, q)` (nonzero since `q ≥ 1`), giving
`C / (max(|p|,q))^μ ≤ |q·log3 − p·log2|`; then `|log₂3 − p/q| = |q·log3 − p·log2| / (q·log2)`, so
divide through by `q·log2` and take `C' = C / log 2`.  No case split is needed because the height is
kept as `max(|p|,q)` (which is `≤ 2q` for the approximations that matter, recovering the usual
`q^{μ+1}` form). -/
theorem log23_measure_of_3d_bound (μ : ℝ)
    (hLI : ∃ C > 0, ∀ (q s t : ℤ), ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
        C / (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ μ
          ≤ |(q : ℝ) + s * Real.log 2 + t * Real.log 3|) :
    ∃ C' > 0, ∀ (p q : ℤ), 1 ≤ q →
        C' / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ μ) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  obtain ⟨C, hCpos, hC⟩ := hLI
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, div_pos hCpos hlog2, ?_⟩
  intro p q hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < q)
  have hqn : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- instantiate the 3-D bound at the test triple (0, -p, q)
  have hne : ¬ ((0 : ℤ) = 0 ∧ -p = 0 ∧ q = 0) := by rintro ⟨_, _, hq0⟩; omega
  have key := hC 0 (-p) q hne
  -- the height simplifies to max(|p|, q) (ℤ-level), the form value to q·log3 − p·log2
  have hHeq : (max (max |(0:ℤ)| |(-p)|) |q| : ℤ) = max |p| q := by
    rw [abs_zero, abs_neg, max_eq_right (abs_nonneg p), abs_of_nonneg (by omega : (0:ℤ) ≤ q)]
  have hXarg : ((0:ℤ) : ℝ) + ((-p : ℤ) : ℝ) * Real.log 2 + ((q : ℤ) : ℝ) * Real.log 3
      = (q : ℝ) * Real.log 3 - (p : ℝ) * Real.log 2 := by push_cast; ring
  rw [hHeq, hXarg] at key
  set H : ℝ := ((max |p| q : ℤ) : ℝ) with hHdef
  -- key : C / H ^ μ ≤ |q·log3 − p·log2|
  have hHpos : 0 < H ^ μ := by
    apply Real.rpow_pos_of_pos
    have h1 : (1 : ℤ) ≤ max |p| q := le_trans hq (le_max_right _ _)
    rw [hHdef]; exact_mod_cast lt_of_lt_of_le zero_lt_one h1
  -- relate |log₂3 − p/q| to the linear form
  have hlogb : |Real.logb 2 3 - (p : ℝ) / q|
      = |(q : ℝ) * Real.log 3 - (p : ℝ) * Real.log 2| / ((q : ℝ) * Real.log 2) := by
    have heq : Real.logb 2 3 - (p : ℝ) / q
        = ((q : ℝ) * Real.log 3 - (p : ℝ) * Real.log 2) / ((q : ℝ) * Real.log 2) := by
      rw [Real.logb]; field_simp
    rw [heq, abs_div, abs_of_pos (mul_pos hqpos hlog2)]
  rw [hlogb]
  have hd : (0 : ℝ) < (q : ℝ) * Real.log 2 := mul_pos hqpos hlog2
  have hrw : C / Real.log 2 / ((q : ℝ) * H ^ μ) = (C / H ^ μ) / ((q : ℝ) * Real.log 2) := by
    have hHμne : H ^ μ ≠ 0 := ne_of_gt hHpos
    field_simp
  rw [hrw]
  exact div_le_div_of_nonneg_right key (le_of_lt hd)

end Log23MeasureRhin
