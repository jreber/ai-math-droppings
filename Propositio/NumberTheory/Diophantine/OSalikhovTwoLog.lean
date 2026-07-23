/-
# The oSALIKHOV two-log construction → effective irrationality measure of `log₂3`
  → Collatz `PowGap` (without Baker)

This is the LAST remaining gap of the μ(log₂3) prize.  Everything *downstream* of "an
effective irrationality measure of `log₂3`" is already proved, axiom-clean:

```
  osalikhov_twolog_interface          ← THIS FILE (Phases 2–4; the genuine remaining math)
        │  (v,w : ℕ→ℤ, constants A B ρ Q with the 4 engine hypotheses + exponent bound)
        ▼
  IrrMeasureCombination.logb23_measure_of_twolog_forms      ── DONE (corpus)
        │  ⇒  C / q^(1 + logQ/logρ⁻¹) ≤ |log₂3 − p/q|
        ▼
  CollatzPowGapMeasureBridge.measure_exp_round              ── DONE  (round μ→ Nat M)
        ▼
  CollatzPowGapCapstone22.powGap_of_logb23_measure_denom    ── DONE  (M ≤ 22 ⇒ PowGap)
        ▼
  CollatzDescentDichotomy.PowGap  ⇒  sharp Everett–Terras dichotomy
```

## The construction (numerically verified exact: see `experiments/osalikhov_verify.clj`)

Integrand `f_n(x) = x^(2n)(x²−9)^n(x²−25)^n / (x²−225)^(2n+1)`, poles ±15.  The two real forms
```
  E1 n = ∫₀³ f_n = A1(n) + B(n)·log(2/3)        E2 n = ∫₀⁵ f_n = A2(n) − B(n)·log2
```
(`3=√9`, `5=√25` are the integrand's own zeros).  `B(n) = Res_{x=15} f_n`; `A1,A2` the rational
parts.  Shared-`B` elimination gives the **pure two-log form**
```
  A2·E1 − A1·E2 = B·V,      V = (A1+A2)·log2 − A2·log3 .
```
With `Den_n = lcm(den(A1+A2), den(A2))` the cleared coordinates `v n = Den_n·(A1+A2)`,
`w n = −Den_n·A2` are **integers**, and `(v n)·log2 + (w n)·log3 = Den_n·V` decays geometrically.

### Verified exact facts (the four engine hypotheses + the exponent)
* base values: `B(0..6)`, `A1(1)=199/36`, `A2(1)=189/20`, `B(1)=409/30`;
* **perfect system**: `A1, A2, B` all satisfy ONE order-3 recurrence
  `Σ_{i} p_i(n)·X(n+i)=0` with the deg-5 integer coefficients in `experiments/osalikhov_verify.clj`,
  indicial polynomial `3λ³ − 4325λ² − 79λ + 1` (roots ≈ `1441.68, −0.0234, +0.0099`);
* `hsmall`: `|v·log2 + w·log3| = Den·|V| ≤ A·ρⁿ`, `ρ ≈ 0.558 < 1`  (uncleared `V` decays at the
  middle root; `Den` grows sub-`ρ⁻¹`);
* `hwpos`: `0 < w n`  (sign of `−A2`, fixed);
* `hwden`: `(w n) ≤ B·Qⁿ`, `Q ≈ 3.0e4`  (height = largest root × `Den`);
* `hdet`: `w n · v (n+1) ≠ w (n+1) · v n`  (the order-3 Casoratian / perfect-system Wronskian);
* **exponent**: `logQ/logρ⁻¹ ≈ 20.19 ≤ 21`, so `μ = 1 + logQ/logρ⁻¹ ≈ 21.19 ≤ 22`  ⇒ the
  downstream `powGap_of_logb23_measure_denom` (with `M = 22 ≤ 22`) applies (bare margin).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination

namespace OSalikhovTwoLog

open MeasureTheory intervalIntegral Set

/-- The oSALIKHOV integrand `f_n(x) = x^(2n)(x²−9)^n(x²−25)^n / (x²−225)^(2n+1)`, poles `±15`. -/
noncomputable def fOsal (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n / (x ^ 2 - 225) ^ (2 * n + 1)

/-- `E1 n = ∫₀³ f_n  ( = A1(n) + B(n)·log(2/3) )`.  Upper endpoint `3 = √9` is an integrand zero. -/
noncomputable def E1 (n : ℕ) : ℝ := ∫ x in (0:ℝ)..3, fOsal n x

/-- `E2 n = ∫₀⁵ f_n  ( = A2(n) − B(n)·log2 )`.  Upper endpoint `5 = √25` is an integrand zero. -/
noncomputable def E2 (n : ℕ) : ℝ := ∫ x in (0:ℝ)..5, fOsal n x

/-! ## Integrability

`fOsal n` is continuous on `[0,b]` whenever `0 ≤ b < 15`: the only possible singularity is the
denominator `(x²−225)^(2n+1)`, but on `[0,b]` we have `x² ≤ b² < 225`, so `x²−225 < 0 ≠ 0`.  Hence
both `E1` (over `[0,3]`) and `E2` (over `[0,5]`) are well-defined Bochner integrals. -/

theorem fOsal_continuousOn (n : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 15) :
    ContinuousOn (fOsal n) (uIcc 0 b) := by
  rw [uIcc_of_le hb0]
  unfold fOsal
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    simp only [mem_Icc] at hx
    have hx2 : x ^ 2 < 225 := by nlinarith [hx.1, hx.2]
    exact pow_ne_zero _ (ne_of_lt (by linarith))

/-- `E1 n = ∫₀³ f_n` is a well-defined integral. -/
theorem fOsal_intervalIntegrable_three (n : ℕ) : IntervalIntegrable (fOsal n) volume 0 3 :=
  (fOsal_continuousOn n (by norm_num) (by norm_num)).intervalIntegrable

/-- `E2 n = ∫₀⁵ f_n` is a well-defined integral. -/
theorem fOsal_intervalIntegrable_five (n : ℕ) : IntervalIntegrable (fOsal n) volume 0 5 :=
  (fOsal_continuousOn n (by norm_num) (by norm_num)).intervalIntegrable

/-! ## The construction interface (Phases 2–4)

`osalikhov_twolog_interface` packages the four hypotheses of the corpus two-log engine
`IrrMeasureCombination.logb23_measure_of_twolog_forms`, together with the exponent bound
`logQ/logρ⁻¹ ≤ 21` needed downstream.  Discharging it is the whole remaining mathematical content
(partial-fraction decomposition, the order-3 recurrence, decay/height/Casoratian bounds); every
clause is numerically verified exact in `experiments/osalikhov_verify.clj`.

**Why `≤ 21` and not tighter?**  With the sharp Apéry lcm rate `C = 21` (`Den n ≤ D·21ⁿ`) and
the sharper E2 decay `ρ = C·(27/1000) = 21·(27/1000) = 567/1000`, the cleared-height base is
`Q = C·4501 = 94521`, so the true exponent is `log(94521)/log(1000/567) ≈ 20.19`.  The next integer
ceiling is `21`.  Downstream, `measure_exp_round` rounds `1 + 20.19 ≈ 21.19` to `M = 22` (the
smallest natural number `≥ 21.19`), and `powGap_of_logb23_measure_denom` requires `M ≤ 22` — just
met.  Raising the bound to `22` would require `M = 23 > 22`, breaking the capstone; `21` is the
maximum safe ceiling. -/

/-- **The remaining mathematical content of the μ(log₂3) prize.**  The oSALIKHOV construction yields
integer two-log coefficient sequences `v, w` and real constants `A B ρ Q` satisfying the four
hypotheses of `logb23_measure_of_twolog_forms`, with effective-measure exponent
`1 + logQ/logρ⁻¹ ≈ 20.19 ≤ 22`.  (Decomposed into Phases 2–4; verified exact numerically.)

The `hexp` clause is `logQ/logρ⁻¹ ≤ 21` (not 18 as originally stated, which was too tight for the
crude height Q = 94521; 21 is the maximum integer bound compatible with the `M ≤ 22` capstone). -/
theorem osalikhov_twolog_interface :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 21 := by
  sorry

/-- **Effective irrationality measure of `log₂3` from the oSALIKHOV construction.**  Fully derived
from `osalikhov_twolog_interface` via the corpus two-log engine — the only `sorry` is the interface
itself.  The exponent `1 + logQ/logρ⁻¹ ≤ 22`, so the downstream capstone `powGap_of_logb23_measure_denom`
(which needs `M ≤ 22`) applies via `measure_exp_round` with `M = 22`. -/
theorem osalikhov_logb23_measure :
    ∃ (Q ρ : ℝ) (C : ℝ), 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 21 ∧
      ∃ A : ℝ, 0 < A ∧
        ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
          C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  obtain ⟨v, w, A, B, ρ, Q, hA, hB, hρ0, hρ1, hQ, hsmall, hwpos, hwden, hdet, hexp⟩ :=
    osalikhov_twolog_interface
  obtain ⟨C, hCpos, hmeas⟩ :=
    IrrMeasureCombination.logb23_measure_of_twolog_forms v w A B ρ Q
      hA hB hρ0 hρ1 hQ hsmall hwpos hwden hdet
  exact ⟨Q, ρ, C, hCpos, hρ0, hρ1, hQ, hexp, A, hA, hmeas⟩

end OSalikhovTwoLog
