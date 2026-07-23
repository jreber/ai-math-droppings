import Propositio.NumberTheory.Diophantine.OSalikhovConsolidated
import Propositio.NumberTheory.Diophantine.OSalikhovDenBoundReduced

/-!
# The μ(log₂3) effective measure, sorry-free, conditional on the single input `hdvd`

`OSalikhovConsolidated.osalikhov_logb23_measure_c30` proves the honest `C = 30` effective
irrationality measure of `log₂3`, but its only axiom-dependency is the `sorry` inside
`OSalikhovDenBound.DenIntN_bound_30`.

Here we replace that `sorry` with the **explicit, elementary** hypothesis

  `hdvd : ∀ m, DenIntN m ∣ 3ᵐ · 30 · lcm(1..2m)`

(the arithmetic `p`-adic divisibility — the prize's last genuine wall — numerically verified to
`n = 96`).  The companion `hlcm` input is already an unconditional theorem
(`CollatzChebyshev30.lcm_two_n_le_target_all`).  The resulting measure theorem
`osalikhov_logb23_measure_of_hdvd` is **sorry-free**: its only non-standard axioms are the two
`native_decide` census axioms (`census_1_to_8499`, `DenIntN_bound_30_fin41`).

This is the honest, precise statement of the prize reduction: *Collatz `PowGap` without Baker*
follows (via the measure → `PowGap` capstones) from the single elementary divisibility `hdvd`.
-/

namespace OSalikhovConsolidated

open OSalikhovIntCoord OSalikhovAssembly OSalikhovTwoLog OSalikhovDenDvd LcmGrowthBound

/-- The honest `C = 30` interface, conditional on `hdvd` (no `sorry`). -/
theorem interface_of_hdvd
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m)) :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 :=
  osalikhov_twolog_interface_of_inputs_c30 DenR 6 (by norm_num)
    DenR_pos (DenR_bound_30_of_hdvd hdvd) vInt wInt vInt_cast_DenR wInt_cast_DenR
    E1_decomp E2_decomp

/-- **Honest effective irrationality measure of `log₂3`, sorry-free, conditional on `hdvd`.**
Identical conclusion to `osalikhov_logb23_measure_c30`, but with the `DenIntN_bound_30` sorry
replaced by the explicit elementary divisibility hypothesis `hdvd`. -/
theorem osalikhov_logb23_measure_of_hdvd
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m)) :
    ∃ (Q ρ C : ℝ), 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 ∧
      ∃ A : ℝ, 0 < A ∧
        ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
          C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  obtain ⟨v, w, A, B, ρ, Q, hA, hB, hρ0, hρ1, hQ, hsmall, hwpos, hwden, hdet, hexp⟩ :=
    interface_of_hdvd hdvd
  obtain ⟨C, hCpos, hmeas⟩ :=
    IrrMeasureCombination.logb23_measure_of_twolog_forms v w A B ρ Q
      hA hB hρ0 hρ1 hQ hsmall hwpos hwden hdet
  exact ⟨Q, ρ, C, hCpos, hρ0, hρ1, hQ, hexp, A, hA, hmeas⟩

#print axioms osalikhov_logb23_measure_of_hdvd

end OSalikhovConsolidated
