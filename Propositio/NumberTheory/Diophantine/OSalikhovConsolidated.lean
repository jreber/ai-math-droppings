import Propositio.NumberTheory.Diophantine.OSalikhovAssembly
import Propositio.NumberTheory.Diophantine.OSalikhovCertificate
import Propositio.NumberTheory.Diophantine.OSalikhovDenBound

/-!
# Honest consolidation: the μ(log₂3) prize reduced to the SINGLE Den-bound sorry

`OSalikhovTwoLog.osalikhov_twolog_interface` (and the measure derived from it) is an isolated
`sorry` carrying the *false* exponent bound `≤ 21` — false because it rests on the FALSE denominator
rate `Den n ≤ D·21ⁿ` (see `OSalikhovDenStructure`; the true rate is `30ⁿ`, giving exponent ≈ 51.8).

This file discharges that interface HONESTLY, at the true rate `C = 30`, by feeding the proved
connectors and the proved decomposition into `osalikhov_twolog_interface_of_inputs_c30`:

* denominator bound  ← `OSalikhovDenBound.DenR_bound_30` (`DenR n ≤ 6·30ⁿ`)
* cast identities     ← `OSalikhovIntCoord.{vInt_cast_DenR, wInt_cast_DenR}` (proved)
* decomposition       ← `OSalikhovTwoLog.{E1_decomp, E2_decomp}` (proved, axiom-clean)

The result `osalikhov_logb23_measure_c30` is the effective irrationality measure of `log₂3` with
the HONEST exponent `1 + log(45000)/log(1000/810) ≈ 51.8 ≤ 60`, and its ONLY remaining
sorry-dependency is `OSalikhovDenBound.DenIntN_bound_30` (the `n ≥ 41` denominator bound — the
genuine prize wall). The standalone interface sorry is thereby eliminated: the prize's two sorries
collapse to one.

**Why this measure does NOT (yet) give the Collatz `PowGap` — and the (mechanical) path that would.**
The downstream `CollatzPowGapCapstone*.powGap_of_logb23_measure_denom` requires the normalized
constant condition `2/C ≤ 100`, but the engine constant here is `C = 1/(2·B·Q²·(2A)^s)` with
`s = log Q / log ρ⁻¹ ≈ 50.84` (the measure exponent), so `(2A)^s ≈ 77.76^50.84 ≈ 10⁹⁶` ⇒
`C ≈ 6.6·10⁻¹¹⁶`.  This tiny `C` is INTRINSIC to a large-exponent construction (here μ ≈ 52).

It is, however, absorbable into a larger exponent — this is NOT a fundamental wall, just substantial
wiring.  The `logb23` specialization uses `A' = A/log2 = 38.88/0.6931 ≈ 56.1`, so the engine constant
is `C = 1/(2·B·Q²·(2A')^s)` with `2A' ≈ 112.2`, `s ≈ 50.85`; numerically `(2A')^s ≈ 10¹⁰⁴`,
`B ≈ 10⁹·⁴`, `Q² ≈ 10⁹·³`, so `1/C ≈ 10¹²³·³` and `C ≈ 10⁻¹²³`.  For `a ≥ 100`,
`1/a^M ≤ C/a^μ ⟺ a^{M−μ} ≥ 1/C`; with `μ = 1+s ≈ 51.85` and `100^{M−μ} ≥ 10¹²³·³`, this needs
`M − μ ≥ 61.7`, i.e. `M ≥ 114`.  So the usable normalized exponent is `M ≈ 114`, and the matching
`PowGap` capstone is `M ≈ 120` for margin (`CollatzPowGapCapstone112` at `M = 112` is ~2 SHORT;
clone it at `a₀ ≈ 1280, M = 120`).  Then `1/a^120 ≤ |θ − p/q|` (constant `1`, `2/1 ≤ 100` ✓) and the
capstone closes it.

The remaining cost is therefore: (i) ✅ DONE — explicit constant exposed
(`IrrMeasureCombination.{irrationality_measure_le_const, logb23_measure_of_twolog_forms_const}`);
(ii) bound the real-power `(2A')^s` to certify `1/C ≤ 10¹²⁴` (via `s ≤ 51` + `rpow` monotonicity +
`norm_num` on `112.2^51 ≤ 10¹⁰⁵`); (iii) the `M ≈ 120` capstone (clone of `CollatzPowGapCapstone112`);
(iv) the four concrete clauses + side-condition + normalization wire.  Mechanical, multi-step.
The prize's two genuine *mathematical* gaps remain the Den bound (`DenIntN_bound_30`) and (only for a
sharper, capstone-free measure) a moderate-`C` construction.
-/

namespace OSalikhovConsolidated

open OSalikhovIntCoord OSalikhovAssembly OSalikhovTwoLog

/-- **The honest `C = 30` interface, PROVED** (modulo only `DenIntN_bound_30`).  Same shape as
`OSalikhovTwoLog.osalikhov_twolog_interface` but with the true exponent bound `≤ 60` (not the false
`≤ 21`), and with the four engine clauses discharged from the proved connectors + decomposition. -/
theorem interface_c30 :
    ∃ (v w : ℕ → ℤ) (A B ρ Q : ℝ),
      0 < A ∧ 0 < B ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      (∀ n, |(v n : ℝ) * Real.log 2 + (w n : ℝ) * Real.log 3| ≤ A * ρ ^ n) ∧
      (∀ n, 0 < w n) ∧
      (∀ n, (w n : ℝ) ≤ B * Q ^ n) ∧
      (∀ n, w n * v (n + 1) ≠ w (n + 1) * v n) ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 :=
  osalikhov_twolog_interface_of_inputs_c30 DenR 6 (by norm_num)
    DenR_pos OSalikhovDenBound.DenR_bound_30 vInt wInt vInt_cast_DenR wInt_cast_DenR
    E1_decomp E2_decomp

/-- **Honest effective irrationality measure of `log₂3`** from the oSALIKHOV construction at the true
denominator rate `C = 30`, reduced to the SINGLE arithmetic input `DenIntN_bound_30`.  Replaces the
vacuous `OSalikhovTwoLog.osalikhov_logb23_measure` (which carried the false `≤ 21` exponent). -/
theorem osalikhov_logb23_measure_c30 :
    ∃ (Q ρ C : ℝ), 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 ∧
      ∃ A : ℝ, 0 < A ∧
        ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
          C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| := by
  obtain ⟨v, w, A, B, ρ, Q, hA, hB, hρ0, hρ1, hQ, hsmall, hwpos, hwden, hdet, hexp⟩ := interface_c30
  obtain ⟨C, hCpos, hmeas⟩ :=
    IrrMeasureCombination.logb23_measure_of_twolog_forms v w A B ρ Q
      hA hB hρ0 hρ1 hQ hsmall hwpos hwden hdet
  exact ⟨Q, ρ, C, hCpos, hρ0, hρ1, hQ, hexp, A, hA, hmeas⟩

end OSalikhovConsolidated
