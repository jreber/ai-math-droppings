/-
# Lonely Runner `k = 4`: reducing `BandPair` to a single-multiplier interval-hitting form

`LonelyRunnerFourThreeResidualCaseAComplete.caseA_of_bandPair` reduces the entire remaining
gap in the honest `k = 4` Lonely Runner Conjecture to the elementary residue statement
`BandPair`:

    ∀ D p q, 6 ≤ D → IsCoprime p D → ¬ (D ∣ q) → ∃ m, inBand (p·m) D ∧ inBand (q·m) D.

This file performs the routine `p⁻¹`-substitution that collapses the *two* multipliers
`p, q` to a *single* multiplier `r = q · p⁻¹`. Because `p` is a unit mod `D`, writing
`m = p⁻¹ · k` turns `p·m ≡ k` and `q·m ≡ (q·p⁻¹)·k = r·k` (mod `D`). So `BandPair` follows
from the cleaner one-multiplier statement `ReducedBandPair`:

    ∀ D r, 6 ≤ D → ¬ (D ∣ r) → ∃ k, inBand k D ∧ inBand (r·k) D.

i.e. *for every modulus `D ≥ 6` and every residue `r ≢ 0 (mod D)`, some `k` lands both `k`
and `r·k` in the middle band `[D/4, 3D/4] (mod D)`.* This isolates the last open link in the
whole chain to a single-variable interval-hitting question about the map `k ↦ r·k mod D`.

Everything here is honest: no `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseAComplete

namespace LonelyRunnerBandPairReduction

open LonelyRunnerFourThreeResidualCaseAComplete

/-- `inBand` depends only on the residue of `n` mod `D`: if `D ∣ (n - n')` then the two
`inBand` propositions coincide. -/
lemma inBand_congr {n n' : ℤ} {D : ℕ} (h : (D : ℤ) ∣ (n - n')) :
    inBand n D ↔ inBand n' D := by
  have h' : (D : ℤ) ∣ (n' - n) := by
    have := h.neg_right; rwa [neg_sub] at this
  have hmod : n % (D : ℤ) = n' % (D : ℤ) := Int.modEq_iff_dvd.mpr h'
  unfold inBand
  rw [hmod]

/-- **The single-multiplier form.** For every modulus `D ≥ 6` and every `r` not divisible by
`D`, some `k` puts both `k` and `r·k` in the middle band mod `D`. This is exactly `BandPair`
after collapsing the unit `p` (see `bandPair_of_reduced`). -/
def ReducedBandPair : Prop :=
  ∀ (D : ℕ) (r : ℤ), 6 ≤ D → ¬ ((D : ℤ) ∣ r) →
    ∃ k : ℤ, inBand k D ∧ inBand (r * k) D

/-- **`BandPair` from `ReducedBandPair`.** The `p⁻¹`-substitution: with `p` a unit mod `D`,
`m = p⁻¹·k` slaves `p·m` to `k` and `q·m` to `(q·p⁻¹)·k`, so the two-multiplier band problem
reduces to the one-multiplier form. -/
theorem bandPair_of_reduced (h : ReducedBandPair) : BandPair := by
  intro D p q hD hp hq
  -- Bezout for the unit `p`: `s·p + t·D = 1`.
  obtain ⟨s, t, hst⟩ := hp
  -- `s` is a unit mod `D` as well (`p·s + t·D = 1`).
  have hs : IsCoprime s (D : ℤ) := ⟨p, t, by linarith [hst]⟩
  -- The single multiplier: `r = q·s`.  It is not divisible by `D` (else `D ∣ q` by cancelling
  -- the unit `s`), contradicting `hq`.
  have hr : ¬ ((D : ℤ) ∣ (q * s)) := by
    intro hdvd
    exact hq (hs.symm.dvd_of_dvd_mul_right hdvd)
  obtain ⟨k, hbk, hbrk⟩ := h D (q * s) hD hr
  refine ⟨s * k, ?_, ?_⟩
  · -- `p·(s·k) ≡ k (mod D)` because `p·s - 1 = -t·D`.
    have hdvd : (D : ℤ) ∣ (p * (s * k) - k) :=
      ⟨-(t * k), by linear_combination k * hst⟩
    exact (inBand_congr hdvd).mpr hbk
  · -- `q·(s·k) = (q·s)·k`, exactly the band membership produced above.
    have : q * (s * k) = (q * s) * k := by ring
    rw [this]; exact hbrk

end LonelyRunnerBandPairReduction
