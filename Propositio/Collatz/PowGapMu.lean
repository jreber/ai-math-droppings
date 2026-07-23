import Propositio.Collatz.PowGapBaker
import Propositio.NumberTheory.Diophantine.PolyExpSlack
import Mathlib.Tactic

/-!
# `PowGap` from an irrationality measure of **any** explicit exponent `μ`

`CollatzPowGapBaker.powGap_of_linFormGap` derives `PowGap` from `LinFormGapLog23`, which hardcodes the
exponent `14` (matching `μ(log₂3) ≤ 13.3`).  But the cleanest *formalizable* construction for
`μ(log₂3)` (the Zeilberger–Zudilin `oSALIKHOV` system, `conj-2026-06-23-R04`) gives `ν ≈ 20.02 > 14`.

This file removes the dependence on the specific exponent: from a `LinFormGapLog23Mu μ` magnitude gap
with **any** real `μ`, plus the general slack `PolyExpSlack.exists_rpow_le_two_pow` (`a^μ ≤ 2^a`
eventually), `PowGap` follows — provided the finite mid-range `100 < a < a₀(μ)` is checked
(`hmid`), where `a₀(μ)` is the slack threshold.  The `a ≤ 100` and `k ≥ 2a` regimes are
exponent-independent (`powGap_of_le_100`, `powGap_of_two_a_le`), so only that finite mid-range needs a
per-`μ` `decide` (isolated here as a hypothesis, the sole remaining input).

Consequence: **any** explicit finite effective irrationality measure of `log₂3` closes the Collatz
`PowGap` — the magic number `14` was never essential.
-/

namespace CollatzPowGapMu

open CollatzDescentDichotomy

/-- The magnitude gap with an arbitrary real exponent `μ` (the `14` of `LinFormGapLog23` replaced by
`μ`). -/
def LinFormGapLog23Mu (μ : ℝ) : Prop :=
  ∀ a k : Nat, 100 < a → 3 ^ a < 2 ^ k → 2 ^ k ≤ 2 * 3 ^ a →
    (3 : ℝ) ^ a ≤ (a : ℝ) ^ μ * ((2 : ℝ) ^ k - (3 : ℝ) ^ a)

/-- **`PowGap` from an arbitrary-exponent measure.**  Mirrors `powGap_of_linFormGap`, but the
sub-threshold (`k < 2a`) regime splits at the slack threshold `a₀`: for `a ≥ a₀` the general slack
`hslack` (from `PolyExpSlack.exists_rpow_le_two_pow`) upgrades `3^a ≤ a^μ·gap` to `3^a ≤ 2^a·gap`;
the finite window `100 < a < a₀` is supplied by `hmid` (a per-`μ` `decide`, the only residual). -/
theorem powGap_of_linFormGapMu (μ : ℝ) (a0 : ℕ) (ha0 : 100 ≤ a0)
    (hslack : ∀ a : Nat, a0 ≤ a → (a : ℝ) ^ μ ≤ (2 : ℝ) ^ a)
    (hmid : ∀ a k : Nat, 100 < a → a < a0 → 3 ^ a < 2 ^ k →
      2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a)
    (h : LinFormGapLog23Mu μ) : PowGap := by
  intro a k h3k
  by_cases ha : a ≤ 100
  · exact CollatzPowGapSmall.powGap_of_le_100 a k ha h3k
  · push_neg at ha
    by_cases hk : 2 * a ≤ k
    · exact powGap_of_two_a_le a k hk h3k
    · push_neg at hk
      by_cases hbig : a0 ≤ a
      · -- slack regime a ≥ a0 > 100, k < 2a
        have hex : ∃ m, 3 ^ a < 2 ^ m := ⟨k, h3k⟩
        set k₀ := Nat.find hex with hk₀def
        have hk₀ : 3 ^ a < 2 ^ k₀ := Nat.find_spec hex
        have hk₀le : k₀ ≤ k := Nat.find_le h3k
        have hk₀pos : 1 ≤ k₀ := by
          rcases Nat.eq_zero_or_pos k₀ with h0 | h0
          · rw [h0, pow_zero] at hk₀
            have := Nat.one_le_pow a 3 (by norm_num); omega
          · exact h0
        have hmin : 2 ^ (k₀ - 1) ≤ 3 ^ a := by
          have := Nat.find_min hex (show k₀ - 1 < k₀ from by omega); omega
        have h2k0 : 2 ^ k₀ ≤ 2 * 3 ^ a := by
          have e : k₀ = (k₀ - 1) + 1 := by omega
          rw [e, pow_succ]; omega
        have hreal := h a k₀ ha hk₀ h2k0
        have hg : (a : ℝ) ^ μ ≤ (2 : ℝ) ^ a := hslack a hbig
        have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k₀ - (3 : ℝ) ^ a := by
          have : (3 : ℝ) ^ a < (2 : ℝ) ^ k₀ := by exact_mod_cast hk₀
          linarith
        have hfin : (3 : ℝ) ^ a ≤ (2 : ℝ) ^ a * ((2 : ℝ) ^ k₀ - (3 : ℝ) ^ a) :=
          le_trans hreal (by gcongr)
        obtain ⟨D, hD, hD1⟩ : ∃ D, 2 ^ k₀ = 3 ^ a + D ∧ 1 ≤ D :=
          ⟨2 ^ k₀ - 3 ^ a, by omega, by omega⟩
        have hDreal : (2 : ℝ) ^ k₀ - (3 : ℝ) ^ a = (D : ℝ) := by
          have : (2 : ℝ) ^ k₀ = (3 : ℝ) ^ a + (D : ℝ) := by exact_mod_cast hD
          rw [this]; ring
        rw [hDreal] at hfin
        have hnat : 3 ^ a ≤ 2 ^ a * D := by exact_mod_cast hfin
        have hpgk0 : 3 ^ a < 2 ^ a * (2 ^ k₀ - 3 ^ a + 1) := by
          have e : 2 ^ k₀ - 3 ^ a + 1 = D + 1 := by omega
          rw [e]
          have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
          calc 3 ^ a < 2 ^ a * D + 2 ^ a := by omega
            _ = 2 ^ a * (D + 1) := by ring
        exact CollatzPowGapReduce.powGap_term_of_le a k₀ k hk₀le hpgk0
      · -- mid range 100 < a < a0
        push_neg at hbig
        exact hmid a k ha hbig h3k

/-- **`PowGap` from `μ(log₂3) ≤ μ` for any explicit `μ`** (slack threshold packaged via
`PolyExpSlack`).  Only the finite window `100 < a < a₀` (`hmid`) remains as a per-`μ` `decide`. -/
theorem powGap_of_measure_exponent (μ : ℝ) (h : LinFormGapLog23Mu μ)
    (hmidAll : ∀ a0 : ℕ, ∀ a k : Nat, 100 < a → a < a0 → 3 ^ a < 2 ^ k →
      2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a) : PowGap := by
  obtain ⟨a1, ha1⟩ := PolyExpSlack.exists_rpow_le_two_pow μ
  refine powGap_of_linFormGapMu μ (max a1 100) (le_max_right _ _)
    (fun a ha => ha1 a (le_trans (le_max_left _ _) ha)) (hmidAll (max a1 100)) h

end CollatzPowGapMu
