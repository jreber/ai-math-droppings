import Propositio.Collatz.PowGapBounded1200
import Propositio.Collatz.PowGapMu
import Propositio.Collatz.PowGapMeasureBridge
import Mathlib.Tactic

/-!
# Capstone: `LinFormGapLog23Mu 112 ⟹ PowGap` — sized for the C-normalized oSALIKHOV measure

The `μ ≤ 112` analogue of `CollatzPowGapCapstone22`/`60`.  It is the size the HONEST oSALIKHOV
measure actually needs once its astronomically small constant `C ≈ 6.6·10⁻¹¹⁶` is normalized away:
`1/a^M ≤ C/a^μ` for `a ≥ 100` holds at `M = μ + 58 ≈ 110`, so the usable exponent is `≈ 110 ≤ 112`
(threshold `a₀ = 1200`, where `a¹¹² ≤ 2ᵃ`).

Wires `CollatzPowGapBounded1200.powGap_of_le_1200` and the slack `a¹¹² ≤ 2ᵃ` (`a ≥ 1200`) into
`CollatzPowGapMu.powGap_of_linFormGapMu` (`a₀ = 1200`).

**⚠ UNDERSIZED / SUPERSEDED — do NOT wire the real engine into this `M = 112` capstone.**
The header's `1/C ≈ 6.6·10⁻¹¹⁶` is stale.  The corrected arithmetic (the `logb23` transform uses
`A' = A/log2 ≈ 56.1`, so `1/C = 2·B·Q²·(2A')ˢ ≈ 10¹²³`) requires the normalization floor `M ≥ 114`
(see `CollatzPowGapNormalize.powGap_of_tiny_measure`: needs `1/C ≤ 100^{M−μ}`, i.e. `M − μ ≥ 61.7`).
So `M = 112` is ~2 short.  Use **`CollatzPowGapCapstone120`** (the correctly-sized one) instead.
This file is retained only as the generic `μ ≤ 112 ⟹ PowGap` lemma.
-/

namespace CollatzPowGapCapstone112

open CollatzPowGapMu CollatzPowGapBounded1200 CollatzPowGapMeasureBridge

set_option maxRecDepth 8000

set_option maxHeartbeats 2000000 in
/-- One-step ratio `(n+1)¹¹² ≤ 2·n¹¹²` for `n ≥ 1200` (`(1+1/1200)¹¹² ≈ 1.098 ≤ 2`). -/
private theorem step112 (n : Nat) (hn : 1200 ≤ n) :
    ((n : ℝ) + 1) ^ 112 ≤ 2 * (n : ℝ) ^ 112 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hexp : (1 + 1 / (n : ℝ)) ^ 112 ≤ 2 := by
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 / 1200 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
    have hbase : 1 + 1 / (n : ℝ) ≤ 1 + 1 / 1200 := by linarith
    have hmono : (1 + 1 / (n : ℝ)) ^ 112 ≤ (1 + 1 / 1200 : ℝ) ^ 112 := by gcongr
    have hnum : ((1 : ℝ) + 1 / 1200) ^ 112 ≤ 2 := by norm_num
    linarith
  have hfac : ((n : ℝ) + 1) ^ 112 = (n : ℝ) ^ 112 * (1 + 1 / (n : ℝ)) ^ 112 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac]
  nlinarith [hexp, pow_nonneg (le_of_lt hnpos) 112]

/-- **`a¹¹² ≤ 2ᵃ` for every `a ≥ 1200`** (the slack for `μ = 112`).  Base case via
`1200⁴ ≤ 2⁴¹` ⇒ `1200¹¹² = (1200⁴)²⁸ ≤ (2⁴¹)²⁸ = 2¹¹⁴⁸ ≤ 2¹²⁰⁰`. -/
theorem poly112_le_two_pow (a : Nat) (ha : 1200 ≤ a) : (a : ℝ) ^ 112 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1200 with hn | hn
    · obtain rfl : n = 1199 := by omega
      have hnat : (1200 : ℕ) ^ 112 ≤ 2 ^ 1200 := by
        calc (1200 : ℕ) ^ 112 = (1200 ^ 4) ^ 28 := by rw [← pow_mul]
          _ ≤ (2 ^ 41) ^ 28 := Nat.pow_le_pow_left (by norm_num) 28
          _ = 2 ^ 1148 := by rw [← pow_mul]
          _ ≤ 2 ^ 1200 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      show (((1199 + 1 : ℕ) : ℝ)) ^ 112 ≤ (2 : ℝ) ^ (1199 + 1)
      rw [show (1199 + 1) = 1200 from rfl]
      calc (((1200 : ℕ) : ℝ)) ^ 112 = ((1200 ^ 112 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ 1200 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ 1200 := by push_cast; ring
    · have hih := ih hn
      have hstep := step112 n hn
      have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hcast : ((n : ℝ) + 1) = ((n + 1 : Nat) : ℝ) := by push_cast; ring
      rw [h2, ← hcast]
      nlinarith [hstep, hih]

/-- **`PowGap` from the magnitude gap `LinFormGapLog23Mu 112`** (explicit threshold `a₀ = 1200`). -/
theorem powGap_of_gap112 (h : LinFormGapLog23Mu ((111 : ℝ) + 1)) :
    CollatzDescentDichotomy.PowGap := by
  refine powGap_of_linFormGapMu ((111 : ℝ) + 1) 1200 (by norm_num) ?_ ?_ h
  · intro a ha1200
    rw [show ((111 : ℝ) + 1) = ((112 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact poly112_le_two_pow a ha1200
  · intro a k _ha1200lt ha1200 h3k
    exact powGap_of_le_1200 a k (by omega) h3k

/-- **`PowGap` from a denominator-height measure `C/a^M ≤ |log₂3 − k/a|` with `M ≤ 112`.** -/
theorem powGap_of_logb23_measure_denom (C : ℝ) (M : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (hM1 : 1 ≤ M) (hM : M ≤ 112)
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ M ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hlin : LinFormGapLog23Mu ((m : ℝ) + 1) := linFormGapMu_of_measure C m hC hCa h
  apply powGap_of_gap112
  intro a k ha h3k h2k
  have hgap := hlin a k ha h3k h2k
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    linarith
  have hle : (m : ℝ) + 1 ≤ (111 : ℝ) + 1 := by
    have h2 : (m : ℝ) ≤ 111 := by exact_mod_cast (by omega : m ≤ 111)
    linarith
  have hpow : (a : ℝ) ^ ((m : ℝ) + 1) ≤ (a : ℝ) ^ ((111 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hle
  calc (3 : ℝ) ^ a ≤ (a : ℝ) ^ ((m : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) := hgap
    _ ≤ (a : ℝ) ^ ((111 : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_right hpow hnn

end CollatzPowGapCapstone112
