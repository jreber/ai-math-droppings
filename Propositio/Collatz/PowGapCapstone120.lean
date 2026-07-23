import Propositio.Collatz.PowGapBounded1280
import Propositio.Collatz.PowGapMu
import Propositio.Collatz.PowGapMeasureBridge
import Mathlib.Tactic

/-!
# Capstone: `LinFormGapLog23Mu 120 ⟹ PowGap` — the size the C-normalized oSALIKHOV measure needs

The honest oSALIKHOV measure has exponent `μ ≈ 51.85` but constant `C ≈ 10⁻¹²³` (the `logb23`
transform uses `A' = A/log2 ≈ 56.1`, so `1/C = 2·B·Q²·(2A')^s ≈ 10¹²³·³`).  Normalizing
(`1/a^M ≤ C/a^μ` for `a ≥ 100` needs `100^{M−μ} ≥ 1/C`, i.e. `M − μ ≥ 61.7`, `M ≥ 114`) gives a usable
exponent `≤ 120`.  So this `M = 120` capstone (threshold `a₀ = 1280`) is the correctly-sized one for
the osalikhov→PowGap closure (`CollatzPowGapCapstone112` at `M = 112` is ~2 short).
-/

namespace CollatzPowGapCapstone120

open CollatzPowGapMu CollatzPowGapBounded1280 CollatzPowGapMeasureBridge

set_option maxRecDepth 8000

set_option maxHeartbeats 2000000 in
/-- One-step ratio `(n+1)¹²⁰ ≤ 2·n¹²⁰` for `n ≥ 1280` (`(1+1/1280)¹²⁰ ≈ 1.098 ≤ 2`). -/
private theorem step120 (n : Nat) (hn : 1280 ≤ n) :
    ((n : ℝ) + 1) ^ 120 ≤ 2 * (n : ℝ) ^ 120 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hexp : (1 + 1 / (n : ℝ)) ^ 120 ≤ 2 := by
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 / 1280 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
    have hbase : 1 + 1 / (n : ℝ) ≤ 1 + 1 / 1280 := by linarith
    have hmono : (1 + 1 / (n : ℝ)) ^ 120 ≤ (1 + 1 / 1280 : ℝ) ^ 120 := by gcongr
    have hnum : ((1 : ℝ) + 1 / 1280) ^ 120 ≤ 2 := by norm_num
    linarith
  have hfac : ((n : ℝ) + 1) ^ 120 = (n : ℝ) ^ 120 * (1 + 1 / (n : ℝ)) ^ 120 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac]
  nlinarith [hexp, pow_nonneg (le_of_lt hnpos) 120]

/-- **`a¹²⁰ ≤ 2ᵃ` for every `a ≥ 1280`**.  Base case via `1280³ ≤ 2³¹` ⇒
`1280¹²⁰ = (1280³)⁴⁰ ≤ (2³¹)⁴⁰ = 2¹²⁴⁰ ≤ 2¹²⁸⁰`. -/
theorem poly120_le_two_pow (a : Nat) (ha : 1280 ≤ a) : (a : ℝ) ^ 120 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1280 with hn | hn
    · obtain rfl : n = 1279 := by omega
      have hnat : (1280 : ℕ) ^ 120 ≤ 2 ^ 1280 := by
        calc (1280 : ℕ) ^ 120 = (1280 ^ 3) ^ 40 := by rw [← pow_mul]
          _ ≤ (2 ^ 31) ^ 40 := Nat.pow_le_pow_left (by norm_num) 40
          _ = 2 ^ 1240 := by rw [← pow_mul]
          _ ≤ 2 ^ 1280 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      show (((1279 + 1 : ℕ) : ℝ)) ^ 120 ≤ (2 : ℝ) ^ (1279 + 1)
      rw [show (1279 + 1) = 1280 from rfl]
      calc (((1280 : ℕ) : ℝ)) ^ 120 = ((1280 ^ 120 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ 1280 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ 1280 := by push_cast; ring
    · have hih := ih hn
      have hstep := step120 n hn
      have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hcast : ((n : ℝ) + 1) = ((n + 1 : Nat) : ℝ) := by push_cast; ring
      rw [h2, ← hcast]
      nlinarith [hstep, hih]

/-- **`PowGap` from `LinFormGapLog23Mu 120`** (explicit threshold `a₀ = 1280`). -/
theorem powGap_of_gap120 (h : LinFormGapLog23Mu ((119 : ℝ) + 1)) :
    CollatzDescentDichotomy.PowGap := by
  refine powGap_of_linFormGapMu ((119 : ℝ) + 1) 1280 (by norm_num) ?_ ?_ h
  · intro a ha1280
    rw [show ((119 : ℝ) + 1) = ((120 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact poly120_le_two_pow a ha1280
  · intro a k _ha1280lt ha1280 h3k
    exact powGap_of_le_1280 a k (by omega) h3k

/-- **`PowGap` from a denominator-height measure `C/a^M ≤ |log₂3 − k/a|` with `M ≤ 120`.** -/
theorem powGap_of_logb23_measure_denom (C : ℝ) (M : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (hM1 : 1 ≤ M) (hM : M ≤ 120)
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ M ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hlin : LinFormGapLog23Mu ((m : ℝ) + 1) := linFormGapMu_of_measure C m hC hCa h
  apply powGap_of_gap120
  intro a k ha h3k h2k
  have hgap := hlin a k ha h3k h2k
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    linarith
  have hle : (m : ℝ) + 1 ≤ (119 : ℝ) + 1 := by
    have h2 : (m : ℝ) ≤ 119 := by exact_mod_cast (by omega : m ≤ 119)
    linarith
  have hpow : (a : ℝ) ^ ((m : ℝ) + 1) ≤ (a : ℝ) ^ ((119 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hle
  calc (3 : ℝ) ^ a ≤ (a : ℝ) ^ ((m : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) := hgap
    _ ≤ (a : ℝ) ^ ((119 : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_right hpow hnn

end CollatzPowGapCapstone120
