import Propositio.Collatz.PowGapBounded560
import Propositio.Collatz.PowGapMu
import Propositio.Collatz.PowGapMeasureBridge
import Mathlib.Tactic

/-!
# Capstone: `LinFormGapLog23Mu 60 ⟹ PowGap`, and `measure(log₂3) ⟹ PowGap` for `μ ≲ 60`

This is the `μ ≤ 60` analogue of `CollatzPowGapCapstone22`, built because the HONEST oSALIKHOV
denominator bound is `Den n ≤ D·30ⁿ` (`OSalikhovDenBound.DenIntN_bound_30`) — the earlier `21ⁿ`/`22ⁿ`
rates are FALSE (`OSalikhovDenStructure`). With `C = 30`, `ρ = 30·(27/1000) = 81/100`,
`Q = 30·1500 = 45000`, the effective measure exponent is `1 + log(45000)/log(100/81) ≈ 51.8 ≤ 60`,
so the `μ ≤ 22` ceiling of `CollatzPowGapCapstone22` no longer applies. Per the corpus note that the
capstone ceiling is a SOFT, mechanically-extendable `native_decide` + poly-induction template, this
file raises it to `60` (threshold `a₀ = 560`, where `a⁶⁰ ≤ 2ᵃ`).

Wires `CollatzPowGapBounded560.powGap_of_le_560` and the slack `a⁶⁰ ≤ 2ᵃ` (`a ≥ 560`) into
`CollatzPowGapMu.powGap_of_linFormGapMu` (`a₀ = 560`), giving `PowGap` from `LinFormGapLog23Mu 60`,
hence (via the engine→gap bridge) from any effective `log₂3` measure with exponent `≤ 60`.
-/

namespace CollatzPowGapCapstone60

open CollatzPowGapMu CollatzPowGapBounded560 CollatzPowGapMeasureBridge

set_option maxRecDepth 8000

/-- One-step ratio `(n+1)⁶⁰ ≤ 2·n⁶⁰` for `n ≥ 560` (`(1+1/560)⁶⁰ ≈ 1.113 ≤ 2`). -/
private theorem step60 (n : Nat) (hn : 560 ≤ n) :
    ((n : ℝ) + 1) ^ 60 ≤ 2 * (n : ℝ) ^ 60 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hexp : (1 + 1 / (n : ℝ)) ^ 60 ≤ 2 := by
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 / 560 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
    have hbase : 1 + 1 / (n : ℝ) ≤ 1 + 1 / 560 := by linarith
    have hmono : (1 + 1 / (n : ℝ)) ^ 60 ≤ (1 + 1 / 560 : ℝ) ^ 60 := by gcongr
    have hnum : ((1 : ℝ) + 1 / 560) ^ 60 ≤ 2 := by norm_num
    linarith
  have hfac : ((n : ℝ) + 1) ^ 60 = (n : ℝ) ^ 60 * (1 + 1 / (n : ℝ)) ^ 60 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac]
  nlinarith [hexp, pow_nonneg (le_of_lt hnpos) 60]

/-- **`a⁶⁰ ≤ 2ᵃ` for every `a ≥ 560`** (the slack for `μ = 60`).  Axiom-clean, by induction from the
base `a = 560` with the one-step ratio `step60`.  Mirrors `CollatzPowGapCapstone22.poly22_le_two_pow`. -/
theorem poly60_le_two_pow (a : Nat) (ha : 560 ≤ a) : (a : ℝ) ^ 60 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 560 with hn | hn
    · obtain rfl : n = 559 := by omega
      -- avoid evaluating 2^560 directly: 560³ ≤ 2²⁸, so 560⁶⁰ = (560³)²⁰ ≤ (2²⁸)²⁰ = 2⁵⁶⁰
      have hnat : (560 : ℕ) ^ 60 ≤ 2 ^ 560 := by
        calc (560 : ℕ) ^ 60 = (560 ^ 3) ^ 20 := by rw [← pow_mul]
          _ ≤ (2 ^ 28) ^ 20 := Nat.pow_le_pow_left (by norm_num) 20
          _ = 2 ^ 560 := by rw [← pow_mul]
      show (((559 + 1 : ℕ) : ℝ)) ^ 60 ≤ (2 : ℝ) ^ (559 + 1)
      rw [show (559 + 1) = 560 from rfl]
      calc (((560 : ℕ) : ℝ)) ^ 60 = ((560 ^ 60 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ 560 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ 560 := by push_cast; ring
    · have hih := ih hn
      have hstep := step60 n hn
      have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hcast : ((n : ℝ) + 1) = ((n + 1 : Nat) : ℝ) := by push_cast; ring
      rw [h2, ← hcast]
      nlinarith [hstep, hih]

/-- **`PowGap` from the magnitude gap `LinFormGapLog23Mu 60`** (explicit threshold `a₀ = 560`).
`k ≥ 2a` and `a ≤ 100` are exponent-independent; the mid-range `100 < a < 560` is
`powGap_of_le_560`; the slack regime `a ≥ 560` uses `poly60_le_two_pow`. -/
theorem powGap_of_gap60 (h : LinFormGapLog23Mu ((59 : ℝ) + 1)) :
    CollatzDescentDichotomy.PowGap := by
  refine powGap_of_linFormGapMu ((59 : ℝ) + 1) 560 (by norm_num) ?_ ?_ h
  · intro a ha560
    rw [show ((59 : ℝ) + 1) = ((60 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact poly60_le_two_pow a ha560
  · intro a k _ha560lt ha560 h3k
    exact powGap_of_le_560 a k (by omega) h3k

/-- **`PowGap` from a denominator-height measure `C/a^M ≤ |log₂3 − k/a|` with `M ≤ 60`** — the
`μ ≤ 60` analogue of `CollatzPowGapCapstone22.powGap_of_logb23_measure_denom`, the entry point for the
oSALIKHOV shared-B two-log construction at the honest rate `C = 30` (effective `M ≈ 52`).  Weakens
`LinFormGapLog23Mu M ⟶ LinFormGapLog23Mu 60` (`a^M ≤ a⁶⁰` for `M ≤ 60`, `a ≥ 1`) and applies
`powGap_of_gap60`. -/
theorem powGap_of_logb23_measure_denom (C : ℝ) (M : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (hM1 : 1 ≤ M) (hM : M ≤ 60)
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ M ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hlin : LinFormGapLog23Mu ((m : ℝ) + 1) := linFormGapMu_of_measure C m hC hCa h
  apply powGap_of_gap60
  intro a k ha h3k h2k
  have hgap := hlin a k ha h3k h2k
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    linarith
  have hle : (m : ℝ) + 1 ≤ (59 : ℝ) + 1 := by
    have h2 : (m : ℝ) ≤ 59 := by exact_mod_cast (by omega : m ≤ 59)
    linarith
  have hpow : (a : ℝ) ^ ((m : ℝ) + 1) ≤ (a : ℝ) ^ ((59 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hle
  calc (3 : ℝ) ^ a ≤ (a : ℝ) ^ ((m : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) := hgap
    _ ≤ (a : ℝ) ^ ((59 : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_right hpow hnn

end CollatzPowGapCapstone60
