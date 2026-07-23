import Propositio.Collatz.PowGapBounded170
import Propositio.Collatz.PowGapMu
import Propositio.Collatz.PowGapMeasureBridge
import Mathlib.Tactic

/-!
# Capstone: `LinFormGapLog23Mu 22 ⟹ PowGap`, and `measure(log₂3) ⟹ PowGap` for `μ ≲ 20`

This wires the finite mid-range `CollatzPowGapBounded170.powGap_of_le_170` and the
polynomial-vs-exponential slack `a²² ≤ 2ᵃ` (`a ≥ 170`) into the explicit-threshold reduction
`CollatzPowGapMu.powGap_of_linFormGapMu` (with `a₀ = 170`), giving `PowGap` from the magnitude gap
`LinFormGapLog23Mu 22`.  Composed with the engine→gap bridge
`CollatzPowGapMeasureBridge.linFormGapMu_of_measure_max` (+ `measure_max_exp_round`), it closes the
Collatz `PowGap` from any 3-D linear-independence measure of `(1, log2, log3)` with exponent `ν ≤ 21`
— exactly the shape `Log23MeasureRhin.log23_measure_of_3d_bound` emits for the Salikhov/
Zeilberger–Zudilin construction (`ν ≈ 20.02`).  The ONLY remaining input is that construction.
-/

namespace CollatzPowGapCapstone22

open CollatzPowGapMu CollatzPowGapBounded170 CollatzPowGapMeasureBridge

set_option maxRecDepth 8000

/-- One-step ratio `(n+1)²² ≤ 2·n²²` for `n ≥ 170` (`(1+1/170)²² ≈ 1.14 ≤ 2`). -/
private theorem step22 (n : Nat) (hn : 170 ≤ n) :
    ((n : ℝ) + 1) ^ 22 ≤ 2 * (n : ℝ) ^ 22 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hexp : (1 + 1 / (n : ℝ)) ^ 22 ≤ 2 := by
    have hle : (1 : ℝ) / (n : ℝ) ≤ 1 / 170 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
    have hbase : 1 + 1 / (n : ℝ) ≤ 1 + 1 / 170 := by linarith
    have hmono : (1 + 1 / (n : ℝ)) ^ 22 ≤ (1 + 1 / 170 : ℝ) ^ 22 := by gcongr
    have hnum : ((1 : ℝ) + 1 / 170) ^ 22 ≤ 2 := by norm_num
    linarith
  have hfac : ((n : ℝ) + 1) ^ 22 = (n : ℝ) ^ 22 * (1 + 1 / (n : ℝ)) ^ 22 := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hfac]
  nlinarith [hexp, pow_nonneg (le_of_lt hnpos) 22]

/-- **`a²² ≤ 2ᵃ` for every `a ≥ 170`** (the slack for `μ = 22`).  Axiom-clean, by induction from the
base `a = 170` with the one-step ratio `step22`.  Mirrors `CollatzPowGapBaker.poly14_le_two_pow`. -/
theorem poly22_le_two_pow (a : Nat) (ha : 170 ≤ a) : (a : ℝ) ^ 22 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 170 with hn | hn
    · obtain rfl : n = 169 := by omega
      norm_num
    · have hih := ih hn
      have hstep := step22 n hn
      have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hcast : ((n : ℝ) + 1) = ((n + 1 : Nat) : ℝ) := by push_cast; ring
      rw [h2, ← hcast]
      nlinarith [hstep, hih]

/-- **`PowGap` from the magnitude gap `LinFormGapLog23Mu 22`** (explicit threshold `a₀ = 170`).
`k ≥ 2a` and `a ≤ 100` are exponent-independent; the mid-range `100 < a < 170` is
`powGap_of_le_170`; the slack regime `a ≥ 170` uses `poly22_le_two_pow`. -/
theorem powGap_of_gap22 (h : LinFormGapLog23Mu ((21 : ℝ) + 1)) :
    CollatzDescentDichotomy.PowGap := by
  refine powGap_of_linFormGapMu ((21 : ℝ) + 1) 170 (by norm_num) ?_ ?_ h
  · intro a ha170
    rw [show ((21 : ℝ) + 1) = ((22 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact poly22_le_two_pow a ha170
  · intro a k _ha170lt ha170 h3k
    exact powGap_of_le_170 a k (by omega) h3k

/-- **`PowGap` from a 3-D measure of `(1, log2, log3)` with exponent `ν ≤ 21`** — the end-to-end
chain for the Salikhov/Zeilberger–Zudilin construction (`ν ≈ 20.02`), modulo only that construction.
Rounds `ν → 21` (`measure_max_exp_round`), folds the height via the max-bridge into
`LinFormGapLog23Mu 22`, then `powGap_of_gap22`.  (The side condition `2²²/C ≤ 100` is met by a
normalized measure constant; a tiny `C` is absorbed by raising the exponent.) -/
theorem powGap_of_log23_measure (C ν : ℝ) (hC : 0 < C) (hν : ν ≤ (21 : ℕ))
    (hCa : (2 : ℝ) ^ (21 + 1) / C ≤ 100)
    (h : ∀ (p q : ℤ), 1 ≤ q →
        C / ((q : ℝ) * (((max |p| q : ℤ) : ℝ)) ^ ν) ≤ |Real.logb 2 3 - (p : ℝ) / (q : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  have hround := measure_max_exp_round C ν 21 hC hν h
  exact powGap_of_gap22 (linFormGapMu_of_measure_max C 21 hC hCa hround)

/-- **`PowGap` from a denominator-height measure `C/a^M ≤ |log₂3 − k/a|` with `M ≤ 22`** — the
one-shot for the 2-D pure-two-log engine's output shape (`IrrMeasureCombination.logb23_measure_of_twolog_forms`,
which the oSALIKHOV shared-B construction feeds via the eliminated two-log form).  Weakens
`LinFormGapLog23Mu M ⟶ LinFormGapLog23Mu 22` (`a^M ≤ a²²` for `M ≤ 22`, `a ≥ 1`) and applies
`powGap_of_gap22`.  Complements `powGap_of_log23_measure` (the 3-D max-height shape). -/
theorem powGap_of_logb23_measure_denom (C : ℝ) (M : ℕ) (hC : 0 < C) (hCa : 2 / C ≤ 100)
    (hM1 : 1 ≤ M) (hM : M ≤ 22)
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ M ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hlin : LinFormGapLog23Mu ((m : ℝ) + 1) := linFormGapMu_of_measure C m hC hCa h
  apply powGap_of_gap22
  intro a k ha h3k h2k
  have hgap := hlin a k ha h3k h2k
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (3 : ℝ) ^ a := by
    have : (3 : ℝ) ^ a < (2 : ℝ) ^ k := by exact_mod_cast h3k
    linarith
  have hle : (m : ℝ) + 1 ≤ (21 : ℝ) + 1 := by
    have : m + 1 ≤ 22 := by omega
    have h2 : (m : ℝ) ≤ 21 := by exact_mod_cast (by omega : m ≤ 21)
    linarith
  have hpow : (a : ℝ) ^ ((m : ℝ) + 1) ≤ (a : ℝ) ^ ((21 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le ha1 hle
  calc (3 : ℝ) ^ a ≤ (a : ℝ) ^ ((m : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) := hgap
    _ ≤ (a : ℝ) ^ ((21 : ℝ) + 1) * ((2 : ℝ) ^ k - (3 : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_right hpow hnn

end CollatzPowGapCapstone22
