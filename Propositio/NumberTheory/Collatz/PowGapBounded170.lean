import Propositio.NumberTheory.Collatz.DescentDichotomy
import Propositio.NumberTheory.Collatz.PowGapReduce
import Propositio.NumberTheory.Collatz.PowGapSmall

/-!
# `PowGap` for `a ≤ 170` — the finite mid-range for `μ(log₂3) ≲ 22`

`CollatzPowGapSmall.powGap_of_le_100` proves the `PowGap` inequality for `a ≤ 100` (any `k`) by
`native_decide`.  The formalizable `μ(log₂3)` construction (the Zeilberger–Zudilin / Salikhov
perfect system, `conj-2026-06-23-R04`) gives `ν ≈ 20.02`; fed through the engine→`PowGap` glue
(`CollatzPowGapMeasureBridge`, with `measure_max_exp_round` rounding `ν → 21` and the structural
`+1`) the resulting magnitude gap is `LinFormGapLog23Mu 22`, whose slack threshold
`a₀` (where `a²² ≤ 2ᵃ`) is `≈ 163`.  `CollatzPowGapMu.powGap_of_linFormGapMu` then needs the finite
mid-range `100 < a < a₀` discharged — i.e. `PowGap` for `a ≤ 170` (a safe margin above `163`).

This file supplies it, extending the bounded `native_decide` from `a ≤ 100` to `a ≤ 170`
(sub-threshold `k < 2a ≤ 340`).  **Construction-independent**: combined with the slack `a²² ≤ 2ᵃ`
(`a ≥ 170`) and any `LinFormGapLog23Mu μ` (`μ ≤ 22`), it closes the Collatz `PowGap` via
`powGap_of_linFormGapMu` with the explicit threshold `a₀ = 170`.
-/

namespace CollatzPowGapBounded170

open CollatzDescentDichotomy CollatzPowGapReduce

/-- **PowGap for `a ≤ 170`, `k ≤ 340`** via `native_decide`.
Sub-threshold for `a ≤ 170` lives in `k < 2a ≤ 340`. -/
theorem powGap_bounded_170 :
    ∀ a : Fin 171, ∀ k : Fin 341,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-- **PowGap holds for all `a ≤ 170` (any `k`).**  Mirrors `CollatzPowGapSmall.powGap_of_le_100`:
`k ≥ 2a` is elementary (`powGap_of_two_a_le`); `k < 2a ≤ 340` is the bounded `native_decide`. -/
theorem powGap_of_le_170 (a k : Nat) (ha : a ≤ 170) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    exact powGap_bounded_170 ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

end CollatzPowGapBounded170
