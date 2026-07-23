import Propositio.Collatz.DescentDichotomy
import Propositio.Collatz.PowGapReduce
import Propositio.Collatz.DensityCount

/-!
# `PowGap` for small a — native_decide verification

`CollatzDescentDichotomy.PowGap` (`∀ a k, 3^a < 2^k → 2^a·(2^k − 3^a + 1) > 3^a`) reduces,
via `CollatzPowGapReduce.powGap_term_of_le`, to checking each `a` at the single minimal `k`:
  k_min(a) = ⌈a log₂3⌉ ∈ {⌈1.585a⌉,...,2a−1}  (sub-threshold, always < 2a since log₂3 < 2).

`CollatzDescentDichotomy.powGap_of_two_a_le` handles `k ≥ 2a`.  This file proves the
**sub-threshold case for a ≤ 40** via `native_decide`, covering k_min(a) ≤ k < 2a ≤ 80.

Open gap: **a > 40** sub-threshold requires a Baker-type lower bound on |3^a − 2^k|.
Specifically: the gap d = 2^{k_min(a)} − 3^a must satisfy d ≥ ⌊(3/2)^a⌋ for all a,
which follows from Baker's theorem but has no elementary proof known.

Empirically verified (density_analysis4.clj): 0 PowGap violations for a ≤ 50, k ≤ 100.
-/

namespace CollatzPowGapSmall

open CollatzDescentDichotomy CollatzPowGapReduce CollatzDensityCount

/-! ## §1  Bounded verification (native_decide) -/

/-- **PowGap for a ≤ 40, k ≤ 80** via `native_decide`.
Covers the entire sub-threshold for `a ≤ 40`: sub-threshold has
`k ∈ {⌈a·log₂3⌉,...,2a−1} ⊆ {0,...,79}` when `a ≤ 40`. -/
theorem powGap_bounded :
    ∀ a : Fin 41, ∀ k : Fin 81,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-! ## §2  Auxiliary: aCoef ≤ k -/

/-- `aCoef n k` counts odd-step occurrences in `k` steps — at most one per step. -/
theorem aCoef_le_k (n k : Nat) : aCoef n k ≤ k := by
  induction k with
  | zero => simp [aCoef]
  | succ k ih => unfold aCoef; split <;> omega

/-! ## §3  Full PowGap for a ≤ 40 -/

/-- **PowGap holds for all `a ≤ 40` (any `k`).** -/
theorem powGap_of_le_40 (a k : Nat) (ha : a ≤ 40) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    -- k < 2*a ≤ 80, so k ≤ 79 < 81
    exact powGap_bounded ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

/-! ## §4  Extended bound: a ≤ 100 -/

/-- **PowGap for a ≤ 100, k ≤ 200** via `native_decide`.
Sub-threshold for `a ≤ 100` lives in `k < 2a ≤ 200`. -/
theorem powGap_bounded_100 :
    ∀ a : Fin 101, ∀ k : Fin 201,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-- **PowGap holds for all `a ≤ 100` (any `k`).** -/
theorem powGap_of_le_100 (a k : Nat) (ha : a ≤ 100) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    exact powGap_bounded_100 ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

/-! ## §5  Note on the remaining gap -/

/-
The following cannot yet be proved:

  theorem powGap_all : PowGap := fun a k h3k => by
    by_cases ha : a ≤ 40
    · exact powGap_of_le_40 a k ha h3k
    · -- a > 40, k < 2*a: needs Baker-type bound d = 2^k - 3^a ≥ ⌊(3/2)^a⌋
      by_cases hk : 2 * a ≤ k
      · exact powGap_of_two_a_le a k hk h3k
      · exact sorry

The `sorry` corresponds to: for a > 40 and k < 2a (sub-threshold), showing
  2^k − 3^a ≥ ⌊(3/2)^a⌋ := ⌊3^a/2^a⌋.
This is a statement about the minimum gap between 3^a and the next power of 2.
Baker's theorem (effective lower bounds on linear forms in logarithms) implies it,
but this theorem is not yet formalised in mathlib.
-/

end CollatzPowGapSmall
