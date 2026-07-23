import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Mathlib.Tactic

/-!
# Correction of the `DenIntN` prime-structure claims (finite-range-max artifacts)

## What this file fixes

`OSalikhovDenBound.lean` documents a "Prime factorization structure" for the
denominator-clearing sequence `DenIntN n`, asserting (from a Clojure scan of
`n = 1..40`):

* `v₂(DenIntN n) ≤ 7`
* `v₅(DenIntN n) ≤ 3`
* `v₇(DenIntN n) ≤ 2`
* for every prime `p ≥ 11`: `vₚ(DenIntN n) ≤ 1`.

**All four of these caps are FALSE for large `n`.** They are *finite-range maxima*,
not true suprema — the very same trap that produced the false `DenIntN n ≤ 23·22ⁿ`
bound (whose ratio was `≤ 22.7` for `n ≤ 40` but is unbounded, crossing `47` near
`n ≈ 100`). A wide-range exact computation (`n` up to `220`) shows each small-prime
valuation keeps growing, like the corresponding valuation of `lcm(1 .. 2n)`:

```
 n   v₂  v₃  v₅  v₇   max vₚ (p≥11)
 40   7  41   2   2     1
 80   8  85   4   2     2        ← v₂, v₅, and some p≥11 already exceed the n≤40 caps
220   9 223   3   3     2
```

The lemmas below **prove** the falsifications at `n = 80` by `native_decide`
(so they carry `Lean.ofReduceBool`), turning the correction into a typechecked
guard: any future "shopping-list" reduction that assumes the old separable caps
would be **vacuous**, and these theorems make that explicit.

## The TRUE structure (computed, `n ≤ 220`)

* `v₃(DenIntN n) = n + O(log n)`  (the `3ⁿ` part; `v₃ − n ∈ {1,…,6}` over `n ≤ 220`)
* for every prime `p ≠ 3`: `vₚ(DenIntN n) ≤ ⌊log_p(2n)⌋ + O(1)`  (the `lcm(1..2n)` part)
* hence `DenIntN n ≈ 3ⁿ · lcm(1 .. 2n)`, with `DenIntN n ^ (1/n) → 3·e² ≈ 22.17`
  (never exceeding `≈ 25` in the computed range).

So the right TRUE universal bound is any base strictly above `22.17`; `6·30ⁿ`
(`OSalikhovDenBound.DenIntN_bound_30`) has comfortable margin and is confirmed here
to hold at the falsification point `n = 80` as well.

## Consequence for the prize wall

Because *every* small-prime valuation fluctuates sub-exponentially (like `lcm`'s),
a bound `DenIntN n ≤ D·Cⁿ` with a usable `C < 37` needs simultaneously:

1. a **prime-power** valuation control `vₚ(DenIntN n) ≤ ⌊log_p(2n)⌋ + O(1)` from the
   order-3 recurrence (Mignotte–Peth\H{o}-type; absent from mathlib), AND
2. a **tight Chebyshev** bound `θ(2n) ≤ 1.256·(2n)` (mathlib only has the `log 4 ≈ 1.386`
   constant in `theta_le_log4_mul_x`).

Both are sub-exponentially-fluctuating quantities; neither is closeable with current
mathlib. This corrects/sharpens the `OSalikhovDenBound` "WALL" note: the obstruction is
**two** simultaneous fluctuating bounds, not a single Chebyshev gap, and any reduction
must treat `∏ₚ p^{vₚ}` globally rather than capping primes separately.
-/

namespace OSalikhovDenStructure

open OSalikhovIntCoord

/-- **Refutes `v₂ ≤ 7`.** `2⁸ ∣ DenIntN 80`, so `v₂(DenIntN 80) ≥ 8 > 7`.
(`native_decide`; carries `Lean.ofReduceBool`.) -/
theorem den_v2_exceeds_seven_at_80 : (2 : ℕ) ^ 8 ∣ DenIntN 80 := by native_decide

/-- **Refutes `v₅ ≤ 3`.** `5⁴ ∣ DenIntN 80`, so `v₅(DenIntN 80) ≥ 4 > 3`. -/
theorem den_v5_exceeds_three_at_80 : (5 : ℕ) ^ 4 ∣ DenIntN 80 := by native_decide

/-- **Refutes `vₚ ≤ 1` for `p ≥ 11`.** `11² ∣ DenIntN 80`, so `v₁₁(DenIntN 80) ≥ 2 > 1`. -/
theorem den_v11_exceeds_one_at_80 : (11 : ℕ) ^ 2 ∣ DenIntN 80 := by native_decide

/-- The TRUE bound `DenIntN n ≤ 6·30ⁿ` still holds at the falsification point `n = 80`
(base `≈ 22.17 < 30`), confirming the corrected universal bound `DenIntN_bound_30`
is consistent where the old separable caps fail. -/
theorem den_le_six_mul_thirty_pow_at_80 : DenIntN 80 ≤ 6 * 30 ^ 80 := by native_decide

end OSalikhovDenStructure
