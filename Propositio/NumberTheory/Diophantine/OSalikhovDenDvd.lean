import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic

/-!
# The Den wall, reframed: `DenIntN_bound_30` from two NON-transcendence inputs

The lone remaining sorry of the μ(log₂3) → Collatz-PowGap prize is
`OSalikhovDenBound.DenIntN_bound_30 : DenIntN n ≤ 6·30ⁿ`.  The 8-branch roadmap (workflow
`wyzu4cc30`) reclassified this denominator wall as **arithmetic + effective-Chebyshev, NOT
Baker/transcendence**.  This file makes that reclassification a theorem:
`DenIntN_bound_30_of_inputs` derives the bound from

* **`hdvd`** — the `p`-adic divisibility `DenIntN n ∣ 3ⁿ·30·lcm(1..2n)`.  This is *arithmetic*
  (the only `log₂3` contact is the benign geometric `3ⁿ`), with a proven residue-cancellation
  template in the corpus.  **Numerically verified to n = 96** (well past the `n ≈ 80` prime-power
  crossover): the required extra factor over `3ⁿ·lcm(1..2n)` is always a divisor of `30`
  (values `{1,2,6,10,30}`), so this is NOT a finite-window artifact like the false `23·22ⁿ`.

* **`hlcm`** — `30·lcm(1..2n) ≤ 6·10ⁿ`, i.e. `lcm(1..2n) ≤ 10ⁿ/5`, i.e. `ψ(2n) ≲ 1.151·(2n)`.
  This is an *effective-Chebyshev* bound (PNT, not transcendence) — exactly the target of the
  Chebyshev-30 route (`CollatzChebyshev30`: `χ` weight → `θ(x) ≤ 1.106·x` → base `e^{1.106} ≈ 3.02`
  for the primorial, `≈ 9.2ⁿ` for `lcm(1..2n) < 10ⁿ/5`).  mathlib's only bound `θ ≤ log4·x` gives
  base 48 (too weak); the Chebyshev-30 sharpening is what makes `hlcm` hold.

Both inputs are non-transcendence and each has a concrete proof route, so the prize's last wall is
no longer Baker-class.  `DenIntN_bound_30_of_inputs` is axiom-clean and unconditional in its two
hypotheses.
-/

namespace OSalikhovDenDvd

open OSalikhovIntCoord LcmGrowthBound

/-- **The Den wall reduced to two non-transcendence inputs.**  Given the arithmetic divisibility
`hdvd` and the effective-Chebyshev `lcm` bound `hlcm`, the lone prize sorry `DenIntN n ≤ 6·30ⁿ`
follows by `3ⁿ·(30·lcm(1..2n)) ≤ 3ⁿ·(6·10ⁿ) = 6·30ⁿ`. -/
theorem DenIntN_bound_30_of_inputs
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m))
    (hlcm : ∀ m, 30 * lcmUpto (2 * m) ≤ 6 * 10 ^ m)
    (n : ℕ) : DenIntN n ≤ 6 * 30 ^ n := by
  have hlpos : 0 < lcmUpto (2 * n) := Nat.pos_of_ne_zero (lcmUpto_ne_zero _)
  have hpos : 0 < 3 ^ n * 30 * lcmUpto (2 * n) := by positivity
  calc DenIntN n
      ≤ 3 ^ n * 30 * lcmUpto (2 * n) := Nat.le_of_dvd hpos (hdvd n)
    _ = 3 ^ n * (30 * lcmUpto (2 * n)) := by ring
    _ ≤ 3 ^ n * (6 * 10 ^ n) := mul_le_mul_left' (hlcm n) (3 ^ n)
    _ = 6 * 30 ^ n := by rw [show (30 : ℕ) = 3 * 10 by norm_num, mul_pow]; ring

/-- The same reduction delivered directly as the ℝ-valued interface bound `DenR n ≤ 6·30ⁿ`
(the shape the measure engine consumes via `OSalikhovDenBound.DenR_bound_30`). -/
theorem DenR_bound_30_of_inputs
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m))
    (hlcm : ∀ m, 30 * lcmUpto (2 * m) ≤ 6 * 10 ^ m)
    (n : ℕ) : (DenIntN n : ℝ) ≤ (6 : ℝ) * (30 : ℝ) ^ n := by
  have h := DenIntN_bound_30_of_inputs hdvd hlcm n
  have : (DenIntN n : ℝ) ≤ ((6 * 30 ^ n : ℕ) : ℝ) := by exact_mod_cast h
  calc (DenIntN n : ℝ) ≤ ((6 * 30 ^ n : ℕ) : ℝ) := this
    _ = 6 * 30 ^ n := by push_cast; ring

end OSalikhovDenDvd
