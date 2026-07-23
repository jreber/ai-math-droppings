import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Propositio.Tactics

/-!
# Local obstructions for the fifth-power mixed Beal signatures `(4,5,z)` and `(3,5,z)`

Companion to `BealThreeFourLocal.lean`, completing the small mixed true-Beal signatures
that involve a fifth power. Both obstructions are **bare** (no coprimality hypothesis):
the sumset already misses a residue.

## `(4,5,z)` : `a⁴ + b⁵` misses `7 (mod 11)`

Fifth powers mod 11 are `{0, 1, 10}` (only two nonzero, since `5 ∣ 10 = |(ZMod 11)ˣ|`)
and fourth powers are `{0, 1, 3, 4, 5, 9}`; the sumset is `{0,…,10} \ {7}`
(`fourfive_notMem_seven_mod11`). The forbidden class is achievable on the right
(`6³ = 216 ≡ 7 (mod 11)`), so

> **`beal_45z_mod11_obstruction`** : `cᶻ ≡ 7 (mod 11)` ⟹ `a⁴ + b⁵ ≠ cᶻ`.

Mod `25` and mod `31` the bare `a⁴ + b⁵` is surjective (checked), so `11` is the
productive prime here.

## `(3,5,z)` : `a³ + b⁵` misses `{12, 19} (mod 31)`

This signature needs a *larger* prime: mod 11 the cube map is already a bijection on
units (`3 ∤ 10`), so `a³` alone is surjective and there is no obstruction; likewise mod
25. At `p = 31` (`5 ∣ 30`, so only six nonzero fifth-power residues) the sumset
`a³ + b⁵` is `{0,…,30} \ {12, 19}` (`threefive_notMem_mod31`). Both forbidden classes are
achievable as `cᶻ (z ≥ 3)`, so

> **`beal_35z_mod31_obstruction`** : `cᶻ ≡ 12 or 19 (mod 31)` ⟹ `a³ + b⁵ ≠ cᶻ`.

## CORRECTNESS / sanity discipline

Each forbidden class and each surjectivity claim was first confirmed by `#eval`
enumeration over the relevant `ZMod p` before assertion, and the forbidden right-hand
residues were checked to be genuine `z`-th-power residues (`z ≥ 3`), so the obstructions
are non-vacuous. All finite facts use `decide` (NOT `native_decide`). Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). House style follows `BealThreeFourLocal.lean`.

Typecheck with `lake env lean BealFifthMixedLocal.lean`.
-/

namespace BealFifthMixedLocal

/-! ## 1. `(4,5,z)` at the prime 11 -/

/-- **`a⁴ + b⁵` is never `≡ 7 (mod 11)`** — for all integers `a, b`. Finite `decide`
over the `11 × 11` grid; the image is `{0,…,10} \ {7}`. -/
theorem fourfive_notMem_seven_mod11 (a b : ℤ) : (a ^ 4 + b ^ 5 : ZMod 11) ≠ 7 := by
  have h : ∀ r s : ZMod 11, r ^ 4 + s ^ 5 ≠ 7 := by decide
  have := h (a : ZMod 11) (b : ZMod 11)
  simpa using this

/-- **Signature-`(4,5,z)` mod-11 obstruction.** If `cᶻ ≡ 7 (mod 11)` then
`a⁴ + b⁵ ≠ cᶻ`. Non-vacuous: `6³ ≡ 7 (mod 11)`. -/
theorem beal_45z_mod11_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 11) ^ z = 7) : a ^ 4 + b ^ 5 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 4 + b ^ 5 : ZMod 11) = (c ^ z : ZMod 11) := by
    have : ((a ^ 4 + b ^ 5 : ℤ) : ZMod 11) = ((c ^ z : ℤ) : ZMod 11) := by rw [heq]
    push_cast_exact
  have hne := fourfive_notMem_seven_mod11 a b
  push_cast at hcast hne
  rw [hcast, hc] at hne
  exact hne rfl

/-! ## 2. `(3,5,z)` at the prime 31 -/

/-- **`a³ + b⁵` avoids `{12, 19} (mod 31)`** — for all integers `a, b`. Finite `decide`
over the `31 × 31` grid. (Mod 11 there is no obstruction, since `a³` is already
surjective; 31 is the productive prime.) -/
theorem threefive_notMem_mod31 (a b : ℤ) :
    (a ^ 3 + b ^ 5 : ZMod 31) ≠ 12 ∧ (a ^ 3 + b ^ 5 : ZMod 31) ≠ 19 := by
  have h : ∀ r s : ZMod 31, r ^ 3 + s ^ 5 ≠ 12 ∧ r ^ 3 + s ^ 5 ≠ 19 := by decide
  have := h (a : ZMod 31) (b : ZMod 31)
  push_cast_exact

/-- **Signature-`(3,5,z)` mod-31 obstruction.** If `cᶻ ≡ 12 or 19 (mod 31)` then
`a³ + b⁵ ≠ cᶻ`. Both classes are achievable as `cᶻ (z ≥ 3)`, so non-vacuous. -/
theorem beal_35z_mod31_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 31) ^ z = 12 ∨ (c : ZMod 31) ^ z = 19) :
    a ^ 3 + b ^ 5 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 5 : ZMod 31) = (c ^ z : ZMod 31) := by
    have : ((a ^ 3 + b ^ 5 : ℤ) : ZMod 31) = ((c ^ z : ℤ) : ZMod 31) := by rw [heq]
    push_cast_exact
  obtain ⟨h12, h19⟩ := threefive_notMem_mod31 a b
  push_cast at hcast
  rcases hc with h | h <;> rw [h] at hcast
  · exact h12 hcast
  · exact h19 hcast

/-! ## 3. Axiom checks -/

#print axioms beal_45z_mod11_obstruction
#print axioms beal_35z_mod31_obstruction

end BealFifthMixedLocal
