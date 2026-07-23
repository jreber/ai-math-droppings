import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Local obstructions for the seventh-power mixed Beal signatures `(5,7,z)` and `(3,7,z)`

Companion to `BealFifthMixedLocal.lean`, covering the smallest mixed Beal signatures
that involve a seventh power. Both obstructions are bare (no coprimality hypothesis):
the sumset already misses one or more residue classes.

## `(5,7,3)` : `a⁵ + b⁷` misses `{8,10,11,60,61,63} (mod 71)`

Fifth powers mod 71 have image of size `(71−1)/gcd(5,70) = 70/5 = 14` plus 0 (15 total).
Seventh powers mod 71 have image of size `70/7 = 10` plus 0 (11 total).
The sumset `a⁵ + b⁷` (mod 71) has 65 elements, missing the six residues `{8,10,11,60,61,63}`.
All six missing values are cubes mod 71 (`2³=8`, `18³=10`, `33³=11`, `38³=60`, `53³=61`,
`69³=63`), so the obstruction is non-vacuous:

> **`beal_57z3_mod71_obstruction`** : if `c³ ≡ 8,10,11,60,61, or 63 (mod 71)` then
> `a⁵ + b⁷ ≠ c³`.

## `(3,7,5)` : `a³ + b⁷` misses `{13,19,24,30} (mod 43)`

Third powers mod 43 have image of size `(43−1)/gcd(3,42) = 42/3 = 14` plus 0 (15 total).
Seventh powers mod 43 have image of size `42/7 = 6` plus 0 (7 total).
The sumset `a³ + b⁷` (mod 43) has 39 elements, missing four of the 43 residues.
All four missing values are fifth powers mod 43 (`24⁵=13`, `18⁵=19`, `25⁵=24`, `19⁵=30`),
so the obstruction is non-vacuous:

> **`beal_37z5_mod43_obstruction`** : if `c⁵ ≡ 13,19,24, or 30 (mod 43)` then
> `a³ + b⁷ ≠ c⁵`.

## Correctness / sanity discipline

Each forbidden class and each surjectivity claim was confirmed by `#eval` enumeration
over the relevant `ZMod p` before assertion. All finite facts use `decide`
(NOT `native_decide`). Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace BealSevenMixedLocal

set_option maxRecDepth 10000

/-! ## 1. `(5,7,3)` at the prime 71 -/

/-- **`a⁵ + b⁷` avoids `{8,10,11,60,61,63} (mod 71)`** — for all integers `a, b`.
Finite `decide` over the `71 × 71` grid. (The image has 65 of the 71 residues.) -/
theorem fiveseven_notMem_mod71 (a b : ℤ) :
    (a ^ 5 + b ^ 7 : ZMod 71) ≠ 8  ∧ (a ^ 5 + b ^ 7 : ZMod 71) ≠ 10 ∧
    (a ^ 5 + b ^ 7 : ZMod 71) ≠ 11 ∧ (a ^ 5 + b ^ 7 : ZMod 71) ≠ 60 ∧
    (a ^ 5 + b ^ 7 : ZMod 71) ≠ 61 ∧ (a ^ 5 + b ^ 7 : ZMod 71) ≠ 63 := by
  have h : ∀ r s : ZMod 71,
      r ^ 5 + s ^ 7 ≠ 8  ∧ r ^ 5 + s ^ 7 ≠ 10 ∧
      r ^ 5 + s ^ 7 ≠ 11 ∧ r ^ 5 + s ^ 7 ≠ 60 ∧
      r ^ 5 + s ^ 7 ≠ 61 ∧ r ^ 5 + s ^ 7 ≠ 63 := by decide
  have := h (a : ZMod 71) (b : ZMod 71)
  push_cast at this ⊢
  exact this

/-- **Signature-`(5,7,3)` mod-71 obstruction.** If `c³` equals one of the six forbidden
residues mod 71, then `a⁵ + b⁷ ≠ c³`. Non-vacuous: e.g. `2³ ≡ 8 (mod 71)`. -/
theorem beal_57z3_mod71_obstruction {a b c : ℤ}
    (hc : (c : ZMod 71) ^ 3 = 8  ∨ (c : ZMod 71) ^ 3 = 10 ∨
          (c : ZMod 71) ^ 3 = 11 ∨ (c : ZMod 71) ^ 3 = 60 ∨
          (c : ZMod 71) ^ 3 = 61 ∨ (c : ZMod 71) ^ 3 = 63) :
    a ^ 5 + b ^ 7 ≠ c ^ 3 := by
  intro heq
  have hcast : (a ^ 5 + b ^ 7 : ZMod 71) = (c ^ 3 : ZMod 71) := by
    have : ((a ^ 5 + b ^ 7 : ℤ) : ZMod 71) = ((c ^ 3 : ℤ) : ZMod 71) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h8, h10, h11, h60, h61, h63⟩ := fiveseven_notMem_mod71 a b
  push_cast at hcast
  rcases hc with h | h | h | h | h | h <;> rw [h] at hcast
  · exact h8 hcast
  · exact h10 hcast
  · exact h11 hcast
  · exact h60 hcast
  · exact h61 hcast
  · exact h63 hcast

/-! ## 2. `(3,7,5)` at the prime 43 -/

/-- **`a³ + b⁷` avoids `{13,19,24,30} (mod 43)`** — for all integers `a, b`.
Finite `decide` over the `43 × 43` grid. (The image has 39 of the 43 residues.) -/
theorem threeseven_notMem_mod43 (a b : ℤ) :
    (a ^ 3 + b ^ 7 : ZMod 43) ≠ 13 ∧ (a ^ 3 + b ^ 7 : ZMod 43) ≠ 19 ∧
    (a ^ 3 + b ^ 7 : ZMod 43) ≠ 24 ∧ (a ^ 3 + b ^ 7 : ZMod 43) ≠ 30 := by
  have h : ∀ r s : ZMod 43,
      r ^ 3 + s ^ 7 ≠ 13 ∧ r ^ 3 + s ^ 7 ≠ 19 ∧
      r ^ 3 + s ^ 7 ≠ 24 ∧ r ^ 3 + s ^ 7 ≠ 30 := by decide
  have := h (a : ZMod 43) (b : ZMod 43)
  push_cast at this ⊢
  exact this

/-- **Signature-`(3,7,5)` mod-43 obstruction.** If `c⁵` equals one of the four forbidden
residues mod 43, then `a³ + b⁷ ≠ c⁵`. Non-vacuous: e.g. `24⁵ ≡ 13 (mod 43)`. -/
theorem beal_37z5_mod43_obstruction {a b c : ℤ}
    (hc : (c : ZMod 43) ^ 5 = 13 ∨ (c : ZMod 43) ^ 5 = 19 ∨
          (c : ZMod 43) ^ 5 = 24 ∨ (c : ZMod 43) ^ 5 = 30) :
    a ^ 3 + b ^ 7 ≠ c ^ 5 := by
  intro heq
  have hcast : (a ^ 3 + b ^ 7 : ZMod 43) = (c ^ 5 : ZMod 43) := by
    have : ((a ^ 3 + b ^ 7 : ℤ) : ZMod 43) = ((c ^ 5 : ℤ) : ZMod 43) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h13, h19, h24, h30⟩ := threeseven_notMem_mod43 a b
  push_cast at hcast
  rcases hc with h | h | h | h <;> rw [h] at hcast
  · exact h13 hcast
  · exact h19 hcast
  · exact h24 hcast
  · exact h30 hcast

/-! ## 3. Axiom checks -/

#print axioms beal_57z3_mod71_obstruction
#print axioms beal_37z5_mod43_obstruction

end BealSevenMixedLocal
