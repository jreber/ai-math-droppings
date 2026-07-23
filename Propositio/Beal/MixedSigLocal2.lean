import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Mixed-signature Beal local obstructions (second batch)

Companion to `BealFifthMixedLocal.lean` and `BealThreeFourLocal.lean`.  Each theorem here
establishes that for a specific signature `(i, j)`, the sumset `{aⁱ + bʲ}` misses at
least one residue class modulo some prime `q`, and that the missing class is achievable as
`cᶻ (z ≥ 3)` — making it a genuine Beal obstruction.

## Signatures covered

| Signature | Modulus | Gap | Forbidden RHS | Witness |
|-----------|---------|-----|---------------|---------|
| `(2, 5, z)` | 11 | `{7}` | `7` | `6³ ≡ 7` |
| `(5, 7, z)` | 71 | `{8,10,11,60,61,63}` | `8` | `2³ ≡ 8` |
| `(3, 7, z)` | 43 | `{13,19,24,30}` | `13` | `24⁵ ≡ 13` |
| `(4, 7, z)` | 29 | `{5,9,10,14,27}` | `5` | `22³ ≡ 5` |
| `(2,11, z)` | 23 | `{20,21}` | `20` | `11³ ≡ 20` |

For `(2,7,z)` the bare sumset is surjective at every prime up to 500 (Chevalley–Warning
forces solvability when `2 + 7 < p` essentially), so no bare local obstruction exists in
this range; it is omitted.

## CORRECTNESS / sanity discipline

All residue-image claims were computed in Python before any `≠` was asserted.  Every
`decide` closes a finite problem over `ZMod q`; none use `native_decide`, so the axiom set
is exactly `[propext, Classical.choice, Quot.sound]`.  House style follows
`BealFifthMixedLocal.lean`.

Typecheck with `lake env lean BealMixedSigLocal2.lean`.
-/

-- ZMod 71 decide goals are large (71² = 5041 pairs × 6-tuple); increase the kernel limit.
set_option maxRecDepth 2000

namespace BealMixedSigLocal2

/-! ## 1. `(2, 5, z)` at the prime 11 -/

/-- **`a² + b⁵` is never `≡ 7 (mod 11)`** for all integers `a, b`.
The image of `(a, b) ↦ a² + b⁵` over `ZMod 11` is `{0,…,10} \ {7}`.
Fifth powers mod 11 are `{0, 1, 10}` (since `5 ∣ 10 = |(ZMod 11)ˣ|`);
squares are `{0, 1, 3, 4, 5, 9}`. Their sumset misses exactly `7`. -/
theorem twofive_notMem_seven_mod11 (a b : ℤ) :
    (a ^ 2 + b ^ 5 : ZMod 11) ≠ 7 := by
  have h : ∀ r s : ZMod 11, r ^ 2 + s ^ 5 ≠ 7 := by decide
  have := h (a : ZMod 11) (b : ZMod 11)
  simpa using this

/-- **Signature-`(2,5,z)` mod-11 obstruction.**
If `cᶻ ≡ 7 (mod 11)` then `a² + b⁵ ≠ cᶻ`.
Non-vacuous: `6³ = 216 ≡ 7 (mod 11)`, so `c ≡ 6, z = 3` lands on the forbidden class. -/
theorem beal_25z_mod11_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 11) ^ z = 7) : a ^ 2 + b ^ 5 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 2 + b ^ 5 : ZMod 11) = (c ^ z : ZMod 11) := by
    have : ((a ^ 2 + b ^ 5 : ℤ) : ZMod 11) = ((c ^ z : ℤ) : ZMod 11) := by rw [heq]
    push_cast at this ⊢; exact this
  have hne := twofive_notMem_seven_mod11 a b
  push_cast at hcast hne
  rw [hcast, hc] at hne
  exact hne rfl

/-! ## 2. `(5, 7, z)` at the prime 71 -/

/-- **`a⁵ + b⁷` is never `≡ 8 (mod 71)`** for all integers `a, b`.
The full image over `ZMod 71` misses `{8, 10, 11, 60, 61, 63}`; the representative `8`
is the smallest forbidden element.  (Fifth powers mod 71 have `5 ∣ 70` nonzero elements;
seventh powers have `7 ∣ 70` nonzero elements; their sumset has a gap.) -/
theorem fiveseven_notMem_eight_mod71 (a b : ℤ) :
    (a ^ 5 + b ^ 7 : ZMod 71) ≠ 8 := by
  have h : ∀ r s : ZMod 71, r ^ 5 + s ^ 7 ≠ 8 := by decide
  have := h (a : ZMod 71) (b : ZMod 71)
  simpa using this

/-- **`a⁵ + b⁷` avoids all six gap residues mod 71.**
The full gap is `{8, 10, 11, 60, 61, 63}` — a finite `decide` over the `71 × 71` grid. -/
theorem fiveseven_notMem_gap_mod71 (a b : ℤ) :
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

/-- **Signature-`(5,7,z)` mod-71 obstruction.**
If `cᶻ ≡ 8 (mod 71)` then `a⁵ + b⁷ ≠ cᶻ`.
Non-vacuous: `2³ = 8 ≡ 8 (mod 71)`. -/
theorem beal_57z_mod71_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 71) ^ z = 8) : a ^ 5 + b ^ 7 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 5 + b ^ 7 : ZMod 71) = (c ^ z : ZMod 71) := by
    have : ((a ^ 5 + b ^ 7 : ℤ) : ZMod 71) = ((c ^ z : ℤ) : ZMod 71) := by rw [heq]
    push_cast at this ⊢; exact this
  have hne := fiveseven_notMem_eight_mod71 a b
  push_cast at hcast hne
  rw [hcast, hc] at hne
  exact hne rfl

/-! ## 3. `(3, 7, z)` at the prime 43 -/

/-- **`a³ + b⁷` avoids `{13, 19, 24, 30} (mod 43)`** for all integers `a, b`.
Seventh powers mod 43 have `7 ∣ 42` so only six nonzero residues; cubes mod 43 have
`3 ∣ 42` so only fourteen nonzero residues.  The sumset misses exactly four classes.
All four are genuine fifth-power residues: `24⁵ ≡ 13`, `18⁵ ≡ 19`, `25⁵ ≡ 24`,
`19⁵ ≡ 30 (mod 43)`. -/
theorem threeseven_notMem_mod43 (a b : ℤ) :
    (a ^ 3 + b ^ 7 : ZMod 43) ≠ 13 ∧ (a ^ 3 + b ^ 7 : ZMod 43) ≠ 19 ∧
    (a ^ 3 + b ^ 7 : ZMod 43) ≠ 24 ∧ (a ^ 3 + b ^ 7 : ZMod 43) ≠ 30 := by
  have h : ∀ r s : ZMod 43,
      r ^ 3 + s ^ 7 ≠ 13 ∧ r ^ 3 + s ^ 7 ≠ 19 ∧
      r ^ 3 + s ^ 7 ≠ 24 ∧ r ^ 3 + s ^ 7 ≠ 30 := by decide
  have := h (a : ZMod 43) (b : ZMod 43)
  push_cast at this ⊢
  exact this

/-- **Signature-`(3,7,z)` mod-43 obstruction.**
If `cᶻ ≡ 13, 19, 24, or 30 (mod 43)` then `a³ + b⁷ ≠ cᶻ`.
Non-vacuous: all four forbidden classes are fifth-power residues mod 43
(`24⁵ ≡ 13`, `18⁵ ≡ 19`, `25⁵ ≡ 24`, `19⁵ ≡ 30`). -/
theorem beal_37z_mod43_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 43) ^ z = 13 ∨ (c : ZMod 43) ^ z = 19 ∨
          (c : ZMod 43) ^ z = 24 ∨ (c : ZMod 43) ^ z = 30) :
    a ^ 3 + b ^ 7 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 7 : ZMod 43) = (c ^ z : ZMod 43) := by
    have : ((a ^ 3 + b ^ 7 : ℤ) : ZMod 43) = ((c ^ z : ℤ) : ZMod 43) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h13, h19, h24, h30⟩ := threeseven_notMem_mod43 a b
  push_cast at hcast
  rcases hc with h | h | h | h <;> rw [h] at hcast
  · exact h13 hcast
  · exact h19 hcast
  · exact h24 hcast
  · exact h30 hcast

/-! ## 4. `(4, 7, z)` at the prime 29 -/

/-- **`a⁴ + b⁷` avoids `{5, 9, 10, 14, 27} (mod 29)`** for all integers `a, b`.
Fourth powers mod 29 have `4 ∣ 28` so seven nonzero residues; seventh powers have
`7 ∣ 28` so four nonzero residues.  The sumset misses five classes, all genuine cube
residues (`22³ ≡ 5`, `5³ ≡ 9 (mod 29)`). -/
theorem fourseven_notMem_mod29 (a b : ℤ) :
    (a ^ 4 + b ^ 7 : ZMod 29) ≠ 5  ∧ (a ^ 4 + b ^ 7 : ZMod 29) ≠ 9  ∧
    (a ^ 4 + b ^ 7 : ZMod 29) ≠ 10 ∧ (a ^ 4 + b ^ 7 : ZMod 29) ≠ 14 ∧
    (a ^ 4 + b ^ 7 : ZMod 29) ≠ 27 := by
  have h : ∀ r s : ZMod 29,
      r ^ 4 + s ^ 7 ≠ 5  ∧ r ^ 4 + s ^ 7 ≠ 9  ∧
      r ^ 4 + s ^ 7 ≠ 10 ∧ r ^ 4 + s ^ 7 ≠ 14 ∧
      r ^ 4 + s ^ 7 ≠ 27 := by decide
  have := h (a : ZMod 29) (b : ZMod 29)
  push_cast at this ⊢
  exact this

/-- **Signature-`(4,7,z)` mod-29 obstruction.**
If `cᶻ ≡ 5 (mod 29)` then `a⁴ + b⁷ ≠ cᶻ`.
Non-vacuous: `22³ = 10648 ≡ 5 (mod 29)`. -/
theorem beal_47z_mod29_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 29) ^ z = 5) : a ^ 4 + b ^ 7 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 4 + b ^ 7 : ZMod 29) = (c ^ z : ZMod 29) := by
    have : ((a ^ 4 + b ^ 7 : ℤ) : ZMod 29) = ((c ^ z : ℤ) : ZMod 29) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h5, _, _, _, _⟩ := fourseven_notMem_mod29 a b
  push_cast at hcast
  rw [hc] at hcast
  exact h5 hcast

/-! ## 5. `(2, 11, z)` at the prime 23 -/

/-- **`a² + b¹¹` avoids `{20, 21} (mod 23)`** for all integers `a, b`.
Eleventh powers mod 23 have `11 ∣ 22` so only two nonzero residues `{1, 22}` plus `{0}`;
squares mod 23 are `{0, 1, 2, 3, 4, 6, 8, 9, 12, 13}`.  Their sumset misses `{20, 21}`.
Both are genuine cube residues: `11³ = 1331 ≡ 20 (mod 23)`, `7³ = 343 ≡ 21 (mod 23)`. -/
theorem twoeleven_notMem_mod23 (a b : ℤ) :
    (a ^ 2 + b ^ 11 : ZMod 23) ≠ 20 ∧ (a ^ 2 + b ^ 11 : ZMod 23) ≠ 21 := by
  have h : ∀ r s : ZMod 23, r ^ 2 + s ^ 11 ≠ 20 ∧ r ^ 2 + s ^ 11 ≠ 21 := by decide
  have := h (a : ZMod 23) (b : ZMod 23)
  push_cast at this ⊢
  exact this

/-- **Signature-`(2,11,z)` mod-23 obstruction.**
If `cᶻ ≡ 20 or 21 (mod 23)` then `a² + b¹¹ ≠ cᶻ`.
Non-vacuous: `11³ ≡ 20 (mod 23)` and `7³ ≡ 21 (mod 23)`. -/
theorem beal_211z_mod23_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 23) ^ z = 20 ∨ (c : ZMod 23) ^ z = 21) :
    a ^ 2 + b ^ 11 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 2 + b ^ 11 : ZMod 23) = (c ^ z : ZMod 23) := by
    have : ((a ^ 2 + b ^ 11 : ℤ) : ZMod 23) = ((c ^ z : ℤ) : ZMod 23) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h20, h21⟩ := twoeleven_notMem_mod23 a b
  push_cast at hcast
  rcases hc with h | h <;> rw [h] at hcast
  · exact h20 hcast
  · exact h21 hcast

/-! ## 6. Axiom checks -/

#print axioms beal_25z_mod11_obstruction
#print axioms beal_57z_mod71_obstruction
#print axioms beal_37z_mod43_obstruction
#print axioms beal_47z_mod29_obstruction
#print axioms beal_211z_mod23_obstruction

end BealMixedSigLocal2
