import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Higher-exponent Beal local obstructions

This file establishes modular obstructions for Beal signatures `aⁱ + bʲ = cᶻ (z ≥ 3)`
involving higher exponents (`i, j ∈ {3,4,5,6,7,9,11,13}`).  Each theorem shows that the
sumset `{aⁱ + bʲ mod q}` misses at least one residue class that is realised as `cᶻ (z ≥ 3)`.

## Obstructions proved

| Signature | Modulus | Gap (selected) | Witness |
|-----------|---------|----------------|---------|
| `(3, 9,z)` | 7  | `{3, 4}` | `5⁵ ≡ 3 (mod 7)` |
| `(4, 9,z)` | 13 | `{7}` | `11⁵ ≡ 7 (mod 13)` |
| `(4,11,z)` | 23 | `{20, 21}` | `11³ ≡ 20 (mod 23)` |
| `(6, 7,z)` | 43 | `{13,19,24,25,26}` | `24⁵ ≡ 13 (mod 43)` |
| `(7, 9,z)` | 43 | `{13,19,24,30}` | `24⁵ ≡ 13 (mod 43)` |
| `(3,11,z)` | 67 | `{17,18,19,48,49}` | `56⁵ ≡ 17 (mod 67)` |
Python residue census (run before coding) verified every gap and witness.  `decide` closes
each finite quantifier over `ZMod q`.  All theorems are axiom-clean
(`propext, Classical.choice, Quot.sound`).
The `(5,13)` signature has an obstruction at q=131 but the 131²=17161-pair search requires
`native_decide`; that case is omitted to maintain the axiom-hygiene policy.

Typecheck: `lake env lean BealHigherExpLocal.lean`
-/

-- Increase kernel limits for large decide goals (mod 67 has 67² = 4489 pairs).
set_option maxRecDepth 4000

namespace BealHigherExpLocal

/-! ## 1. Signature `(3, 9, z)` at the prime 7 -/

/-- **`a³ + b⁹` avoids `{3, 4} (mod 7)`** for all integers `a, b`.
Cubes mod 7 are `{0,1,6}` and ninth powers equal cubes mod 7 (since `9 ≡ 3 (mod 6)`).
Their sumset is `{0,1,2,5,6}`, missing `{3,4}`. -/
theorem threenine_notMem_mod7 (a b : ℤ) :
    (a ^ 3 + b ^ 9 : ZMod 7) ≠ 3 ∧ (a ^ 3 + b ^ 9 : ZMod 7) ≠ 4 := by
  have h : ∀ r s : ZMod 7, r ^ 3 + s ^ 9 ≠ 3 ∧ r ^ 3 + s ^ 9 ≠ 4 := by decide
  have := h (a : ZMod 7) (b : ZMod 7)
  push_cast at this ⊢
  exact this

/-- **Signature-`(3,9,z)` mod-7 obstruction.**
If `cᶻ ≡ 3 or 4 (mod 7)` then `a³ + b⁹ ≠ cᶻ`.
Non-vacuous: `5⁵ = 3125 ≡ 3 (mod 7)`, so `c ≡ 5, z = 5` provides a realised forbidden class. -/
theorem beal_39z_mod7_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 7) ^ z = 3 ∨ (c : ZMod 7) ^ z = 4) :
    a ^ 3 + b ^ 9 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 9 : ZMod 7) = (c ^ z : ZMod 7) := by
    have : ((a ^ 3 + b ^ 9 : ℤ) : ZMod 7) = ((c ^ z : ℤ) : ZMod 7) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h3, h4⟩ := threenine_notMem_mod7 a b
  push_cast at hcast
  rcases hc with h | h <;> rw [h] at hcast
  · exact h3 hcast
  · exact h4 hcast

/-! ## 2. Signature `(4, 9, z)` at the prime 13 -/

/-- **`a⁴ + b⁹` is never `≡ 7 (mod 13)`** for all integers `a, b`.
Fourth powers mod 13 have `gcd(4,12) = 4` so three nonzero residues `{1,3,9}`;
ninth powers mod 13 have `gcd(9,12) = 3` so four nonzero residues.
Their sumset misses `7`. -/
theorem fournine_notMem_seven_mod13 (a b : ℤ) :
    (a ^ 4 + b ^ 9 : ZMod 13) ≠ 7 := by
  have h : ∀ r s : ZMod 13, r ^ 4 + s ^ 9 ≠ 7 := by decide
  have := h (a : ZMod 13) (b : ZMod 13)
  simpa using this

/-- **Signature-`(4,9,z)` mod-13 obstruction.**
If `cᶻ ≡ 7 (mod 13)` then `a⁴ + b⁹ ≠ cᶻ`.
Non-vacuous: `11⁵ = 161051 ≡ 7 (mod 13)`, so `c ≡ 11, z = 5` is realised. -/
theorem beal_49z_mod13_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 13) ^ z = 7) : a ^ 4 + b ^ 9 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 4 + b ^ 9 : ZMod 13) = (c ^ z : ZMod 13) := by
    have : ((a ^ 4 + b ^ 9 : ℤ) : ZMod 13) = ((c ^ z : ℤ) : ZMod 13) := by rw [heq]
    push_cast at this ⊢; exact this
  have hne := fournine_notMem_seven_mod13 a b
  push_cast at hcast hne
  rw [hcast, hc] at hne
  exact hne rfl

/-! ## 3. Signature `(4, 11, z)` at the prime 23 -/

/-- **`a⁴ + b¹¹` avoids `{20, 21} (mod 23)`** for all integers `a, b`.
Fourth powers mod 23 have `gcd(4,22) = 2` so eleven nonzero residues;
eleventh powers mod 23 have `gcd(11,22) = 11` so two nonzero residues `{1,22}`.
Their sumset misses `{20, 21}`. -/
theorem foureleven_notMem_mod23 (a b : ℤ) :
    (a ^ 4 + b ^ 11 : ZMod 23) ≠ 20 ∧ (a ^ 4 + b ^ 11 : ZMod 23) ≠ 21 := by
  have h : ∀ r s : ZMod 23, r ^ 4 + s ^ 11 ≠ 20 ∧ r ^ 4 + s ^ 11 ≠ 21 := by decide
  have := h (a : ZMod 23) (b : ZMod 23)
  push_cast at this ⊢
  exact this

/-- **Signature-`(4,11,z)` mod-23 obstruction.**
If `cᶻ ≡ 20 or 21 (mod 23)` then `a⁴ + b¹¹ ≠ cᶻ`.
Non-vacuous: `11³ = 1331 ≡ 20 (mod 23)`, so `c ≡ 11, z = 3` is realised. -/
theorem beal_411z_mod23_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 23) ^ z = 20 ∨ (c : ZMod 23) ^ z = 21) :
    a ^ 4 + b ^ 11 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 4 + b ^ 11 : ZMod 23) = (c ^ z : ZMod 23) := by
    have : ((a ^ 4 + b ^ 11 : ℤ) : ZMod 23) = ((c ^ z : ℤ) : ZMod 23) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h20, h21⟩ := foureleven_notMem_mod23 a b
  push_cast at hcast
  rcases hc with h | h <;> rw [h] at hcast
  · exact h20 hcast
  · exact h21 hcast

/-! ## 4. Signature `(6, 7, z)` at the prime 43 -/

/-- **`a⁶ + b⁷` avoids `{13, 19, 24, 25, 26} (mod 43)`** for all integers `a, b`.
Sixth powers mod 43 have `gcd(6,42) = 6` so seven nonzero residues;
seventh powers have `gcd(7,42) = 7` so six nonzero residues.
Their sumset misses five classes, all fifth-power residues. -/
theorem sixseven_notMem_mod43 (a b : ℤ) :
    (a ^ 6 + b ^ 7 : ZMod 43) ≠ 13 ∧ (a ^ 6 + b ^ 7 : ZMod 43) ≠ 19 ∧
    (a ^ 6 + b ^ 7 : ZMod 43) ≠ 24 ∧ (a ^ 6 + b ^ 7 : ZMod 43) ≠ 25 ∧
    (a ^ 6 + b ^ 7 : ZMod 43) ≠ 26 := by
  have h : ∀ r s : ZMod 43,
      r ^ 6 + s ^ 7 ≠ 13 ∧ r ^ 6 + s ^ 7 ≠ 19 ∧
      r ^ 6 + s ^ 7 ≠ 24 ∧ r ^ 6 + s ^ 7 ≠ 25 ∧
      r ^ 6 + s ^ 7 ≠ 26 := by decide
  have := h (a : ZMod 43) (b : ZMod 43)
  push_cast at this ⊢
  exact this

/-- **Signature-`(6,7,z)` mod-43 obstruction.**
If `cᶻ ≡ 13, 19, 24, 25, or 26 (mod 43)` then `a⁶ + b⁷ ≠ cᶻ`.
Non-vacuous: `24⁵ ≡ 13 (mod 43)`, so `c ≡ 24, z = 5` is realised. -/
theorem beal_67z_mod43_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 43) ^ z = 13 ∨ (c : ZMod 43) ^ z = 19 ∨
          (c : ZMod 43) ^ z = 24 ∨ (c : ZMod 43) ^ z = 25 ∨
          (c : ZMod 43) ^ z = 26) :
    a ^ 6 + b ^ 7 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 6 + b ^ 7 : ZMod 43) = (c ^ z : ZMod 43) := by
    have : ((a ^ 6 + b ^ 7 : ℤ) : ZMod 43) = ((c ^ z : ℤ) : ZMod 43) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h13, h19, h24, h25, h26⟩ := sixseven_notMem_mod43 a b
  push_cast at hcast
  rcases hc with h | h | h | h | h <;> rw [h] at hcast
  · exact h13 hcast
  · exact h19 hcast
  · exact h24 hcast
  · exact h25 hcast
  · exact h26 hcast

/-! ## 5. Signature `(7, 9, z)` at the prime 43 -/

/-- **`a⁷ + b⁹` avoids `{13, 19, 24, 30} (mod 43)`** for all integers `a, b`.
Seventh powers mod 43 have `gcd(7,42) = 7` so six nonzero residues;
ninth powers have `gcd(9,42) = 3` so fourteen nonzero residues.
Their sumset misses four classes, all fifth-power residues mod 43. -/
theorem sevennine_notMem_mod43 (a b : ℤ) :
    (a ^ 7 + b ^ 9 : ZMod 43) ≠ 13 ∧ (a ^ 7 + b ^ 9 : ZMod 43) ≠ 19 ∧
    (a ^ 7 + b ^ 9 : ZMod 43) ≠ 24 ∧ (a ^ 7 + b ^ 9 : ZMod 43) ≠ 30 := by
  have h : ∀ r s : ZMod 43,
      r ^ 7 + s ^ 9 ≠ 13 ∧ r ^ 7 + s ^ 9 ≠ 19 ∧
      r ^ 7 + s ^ 9 ≠ 24 ∧ r ^ 7 + s ^ 9 ≠ 30 := by decide
  have := h (a : ZMod 43) (b : ZMod 43)
  push_cast at this ⊢
  exact this

/-- **Signature-`(7,9,z)` mod-43 obstruction.**
If `cᶻ ≡ 13, 19, 24, or 30 (mod 43)` then `a⁷ + b⁹ ≠ cᶻ`.
Non-vacuous: `24⁵ ≡ 13 (mod 43)`, so `c ≡ 24, z = 5` is realised. -/
theorem beal_79z_mod43_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 43) ^ z = 13 ∨ (c : ZMod 43) ^ z = 19 ∨
          (c : ZMod 43) ^ z = 24 ∨ (c : ZMod 43) ^ z = 30) :
    a ^ 7 + b ^ 9 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 7 + b ^ 9 : ZMod 43) = (c ^ z : ZMod 43) := by
    have : ((a ^ 7 + b ^ 9 : ℤ) : ZMod 43) = ((c ^ z : ℤ) : ZMod 43) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h13, h19, h24, h30⟩ := sevennine_notMem_mod43 a b
  push_cast at hcast
  rcases hc with h | h | h | h <;> rw [h] at hcast
  · exact h13 hcast
  · exact h19 hcast
  · exact h24 hcast
  · exact h30 hcast

/-! ## 6. Signature `(3, 11, z)` at the prime 67 -/

/-- **`a³ + b¹¹` avoids `{17, 18, 19, 48, 49} (mod 67)`** for all integers `a, b`.
Cubes mod 67 have `gcd(3,66) = 3` so twenty-two nonzero residues;
eleventh powers have `gcd(11,66) = 11` so six nonzero residues.
Their sumset misses five classes, all fifth-power residues. -/
theorem threeeleven_notMem_mod67 (a b : ℤ) :
    (a ^ 3 + b ^ 11 : ZMod 67) ≠ 17 ∧ (a ^ 3 + b ^ 11 : ZMod 67) ≠ 18 ∧
    (a ^ 3 + b ^ 11 : ZMod 67) ≠ 19 ∧ (a ^ 3 + b ^ 11 : ZMod 67) ≠ 48 ∧
    (a ^ 3 + b ^ 11 : ZMod 67) ≠ 49 := by
  have h : ∀ r s : ZMod 67,
      r ^ 3 + s ^ 11 ≠ 17 ∧ r ^ 3 + s ^ 11 ≠ 18 ∧
      r ^ 3 + s ^ 11 ≠ 19 ∧ r ^ 3 + s ^ 11 ≠ 48 ∧
      r ^ 3 + s ^ 11 ≠ 49 := by decide
  have := h (a : ZMod 67) (b : ZMod 67)
  push_cast at this ⊢
  exact this

/-- **Signature-`(3,11,z)` mod-67 obstruction.**
If `cᶻ ≡ 17, 18, 19, 48, or 49 (mod 67)` then `a³ + b¹¹ ≠ cᶻ`.
Non-vacuous: `56⁵ ≡ 17 (mod 67)`, so `c ≡ 56, z = 5` is realised. -/
theorem beal_311z_mod67_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 67) ^ z = 17 ∨ (c : ZMod 67) ^ z = 18 ∨
          (c : ZMod 67) ^ z = 19 ∨ (c : ZMod 67) ^ z = 48 ∨
          (c : ZMod 67) ^ z = 49) :
    a ^ 3 + b ^ 11 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 11 : ZMod 67) = (c ^ z : ZMod 67) := by
    have : ((a ^ 3 + b ^ 11 : ℤ) : ZMod 67) = ((c ^ z : ℤ) : ZMod 67) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h17, h18, h19, h48, h49⟩ := threeeleven_notMem_mod67 a b
  push_cast at hcast
  rcases hc with h | h | h | h | h <;> rw [h] at hcast
  · exact h17 hcast
  · exact h18 hcast
  · exact h19 hcast
  · exact h48 hcast
  · exact h49 hcast

-- NOTE: (5,13,z) at q=131 has an obstruction (12 mod 131) but requires native_decide
-- for the 131²=17161 pair search. Omitted here to maintain axiom-clean policy.
-- To include: uncomment and note Lean.reduceBool in the axiom set.

end BealHigherExpLocal
