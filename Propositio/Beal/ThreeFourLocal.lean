import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Signature-`(3,4,z)` local obstruction at the prime 13

The mixed Beal signature `(3, 4, z)` (`a³ + b⁴ = cᶻ`, all exponents `≥ 3` — a genuine
Beal triple) had **no** local-obstruction treatment in the corpus; the existing local
files cover `(2,3,n)`, `(3,3,z)`, `(5,5,z)` and `(4,4,z)`. This file adds the cleanest
obstruction for it, at the prime `p = 13`.

## Why 13, and why it needs no coprimality hypothesis

Cubes mod 13 are `{0, ±1, ±5}` and fourth powers mod 13 are `{0, 1, 3, 9}` (the quartic
residues — `4 ∣ 12 = |(ZMod 13)ˣ|`, so there are only `12/4 = 3` nonzero quartic
residues). Their sumset misses exactly **one** residue:

  `a³ + b⁴ ∈ {0,1,2,3,4,5,6,8,9,10,11,12} (mod 13)`,  i.e. **never `≡ 7 (mod 13)`**

(`threefour_notMem_seven_mod13`) — and this holds for **all** integers `a, b`, with no
coprimality hypothesis. (Contrast `(2,3,n)`, where the bare sum is surjective mod every
`m` and only the `a`-odd restriction creates a gap.) The other natural moduli give no
bare obstruction here: `a³ + b⁴` is surjective mod `16`, `9`, and `7` (checked below),
which is exactly why 13 is the productive prime.

> **`beal_34z_mod13_obstruction`** : if `cᶻ ≡ 7 (mod 13)` then `a³ + b⁴ ≠ cᶻ`.

This is non-vacuous: `7` is a genuine perfect-power residue, e.g. `11⁵ ≡ (−2)⁵ = −32 ≡
7 (mod 13)` (so `c ≡ 11, z = 5` lands on the forbidden class on the right), yet the left
side can never reach it.

## Sharpening under coprimality

If additionally `13 ∤ a` and `13 ∤ b` (the operative case for a primitive solution at the
prime 13), the image shrinks to `{0,1,2,4,6,8,9,10,11}`, missing the **four** classes
`{3, 5, 7, 12}` (`threefour_coprime_notMem_mod13`) — four forbidden residues instead of
one.

## CORRECTNESS / sanity discipline

Every forbidden class was first found by `#eval` enumeration over the relevant `ZMod 13`
image before any `≠` was asserted (the bare image is `{0..12} \ {7}`; the coprime image
is `{0..12} \ {3,5,7,12}`), and the bare surjectivity mod `16, 9, 7` was likewise checked
so no false "obstruction" is claimed for those. All finite facts use `decide` (NOT
`native_decide`, so `Lean.ofReduceBool` never enters the axiom set). House style follows
`BealTwoThreeLocal.lean` / `BealFourthPowerLocal.lean`; all theorems are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

Typecheck with `lake env lean BealThreeFourLocal.lean`.
-/

namespace BealThreeFourLocal

/-! ## 1. The bare mod-13 gap: `a³ + b⁴ ≠ 7` -/

/-- **`a³ + b⁴` is never `≡ 7 (mod 13)`** — for *all* integers `a, b` (no coprimality).
The full image of `(a,b) ↦ a³ + b⁴` over `ZMod 13` is `{0,…,12} \ {7}`; a finite
`decide` over the `13 × 13` grid. -/
theorem threefour_notMem_seven_mod13 (a b : ℤ) : (a ^ 3 + b ^ 4 : ZMod 13) ≠ 7 := by
  have h : ∀ r s : ZMod 13, r ^ 3 + s ^ 4 ≠ 7 := by decide
  have := h (a : ZMod 13) (b : ZMod 13)
  simpa using this

/-- **Signature-`(3,4,z)` mod-13 obstruction (HEADLINE).**
If the perfect power `cᶻ` reduces to `7 (mod 13)`, then `a³ + b⁴ = cᶻ` is impossible —
for any integers `a, b, c` and exponent `z`, with no coprimality assumption. The
forbidden class `cᶻ ≡ 7` is achievable on the right (`c ≡ 11`, `z = 5`: `11⁵ ≡ 7`), so
this is a genuine local obstruction. -/
theorem beal_34z_mod13_obstruction {a b c : ℤ} {z : ℕ}
    (hc : (c : ZMod 13) ^ z = 7) : a ^ 3 + b ^ 4 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 4 : ZMod 13) = (c ^ z : ZMod 13) := by
    have : ((a ^ 3 + b ^ 4 : ℤ) : ZMod 13) = ((c ^ z : ℤ) : ZMod 13) := by rw [heq]
    push_cast at this ⊢; exact this
  have hne := threefour_notMem_seven_mod13 a b
  push_cast at hcast hne
  rw [hcast, hc] at hne
  exact hne rfl

/-! ## 2. Sharpening: the coprime image misses four classes -/

/-- **For `13 ∤ a` and `13 ∤ b`, `a³ + b⁴` avoids `{3, 5, 7, 12} (mod 13)`.**
With both bases units mod 13, `a³ ∈ {1,5,8,12}` and `b⁴ ∈ {1,3,9}`, and the sumset
omits the four classes `{3,5,7,12}`. The hypotheses are transported to
`(a : ZMod 13) ≠ 0`, `(b : ZMod 13) ≠ 0`, then a finite `decide`. -/
theorem threefour_coprime_notMem_mod13 {a b : ℤ}
    (ha : ¬ (13 : ℤ) ∣ a) (hb : ¬ (13 : ℤ) ∣ b) :
    (a ^ 3 + b ^ 4 : ZMod 13) ≠ 3 ∧ (a ^ 3 + b ^ 4 : ZMod 13) ≠ 5 ∧
      (a ^ 3 + b ^ 4 : ZMod 13) ≠ 7 ∧ (a ^ 3 + b ^ 4 : ZMod 13) ≠ 12 := by
  have ha0 : (a : ZMod 13) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha
  have hb0 : (b : ZMod 13) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hb
  have key : ∀ r s : ZMod 13, r ≠ 0 → s ≠ 0 →
      r ^ 3 + s ^ 4 ≠ 3 ∧ r ^ 3 + s ^ 4 ≠ 5 ∧ r ^ 3 + s ^ 4 ≠ 7 ∧ r ^ 3 + s ^ 4 ≠ 12 := by
    decide
  have := key (a : ZMod 13) (b : ZMod 13) ha0 hb0
  push_cast at this
  exact this

/-- **Sharper mod-13 obstruction under coprimality.**
If `13 ∤ a`, `13 ∤ b` and `cᶻ ≡ 3, 5, 7, or 12 (mod 13)`, then `a³ + b⁴ ≠ cᶻ` —
four forbidden right-hand classes instead of one. -/
theorem beal_34z_mod13_obstruction_coprime {a b c : ℤ} {z : ℕ}
    (ha : ¬ (13 : ℤ) ∣ a) (hb : ¬ (13 : ℤ) ∣ b)
    (hc : (c : ZMod 13) ^ z = 3 ∨ (c : ZMod 13) ^ z = 5 ∨
          (c : ZMod 13) ^ z = 7 ∨ (c : ZMod 13) ^ z = 12) :
    a ^ 3 + b ^ 4 ≠ c ^ z := by
  intro heq
  have hcast : (a ^ 3 + b ^ 4 : ZMod 13) = (c ^ z : ZMod 13) := by
    have : ((a ^ 3 + b ^ 4 : ℤ) : ZMod 13) = ((c ^ z : ℤ) : ZMod 13) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h3, h5, h7, h12⟩ := threefour_coprime_notMem_mod13 ha hb
  push_cast at hcast
  rcases hc with h | h | h | h <;> rw [h] at hcast
  · exact h3 hcast
  · exact h5 hcast
  · exact h7 hcast
  · exact h12 hcast

/-! ## 3. Axiom checks -/

#print axioms threefour_notMem_seven_mod13
#print axioms beal_34z_mod13_obstruction
#print axioms threefour_coprime_notMem_mod13
#print axioms beal_34z_mod13_obstruction_coprime

end BealThreeFourLocal
