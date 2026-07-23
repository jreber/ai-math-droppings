import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.MixedSignatureGeneral
import Propositio.Tactics

/-!
# Signature-`(2,4,n)` local obstruction (Ellenberg's `x² + y⁴ = zⁿ`)

Completes the small mixed/generalized-Fermat signature census. Unlike `(2,3,n)` (whose
bare sum is surjective mod everything), `(2,4,n)` carries a **bare** 2-adic obstruction:
fourth powers are `0, 1 (mod 8)` and squares are `0, 1, 4 (mod 8)`, so

  `a² + b⁴ ∈ {0, 1, 2, 4, 5} (mod 8)`,  i.e. **never `≡ 3, 6, 7 (mod 8)`**

(`twofour_notMem_mod8`) — for all integers `a, b`. The classes `3, 7` are achievable
`cⁿ`-residues (`c ≡ 3, 7 (mod 8)`, `n` odd), giving genuine obstructions; the bare ones
are immediate instances of the parametric `BealMixedSignatureGeneral.mixed_signature_obstruction`.

Sharpening with `a` odd (the operative branch when `cⁿ` is even): `a² ≡ 1 (mod 8)`, so
`a² + b⁴ ∈ {1, 2} (mod 8)` (`twofour_odd_a_image_mod8`), missing **six** residues.

All finite facts use `decide` (NOT `native_decide`). Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). House style follows `BealTwoThreeLocal.lean`.
-/

namespace BealTwoFourLocal

open BealMixedSignatureGeneral (mixed_signature_obstruction)

/-! ## 1. The bare mod-8 obstruction -/

/-- **`a² + b⁴` avoids `{3, 6, 7} (mod 8)`** — for all integers `a, b` (no coprimality).
Finite `decide`; the image is `{0,1,2,4,5}`. -/
theorem twofour_notMem_mod8 (a b : ℤ) :
    (a ^ 2 + b ^ 4 : ZMod 8) ≠ 3 ∧ (a ^ 2 + b ^ 4 : ZMod 8) ≠ 6 ∧
      (a ^ 2 + b ^ 4 : ZMod 8) ≠ 7 := by
  have h : ∀ r s : ZMod 8, r ^ 2 + s ^ 4 ≠ 3 ∧ r ^ 2 + s ^ 4 ≠ 6 ∧ r ^ 2 + s ^ 4 ≠ 7 := by decide
  have := h (a : ZMod 8) (b : ZMod 8)
  push_cast_exact

/-- **Signature-`(2,4,n)` bare mod-8 obstruction.** If `cⁿ ≡ 3 or 7 (mod 8)` then
`a² + b⁴ ≠ cⁿ`, for any integers (no coprimality). A direct instance of the parametric
`mixed_signature_obstruction`. The classes `3, 7` are achievable (`c ≡ 3, 7`, `n` odd). -/
theorem beal_24n_mod8_obstruction {a b c : ℤ} {n : ℕ}
    (hc : (c : ZMod 8) ^ n = 3 ∨ (c : ZMod 8) ^ n = 7) :
    a ^ 2 + b ^ 4 ≠ c ^ n := by
  rcases hc with h | h
  · exact mixed_signature_obstruction (by decide) h
  · exact mixed_signature_obstruction (by decide) h

/-! ## 2. Sharpening with `a` odd -/

/-- **For `a` odd, `a² + b⁴ ∈ {1, 2} (mod 8)`** — missing six residues. Since `a² ≡ 1`
and `b⁴ ∈ {0, 1}`. The hypothesis `2 ∤ a` is transported to `(a : ZMod 2) ≠ 0`. -/
theorem twofour_odd_a_image_mod8 {a b : ℤ} (ha : ¬ (2 : ℤ) ∣ a) :
    (a ^ 2 + b ^ 4 : ZMod 8) = 1 ∨ (a ^ 2 + b ^ 4 : ZMod 8) = 2 := by
  have h2 : (a : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast ha
  have key : ∀ r s : ZMod 8, (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) r ≠ 0) →
      r ^ 2 + s ^ 4 = 1 ∨ r ^ 2 + s ^ 4 = 2 := by decide
  have hcast : ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2) (a : ZMod 8) ≠ 0 := by
    rw [map_intCast]; exact h2
  have := key (a : ZMod 8) (b : ZMod 8) hcast
  push_cast_exact

/-- **Sharper `(2,4,n)` mod-8 obstruction for `a` odd.** If `a` is odd and
`cⁿ ∉ {1, 2} (mod 8)` (i.e. `cⁿ ≡ 0,3,4,5,6,7`), then `a² + b⁴ ≠ cⁿ`. -/
theorem beal_24n_mod8_obstruction_odd {a b c : ℤ} {n : ℕ} (ha : ¬ (2 : ℤ) ∣ a)
    (hc : (c : ZMod 8) ^ n ≠ 1 ∧ (c : ZMod 8) ^ n ≠ 2) :
    a ^ 2 + b ^ 4 ≠ c ^ n := by
  intro heq
  have hcast : (a ^ 2 + b ^ 4 : ZMod 8) = (c ^ n : ZMod 8) := by
    have : ((a ^ 2 + b ^ 4 : ℤ) : ZMod 8) = ((c ^ n : ℤ) : ZMod 8) := by rw [heq]
    push_cast_exact
  obtain ⟨h1, h2⟩ := hc
  push_cast at hcast
  rcases twofour_odd_a_image_mod8 (a := a) (b := b) ha with h | h <;> rw [h] at hcast
  · exact h1 hcast.symm
  · exact h2 hcast.symm

#print axioms beal_24n_mod8_obstruction
#print axioms beal_24n_mod8_obstruction_odd

end BealTwoFourLocal
