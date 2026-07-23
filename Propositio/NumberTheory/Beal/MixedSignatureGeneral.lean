import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# A parametric local obstruction for any mixed Beal signature

The files `BealThreeFourLocal`, `BealFifthMixedLocal`, `BealTwoThreeLocal`, `BealCubeMod9`,
… each prove a *specific* obstruction "`a^i + b^j` misses a residue mod `q`, so the
equation cannot hold when `c^z` lands on it." This file extracts the **one reusable
theorem** behind all of them (the B3 "build once, every instance falls" pattern): given
the purely-local fact that `a^i + b^j` never equals a residue `f` over `ZMod q`, the Beal
equation `A^i + B^j = C^z` is impossible whenever `C^z ≡ f (mod q)`.

The local input `hmiss : ∀ a b : ZMod q, a^i + b^j ≠ f` is **decidable** for any concrete
`(i, j, q, f)` — a single `by decide` — so every present and future small-prime
mixed-signature obstruction is a two-line instance of `mixed_signature_obstruction`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

Typecheck with `lake env lean BealMixedSignatureGeneral.lean`.
-/

namespace BealMixedSignatureGeneral

/-- **Parametric mixed-signature local obstruction.**

If, over `ZMod q`, the sum of an `i`-th power and a `j`-th power never equals the residue
`f` (`hmiss`), then the integer equation `A^i + B^j = C^z` cannot hold whenever
`C^z ≡ f (mod q)`. The hypothesis `hmiss` is a finite `decide` for concrete `i, j, q, f`;
this theorem turns it into a statement about all integers `A, B, C` and exponents `z`. -/
theorem mixed_signature_obstruction {i j q : ℕ} {f : ZMod q}
    (hmiss : ∀ a b : ZMod q, a ^ i + b ^ j ≠ f)
    {A B C : ℤ} {z : ℕ} (hc : (C : ZMod q) ^ z = f) :
    A ^ i + B ^ j ≠ C ^ z := by
  intro heq
  have hcast : ((A : ZMod q) ^ i + (B : ZMod q) ^ j) = (C : ZMod q) ^ z := by
    have h : ((A ^ i + B ^ j : ℤ) : ZMod q) = ((C ^ z : ℤ) : ZMod q) := by rw [heq]
    push_cast at h; exact h
  rw [hc] at hcast
  exact hmiss (A : ZMod q) (B : ZMod q) hcast

/-! ## Demonstration: the per-signature obstructions are two-line instances -/

/-- `(3,4,z)` at `p = 13` — recovered from the general theorem (cf.
`BealThreeFourLocal.beal_34z_mod13_obstruction`). -/
example {A B C : ℤ} {z : ℕ} (hc : (C : ZMod 13) ^ z = 7) : A ^ 3 + B ^ 4 ≠ C ^ z :=
  mixed_signature_obstruction (by decide) hc

/-- `(4,5,z)` at `p = 11` — recovered from the general theorem. -/
example {A B C : ℤ} {z : ℕ} (hc : (C : ZMod 11) ^ z = 7) : A ^ 4 + B ^ 5 ≠ C ^ z :=
  mixed_signature_obstruction (by decide) hc

/-- `(3,5,z)` at `p = 31` — recovered from the general theorem (cf.
`BealFifthMixedLocal.beal_35z_mod31_obstruction`). -/
example {A B C : ℤ} {z : ℕ} (hc : (C : ZMod 31) ^ z = 12) : A ^ 3 + B ^ 5 ≠ C ^ z :=
  mixed_signature_obstruction (by decide) hc

#print axioms mixed_signature_obstruction

end BealMixedSignatureGeneral
