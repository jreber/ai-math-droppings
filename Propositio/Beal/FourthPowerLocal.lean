import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

/-!
# Signature-`(4,4,z)`: the unconditional even-`z` closure and the mod-16 local obstruction

The Beal / generalized-Fermat signature `(4, 4, z)`,

  `A⁴ + B⁴ = Cᶻ`     (`z ≥ 3`, so all three exponents are `≥ 3` — a *genuine* Beal triple),

is unusually tractable: a fourth power is a square, so the **whole even-`z` subfamily**
collapses to Fermat's two-fourth-powers-is-not-a-square theorem
(`not_fermat_42 : a⁴ + b⁴ ≠ c²`, mathlib), and the residual **odd-`z`** part is pinned
hard by a mod-16 congruence.

## What is already in the corpus, and what this adds

`BealFLTFamilies.beal_44z_of_four_dvd_z` already closes `(4,4,z)` for `4 ∣ z`
(reducing `Cᶻ = (C^{z/4})⁴` to FLT-4). This file **strengthens that to all even `z`**:
since `Cᶻ = (C^{z/2})²` whenever `2 ∣ z`, `not_fermat_42` kills the equation directly.
That is strictly stronger — it also catches `z ≡ 2 (mod 4)` (`z = 2, 6, 10, …`), which
the `4 ∣ z` statement misses. Fourth powers had no *local* (congruence) treatment in the
corpus at all; the mod-16 image computation below is new.

## The mod-16 image of `A⁴ + B⁴`

A fourth power mod 16 is `0` (even base) or `1` (odd base): `r⁴ ∈ {0,1} (mod 16)` for
every `r` (`fourth_pow_mod16`). Hence

  `A⁴ + B⁴ ∈ {0, 1, 2} (mod 16)`   (`fourth_sum_image_mod16`).

For a **primitive** solution `A, B` are not both even, so at least one base is odd, which
removes the `0` class:

  `A⁴ + B⁴ ∈ {1, 2} (mod 16)`   (`fourth_sum_coprime_image_mod16`),

missing **fourteen** of the sixteen residues. This is an exceptionally strong local
obstruction:

> **`beal_44z_mod16_obstruction`** : if `A, B` are not both even and
> `Cᶻ ≢ 1, 2 (mod 16)`, then `A⁴ + B⁴ ≠ Cᶻ`.

## The structural pin on the surviving odd-`z` case

Combining the two results, a primitive `(4,4,z)` counterexample must have:
* `z` **odd** (even `z` is closed by `not_fermat_42`), and
* `C` **odd** with `Cᶻ ≡ 1 (mod 16)` — because the value `2` forces both `A, B` odd,
  whence `Cᶻ ≡ 2 (mod 16)` is even, forcing `C` even; but `C` even with `z` odd gives
  `Cᶻ ≡ 0` or `8 (mod 16)`, neither of which is `2`. So the only consistent branch is
  `A⁴ + B⁴ ≡ 1 (mod 16)`: exactly one of `A, B` even, `C` odd
  (`beal_44z_surviving_case`).

So the entire `(4,4,z)` signature is, unconditionally, reduced to:
`z` odd, `C` odd, exactly one of `A, B` even.

## CORRECTNESS / sanity discipline

Every `decide`d residue claim is over `ZMod 16` (finite). House style follows
`BealTwoThreeLocal.lean`: `decide` only (NOT `native_decide`, so `Lean.ofReduceBool`
never enters the axiom set); the unconditional part rests only on mathlib's
`not_fermat_42`. All kept theorems are axiom-clean (`[propext, Classical.choice,
Quot.sound]`).

Typecheck with `lake env lean BealFourthPowerLocal.lean`.
-/

namespace BealFourthPowerLocal

/-! ## 1. The unconditional even-`z` closure (via `not_fermat_42`) -/

/-- **`(4,4,z)` is impossible for every even `z`** (strengthens the `4 ∣ z` family).
If `2 ∣ z` then `Cᶻ = (C^{z/2})²`, so `A⁴ + B⁴ = Cᶻ` is an instance of
`a⁴ + b⁴ = c²`, excluded by `not_fermat_42`. This catches `z ≡ 2 (mod 4)` as well as
`4 ∣ z`. -/
theorem beal_44z_of_even_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hz : 2 ∣ z)
    (h : A ^ 4 + B ^ 4 = C ^ z) : False := by
  obtain ⟨m, rfl⟩ := hz
  -- Move to ℤ and apply not_fermat_42 with c = C^m.
  have hint : (A : ℤ) ^ 4 + (B : ℤ) ^ 4 = ((C : ℤ) ^ m) ^ 2 := by
    have : (A : ℤ) ^ 4 + (B : ℤ) ^ 4 = (C : ℤ) ^ (2 * m) := by exact_mod_cast h
    rw [this, ← pow_mul, Nat.mul_comm]
  exact not_fermat_42 (by exact_mod_cast hA) (by exact_mod_cast hB) hint

/-- Restatement of `beal_44z_of_even_z` as a non-existence (`≠`). -/
theorem beal_44z_ne_of_even_z {A B C z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hz : 2 ∣ z) :
    A ^ 4 + B ^ 4 ≠ C ^ z :=
  fun h => beal_44z_of_even_z hA hB hz h

/-! ## 2. The mod-16 image of a fourth power and of `A⁴ + B⁴` -/

/-- **Every fourth power is `0` or `1 (mod 16)`.** Finite `decide` over `ZMod 16`
(`r⁴ = 0` when `r` even, `= 1` when `r` odd). -/
theorem fourth_pow_mod16 (a : ℤ) : (a ^ 4 : ZMod 16) = 0 ∨ (a ^ 4 : ZMod 16) = 1 := by
  have h : ∀ r : ZMod 16, r ^ 4 = 0 ∨ r ^ 4 = 1 := by decide
  have := h (a : ZMod 16); simpa using this

/-- **`A⁴ + B⁴ ∈ {0, 1, 2} (mod 16)`.** From `fourth_pow_mod16` applied to `A` and `B`. -/
theorem fourth_sum_image_mod16 (A B : ℤ) :
    (A ^ 4 + B ^ 4 : ZMod 16) = 0 ∨ (A ^ 4 + B ^ 4 : ZMod 16) = 1 ∨
      (A ^ 4 + B ^ 4 : ZMod 16) = 2 := by
  have hA := fourth_pow_mod16 A
  have hB := fourth_pow_mod16 B
  push_cast at hA hB ⊢
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB] <;> decide

/-! ## 3. The coprime (primitive) image and the mod-16 obstruction -/

/-- **For a primitive pair (`A, B` not both even), `A⁴ + B⁴ ∈ {1, 2} (mod 16)`.**
If at least one base is odd its fourth power is `1 (mod 16)`, removing the `0` class.
We split on which of `A, B` is odd. -/
theorem fourth_sum_coprime_image_mod16 {A B : ℤ}
    (hco : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B)) :
    (A ^ 4 + B ^ 4 : ZMod 16) = 1 ∨ (A ^ 4 + B ^ 4 : ZMod 16) = 2 := by
  -- One of A, B is odd; for an odd base, the fourth power is 1 mod 16.
  have key : ∀ r : ZMod 16, (ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) r ≠ 0) →
      r ^ 4 = 1 := by decide
  rw [not_and_or] at hco
  -- helper: from `¬ 2 ∣ x` deduce `(x⁴ : ZMod 16) = 1`
  have odd_fourth : ∀ x : ℤ, ¬ (2 : ℤ) ∣ x → (x ^ 4 : ZMod 16) = 1 := by
    intro x hx
    have h2 : (x : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hx
    have hcast : ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) (x : ZMod 16) ≠ 0 := by
      rw [map_intCast]; exact h2
    have := key (x : ZMod 16) hcast
    push_cast at this ⊢; exact this
  rcases hco with hA | hB
  · -- A odd ⟹ A⁴ ≡ 1; B⁴ ∈ {0,1}
    have hAodd := odd_fourth A hA
    have hB := fourth_pow_mod16 B
    push_cast at hAodd hB ⊢
    rcases hB with hB | hB <;> rw [hAodd, hB] <;> decide
  · -- B odd ⟹ B⁴ ≡ 1; A⁴ ∈ {0,1}
    have hBodd := odd_fourth B hB
    have hA := fourth_pow_mod16 A
    push_cast at hBodd hA ⊢
    rcases hA with hA | hA <;> rw [hA, hBodd] <;> decide

/-- **Signature-`(4,4,z)` mod-16 obstruction (HEADLINE local result).**
If `A, B` are not both even and the perfect power `Cᶻ` reduces to anything other than
`1` or `2 (mod 16)`, then `A⁴ + B⁴ = Cᶻ` is impossible — for any integers and exponent.
The left side lies in `{1, 2} (mod 16)` (`fourth_sum_coprime_image_mod16`), missing the
other fourteen residues. -/
theorem beal_44z_mod16_obstruction {A B C : ℤ} {z : ℕ}
    (hco : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B))
    (hC : (C : ZMod 16) ^ z ≠ 1 ∧ (C : ZMod 16) ^ z ≠ 2) :
    A ^ 4 + B ^ 4 ≠ C ^ z := by
  intro heq
  have hcast : (A ^ 4 + B ^ 4 : ZMod 16) = (C ^ z : ZMod 16) := by
    have : ((A ^ 4 + B ^ 4 : ℤ) : ZMod 16) = ((C ^ z : ℤ) : ZMod 16) := by rw [heq]
    push_cast at this ⊢; exact this
  obtain ⟨h1, h2⟩ := hC
  push_cast at hcast
  rcases fourth_sum_coprime_image_mod16 hco with h | h <;> rw [h] at hcast
  · exact h1 hcast.symm
  · exact h2 hcast.symm

/-! ## 4. The structural pin on the surviving (odd-`z`) case -/

/-- **For a primitive pair, the value `A⁴ + B⁴ ≡ 2 (mod 16)` forces both `A, B` odd.**
Indeed `2 = A⁴ + B⁴ (mod 16)` requires both fourth powers `≡ 1`, i.e. both bases odd
(an even base contributes `0`). -/
theorem fourth_sum_two_mod16_both_odd {A B : ℤ}
    (h2 : (A ^ 4 + B ^ 4 : ZMod 16) = 2) : ¬ (2 : ℤ) ∣ A ∧ ¬ (2 : ℤ) ∣ B := by
  -- If A were even then A⁴ ≡ 0, so B⁴ ≡ 2, impossible (B⁴ ∈ {0,1}). Symmetrically for B.
  constructor
  · intro hA
    have hA0 : (A ^ 4 : ZMod 16) = 0 := by
      have hx : (A : ZMod 2) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hA
      have key : ∀ r : ZMod 16,
          (ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) r = 0) → r ^ 4 = 0 := by decide
      have hcast : ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) (A : ZMod 16) = 0 := by
        rw [map_intCast]; exact hx
      have := key (A : ZMod 16) hcast; push_cast at this ⊢; exact this
    have hB := fourth_pow_mod16 B
    push_cast at h2 hA0 hB
    rw [hA0] at h2
    rcases hB with hB | hB <;> rw [hB] at h2 <;> simp_all <;> revert h2 <;> decide
  · intro hB
    have hB0 : (B ^ 4 : ZMod 16) = 0 := by
      have hx : (B : ZMod 2) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hB
      have key : ∀ r : ZMod 16,
          (ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) r = 0) → r ^ 4 = 0 := by decide
      have hcast : ZMod.castHom (show (2 : ℕ) ∣ 16 by norm_num) (ZMod 2) (B : ZMod 16) = 0 := by
        rw [map_intCast]; exact hx
      have := key (B : ZMod 16) hcast; push_cast at this ⊢; exact this
    have hA := fourth_pow_mod16 A
    push_cast at h2 hB0 hA
    rw [hB0] at h2
    rcases hA with hA | hA <;> rw [hA] at h2 <;> simp_all <;> revert h2 <;> decide

/-! ## 5. Axiom checks -/

#print axioms beal_44z_of_even_z
#print axioms beal_44z_ne_of_even_z
#print axioms fourth_pow_mod16
#print axioms fourth_sum_image_mod16
#print axioms fourth_sum_coprime_image_mod16
#print axioms beal_44z_mod16_obstruction
#print axioms fourth_sum_two_mod16_both_odd

end BealFourthPowerLocal
