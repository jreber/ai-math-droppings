import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Beal cube-sum local obstruction mod 9 — "Case 1" cube-residue constraint

The elementary, fully **unconditional** local input for the cube-sum equation
`A^3 + B^3 = C^z` that complements the `ℤ[ζ₃]` ("Eisenstein") descent.

## The residue arithmetic

Cubes modulo `9` take only the values `{0, 1, 8} = {0, ±1}`:

* if `3 ∣ n` then `27 ∣ n^3`, so in particular `n^3 ≡ 0 (mod 9)`;
* if `3 ∤ n` then `n^3 ≡ ±1 (mod 9)`.

The reason is that the unit group `(ℤ/9)^×` is cyclic of order `6`, so cubing
maps it onto the subgroup of order `2`, namely `{1, 8} = {±1}`.

Consequently a **sum of two coprime-to-3 cubes** is pinned:
`A^3 + B^3 ≡ (±1) + (±1) ∈ {0, 2, 7} (mod 9)` (`cube_sum_residues`).

## What is and is not obstructed (CORRECTNESS NOTE)

A *fully unconditional* "Case 1" obstruction — `3 ∤ A·B·C ⟹ A^3 + B^3 ≠ C^z` for
**every** exponent `z ≥ 1` — is **FALSE**. The achievable residues of `C^z` for
`3 ∤ C` range over the whole unit group `{1,2,4,5,7,8}` mod 9 (it is cyclic of
order 6), which *does* meet the left-hand set `{0,2,7}` in `{2,7}`. Concrete
counterexamples (genuine integer equations with `3 ∤ A·B·C`):

* `1^3 + 1^3 = 2 = 2^1` (`z = 1`);
* `2^3 + 2^3 = 16 = 2^4` (`z = 4 ≥ 3`).

So neither dropping the exponent bound nor demanding `z ≥ 3` rescues the bare
mod-9 argument: the residues genuinely overlap.

The **sharp clean obstruction** that *is* unconditional adds the hypothesis
`3 ∣ z`. When `3 ∣ z` the right-hand side `C^z = (C^(z/3))^3` is itself a cube,
so for `3 ∤ C` it lies in `{1, 8} (mod 9)`, which is **disjoint** from the
left-hand set `{0, 2, 7}`. Hence:

> **`case_one_obstruction`** : if `3 ∣ z`, `3 ∤ A`, `3 ∤ B`, `3 ∤ C` then
> `A^3 + B^3 ≠ C^z`.

In the Beal cube-sum descent the relevant branch is exactly `z` a multiple of `3`
(the equation `A^3 + B^3 = C^z` reduced to the cube exponent), so this is the
local input that forces `3 ∣ A·B·C` — i.e. one always lands in the "`3 ∣ C`"
regime handled by the `ℤ[ζ₃]` descent (Case 2). The residual case the mod-9
argument cannot reach is `3 ∤ z` with `C^z ∈ {2,7} (mod 9)`; that case requires
the algebraic (cyclotomic) descent, not a local congruence.

All facts here are finite computations over `ZMod 9`, discharged by `decide`
(NOT `native_decide`, so no `Lean.ofReduceBool` enters the axiom set). House
style follows `BealModEight.lean` / `BealEisenstein.lean`.

Typecheck with `lake env lean BealCubeMod9.lean`.

Key mathlib lemmas relied on:
* `decide` — the finite `ZMod 9` residue computations.
* `ZMod.intCast_zmod_eq_zero_iff_dvd` — bridge `(x : ZMod n) = 0 ↔ (n:ℤ) ∣ x`.
* `pow_mul`, `one_pow` — power bookkeeping over `ZMod 9`.
-/

namespace BealCubeMod9

/-! ## 1. Cube residues mod 9 -/

/-- **Every cube is `0`, `1`, or `8` mod 9.**
The cube of any integer `n` reduces mod 9 to one of `{0, 1, 8} = {0, ±1}`.
Proof: push the cube onto `(n : ZMod 9)` and `decide` the finite statement
`∀ r : ZMod 9, r^3 = 0 ∨ r^3 = 1 ∨ r^3 = 8`. -/
theorem cube_residue_mod9 (n : ℤ) :
    (n ^ 3 : ZMod 9) = 0 ∨ (n ^ 3 : ZMod 9) = 1 ∨ (n ^ 3 : ZMod 9) = 8 := by
  have h : ∀ r : ZMod 9, r ^ 3 = 0 ∨ r ^ 3 = 1 ∨ r ^ 3 = 8 := by decide
  have := h (n : ZMod 9)
  simpa using this

/-- **For `3 ∤ n`, the cube is `±1` mod 9.**
If `3` does not divide `n` then `n^3 ≡ 1` or `n^3 ≡ 8 (mod 9)` — the value `0` is
excluded. The hypothesis `3 ∤ n` is transported to `(n : ZMod 9) ∉ {0,3,6}` via
`(n : ZMod 3) ≠ 0`, after which the residue fact is a finite `decide`. -/
theorem cube_not_dvd_three_mod9 {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) :
    (n ^ 3 : ZMod 9) = 1 ∨ (n ^ 3 : ZMod 9) = 8 := by
  -- Among the three possible cube residues `{0,1,8}`, rule out `0`: a cube
  -- `≡ 0 (mod 9)` means `9 ∣ n^3`, hence `3 ∣ n^3`, hence (3 prime) `3 ∣ n`.
  rcases cube_residue_mod9 n with h0 | h1 | h8
  · exfalso
    apply h
    have hdvd : (9 : ℤ) ∣ n ^ 3 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 3) 9).mp (by push_cast at h0 ⊢; exact h0)
      exact_mod_cast this
    have h3 : (3 : ℤ) ∣ n ^ 3 := dvd_trans (by norm_num) hdvd
    exact (Int.Prime.dvd_pow' (by norm_num) h3)
  · exact Or.inl h1
  · exact Or.inr h8

/-! ## 2. The sum-of-two-coprime-cubes residue constraint -/

/-- **Sum of two coprime-to-3 cubes is `0`, `2`, or `7` mod 9** (deliverable 4).
For `3 ∤ A` and `3 ∤ B`, `A^3 + B^3 ≡ 0`, `2`, or `7 (mod 9)`. Indeed each cube
is `±1` (`cube_not_dvd_three_mod9`), so the sum is in `{(±1)+(±1)} = {2,0,7}`. -/
theorem cube_sum_residues {A B : ℤ} (hA : ¬ (3 : ℤ) ∣ A) (hB : ¬ (3 : ℤ) ∣ B) :
    (A ^ 3 + B ^ 3 : ZMod 9) = 0 ∨ (A ^ 3 + B ^ 3 : ZMod 9) = 2 ∨
      (A ^ 3 + B ^ 3 : ZMod 9) = 7 := by
  have hA' := cube_not_dvd_three_mod9 hA
  have hB' := cube_not_dvd_three_mod9 hB
  push_cast at hA' hB' ⊢
  rcases hA' with ha | ha <;> rcases hB' with hb | hb <;>
    rw [ha, hb] <;> decide

/-! ## 3. The right-hand side when `3 ∣ z`: a cube residue -/

/-- **For `3 ∤ C` and `3 ∣ z`, `C^z` is `±1` mod 9.**
If `z = 3*k` then `C^z = (C^k)^3` is a perfect cube, so by
`cube_not_dvd_three_mod9` (applied to `C^k`, which is also coprime to 3) it lies
in `{1, 8} (mod 9)`. -/
theorem powz_dvd_three_mod9 {C : ℤ} {z : ℕ} (hz : (3 : ℕ) ∣ z)
    (hC : ¬ (3 : ℤ) ∣ C) : (C ^ z : ZMod 9) = 1 ∨ (C ^ z : ZMod 9) = 8 := by
  obtain ⟨k, rfl⟩ := hz
  -- `C^(3*k) = (C^k)^3`, and `C^k` is also coprime to 3.
  have hck : ¬ (3 : ℤ) ∣ C ^ k := by
    intro hdvd
    exact hC (Int.Prime.dvd_pow' (by norm_num) hdvd)
  have hcube := cube_not_dvd_three_mod9 hck
  -- `(C^(3*k) : ZMod 9) = ((C^k)^3 : ZMod 9)`, matching the cube residue fact.
  have heq : ((C : ZMod 9)) ^ (3 * k) = ((C ^ k : ℤ) : ZMod 9) ^ 3 := by
    push_cast; rw [← pow_mul, mul_comm]
  rw [heq]
  exact hcube

/-! ## 4. HEADLINE: the Case-1 obstruction (with `3 ∣ z`) -/

/-- **Case-1 mod-9 obstruction (HEADLINE).**
If `3 ∣ z`, `3 ∤ A`, `3 ∤ B`, `3 ∤ C` then `A^3 + B^3 ≠ C^z`.

The left-hand residue lies in `{0, 2, 7}` (`cube_sum_residues`); the right-hand
residue, since `3 ∣ z` makes `C^z` a cube of a unit, lies in `{1, 8}`
(`powz_dvd_three_mod9`). These two sets are **disjoint**, so the equation is
impossible mod 9.

**Correctness scope.** The hypothesis `3 ∣ z` is *necessary*: with `3 ∤ z` the
bare mod-9 argument fails (e.g. `1^3 + 1^3 = 2^1` and `2^3 + 2^3 = 2^4`, both with
`3 ∤ A·B·C`). See the module doc. In the cube-sum descent `z` is the cube
exponent (a multiple of 3 after reduction), so this hypothesis is exactly the
operative branch, and the conclusion forces `3 ∣ A·B·C` — the input to the
`ℤ[ζ₃]` descent (Case 2). -/
theorem case_one_obstruction {A B C : ℤ} {z : ℕ} (hz : (3 : ℕ) ∣ z)
    (hA : ¬ (3 : ℤ) ∣ A) (hB : ¬ (3 : ℤ) ∣ B) (hC : ¬ (3 : ℤ) ∣ C) :
    A ^ 3 + B ^ 3 ≠ C ^ z := by
  intro heq
  have hlhs := cube_sum_residues hA hB
  have hrhs := powz_dvd_three_mod9 hz hC
  -- Cast the integer equation to `ZMod 9`.
  have hcast : (A ^ 3 + B ^ 3 : ZMod 9) = (C ^ z : ZMod 9) := by
    have : ((A ^ 3 + B ^ 3 : ℤ) : ZMod 9) = ((C ^ z : ℤ) : ZMod 9) := by rw [heq]
    push_cast at this ⊢; exact this
  rw [hcast] at hlhs
  -- Now `C^z ∈ {0,2,7}` and `C^z ∈ {1,8}`; contradiction by cases.
  rcases hrhs with hr | hr <;> rw [hr] at hlhs <;> revert hlhs <;> decide

end BealCubeMod9
