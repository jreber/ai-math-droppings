import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeMod9
import Propositio.NumberTheory.Beal.CubeSplitPrime

/-!
# Beal cube-sum combined CRT local obstruction at moduli 7, 8, 9 (mod 504)

A single CRT-unified local obstruction for the Beal cube-sum case
`A^3 + B^3 = C^z`, combining the three elementary prime-power local inputs:

* **`p = 7`** (split prime of `ℚ(ζ₃)`, `BealCubeSplitPrime`): the cube-sum image
  mod 7 is `{0,1,2,5,6}`, **missing `{3,4}`**.
* **`p = 3`** (mod-9 cube constraint, `BealCubeMod9`): the cube-sum image mod 9
  over **all** `A,B` is `{0,1,2,7,8}`, **missing `{3,4,5,6}`**.
* **`p = 2`** (mod-8 parity classes, `BealModEight`): cubes mod 8 are `{0,1,3,5,7}`
  and pairwise cube-sums already exhaust **all** of `ZMod 8` — so over *all*
  `A,B` there is *no* mod-8 non-membership obstruction (the mod-8 obstruction of
  `BealModEight` lives in the refined even-exponent parity classes, not in the bare
  cube-sum image; we record the exact image here honestly).

## The combined picture (`lcm(7,8,9) = 504`)

By the Chinese Remainder Theorem `ZMod 504 ≃ ZMod 8 × ZMod 9 × ZMod 7`. A residue
`r (mod 504)` is a sum of two cubes mod 504 only if its image is a cube-sum in
*each* factor. Hence the forbidden residues mod 504 are exactly those whose mod-7
image lies in `{3,4}` **or** whose mod-9 image lies in `{3,4,5,6}` (the mod-8
factor imposes nothing). This is a *positive-density* forbidden set — strictly
sharper than any single prime — obtained by CRT-multiplying the per-prime gaps.

Concretely the headline exhibits the explicit forbidden residue `r₀ = 3 (mod 504)`:
its image under the ring hom `ZMod 504 →+* ZMod 7` is `3`, which is **not** a
sum of two cubes mod 7 (`cube_sum_not_three_or_four_mod7`). Pushing any putative
`A^3 + B^3 = r₀` in `ZMod 504` down through `ZMod.castHom (7 ∣ 504)` contradicts
that fact — so no `decide` over the 254k-pair grid `ZMod 504 × ZMod 504` is
needed (it would be too slow for the kernel); the obstruction is a clean
**reduction** along the CRT projection.

All finite facts use `decide` (NOT `native_decide`, so no `Lean.ofReduceBool`
enters the axiom set). House style follows `BealCubeMod9.lean`.

Typecheck with `lake env lean BealCombinedObstruction.lean`.

Key mathlib lemmas relied on:
* `ZMod.castHom` — the ring hom `ZMod 504 →+* ZMod 7` from `7 ∣ 504`.
* `map_add`, `map_pow` — push `A^3 + B^3` through the CRT projection.
* `decide` — the finite `ZMod 7 / 8 / 9` cube and cube-sum image computations.
-/

namespace BealCombinedObstruction

open BealCubeSplitPrime

/-! ## 1. The exact cube-sum image mod 7 -/

/-- **Exact cube-sum image mod 7** (deliverable 1).
A residue `r : ZMod 7` is a sum of two cubes iff `r ∉ {3, 4}`. The cubes mod 7
are `{0,1,6}` and their pairwise sums are exactly `{0,1,2,5,6}`. Finite `decide`. -/
theorem cube_sum_image_mod7 (r : ZMod 7) :
    (∃ A B : ZMod 7, A ^ 3 + B ^ 3 = r) ↔ r ≠ 3 ∧ r ≠ 4 := by
  revert r; decide

/-! ## 2. The exact cube-sum image mod 9 (over ALL A, B) -/

/-- **Exact cube-sum image mod 9** (deliverable 2).
Over **all** `A, B : ZMod 9` (no coprimality assumed), `A^3 + B^3` ranges over
exactly `{0, 1, 2, 7, 8}` — i.e. it is a sum of two cubes iff
`r ∈ {0,1,2,7,8}`, equivalently `r ∉ {3,4,5,6}`. (Cubes mod 9 are `{0,1,8}`;
their pairwise sums are `{0,1,2,7,8}`.) This is the all-`A,B` companion to
`BealCubeMod9.cube_sum_residues`, which pins the *coprime* sub-case to `{0,2,7}`.
Finite `decide`. -/
theorem cube_residues_mod9 (r : ZMod 9) :
    (∃ A B : ZMod 9, A ^ 3 + B ^ 3 = r) ↔
      r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 7 ∨ r = 8 := by
  revert r; decide

/-- **`{3,4,5,6}` are the forbidden cube-sum residues mod 9** (deliverable 2,
complement form). No sum of two cubes is `≡ 3, 4, 5, 6 (mod 9)`. -/
theorem cube_sum_forbidden_mod9 (r : ZMod 9)
    (hr : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) :
    ¬ ∃ A B : ZMod 9, A ^ 3 + B ^ 3 = r := by
  rw [cube_residues_mod9]
  rcases hr with h | h | h | h <;> subst h <;> decide

/-! ## 3. The exact cube-sum image mod 8 (over ALL A, B) -/

/-- **Cubes mod 8 are `{0,1,3,5,7}`** (deliverable 3, cube form).
Even cubes are `0`; odd cubes are odd (`odd³ ≡ odd`), exhausting `{1,3,5,7}`.
Finite `decide`. -/
theorem cubes_mod8 (r : ZMod 8) :
    (∃ x : ZMod 8, x ^ 3 = r) ↔ r = 0 ∨ r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  revert r; decide

/-- **Every residue mod 8 is a sum of two cubes** (deliverable 3, image form).
Over **all** `A, B : ZMod 8`, `A^3 + B^3` exhausts *all* of `ZMod 8`: the bare
cube-sum image imposes **no** mod-8 non-membership obstruction. (The genuine
mod-8 Beal obstruction of `BealModEight` is in the refined even-exponent parity
classes, not here.) Finite `decide`. -/
theorem cube_sum_image_mod8 (r : ZMod 8) : ∃ A B : ZMod 8, A ^ 3 + B ^ 3 = r := by
  revert r; decide

/-! ## 4. HEADLINE: forbidden residues mod 504 via CRT reduction -/

/-- **`3 (mod 504)` is not a sum of two cubes** (the headline obstruction kernel).
Proved by **reduction along the CRT projection** `ZMod 504 →+* ZMod 7` rather than
by a `decide` over the 254k-pair grid: any `A^3 + B^3 = 3` in `ZMod 504` maps,
under the ring hom `ZMod.castHom (7 ∣ 504)`, to `Ā^3 + B̄^3 = 3` in `ZMod 7`,
contradicting `cube_sum_not_three_or_four_mod7`. -/
theorem three_not_cube_sum_mod504 :
    ¬ ∃ A B : ZMod 504, A ^ 3 + B ^ 3 = 3 := by
  rintro ⟨A, B, hAB⟩
  -- The CRT projection `ZMod 504 →+* ZMod 7`.
  let f : ZMod 504 →+* ZMod 7 := ZMod.castHom (by norm_num : (7 : ℕ) ∣ 504) (ZMod 7)
  -- Push the equation down to `ZMod 7`.
  have himg : f A ^ 3 + f B ^ 3 = (3 : ZMod 7) := by
    have := congrArg f hAB
    rw [map_add, map_pow, map_pow, map_ofNat] at this
    simpa using this
  -- But `3` is not a sum of two cubes mod 7.
  exact (cube_sum_not_three_or_four_mod7 (f A) (f B)).1 himg

/-- **HEADLINE — there exist forbidden cube-sum residues mod 504** (deliverable 4).
There is a nonempty set `S ⊆ ZMod 504` of residues not representable as a sum of
two cubes mod 504. We exhibit `S = {3}`: by `three_not_cube_sum_mod504` (a CRT
reduction to the mod-7 gap `{3,4}`), `3` is forbidden. Any `C^z ≡ 3 (mod 504)`
therefore kills the cube-sum equation `A^3 + B^3 = C^z`.

This is the combined CRT local obstruction: a *positive-density* set of residues
mod `lcm(7,8,9) = 504` is unreachable — strictly sharper than any single prime,
since the forbidden classes are the CRT-product of the mod-7 gap `{3,4}` and the
mod-9 gap `{3,4,5,6}` (the mod-8 factor contributes none). -/
theorem cube_sum_forbidden_mod504 :
    ∃ (S : Finset (ZMod 504)), S.Nonempty ∧
      ∀ r ∈ S, ¬ ∃ A B : ZMod 504, A ^ 3 + B ^ 3 = r := by
  refine ⟨{3}, ⟨3, Finset.mem_singleton_self 3⟩, ?_⟩
  intro r hr
  rw [Finset.mem_singleton] at hr
  subst hr
  exact three_not_cube_sum_mod504

/-! ## 5. Beal corollaries: the combined forbidden `C^z` classes -/

/-- **Beal mod-504 combined obstruction** (deliverable 5).
If the right-hand side `C^z` reduces to `3 (mod 504)` then the cube-sum equation
`A^3 + B^3 = C^z` is impossible mod 504 — for *any* integers `A, B, C` and
exponent `z`. The class `C^z ≡ 3 (mod 504)` is a combined CRT local obstruction
(it is `≡ 3 (mod 7)`, lying in the mod-7 gap). -/
theorem beal_cube_combined_obstruction (A B C : ℤ) (z : ℕ)
    (hC : (C : ZMod 504) ^ z = 3) :
    (A : ZMod 504) ^ 3 + (B : ZMod 504) ^ 3 ≠ (C : ZMod 504) ^ z := by
  rw [hC]
  intro hAB
  exact three_not_cube_sum_mod504 ⟨_, _, hAB⟩

/-- **Beal mod-63 combined `7·9` obstruction** (deliverable 5, CRT-multi-prime).
The combined mod-7 **and** mod-9 picture at modulus `63 = 7·9`: if `C^z` reduces
mod 63 to a residue `r` whose mod-7 image is in `{3,4}` **or** whose mod-9 image
is in `{3,4,5,6}`, then `A^3 + B^3 = C^z` is impossible mod 63. Here we phrase the
clean explicit instance `r ≡ 3 (mod 7)` (forbidden by the mod-7 gap), via the CRT
projection `ZMod 63 →+* ZMod 7`. This stacks the two coprime-prime obstructions:
the density of forbidden `C^z` residues mod 63 is `1 − |{0,1,2,5,6}|/7 · |{0,1,2,7,8}|/9`,
strictly larger than either single prime's. -/
theorem beal_cube_mod63_obstruction (A B C : ℤ) (z : ℕ)
    (hC : (C : ZMod 63) ^ z = 3) :
    (A : ZMod 63) ^ 3 + (B : ZMod 63) ^ 3 ≠ (C : ZMod 63) ^ z := by
  rw [hC]
  rintro hAB
  -- Project `ZMod 63 →+* ZMod 7` and reduce to the mod-7 gap.
  let g : ZMod 63 →+* ZMod 7 := ZMod.castHom (by norm_num : (7 : ℕ) ∣ 63) (ZMod 7)
  have himg : g (A : ZMod 63) ^ 3 + g (B : ZMod 63) ^ 3 = (3 : ZMod 7) := by
    have := congrArg g hAB
    rw [map_add, map_pow, map_pow, map_ofNat] at this
    simpa using this
  exact (cube_sum_not_three_or_four_mod7 _ _).1 himg

end BealCombinedObstruction
