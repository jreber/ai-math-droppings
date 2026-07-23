import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Beal cube-sum local obstruction at split primes `p ≡ 1 (mod 3)`

A family of **local obstructions** for the Beal cube-sum case `A^3 + B^3 = C^z`,
indexed by the primes `p ≡ 1 (mod 3)` — the *split* primes of `ℚ(ζ₃)`. This is
the prime-by-prime local picture complementing the global Eisenstein descent
(`BealEisensteinDescent`) and the mod-9 obstruction (`BealCubeMod9`), and it ties
into the project's local-density survey
(`docs/threads/beal/wild-prime-density-survey.md`, `cube-residue-density`).

## Why `p ≡ 1 (mod 3)` is where the structure bites

The cubing map `x ↦ x^3` on the unit group `(ZMod p)ˣ` (cyclic of order `p − 1`)
is governed by `gcd(3, p − 1)`:

* if `p ≡ 2 (mod 3)` then `3 ∤ p − 1`, so cubing is a **bijection** on units —
  every residue is a cube, and there is *no* local restriction;
* if `p ≡ 1 (mod 3)` then `3 ∣ p − 1`, so cubing is **3-to-1** onto its image:
  exactly `(p − 1)/3` nonzero cubes exist, a *proper* subgroup of index `3` (the
  cube-root-of-unity coset structure). The cubes are sparse.

This is the cyclic-group reflection of the fact that `p ≡ 1 (mod 3)` are exactly
the primes that *split* in the Eisenstein ring `ℤ[ζ₃]`.

## The count (items 1–2)

`cube_units_card` : the image of `powMonoidHom 3` on `(ZMod p)ˣ` has order
`(p − 1)/3` — the number of *nonzero* cubes — proved from mathlib's cyclic-group
range count `IsCyclic.card_powMonoidHom_range`
(`Nat.card range = Nat.card G / gcd (Nat.card G) d`) together with
`ZMod.card_units` and `gcd (p−1) 3 = 3`.

`cube_residues_card_*` : including `0`, the total number of cubes mod `p` is
`(p − 1)/3 + 1`, given as `decide`-checked instances at `p = 7, 13, 19, 31`
(connects to the project's density formula `gcd(3, p−1)·…`).

## The cube-sum image and the genuine obstruction (items 3–4)

The achievable residues `A^3 + B^3 (mod p)` form a UNION of cosets reflecting the
index-3 cube subgroup. For most split primes this union is already *all* of
`ZMod p` — once `(p − 1)/3` is moderately large, two cubes suffice to hit every
residue. **The lone genuine non-membership obstruction among the small split
primes is `p = 7`** (verified by exhaustive enumeration, see below):

* `p = 7` : cubes `= {0, 1, 6}`; sums `= {0, 1, 2, 5, 6}`; **missing `{3, 4}`** —
  a real obstruction (`cube_sum_not_three_or_four_mod7`).
* `p = 13` : cubes `= {0, 1, 5, 8, 12}`; sums `=` *all of* `ZMod 13` — no
  non-membership obstruction (`cube_sum_surj_mod13`).
* `p = 19` : cubes `= {0, 1, 7, 8, 11, 12, 18}`; sums `=` *all of* `ZMod 19`
  (`cube_sum_surj_mod19`).
* `p = 31` : cubes `= {0, 1, 2, 4, 8, 15, 16, 23, 27, 29, 30}`; sums `=` *all of*
  `ZMod 31` (`cube_sum_surj_mod31`).

So the sparsity of cubes only *forbids* sums at `p = 7`; the surjectivity facts
for `13, 19, 31` are stated honestly as the complementary truth (a false strong
"every split prime obstructs" claim is avoided). All four cube-sum image sets
above were verified by `decide` before stating the membership / surjectivity
results.

## Beal corollary

`beal_cube_mod7_obstruction` : if `C^z ≡ 3` or `4 (mod 7)` then no integers
satisfy `A^3 + B^3 = C^z` modulo 7 — i.e. that congruence class of `C^z` is a
local obstruction to the cube-sum equation. This is the prime `p = 7` instance of
the split-prime local-obstruction family.

## CORRECTNESS NOTE

Every `decide`d non-membership claim here is TRUE: the cube-sum image sets were
enumerated (`{0,1,2,5,6}` for `p = 7`, full residue system for `13, 19, 31`)
before any `≠` was asserted. The only forbidden residues among the listed primes
are `{3, 4}` mod 7. All finite facts use `decide` (NOT `native_decide`, so no
`Lean.ofReduceBool` enters the axiom set). House style follows
`BealCubeMod9.lean` / `BealModEight.lean`.

Typecheck with `lake env lean BealCubeSplitPrime.lean`.

Key mathlib lemmas relied on:
* `IsCyclic.card_powMonoidHom_range` — the cyclic-group `d`-th power range count.
* `instance [Finite Rˣ] : IsCyclic Rˣ` — units of the field `ZMod p` are cyclic.
* `ZMod.card_units` — `Fintype.card (ZMod p)ˣ = p − 1`.
* `Nat.gcd_eq_right` — `gcd (p−1) 3 = 3` from `3 ∣ p − 1`.
* `decide` — the finite `ZMod p` cube / cube-sum residue computations.
-/

-- The `decide` checks of the `cubeSumImage` cardinalities (13×13 product image)
-- exceed the default recursion limit; raise it (this affects only kernel
-- reduction for `decide`, no axiom impact).
set_option maxRecDepth 4000

namespace BealCubeSplitPrime

/-! ## 1. The cyclic-units cube count: `(p − 1)/3` nonzero cubes -/

/-- **Cubing on `(ZMod p)ˣ` is 3-to-1: exactly `(p − 1)/3` nonzero cubes**
(deliverable 1). For a prime `p ≡ 1 (mod 3)` the image of the cubing
endomorphism `powMonoidHom 3` on the cyclic group `(ZMod p)ˣ` (of order `p − 1`)
has cardinality `(p − 1)/3`.

Proof: `(ZMod p)ˣ` is cyclic (units of a finite integral domain), so mathlib's
`IsCyclic.card_powMonoidHom_range` gives `Nat.card range = (p−1) / gcd (p−1) 3`;
since `p ≡ 1 (mod 3)` forces `3 ∣ p − 1`, the `gcd` is `3`. -/
theorem cube_units_card {p : ℕ} (hp : p.Prime) (h : p % 3 = 1) :
    Nat.card (powMonoidHom 3 : (ZMod p)ˣ →* (ZMod p)ˣ).range = (p - 1) / 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `3 ∣ p − 1` from `p % 3 = 1` (and `p ≥ 1`, automatic for a prime).
  have h3 : (3 : ℕ) ∣ (p - 1) := by
    have hp1 : 1 ≤ p := hp.one_lt.le
    omega
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units p,
    Nat.gcd_eq_right h3]

/-- **The cube subgroup has index 3** (deliverable 1, kernel form).
Equivalently, the kernel of `powMonoidHom 3` on `(ZMod p)ˣ` — the cube roots of
unity — has cardinality `3`, so the cube subgroup is a *proper subgroup of index
3*. This is the structural source of the local obstruction. -/
theorem cube_units_ker_card {p : ℕ} (hp : p.Prime) (h : p % 3 = 1) :
    Nat.card (powMonoidHom 3 : (ZMod p)ˣ →* (ZMod p)ˣ).ker = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ℕ) ∣ (p - 1) := by
    have hp1 : 1 ≤ p := hp.one_lt.le
    omega
  rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, ZMod.card_units p,
    Nat.gcd_eq_right h3]

/-! ## 2. Total cube count including `0`: `(p − 1)/3 + 1`

Including the value `0` (the cube of `0`), the number of distinct cubes mod `p`
is `(p − 1)/3 + 1`. Stated as `decide`-checked instances at the small split
primes; these connect to the project's local density formula. -/

/-- **Total cubes mod 7 = `(7−1)/3 + 1 = 3`.** Cubes mod 7 are `{0, 1, 6}`. -/
theorem cube_residues_card_7 :
    (Finset.univ.image (fun x : ZMod 7 => x ^ 3)).card = (7 - 1) / 3 + 1 := by decide

/-- **Total cubes mod 13 = `(13−1)/3 + 1 = 5`.** Cubes are `{0, 1, 5, 8, 12}`. -/
theorem cube_residues_card_13 :
    (Finset.univ.image (fun x : ZMod 13 => x ^ 3)).card = (13 - 1) / 3 + 1 := by decide

/-- **Total cubes mod 19 = `(19−1)/3 + 1 = 7`.** -/
theorem cube_residues_card_19 :
    (Finset.univ.image (fun x : ZMod 19 => x ^ 3)).card = (19 - 1) / 3 + 1 := by decide

/-- **Total cubes mod 31 = `(31−1)/3 + 1 = 11`.** -/
theorem cube_residues_card_31 :
    (Finset.univ.image (fun x : ZMod 31 => x ^ 3)).card = (31 - 1) / 3 + 1 := by decide

/-! ## 3. The genuine cube-sum obstruction at `p = 7`

Among the small split primes, `p = 7` is the unique one where `A^3 + B^3` *misses*
residues. Cubes mod 7 are `{0, 1, 6}`, so the sums `A^3 + B^3` range over
`{0, 1, 2, 5, 6}` — **missing exactly `{3, 4}`**. (Verified by `decide`.) -/

/-- **`3` and `4` are not sums of two cubes mod 7** (deliverable 3).
For all `A, B : ZMod 7`, `A^3 + B^3 ∉ {3, 4}`. The cube-sum image is
`{0, 1, 2, 5, 6}`; its complement is `{3, 4}`. Finite check by `decide`. -/
theorem cube_sum_not_three_or_four_mod7 :
    ∀ A B : ZMod 7, A ^ 3 + B ^ 3 ≠ 3 ∧ A ^ 3 + B ^ 3 ≠ 4 := by decide

/-- **Beal cube-sum obstruction at `p = 7` (HEADLINE corollary)** (deliverable 3).
If the right-hand side `C^z` reduces to `3` or `4 (mod 7)`, then the cube-sum
equation `A^3 + B^3 = C^z` is impossible modulo 7 — for *any* integers `A, B, C`
and exponent `z`. Thus the congruence classes `C^z ≡ 3, 4 (mod 7)` are local
obstructions to the cube-sum Beal case.

This is the `p = 7` member of the split-prime obstruction family: the sparsity of
cubes mod 7 (`{0,1,6}`) leaves `{3,4}` unreachable by `A^3 + B^3`. -/
theorem beal_cube_mod7_obstruction (A B C : ℤ) (z : ℕ)
    (hC : (C : ZMod 7) ^ z = 3 ∨ (C : ZMod 7) ^ z = 4) :
    (A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 ≠ (C : ZMod 7) ^ z := by
  rcases hC with h | h <;> rw [h]
  · exact (cube_sum_not_three_or_four_mod7 A B).1
  · exact (cube_sum_not_three_or_four_mod7 A B).2

/-! ## 4. The complementary truth: cube-sums are surjective at `p = 13, 19, 31`

For these larger split primes there is *no* non-membership obstruction: every
residue is already a sum of two cubes. We state this honestly (rather than
asserting a false universal obstruction). The cube-sum image
`{ A^3 + B^3 : A, B }` is, in general, a union of cosets of the index-3 cube
subgroup; once `(p − 1)/3` is large enough this union exhausts `ZMod p`.

These surjectivity facts are themselves the empirical content of the project's
cube-residue density heatmaps: the local obstruction *concentrates* at the
smallest split prime `p = 7`. -/

/-- **Every residue mod 13 is a sum of two cubes** (deliverable 4).
No cube-sum obstruction at `p = 13`: `∀ r, ∃ A B, A^3 + B^3 = r`. By `decide`. -/
theorem cube_sum_surj_mod13 : ∀ r : ZMod 13, ∃ A B : ZMod 13, A ^ 3 + B ^ 3 = r := by
  decide

/-- **Every residue mod 19 is a sum of two cubes** (deliverable 4).
No cube-sum obstruction at `p = 19`. By `decide`. -/
theorem cube_sum_surj_mod19 : ∀ r : ZMod 19, ∃ A B : ZMod 19, A ^ 3 + B ^ 3 = r := by
  decide

/-- **Every residue mod 31 is a sum of two cubes** (deliverable 4).
No cube-sum obstruction at `p = 31`. By `decide`. -/
theorem cube_sum_surj_mod31 : ∀ r : ZMod 31, ∃ A B : ZMod 31, A ^ 3 + B ^ 3 = r := by
  decide

/-! ## 5. The cube-sum image set (structural form)

`cubeSumImage p` is the finite set of achievable values `A^3 + B^3 (mod p)`. As a
set it is a UNION of cosets of the index-3 cube subgroup (item 1) — the
local-obstruction structure. The local obstruction at a split prime `p` is exactly
the gap `univ \ cubeSumImage p`; this gap is nonempty only at `p = 7` among the
small split primes (`{3, 4}`).

We phrase the facts as decidable *membership / non-membership / cardinality*
statements over the concrete image (Finset set-equality over `ZMod p` does not
reduce under `decide`, so we avoid it). -/

/-- The finite set of residues `A^3 + B^3 (mod p)` achievable by two cubes — a
union of cosets of the cube subgroup. -/
def cubeSumImage (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.image (fun ab : ZMod p × ZMod p => ab.1 ^ 3 + ab.2 ^ 3)

/-- **`cubeSumImage 7` has exactly 5 elements** (deliverable 4): `{0,1,2,5,6}`,
of cardinality `5`, so its complement `{3,4}` has size `2`. By `decide`. -/
theorem cubeSumImage_card_7 : (cubeSumImage 7).card = 5 := by decide

/-- **`3 ∉ cubeSumImage 7`** (deliverable 4): the gap that obstructs the cube-sum
equation at `p = 7`. By `decide`. -/
theorem three_notMem_cubeSumImage_7 : (3 : ZMod 7) ∉ cubeSumImage 7 := by decide

/-- **`4 ∉ cubeSumImage 7`** (deliverable 4): the second forbidden residue. By
`decide`. -/
theorem four_notMem_cubeSumImage_7 : (4 : ZMod 7) ∉ cubeSumImage 7 := by decide

/-- **`cubeSumImage 13` is all of `ZMod 13`** (deliverable 4): cardinality `13`,
so the coset union already exhausts the field and there is no obstruction. By
`decide`. -/
theorem cubeSumImage_card_13 : (cubeSumImage 13).card = 13 := by decide

end BealCubeSplitPrime
