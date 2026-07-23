import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeSplitPrime

/-!
# Beal fifth-power local obstruction at split primes `q ≡ 1 (mod 5)`

The `p ≡ 1 (mod 5)` analogue of the cube-residue work in `BealCubeSplitPrime`.
A family of **local obstructions** for the Beal fifth-power-sum case
`A^5 + B^5 = C^z`, indexed by the primes `q ≡ 1 (mod 5)` — the *split* primes of
`ℚ(ζ₅)`. This is the prime-by-prime local picture complementing the global
`(5,5,z)` cyclotomic descent (`BealFiveStructure`), and it generalizes the
split-prime cube obstruction (`BealCubeSplitPrime`, exponent 3) to exponent 5.

## Why `q ≡ 1 (mod 5)` is where the structure bites

The fifth-power map `x ↦ x^5` on the unit group `(ZMod q)ˣ` (cyclic of order
`q − 1`) is governed by `gcd(5, q − 1)`:

* if `q ≢ 1 (mod 5)` then (for `q` prime, `q ≠ 5`) `5 ∤ q − 1`, so fifth-powering
  is a **bijection** on units — every residue is a fifth power, *no* restriction;
* if `q ≡ 1 (mod 5)` then `5 ∣ q − 1`, so fifth-powering is **5-to-1** onto its
  image: exactly `(q − 1)/5` nonzero fifth powers exist, a *proper* subgroup of
  index `5`. Fifth powers are sparse — sparser than cubes.

This is the cyclic-group reflection of the fact that `q ≡ 1 (mod 5)` are exactly
the primes that *split completely* in the cyclotomic ring `ℤ[ζ₅]`.

## The general `p`-th power count (deliverable 1)

`pth_power_units_card` : for primes `p, q` with `q ≡ 1 (mod p)`, the image of the
`p`-th power endomorphism `powMonoidHom p` on the cyclic group `(ZMod q)ˣ` (of
order `q − 1`) has cardinality `(q − 1)/p`. Proved from mathlib's cyclic-group
range count `IsCyclic.card_powMonoidHom_range`
(`Nat.card range = Nat.card G / gcd (Nat.card G) d`) together with
`ZMod.card_units` and `gcd (q−1) p = p` (which needs `p ∣ q − 1`, from `q%p=1`).
This **subsumes** the cube count (`BealCubeSplitPrime.cube_units_card`, `p = 3`)
and the fifth-power count below (`p = 5`), both derived as corollaries.

`fifth_power_units_card` : the `p = 5` corollary — `(q − 1)/5` nonzero fifth
powers for `q ≡ 1 (mod 5)`.

## Fifth powers mod 11 and the genuine obstruction (deliverables 2–4)

The smallest split prime is `q = 11`. Fifth powers mod 11 are `{0, 1, 10}`
(`x^5 ≡ ±1` for `5 ∤ x`, since the fifth-power subgroup of `(ZMod 11)ˣ` is
`{±1}` of order `(11−1)/5 = 2`). The achievable sums `A^5 + B^5 (mod 11)` are
therefore drawn from `{0,1,10} + {0,1,10} = {0, 1, 2, 9, 10}` — **missing exactly
`{3, 4, 5, 6, 7, 8}`**, a LARGE gap: 6 of the 11 residues are forbidden. This is
a far stronger local obstruction than any in the cube case (where `p = 7`
forbade only `{3, 4}`). Verified by exhaustive `decide` before being asserted.

`fifth_powers_mod11` : `x^5 ∈ {0, 1, 10}` for all `x : ZMod 11`.
`fifth_sum_image_mod11` : the EXACT image `{ r : ∃ A B, A^5+B^5 = r }` is the
complement of `{3,4,5,6,7,8}`.
`fifth_sum_forbidden_mod11_card` : `6` forbidden residues — a genuine obstruction.
`beal_fifth_mod11_obstruction` : the Beal corollary.

## The next split prime `q = 31` (deliverable 5)

`q = 31 ≡ 1 (mod 5)`. Unlike the cube case (where the obstruction *concentrated*
at the smallest split prime `p = 7` and `13,19,31` were already surjective),
fifth powers stay sparse enough that `q = 31` **also has a gap**: the fifth-power
sum image misses `12` of the `31` residues (`fifth_sum_forbidden_mod31_card`).
The fifth-power subgroup mod 31 has order `(31−1)/5 = 6` (fifth powers
`{0,1,5,6,25,26,30}`), still small enough that two of them cannot reach every
residue. So we state the honest truth: a genuine obstruction persists at `q = 31`
(stated as non-surjectivity, NOT a false surjectivity claim).

## CORRECTNESS NOTE

Every `decide`d non-membership / cardinality claim here is TRUE: the fifth-power
sum image sets were enumerated (`{0,1,2,9,10}` for `q = 11`; `19`-element gap-set
for `q = 31`) before any `≠` or forbidden-set claim was asserted. All finite
facts use `decide` (NOT `native_decide`, so no `Lean.ofReduceBool` enters the
axiom set). House style follows `BealCubeSplitPrime.lean`.

Typecheck with `lake env lean BealFifthPower.lean`.

Key mathlib lemmas relied on:
* `IsCyclic.card_powMonoidHom_range` — the cyclic-group `d`-th power range count.
* `instance [Finite Rˣ] : IsCyclic Rˣ` — units of the field `ZMod q` are cyclic.
* `ZMod.card_units` — `Fintype.card (ZMod q)ˣ = q − 1`.
* `Nat.gcd_eq_right` — `gcd (q−1) p = p` from `p ∣ q − 1`.
* `decide` — the finite `ZMod q` fifth-power / fifth-power-sum computations.
-/

-- The `decide` checks of the fifth-power-sum images (11×11 and, for the forbidden
-- counts, 31×31 product images) exceed the default recursion limit; raise it
-- (affects only kernel reduction for `decide`, no axiom impact).
set_option maxRecDepth 8000

namespace BealFifthPower

/-! ## 1. The general `p`-th power count on cyclic units: `(q − 1)/p` -/

/-- **General `p`-th power count: exactly `(q − 1)/p` nonzero `p`-th powers**
(deliverable 1, fully general form). For primes `p, q` with `q ≡ 1 (mod p)`, the
image of the `p`-th power endomorphism `powMonoidHom p` on the cyclic group
`(ZMod q)ˣ` (of order `q − 1`) has cardinality `(q − 1)/p`.

Proof: `(ZMod q)ˣ` is cyclic (units of a finite field), so mathlib's
`IsCyclic.card_powMonoidHom_range` gives `Nat.card range = (q−1) / gcd (q−1) p`;
since `q ≡ 1 (mod p)` forces `p ∣ q − 1`, the `gcd` is `p`. This subsumes the
cube count (`p = 3`) and the fifth-power count (`p = 5`) below. -/
theorem pth_power_units_card {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h : q % p = 1) :
    Nat.card (powMonoidHom p : (ZMod q)ˣ →* (ZMod q)ˣ).range = (q - 1) / p := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `p ∣ q − 1` from `q % p = 1` (and `q ≥ 1`, automatic for a prime).
  have hpd : p ∣ (q - 1) := by
    have hq1 : 1 ≤ q := hq.one_lt.le
    have hp1 : 1 ≤ p := hp.one_lt.le
    -- `q = p * (q / p) + 1`, so `q - 1 = p * (q / p)`.
    have hdm : q = p * (q / p) + q % p := (Nat.div_add_mod q p).symm ▸ by ring
    rw [h] at hdm
    exact ⟨q / p, by omega⟩
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units q,
    Nat.gcd_eq_right hpd]

/-- **Fifth-powering on `(ZMod q)ˣ` is 5-to-1: exactly `(q − 1)/5` nonzero fifth
powers** (deliverable 1). The `p = 5` corollary of `pth_power_units_card`, for a
prime `q ≡ 1 (mod 5)`. -/
theorem fifth_power_units_card {q : ℕ} (hq : q.Prime) (h : q % 5 = 1) :
    Nat.card (powMonoidHom 5 : (ZMod q)ˣ →* (ZMod q)ˣ).range = (q - 1) / 5 :=
  pth_power_units_card hq (by norm_num) h

/-- **The cube count, re-derived from the general lemma** (`p = 3`). Matches
`BealCubeSplitPrime.cube_units_card`; included to show `pth_power_units_card`
unifies all signatures. -/
theorem cube_power_units_card {q : ℕ} (hq : q.Prime) (h : q % 3 = 1) :
    Nat.card (powMonoidHom 3 : (ZMod q)ˣ →* (ZMod q)ˣ).range = (q - 1) / 3 :=
  pth_power_units_card hq (by norm_num) h

/-! ## 2. Fifth powers mod 11 are `{0, 1, 10}` -/

/-- **Fifth powers mod 11 are `{0, 1, 10}`** (deliverable 2). For all
`x : ZMod 11`, `x^5 ∈ {0, 1, 10}` — i.e. `x^5 ≡ 0, ±1`. The nonzero fifth powers
`{1, 10} = {±1}` form the order-`(11−1)/5 = 2` fifth-power subgroup. By `decide`. -/
theorem fifth_powers_mod11 : ∀ x : ZMod 11, x ^ 5 = 0 ∨ x ^ 5 = 1 ∨ x ^ 5 = 10 := by
  decide

/-- **Total fifth powers mod 11 = `(11−1)/5 + 1 = 3`.** Including `0`, the fifth
powers are `{0, 1, 10}`, of cardinality `3`. By `decide`. -/
theorem fifth_residues_card_11 :
    (Finset.univ.image (fun x : ZMod 11 => x ^ 5)).card = (11 - 1) / 5 + 1 := by decide

/-! ## 3. The genuine fifth-power-sum obstruction at `q = 11` (HEADLINE)

Cubes mod 7 forbade only `{3,4}`; fifth powers mod 11 forbid the LARGE block
`{3,4,5,6,7,8}` — `6` of the `11` residues. The achievable sums are
`{0,1,10} + {0,1,10} = {0, 1, 2, 9, 10}`. -/

/-- **EXACT fifth-power-sum image mod 11 (HEADLINE)** (deliverable 3).
A residue `r : ZMod 11` is a sum of two fifth powers `A^5 + B^5` **iff** it lies
outside the forbidden block `{3, 4, 5, 6, 7, 8}`. Equivalently the image is
exactly `{0, 1, 2, 9, 10}`. The `→` (image is contained in the complement of the
gap) and `←` (every non-gap residue is hit) are both verified by exhaustive
`decide`. -/
theorem fifth_sum_image_mod11 (r : ZMod 11) :
    (∃ A B : ZMod 11, A ^ 5 + B ^ 5 = r) ↔
      (r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8) := by
  revert r; decide

/-- **The forbidden block `{3,...,8}` is unreachable by `A^5 + B^5` mod 11**
(deliverable 3, non-membership form). By `decide`. -/
theorem fifth_sum_not_mem_gap_mod11 :
    ∀ A B : ZMod 11,
      A ^ 5 + B ^ 5 ≠ 3 ∧ A ^ 5 + B ^ 5 ≠ 4 ∧ A ^ 5 + B ^ 5 ≠ 5 ∧
      A ^ 5 + B ^ 5 ≠ 6 ∧ A ^ 5 + B ^ 5 ≠ 7 ∧ A ^ 5 + B ^ 5 ≠ 8 := by decide

/-- **Beal fifth-power-sum obstruction at `q = 11` (HEADLINE corollary)**
(deliverable 3). If the right-hand side `C^z` reduces mod 11 into the forbidden
block `{3, 4, 5, 6, 7, 8}`, then the fifth-power-sum equation `A^5 + B^5 = C^z`
is impossible modulo 11 — for *any* integers `A, B, C` and exponent `z`. Thus the
congruence classes `C^z ≡ 3,4,5,6,7,8 (mod 11)` are local obstructions to the
`(5,5,z)` Beal case.

This is the `q = 11` member of the split-prime fifth-power obstruction family:
the sparsity of fifth powers mod 11 (`{0,1,10}`) leaves the whole block
`{3,...,8}` (`6` of `11` residues) unreachable by `A^5 + B^5`. -/
theorem beal_fifth_mod11_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 11) ^ z = 3 ∨ (C : ZMod 11) ^ z = 4 ∨ (C : ZMod 11) ^ z = 5 ∨
          (C : ZMod 11) ^ z = 6 ∨ (C : ZMod 11) ^ z = 7 ∨ (C : ZMod 11) ^ z = 8) :
    (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ (C : ZMod 11) ^ z := by
  have hgap := fifth_sum_not_mem_gap_mod11 (A : ZMod 11) (B : ZMod 11)
  rcases hC with h | h | h | h | h | h <;> rw [h]
  · exact hgap.1
  · exact hgap.2.1
  · exact hgap.2.2.1
  · exact hgap.2.2.2.1
  · exact hgap.2.2.2.2.1
  · exact hgap.2.2.2.2.2

/-! ## 4. The forbidden-residue count mod 11: `6` (a large obstruction) -/

/-- **`6` residues mod 11 are forbidden** (deliverable 4): the complement of the
fifth-power-sum image has cardinality `6` — `{3, 4, 5, 6, 7, 8}`, more than half
of `ZMod 11`. A genuine, large local obstruction. By `decide`. -/
theorem fifth_sum_forbidden_mod11_card :
    (Finset.univ.filter (fun r : ZMod 11 => ¬ ∃ A B : ZMod 11, A ^ 5 + B ^ 5 = r)).card = 6 := by
  decide

/-! ## 5. The fifth-power-sum image set (structural form) at `q = 11`

`fifthSumImage q` is the finite set of achievable values `A^5 + B^5 (mod q)`. As
a set it is a UNION of cosets of the index-5 fifth-power subgroup (item 1). The
local obstruction at a split prime `q` is exactly the gap
`univ \ fifthSumImage q`. -/

/-- The finite set of residues `A^5 + B^5 (mod q)` achievable by two fifth powers
— a union of cosets of the fifth-power subgroup. -/
def fifthSumImage (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.image (fun ab : ZMod q × ZMod q => ab.1 ^ 5 + ab.2 ^ 5)

/-- **`fifthSumImage 11` has exactly `5` elements** (deliverable 4): `{0,1,2,9,10}`,
so its complement `{3,...,8}` has size `6`. By `decide`. -/
theorem fifthSumImage_card_11 : (fifthSumImage 11).card = 5 := by decide

/-- **`5 ∉ fifthSumImage 11`** — a representative of the forbidden block. By
`decide`. -/
theorem five_notMem_fifthSumImage_11 : (5 : ZMod 11) ∉ fifthSumImage 11 := by decide

/-! ## 6. The next split prime `q = 31`: the obstruction PERSISTS

`q = 31 ≡ 1 (mod 5)`. In contrast to the cube case (where `13,19,31` were already
surjective and the obstruction concentrated at `p = 7`), fifth powers remain
sparse: the fifth-power subgroup mod 31 has order `(31−1)/5 = 6`
(fifth powers `{0,1,5,6,25,26,30}`), and two of them still cannot reach every
residue. So `q = 31` has a genuine gap of `12` forbidden residues — we state this
honest non-surjectivity (NOT a false surjectivity claim). -/

/-- **Fifth-power-sum is NOT surjective mod 31** (deliverable 5). There exists a
residue `r : ZMod 31` not of the form `A^5 + B^5`. The obstruction persists at the
second split prime. By `decide`. -/
theorem fifth_sum_not_surj_mod31 :
    ∃ r : ZMod 31, ¬ ∃ A B : ZMod 31, A ^ 5 + B ^ 5 = r := by decide

/-- **`12` residues mod 31 are forbidden** (deliverable 5): the fifth-power-sum
image misses `12` of the `31` residues — a substantial obstruction surviving to
the next split prime. By `decide`. -/
theorem fifth_sum_forbidden_mod31_card :
    (Finset.univ.filter (fun r : ZMod 31 => ¬ ∃ A B : ZMod 31, A ^ 5 + B ^ 5 = r)).card = 12 := by
  decide

end BealFifthPower
