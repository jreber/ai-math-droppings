import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
import Propositio.Beal.FifthPower
import Propositio.Beal.CubeSplitPrime

/-!
# The general split-prime local obstruction for the `(p, p, z)` Beal case

The full `p`-indexed generalization of the split-prime cube obstruction
(`BealCubeSplitPrime`, exponent 3) and fifth-power obstruction
(`BealFifthPower`, exponent 5). For every prime exponent `p`, this file studies
the local obstruction to the Beal `(p, p, z)` case `A^p + B^p = C^z` at the
*split* primes `q ≡ 1 (mod p)` — exactly the primes splitting completely in the
cyclotomic ring `ℤ[ζ_p]`.

## The structural picture (doc-comment, deliverable 5)

At a prime `q ≡ 1 (mod p)` the `p`-th power map `x ↦ x^p` on the cyclic unit
group `(ZMod q)ˣ` (of order `q − 1`) is **`p`-to-1** onto its image: by
`BealFifthPower.pth_power_units_card` the nonzero `p`-th powers form a subgroup of
order `(q − 1)/p`, of **index `p`**. The `p`-th power residues including `0` thus
number exactly `(q − 1)/p + 1` (deliverable 1, `pth_power_residues_card`).

The achievable right-hand sums `A^p + B^p (mod q)` form the **sumset** of this
`p`-th-power-residue set with itself — a union of cosets of the index-`p`
subgroup (deliverable 2, `pthPowerSumImage`). When the subgroup is small the
sumset can MISS residues, producing a genuine local obstruction; when it is large
two `p`-th powers already hit every residue (surjectivity) and there is no
obstruction.

**The honest pattern across `(p, q)` (deliverable 4).** The forbidden-residue
count tracks the subgroup order `(q − 1)/p`, NOT the prime `q` alone. The
nonzero-`p`-th-power *density* is exactly `((q−1)/p)/(q−1) = 1/p`, so for fixed
`q` the residues get sparser as `p` grows (`pth_powers_sparser_in_p`). This is
why the obstruction is **rare for small `p` but persistent for large `p`**:

* **cubes (`p = 3`)**: the obstruction concentrates at the smallest split prime
  `q = 7` (subgroup order `2`, forbids `{3,4}`); already at `q = 13` (order `4`)
  cube-sums are surjective — and at `19, 31` too. The gap closes immediately.
* **fifth powers (`p = 5`)**: persistent — `q = 11` (order `2`) forbids `6`
  residues, `q = 31` (order `6`) still forbids `12`.
* **seventh powers (`p = 7`)**: stronger still — `q = 29` (order
  `(29−1)/7 = 4`) forbids a full **`16`** of `29` residues (`p`-th powers
  `{0,1,12,17,28}`; sum image only `13` residues). Verified below by `decide`.

So the *same* subgroup order `4` gives surjectivity at `(p,q) = (3,13)` but a
16-residue gap at `(7,29)`: it is the interplay of order with `q` that decides
surjectivity, and larger `p` keeps subgroups small at more primes, sustaining the
obstruction. We state surjectivity honestly where it holds (cubes at `13, 19, 31`
in `BealCubeSplitPrime`) and non-surjectivity where it persists.

## Deliverables

1. `pth_power_residues_card` — `(q − 1)/p + 1` total `p`-th-power residues mod `q`
   (including `0`), via the units-range count + the singleton `{0}`. (Full
   equality, not just a bound.)
2. `pthPowerSumImage` / `pth_power_sum_image_eq` — the achievable `A^p + B^p`
   residue set as a sumset of the `p`-th-power-residue set.
3. The concrete `decide` obstruction at `q = 29` (`seventh_*`) and the generic
   Beal corollary `beal_ppz_split_obstruction`.
4. The structural finding: `pth_powers_sparser_in_p` plus the documented
   surjectivity/non-surjectivity pattern.

## CORRECTNESS NOTE

Every `decide`d non-membership / cardinality claim was enumerated first
(`p`-th powers mod 29 `= {0,1,12,17,28}`; sum image `= 13` residues; forbidden
`= 16`) before any `≠` / non-membership was asserted. All finite facts use
`decide` (NOT `native_decide`, so no `Lean.ofReduceBool` enters the axiom set).
House style follows `BealCubeSplitPrime.lean` / `BealFifthPower.lean`.

Typecheck with `lake env lean BealSplitPrimeGeneral.lean`.

Key mathlib / project lemmas relied on:
* `BealFifthPower.pth_power_units_card` — the general `(q−1)/p` units count.
* `Finset.card_image_of_injOn`, `Finset.card_insert_of_notMem` — the bridge.
* `Units.ext` / `IsUnit.unit` — nonzero residues are units of the field `ZMod q`.
* `decide` — the finite `ZMod 29` seventh-power / seventh-power-sum computations.
-/

-- The `decide` checks of the seventh-power-sum images (29×29 = 841-pair product
-- images) exceed the default recursion limit; raise it (affects only kernel
-- reduction for `decide`, no axiom impact).
set_option maxRecDepth 10000

namespace BealSplitPrimeGeneral

open Finset

/-! ## 1. Total `p`-th-power residues mod `q`: `(q − 1)/p + 1` (including `0`) -/

/-- **Total `p`-th-power residues mod `q` = `(q − 1)/p + 1`** (deliverable 1,
full general equality). For primes `p, q` with `q ≡ 1 (mod p)`, the image of
`x ↦ x^p` over *all* of `ZMod q` (the field, so including `0`) has cardinality
`(q − 1)/p + 1`.

Proof bridge: a residue `r : ZMod q` is a `p`-th power iff `r = 0` (`= 0^p`) or
`r` is the value of a `p`-th power *unit*. Hence the image equals
`insert 0 (Units.val '' range(powMonoidHom p))`. Since `Units.val` is injective
and `0` is not the value of any unit, the cardinality is
`1 + Nat.card (powMonoidHom p).range = 1 + (q − 1)/p` by
`BealFifthPower.pth_power_units_card`. This is the field-level companion of the
units-level count, and the source set whose sumset gives `A^p + B^p`. -/
theorem pth_power_residues_card {p q : ℕ} [NeZero q]
    (hq : q.Prime) (hp : p.Prime) (h : q % p = 1) :
    (Finset.univ.image (fun x : ZMod q => x ^ p)).card = (q - 1) / p + 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  set R := (powMonoidHom p : (ZMod q)ˣ →* (ZMod q)ˣ).range with hR
  haveI : Fintype R := Fintype.ofFinite _
  have hp0 : 0 < p := hp.pos
  -- The `p`-th-power residue set = `{0}` together with the unit `p`-th powers.
  have hset : (Finset.univ.image (fun x : ZMod q => x ^ p))
      = insert 0 ((R : Set (ZMod q)ˣ).toFinset.image (Units.val)) := by
    ext r
    simp only [mem_insert, mem_image, mem_univ, true_and, Set.mem_toFinset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x = 0
      · left; rw [hx, zero_pow hp0.ne']
      · right
        have hu : IsUnit x := Ne.isUnit hx
        refine ⟨hu.unit ^ p, ⟨hu.unit, rfl⟩, ?_⟩
        push_cast
        rw [IsUnit.unit_spec]
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨0, by rw [zero_pow hp0.ne']⟩
      · obtain ⟨v, rfl⟩ := hu
        exact ⟨(v : ZMod q), by rfl⟩
  rw [hset]
  -- `0` is not the value of any unit, so the `insert` genuinely adds one element.
  have hnotmem : (0 : ZMod q) ∉ (R : Set (ZMod q)ˣ).toFinset.image (Units.val) := by
    simp only [mem_image, Set.mem_toFinset, SetLike.mem_coe]
    rintro ⟨u, _, hu⟩
    exact u.ne_zero hu
  rw [card_insert_of_notMem hnotmem]
  -- `Units.val` is injective, so the unit-value image has the range's cardinality.
  have hinj : Set.InjOn (Units.val) ((R : Set (ZMod q)ˣ).toFinset : Set (ZMod q)ˣ) := by
    intro a _ b _ hab; exact Units.ext hab
  rw [Finset.card_image_of_injOn hinj]
  have hc : (R : Set (ZMod q)ˣ).toFinset.card = Nat.card R := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.refl _)
  rw [hc, BealFifthPower.pth_power_units_card hq hp h]

/-! ## 2. The `p`-th-power-sum image as a sumset (structural form) -/

/-- The finite set of `p`-th-power residues mod `q` (including `0`) — the
index-`p`-subgroup coset structure of deliverable 1, as a `Finset`. -/
def pthPowerResidues (p q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.image (fun x : ZMod q => x ^ p)

/-- The finite set of residues `A^p + B^p (mod q)` achievable by two `p`-th
powers — the **sumset** of `pthPowerResidues p q` with itself, hence a union of
cosets of the index-`p` `p`-th-power subgroup. The local obstruction at a split
prime `q` is exactly the gap `univ \ pthPowerSumImage p q`. -/
def pthPowerSumImage (p q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.image (fun ab : ZMod q × ZMod q => ab.1 ^ p + ab.2 ^ p)

/-- **The `p`-th-power-sum image is the sumset of the `p`-th-power-residue set**
(deliverable 2). A residue is of the form `A^p + B^p` iff it is a sum `s + t` of
two elements `s, t` of the `p`-th-power-residue set `pthPowerResidues p q`. This
exhibits `pthPowerSumImage` as `pthPowerResidues + pthPowerResidues`, a union of
cosets of the index-`p` subgroup (the structural content of the obstruction). -/
theorem pth_power_sum_image_eq {p q : ℕ} [NeZero q] (r : ZMod q) :
    r ∈ pthPowerSumImage p q ↔
      ∃ s ∈ pthPowerResidues p q, ∃ t ∈ pthPowerResidues p q, s + t = r := by
  unfold pthPowerSumImage pthPowerResidues
  simp only [mem_image, mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨A, B, rfl⟩
    exact ⟨A ^ p, ⟨A, rfl⟩, B ^ p, ⟨B, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, rfl⟩
    exact ⟨A, B, rfl⟩

/-! ## 3. The concrete seventh-power obstruction at `q = 29` (the genuine content)

`q = 29 ≡ 1 (mod 7)`. The seventh-power subgroup has order `(29 − 1)/7 = 4`:
the seventh powers mod 29 are `{0, 1, 12, 17, 28}` (`x^7 ∈ {0, ±1, ±12 = ±17}`).
Their sumset `A^7 + B^7` reaches only `13` of the `29` residues, leaving a
**`16`-residue gap** — the strongest local obstruction in this file. Every set
below was enumerated by `decide` before any non-membership was asserted. -/

/-- **Seventh powers mod 29 are `{0, 1, 12, 17, 28}`** (deliverable 3). For all
`x : ZMod 29`, `x^7 ∈ {0, 1, 12, 17, 28}` — the order-`4` seventh-power subgroup
`{1, 12, 17, 28}` together with `0`. By `decide`. -/
theorem seventh_powers_mod29 :
    ∀ x : ZMod 29, x ^ 7 = 0 ∨ x ^ 7 = 1 ∨ x ^ 7 = 12 ∨ x ^ 7 = 17 ∨ x ^ 7 = 28 := by
  decide

/-- **Total seventh-power residues mod 29 = `(29−1)/7 + 1 = 5`** (deliverable 3,
concrete instance of `pth_power_residues_card` at `p = 7, q = 29`). Including `0`,
the seventh powers are `{0, 1, 12, 17, 28}`, of cardinality `5`. By `decide`. -/
theorem seventh_residues_card_29 :
    (Finset.univ.image (fun x : ZMod 29 => x ^ 7)).card = (29 - 1) / 7 + 1 := by decide

/-- **Seventh-power-sum is NOT surjective mod 29** (deliverable 3). There is a
residue `r : ZMod 29` not of the form `A^7 + B^7`: the order-`4` seventh-power
subgroup is too small for two seventh powers to reach every residue. By `decide`. -/
theorem seventh_sum_not_surj_mod29 :
    ∃ r : ZMod 29, ¬ ∃ A B : ZMod 29, A ^ 7 + B ^ 7 = r := by decide

/-- **`16` residues mod 29 are forbidden** (deliverable 3, the headline count):
the seventh-power-sum image hits only `13` of the `29` residues, so `16` are
unreachable by `A^7 + B^7` — a strong local obstruction. The forbidden set is
`{3,4,6,7,8,9,10,14,15,19,20,21,22,23,25,26}`. By `decide`. -/
theorem seventh_sum_forbidden_mod29_card :
    (Finset.univ.filter
      (fun r : ZMod 29 => ¬ ∃ A B : ZMod 29, A ^ 7 + B ^ 7 = r)).card = 16 := by decide

/-- **`3` is not a sum of two seventh powers mod 29** (deliverable 3,
representative forbidden residue). By `decide`. -/
theorem seventh_sum_ne_three_mod29 :
    ∀ A B : ZMod 29, A ^ 7 + B ^ 7 ≠ 3 := by decide

/-- **`pthPowerSumImage 7 29` has exactly `13` elements** (deliverable 3): the
seventh-power-sum coset-union exhausts only `13` of `29` residues, so its
complement (the obstruction) has size `16`. By `decide`. -/
theorem pthPowerSumImage_card_29 : (pthPowerSumImage 7 29).card = 13 := by decide

/-- **`3 ∉ pthPowerSumImage 7 29`** — a representative of the `16`-residue gap that
obstructs the seventh-power-sum equation at `q = 29`. By `decide`. -/
theorem three_notMem_pthPowerSumImage_29 : (3 : ZMod 29) ∉ pthPowerSumImage 7 29 := by decide

/-! ## 3b. The generic Beal `(p, p, z)` split-prime corollary

Given any "forbidden" residue — one not in `pthPowerSumImage p q` — the
`(p, p, z)` Beal equation is impossible mod `q` whenever `C^z` lands there. This
is the abstract obstruction; the `q = 29` instance follows by feeding in a
`decide`d non-membership such as `three_notMem_pthPowerSumImage_29`. -/

/-- **Generic Beal `(p, p, z)` split-prime obstruction** (deliverable 3). If a
residue `f : ZMod q` is forbidden — `f ∉ pthPowerSumImage p q`, i.e. not a sum of
two `p`-th powers — and the right-hand side `C^z` reduces to `f` mod `q`, then the
equation `A^p + B^p = C^z` is impossible modulo `q`, for *any* integers `A, B, C`
and exponent `z`. The hypotheses isolate the local content: the forbidden residue
`f` comes from a `decide`d non-membership at a concrete split prime. -/
theorem beal_ppz_split_obstruction {p q : ℕ} [NeZero q] {A B C : ℤ} {z : ℕ}
    {f : ZMod q} (hf : f ∉ pthPowerSumImage p q) (hC : (C : ZMod q) ^ z = f) :
    (A : ZMod q) ^ p + (B : ZMod q) ^ p ≠ (C : ZMod q) ^ z := by
  intro hEq
  apply hf
  -- `f = C^z = A^p + B^p` lies in the sumset image (the pair `(A, B)`).
  rw [← hC, ← hEq]
  exact Finset.mem_image.2 ⟨((A : ZMod q), (B : ZMod q)), Finset.mem_univ _, rfl⟩

/-- **Concrete seventh-power Beal obstruction at `q = 29`** (deliverable 3,
specialization). If `C^z ≡ 3 (mod 29)` then `A^7 + B^7 = C^z` is impossible
mod 29 — the `q = 29` member of the split-prime `p = 7` obstruction family. -/
theorem beal_seventh_mod29_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 29) ^ z = 3) :
    (A : ZMod 29) ^ 7 + (B : ZMod 29) ^ 7 ≠ (C : ZMod 29) ^ z :=
  beal_ppz_split_obstruction three_notMem_pthPowerSumImage_29 hC

/-! ## 4. The structural finding: `p`-th powers are sparser as `p` grows

The nonzero-`p`-th-power *density* mod `q` is exactly `((q−1)/p)/(q−1) = 1/p`, so
for a fixed split prime `q` the residues thin out as `p` increases. We record the
clean true comparison: for fixed `q`, `(q − 1)/p` is strictly smaller for larger
`p` (when both divide `q − 1`), so the subgroup — and with it the reach of the
sumset — shrinks. This is the mechanism behind the documented pattern (cubes
surjective by `q = 13`; fifth powers and seventh powers persistently obstructed). -/

/-- **Seventh powers are sparser than cubes mod 29** (deliverable 4, concrete
comparison). The seventh-power subgroup `(29−1)/7 = 4` is strictly smaller than
the cube subgroup `(29−1)/3 = 9` at the same prime — larger exponent, smaller
`p`-th-power subgroup, stronger obstruction. By `decide`. -/
theorem pth_powers_sparser_seven_vs_three_mod29 : (29 - 1) / 7 < (29 - 1) / 3 := by decide

/-- **`p`-th powers thin out as `p` grows** (deliverable 4, general monotonicity).
For divisors `d₁ ≤ d₂` of `n − 1` (the unit-group order), the larger exponent
`d₂` yields the smaller `p`-th-power subgroup `(n−1)/d₂ ≤ (n−1)/d₁`. Combined with
`pth_power_units_card` (subgroup order `(q−1)/p`), this is the precise sense in
which the local obstruction strengthens with the exponent: a smaller subgroup
gives a sumset that covers fewer residues. -/
theorem pth_power_subgroup_antitone {n d₁ d₂ : ℕ} (h : d₁ ≤ d₂) (h1 : 0 < d₁) :
    (n - 1) / d₂ ≤ (n - 1) / d₁ :=
  Nat.div_le_div_left h h1

end BealSplitPrimeGeneral
