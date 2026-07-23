import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
import Propositio.Beal.FifthPower
import Propositio.Beal.CubeSplitPrime
import Propositio.Beal.SplitPrimeGeneral

/-!
# New split-prime local obstructions + a density/counting bound for `(p, p, z)`

This file extends `BealSplitPrimeGeneral` in two directions, both unconditional
and axiom-clean (only `decide`, no `native_decide`, no `sorry`, no new axioms):

## A. New concrete local obstructions (beyond the existing `p = 7` at `q = 29`)

* **`p = 5` at `q = 11`** (`beal_fifth_mod11_obstruction'`). The smallest split
  prime of `ℚ(ζ₅)`. Fifth powers mod 11 are `{0, 1, 10}` (subgroup order
  `(11−1)/5 = 2`), so the sumset `A⁵ + B⁵` reaches only `{0,1,2,9,10}` and the
  whole block `{3,4,5,6,7,8}` (`6` of `11` residues) is forbidden. We give the
  obstruction at the representative forbidden residue `5`, routed through the
  *general* corollary `beal_ppz_split_obstruction` (rather than the bespoke
  disjunction in `BealFifthPower`), via the `decide`d non-membership
  `five_notMem_pthPowerSumImage_11`.

* **`p = 11` at `q = 23`** (`beal_eleventh_mod23_obstruction`). `q = 23 ≡ 1
  (mod 11)` is the smallest split prime of `ℚ(ζ₁₁)`. The `11`-th-power subgroup
  has order `(23−1)/11 = 2`: the `11`-th powers mod 23 are `{0, 1, 22}` (i.e.
  `x¹¹ ≡ 0, ±1`). Their sumset reaches only `{0,1,2,21,22}`, so a massive **`18`
  of `23`** residues are forbidden — the strongest gap in the corpus. We give the
  obstruction at the representative forbidden residue `5`.

  This is a genuinely NEW exponent: the corpus previously stopped at `p = 7`.

## B. A density/counting bound: the forbidden set grows when `p`-th powers thin out

The achievable sums `A^p + B^p (mod q)` are the **sumset** of the
`p`-th-power-residue set with itself (`pth_power_sum_image_eq`). A sumset of a set
of size `k` has size at most `k²`, so combining with the exact residue count
`pth_power_residues_card` (`k = (q−1)/p + 1`) gives the clean closed-form bound

> `|pthPowerSumImage p q| ≤ ((q−1)/p + 1)²`   (`sumImage_card_le_closed`)

and hence a lower bound on the forbidden set

> `q − ((q−1)/p + 1)² ≤ |univ \ pthPowerSumImage p q|`   (`forbidden_card_ge`).

Whenever `((q−1)/p + 1)² < q` this forces a **nonempty** obstruction
(`forbidden_nonempty`). This is the quantitative mechanism behind the documented
pattern: for a *fixed* split prime the subgroup order `(q−1)/p` shrinks as `p`
grows, so `((q−1)/p + 1)²` drops below `q` and a forbidden block is *guaranteed*
to appear. Concretely the hypothesis fires at every instance in the corpus:

* `p = 5, q = 11`:  `((10)/5 + 1)² = 9  < 11`  ⇒ obstruction guaranteed.
* `p = 7, q = 29`:  `((28)/7 + 1)² = 25 < 29`  ⇒ obstruction guaranteed.
* `p = 11, q = 23`: `((22)/11 + 1)² = 9 < 23`  ⇒ obstruction guaranteed.

(The bound is not tight — e.g. at `(11,23)` it only certifies `23 − 9 = 14`
forbidden residues, while the true count is `18` — but it is an *unconditional,
`p`-uniform* guarantee, no per-prime enumeration required.)

## CORRECTNESS NOTE

Every `decide`d non-membership / cardinality claim below was enumerated by `#eval`
FIRST (pure-`Nat` modular arithmetic) before being asserted:

* `p=5, q=11`:  fifth powers `{0,1,10}`; sum image `{0,1,2,9,10}`;
  forbidden `{3,4,5,6,7,8}` (count `6`); chosen residue `5` is forbidden.
* `p=11, q=23`: 11th powers `{0,1,22}`; sum image `{0,1,2,21,22}`;
  forbidden `{3,…,20}` (count `18`); chosen residue `5` is forbidden.

All finite facts use `decide` (NOT `native_decide`, so no `Lean.ofReduceBool`
enters the axiom set). The density bounds are proved abstractly from
`pth_power_sum_image_eq` + `pth_power_residues_card`, so they carry only
`[propext, Classical.choice, Quot.sound]`. House style follows
`BealSplitPrimeGeneral.lean`.

Typecheck with `lake env lean BealSplitPrimeDensity.lean`.

Key lemmas relied on:
* `BealSplitPrimeGeneral.beal_ppz_split_obstruction` — the generic forbidden ⇒ Beal step.
* `BealSplitPrimeGeneral.pth_power_residues_card` — `|residues| = (q−1)/p + 1`.
* `BealSplitPrimeGeneral.pth_power_sum_image_eq` — sum image is the residue sumset.
* `Finset.card_image_le`, `Finset.card_product`, `Finset.card_univ_diff`.
* `decide` — the finite `ZMod 11` / `ZMod 23` `p`-th-power-sum computations.
-/

-- The `decide` checks of the 11th-power-sum images (23×23 = 529-pair product) and
-- residue counts exceed the default recursion limit; raise it (kernel reduction
-- only, no axiom impact).
set_option maxRecDepth 10000

namespace BealSplitPrimeDensity

open Finset BealSplitPrimeGeneral

/-! ## A1. New concrete obstruction: `p = 5` at `q = 11`, via the general corollary

Fifth powers mod 11 are `{0, 1, 10}`; the sumset `A⁵ + B⁵` is `{0,1,2,9,10}`, so
`{3,4,5,6,7,8}` is forbidden. We expose `5` as a forbidden residue *for the
`pthPowerSumImage` machinery* and route the Beal obstruction through the general
`beal_ppz_split_obstruction` (complementing `BealFifthPower.beal_fifth_mod11_obstruction`,
which uses a bespoke disjunction). -/

/-- **`5 ∉ pthPowerSumImage 5 11`** — `5` is not a sum of two fifth powers mod 11.
Enumerated (`#eval`) before asserting: forbidden block is `{3,4,5,6,7,8}`. By
`decide`. -/
theorem five_notMem_pthPowerSumImage_11 : (5 : ZMod 11) ∉ pthPowerSumImage 5 11 := by decide

/-- **New Beal fifth-power obstruction at `q = 11`** (via the general corollary).
If `C^z ≡ 5 (mod 11)` then `A⁵ + B⁵ = C^z` is impossible mod 11, for any integers
`A, B, C` and exponent `z`. This is the `(p,q) = (5,11)` instance of the
split-prime family, obtained by feeding the `decide`d non-membership
`five_notMem_pthPowerSumImage_11` into `beal_ppz_split_obstruction`. -/
theorem beal_fifth_mod11_obstruction' {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 11) ^ z = 5) :
    (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ (C : ZMod 11) ^ z :=
  beal_ppz_split_obstruction five_notMem_pthPowerSumImage_11 hC

/-! ## A2. New concrete obstruction: `p = 11` at `q = 23` (a NEW exponent)

`q = 23 ≡ 1 (mod 11)` is the smallest split prime of `ℚ(ζ₁₁)`. The `11`-th-power
subgroup has order `(23−1)/11 = 2`, so the `11`-th powers mod 23 are `{0, 1, 22}`
(`x¹¹ ≡ 0, ±1`). Their sumset reaches only `{0,1,2,21,22}`, leaving `18` of `23`
residues forbidden — the strongest gap in the corpus. Everything `#eval`-enumerated
before being asserted. -/

/-- **11th powers mod 23 are `{0, 1, 22}`** (the order-`2` `11`-th-power subgroup
`{1, 22} = {±1}` together with `0`). For all `x : ZMod 23`,
`x¹¹ ∈ {0, 1, 22}`. By `decide`. -/
theorem eleventh_powers_mod23 :
    ∀ x : ZMod 23, x ^ 11 = 0 ∨ x ^ 11 = 1 ∨ x ^ 11 = 22 := by decide

/-- **Total 11th-power residues mod 23 = `(23−1)/11 + 1 = 3`** (concrete instance
of `pth_power_residues_card` at `p = 11, q = 23`): including `0`, the `11`-th
powers `{0, 1, 22}` number `3`. By `decide`. -/
theorem eleventh_residues_card_23 :
    (Finset.univ.image (fun x : ZMod 23 => x ^ 11)).card = (23 - 1) / 11 + 1 := by decide

/-- **`18` residues mod 23 are forbidden** (the headline count): the
`11`-th-power-sum image hits only `5` of the `23` residues
(`{0,1,2,21,22}`), so `18` are unreachable by `A¹¹ + B¹¹`. The forbidden set is
`{3,4,…,20}`. By `decide`. -/
theorem eleventh_sum_forbidden_mod23_card :
    (Finset.univ.filter
      (fun r : ZMod 23 => ¬ ∃ A B : ZMod 23, A ^ 11 + B ^ 11 = r)).card = 18 := by decide

/-- **`pthPowerSumImage 11 23` has exactly `5` elements**: the `11`-th-power-sum
coset-union `{0,1,2,21,22}` exhausts only `5` of `23` residues, so its complement
(the obstruction) has size `18`. By `decide`. -/
theorem pthPowerSumImage_card_23 : (pthPowerSumImage 11 23).card = 5 := by decide

/-- **`5 ∉ pthPowerSumImage 11 23`** — a representative of the `18`-residue gap.
Enumerated before asserting. By `decide`. -/
theorem five_notMem_pthPowerSumImage_23 : (5 : ZMod 23) ∉ pthPowerSumImage 11 23 := by decide

/-- **New Beal eleventh-power obstruction at `q = 23`** (NEW exponent `p = 11`).
If `C^z ≡ 5 (mod 23)` then `A¹¹ + B¹¹ = C^z` is impossible mod 23, for any
integers `A, B, C` and exponent `z`. The `(p,q) = (11,23)` instance of the
split-prime family, via `beal_ppz_split_obstruction` fed the `decide`d
non-membership `five_notMem_pthPowerSumImage_23`. -/
theorem beal_eleventh_mod23_obstruction {A B C : ℤ} {z : ℕ}
    (hC : (C : ZMod 23) ^ z = 5) :
    (A : ZMod 23) ^ 11 + (B : ZMod 23) ^ 11 ≠ (C : ZMod 23) ^ z :=
  beal_ppz_split_obstruction five_notMem_pthPowerSumImage_23 hC

/-! ## B. The density/counting bound

The sum image is a sumset of the `p`-th-power-residue set, hence bounded in size by
the square of the residue count. Combined with the exact count
`pth_power_residues_card`, this gives an unconditional, `p`-uniform forbidden-set
lower bound. -/

/-- **The `p`-th-power-sum image is a sumset, so its size is at most the square of
the residue count** (abstract form). `|pthPowerSumImage p q| ≤ |pthPowerResidues p q|²`.
Proved from `pth_power_sum_image_eq` (the sum image is contained in the image of
`residues ×ˢ residues` under `+`) and `card_image_le`. No `decide`. -/
theorem sumImage_card_le {p q : ℕ} [NeZero q] :
    (pthPowerSumImage p q).card ≤ (pthPowerResidues p q).card ^ 2 := by
  have hsub : pthPowerSumImage p q ⊆
      (pthPowerResidues p q ×ˢ pthPowerResidues p q).image (fun st => st.1 + st.2) := by
    intro r hr
    rw [pth_power_sum_image_eq] at hr
    obtain ⟨s, hs, t, ht, hst⟩ := hr
    exact mem_image.2 ⟨(s, t), mem_product.2 ⟨hs, ht⟩, hst⟩
  calc (pthPowerSumImage p q).card
      ≤ ((pthPowerResidues p q ×ˢ pthPowerResidues p q).image (fun st => st.1 + st.2)).card :=
        card_le_card hsub
    _ ≤ (pthPowerResidues p q ×ˢ pthPowerResidues p q).card := card_image_le
    _ = (pthPowerResidues p q).card * (pthPowerResidues p q).card := card_product _ _
    _ = (pthPowerResidues p q).card ^ 2 := by ring

/-- **Closed-form density bound** (deliverable B). For primes `p, q` with
`q ≡ 1 (mod p)`, the achievable `p`-th-power-sum residues number at most
`((q−1)/p + 1)²`:

> `|pthPowerSumImage p q| ≤ ((q−1)/p + 1)²`.

Proof: `sumImage_card_le` bounds the sum image by `|residues|²`, and
`pth_power_residues_card` gives `|residues| = (q−1)/p + 1`. No `decide`. -/
theorem sumImage_card_le_closed {p q : ℕ} [NeZero q]
    (hq : q.Prime) (hp : p.Prime) (h : q % p = 1) :
    (pthPowerSumImage p q).card ≤ ((q - 1) / p + 1) ^ 2 := by
  have hcard : (pthPowerResidues p q).card = (q - 1) / p + 1 := by
    unfold pthPowerResidues
    exact pth_power_residues_card hq hp h
  calc (pthPowerSumImage p q).card ≤ (pthPowerResidues p q).card ^ 2 := sumImage_card_le
    _ = ((q - 1) / p + 1) ^ 2 := by rw [hcard]

/-- **Forbidden-set lower bound** (deliverable B, the counting statement). For
primes `p, q` with `q ≡ 1 (mod p)`, the number of residues NOT of the form
`A^p + B^p` is at least `q − ((q−1)/p + 1)²`:

> `q − ((q−1)/p + 1)² ≤ |univ \ pthPowerSumImage p q|`.

As `p` grows (for fixed `q`) the subgroup order `(q−1)/p` shrinks, the right-hand
side `((q−1)/p + 1)²` drops, and this guaranteed forbidden count rises — the exact
quantitative sense in which larger exponents strengthen the local obstruction.
Proof: `Finset.card_univ_diff` turns the complement card into `q − |image|`, then
`sumImage_card_le_closed` + `omega`. No `decide`. -/
theorem forbidden_card_ge {p q : ℕ} [NeZero q]
    (hq : q.Prime) (hp : p.Prime) (h : q % p = 1) :
    q - ((q - 1) / p + 1) ^ 2 ≤ (Finset.univ \ pthPowerSumImage p q).card := by
  have himg : (pthPowerSumImage p q).card ≤ ((q - 1) / p + 1) ^ 2 :=
    sumImage_card_le_closed hq hp h
  rw [Finset.card_univ_diff, ZMod.card]
  omega

/-- **Guaranteed nonempty obstruction** (deliverable B, the qualitative payoff).
If the density bound `((q−1)/p + 1)² < q` holds at a split prime `q ≡ 1 (mod p)`,
then a forbidden residue is *guaranteed* to exist — without any per-prime
enumeration. This fires at every corpus instance:
`(5,11): 9 < 11`, `(7,29): 25 < 29`, `(11,23): 9 < 23`.
Proof: `forbidden_card_ge` + `omega`. No `decide`. -/
theorem forbidden_nonempty {p q : ℕ} [NeZero q]
    (hq : q.Prime) (hp : p.Prime) (h : q % p = 1)
    (hgap : ((q - 1) / p + 1) ^ 2 < q) :
    0 < (Finset.univ \ pthPowerSumImage p q).card := by
  have := forbidden_card_ge hq hp h
  omega

/-! ## B'. The density hypothesis fires at the corpus instances

The `decide`d numeric inequalities certifying that `forbidden_nonempty` applies at
each concrete split prime — so the guaranteed-obstruction theorem is not vacuous. -/

/-- The density gap hypothesis holds at `(p, q) = (5, 11)`:
`((11−1)/5 + 1)² = 9 < 11`. By `decide`. -/
theorem density_gap_5_11 : ((11 - 1) / 5 + 1) ^ 2 < 11 := by decide

/-- The density gap hypothesis holds at `(p, q) = (7, 29)`:
`((29−1)/7 + 1)² = 25 < 29`. By `decide`. -/
theorem density_gap_7_29 : ((29 - 1) / 7 + 1) ^ 2 < 29 := by decide

/-- The density gap hypothesis holds at `(p, q) = (11, 23)`:
`((23−1)/11 + 1)² = 9 < 23`. By `decide`. -/
theorem density_gap_11_23 : ((23 - 1) / 11 + 1) ^ 2 < 23 := by decide

/-- **Guaranteed obstruction at `q = 23` for `p = 11`, from the density bound
alone.** Combines `forbidden_nonempty` with the `decide`d gap `density_gap_11_23`
and the primality/congruence facts — a forbidden residue exists with NO sum-image
enumeration. (The explicit witness `5` is `five_notMem_pthPowerSumImage_23`.) -/
theorem forbidden_nonempty_11_23 :
    0 < (Finset.univ \ pthPowerSumImage 11 23).card :=
  forbidden_nonempty (by norm_num) (by norm_num) (by norm_num) density_gap_11_23

/-- **Guaranteed obstruction at `q = 11` for `p = 5`, from the density bound
alone.** As above at `(5, 11)`. -/
theorem forbidden_nonempty_5_11 :
    0 < (Finset.univ \ pthPowerSumImage 5 11).card :=
  forbidden_nonempty (by norm_num) (by norm_num) (by norm_num) density_gap_5_11

end BealSplitPrimeDensity
