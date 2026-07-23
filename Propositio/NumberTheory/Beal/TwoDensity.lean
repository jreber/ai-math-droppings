import Mathlib.Algebra.Group.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Propositio.NumberTheory.Beal.UnitsDensity

/-!
# Beal MULTIPLICATIVE unit-group density — the `p = 2` (even-modulus) case

NEW — `p = 2` case of the unit-group Beal-local density. `(ZMod (2^k))ˣ` is
cyclic for `k ≤ 2` (clean) but NOT for `k ≥ 3` (the design-memo "wild 2-adic"
case).

`BealUnitsDensity.cyclic_pair_solution_count` proves, for a finite **cyclic**
group `G` of order `N`,

  `Nat.card { (A,B) : G×G // A^x · B^y = 1 } = N · gcd(N, gcd(x,y))`,

and `BealUnitsDensity.units_pair_solution_count_prime_pow` specializes it to
`(ZMod (p^k))ˣ` for an **odd** prime `p` (where the unit group is cyclic).

For `p = 2` the unit group is no longer cyclic in general, so that headline does
not directly apply. The structure is:

* `k = 0`: `(ZMod 1)ˣ` trivial, order `1`.
* `k = 1`: `(ZMod 2)ˣ` trivial, order `1 = φ(2)`.
* `k = 2`: `(ZMod 4)ˣ` cyclic of order `2 = φ(4)`.   (mathlib: `isCyclic_units_four`)
* `k ≥ 3`: `(ZMod (2^k))ˣ ≅ C₂ × C_{2^(k-2)}` — **NOT cyclic**
  (mathlib: `isCyclic_units_two_pow_iff` says cyclic ↔ `k ≤ 2`;
  `not_isCyclic_units_eight` is the base obstruction).

## What this file lands (sorry-free)

1. **`k = 1` and `k = 2`** as direct corollaries of the cyclic headline — the
   clean cases. (`units_two_one_count`, `units_four_count`.)

2. **The product factorization** (the structurally correct route for the
   non-cyclic case): for *any* two finite groups `G`, `H`,

     `#{ (A,B) : (G×H)² // A^x·B^y = 1 }
        = #{ over G } · #{ over H }`,

   because `A^x·B^y = 1` in a product holds **componentwise**. When both factors
   are cyclic this gives the explicit count

     `(|G|·gcd(|G|,g)) · (|H|·gcd(|H|,g))`,  `g = gcd(x,y)`.

   (`prodSolnEquiv`, `prod_pair_solution_count`, `prod_cyclic_pair_solution_count`.)

   This is the *engine* for `k ≥ 3`: once one has
   `(ZMod (2^k))ˣ ≃* ZMod 2 × ZMod (2^(k-2))` one transports
   `prod_cyclic_pair_solution_count` across it. With `|C₂| = 2` and
   `|C_{2^(k-2)}| = 2^(k-2)` the closed form for `k ≥ 3` is

     `2·gcd(2, g) · 2^(k-2)·gcd(2^(k-2), g)`.

## The `k ≥ 3` case — NOW CLOSED in `BealTwoAdicIso.lean`

3. **`k ≥ 3` concrete count for `(ZMod (2^k))ˣ`.** This was the documented gap;
   it is now CLOSED in `BealTwoAdicIso.lean` (`units_two_pow_count_ge_three`,
   sorry-free, axiom-clean), which builds the missing isomorphism
   `(ZMod (2^k))ˣ ≃* ⟨-1⟩ × ⟨5⟩` (internal product of cyclic subgroups) and
   transports the `count_of_mulEquiv_prod_cyclic` engine below across it. The
   historical note on the (former) gap is kept for context:
   the single missing mathlib object was an explicit multiplicative isomorphism

     `(ZMod (2^k))ˣ ≃* ZMod 2 × ZMod (2^(k-2))`   (k ≥ 3, additive `ZMod` = cyclic factors)

   mathlib (as of v4.29.1) proves the *cyclicity dichotomy*
   (`ZMod.isCyclic_units_two_pow_iff`) and the order of the generator `5`
   (`ZMod.orderOf_five : orderOf (5 : ZMod (2^(n+2))) = 2^n`), but provides **no
   product-decomposition `MulEquiv`** for the 2-adic unit group. Building it from
   scratch requires the internal direct product `{±1} × ⟨5⟩`: lifting
   `orderOf_five` to the unit `5`, proving `-1 ∉ ⟨5⟩`, and a cardinality argument
   that `{±1} × ⟨5⟩` exhausts the group — a self-contained multi-hundred-line
   development. It is deliberately left as the documented gap rather than forced.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealTwoDensity.lean` to typecheck.
-/

namespace BealTwoDensity

open BealUnitsDensity

/-!
## 1. The clean cyclic small cases `k = 1, 2`
-/

/-- **`k = 1`.** `(ZMod 2)ˣ` is the trivial group (order `1 = φ(2)`), so the only
solution pair is `(1,1)`: the count is `1 · gcd(1, gcd x y) = 1`. -/
theorem units_two_one_count (x y : ℕ) :
    Nat.card {p : (ZMod 2)ˣ × (ZMod 2)ˣ // p.1 ^ x * p.2 ^ y = 1} = 1 := by
  haveI : IsCyclic (ZMod 2)ˣ := ZMod.isCyclic_units_two
  have hc : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
  rw [cyclic_pair_solution_count (G := (ZMod 2)ˣ) x y, hc, Nat.one_mul,
    Nat.gcd_one_left]

/-- **`k = 2`.** `(ZMod 4)ˣ` is cyclic of order `2 = φ(4)`
(`ZMod.isCyclic_units_four`), so the count is the cyclic headline at `N = 2`:
`2 · gcd(2, gcd x y)`. -/
theorem units_four_count (x y : ℕ) :
    Nat.card {p : (ZMod 4)ˣ × (ZMod 4)ˣ // p.1 ^ x * p.2 ^ y = 1}
      = 2 * Nat.gcd 2 (Nat.gcd x y) := by
  haveI : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_four
  have hc : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
  rw [cyclic_pair_solution_count (G := (ZMod 4)ˣ) x y, hc]

/-!
## 2. The product factorization — the engine for the non-cyclic case

`A^x · B^y = 1` in a product group `G × H` holds **componentwise**, so the
solution set over `(G × H)²` is the *product* of the per-factor solution sets.
This is exactly what lets the `k ≥ 3` count factor through
`(ZMod (2^k))ˣ ≅ C₂ × C_{2^(k-2)}` — modulo the missing structure `MulEquiv`.
-/

/-- **Component-wise solution equivalence.** A pair `(A,B)` of units in a product
group `G × H` satisfies `A^x·B^y = 1` iff each component does, giving a bijection
between the product solution set and the product of the per-factor solution sets. -/
def prodSolnEquiv {G H : Type*} [Group G] [Group H] (x y : ℕ) :
    {p : (G × H) × (G × H) // p.1 ^ x * p.2 ^ y = 1} ≃
      ({p : G × G // p.1 ^ x * p.2 ^ y = 1} × {p : H × H // p.1 ^ x * p.2 ^ y = 1}) where
  toFun := fun ⟨⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩, h⟩ =>
    let h' : a₁ ^ x * b₁ ^ y = 1 ∧ a₂ ^ x * b₂ ^ y = 1 := by
      rw [Prod.pow_mk, Prod.pow_mk] at h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    (⟨(a₁, b₁), h'.1⟩, ⟨(a₂, b₂), h'.2⟩)
  invFun := fun ⟨⟨⟨a₁, b₁⟩, h1⟩, ⟨⟨a₂, b₂⟩, h2⟩⟩ =>
    ⟨((a₁, a₂), (b₁, b₂)), by rw [Prod.pow_mk, Prod.pow_mk]; exact Prod.ext h1 h2⟩
  left_inv := by rintro ⟨⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨⟨a₁, b₁⟩, h1⟩, ⟨⟨a₂, b₂⟩, h2⟩⟩; rfl

/-- **Product count factorizes.** For any two finite groups, the number of
solution pairs over `G × H` is the product of the per-factor counts. -/
theorem prod_pair_solution_count {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (x y : ℕ) :
    Nat.card {p : (G × H) × (G × H) // p.1 ^ x * p.2 ^ y = 1}
      = Nat.card {p : G × G // p.1 ^ x * p.2 ^ y = 1}
        * Nat.card {p : H × H // p.1 ^ x * p.2 ^ y = 1} := by
  rw [Nat.card_congr (prodSolnEquiv x y), Nat.card_prod]

/-- **Product of two cyclic factors — explicit count.** For finite cyclic `G`,
`H`, the solution count over `G × H` is

  `(|G|·gcd(|G|, gcd x y)) · (|H|·gcd(|H|, gcd x y))`.

This is the formula the `k ≥ 3` case needs: instantiate `G = C₂`,
`H = C_{2^(k-2)}` once the structure isomorphism is supplied. -/
theorem prod_cyclic_pair_solution_count {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] [IsCyclic G] [IsCyclic H] [Nonempty G] [Nonempty H]
    (x y : ℕ) :
    Nat.card {p : (G × H) × (G × H) // p.1 ^ x * p.2 ^ y = 1}
      = (Nat.card G * Nat.gcd (Nat.card G) (Nat.gcd x y))
        * (Nat.card H * Nat.gcd (Nat.card H) (Nat.gcd x y)) := by
  rw [prod_pair_solution_count, cyclic_pair_solution_count,
    cyclic_pair_solution_count]

/-!
## 3. The closed form for a `C₂ × C_{2^(k-2)}` group (still sorry-free)

If a group `G` is *given* as `MulEquiv` to `ZMod 2 × ZMod (2^(k-2))` (the
additive `ZMod`s are the cyclic factors, treated multiplicatively), we can read
off the count. This isolates exactly the one ingredient the 2-adic case is
missing — the isomorphism — from the counting, which is done here in full.
-/

/-- **Transport along any product-of-cyclics description.** If a finite group `G`
is multiplicatively isomorphic to `H₁ × H₂` with both `Hᵢ` finite cyclic, then
its solution count is the product-of-cyclics formula for `H₁ × H₂`.

For the 2-adic case `G = (ZMod (2^k))ˣ`, `H₁ = (ZMod 2)` (cyclic, order 2,
multiplicative copy), `H₂ = (ZMod (2^(k-2)))`-as-`C_{2^(k-2)}`. The ONLY missing
piece is the `MulEquiv e` — once supplied, this closes `k ≥ 3` immediately. -/
theorem count_of_mulEquiv_prod_cyclic
    {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂]
    [Finite H₁] [Finite H₂] [IsCyclic H₁] [IsCyclic H₂] [Nonempty H₁] [Nonempty H₂]
    (e : G ≃* (H₁ × H₂)) (x y : ℕ) :
    Nat.card {p : G × G // p.1 ^ x * p.2 ^ y = 1}
      = (Nat.card H₁ * Nat.gcd (Nat.card H₁) (Nat.gcd x y))
        * (Nat.card H₂ * Nat.gcd (Nat.card H₂) (Nat.gcd x y)) := by
  -- transport the solution set across the MulEquiv `e`, then apply the
  -- product-of-cyclics count.
  have hbij : {p : G × G // p.1 ^ x * p.2 ^ y = 1}
      ≃ {p : (H₁ × H₂) × (H₁ × H₂) // p.1 ^ x * p.2 ^ y = 1} := by
    refine Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) ?_
    intro p
    simp only [Equiv.prodCongr_apply, Prod.map, MulEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe]
    rw [← map_pow, ← map_pow, ← map_mul]
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact e.injective (by rw [h, map_one])
  rw [Nat.card_congr hbij, prod_cyclic_pair_solution_count]

/-!
## 4. The `k ≥ 3` concrete count — NOW CLOSED in `BealTwoAdicIso.lean`

UPDATE (2026-06): the blocker documented below has been **resolved**. The missing
isomorphism `(ZMod (2^(n+2)))ˣ ≃* ⟨-1⟩ × ⟨5⟩` is built sorry-free as
`BealTwoAdicIso.unitsEquiv`, and the `k ≥ 3` count is proved as
`BealTwoAdicIso.units_two_pow_count_ge_three` via `count_of_mulEquiv_prod_cyclic`
(below). The historical blocker note is retained for context.
-/

/- **`k ≥ 3` (NON-cyclic).** For `k ≥ 3` the unit group `(ZMod (2^k))ˣ` is
isomorphic to `C₂ × C_{2^(k-2)}` and is **not** cyclic
(`ZMod.isCyclic_units_two_pow_iff`). Its Beal-local solution count is therefore
the product-of-cyclics formula with factors of orders `2` and `2^(k-2)`:

  `(2 · gcd(2, gcd x y)) · (2^(k-2) · gcd(2^(k-2), gcd x y))`.

### Blocker (precise)

The counting half of this is fully proved in this file
(`count_of_mulEquiv_prod_cyclic`, `prod_cyclic_pair_solution_count`). The single
missing ingredient is a mathlib object:

  `(ZMod (2^k))ˣ ≃* ZMod 2 × ZMod (2^(k-2))`   (for `k ≥ 3`)

i.e. the explicit internal-direct-product decomposition `{±1} × ⟨5⟩`. mathlib
v4.29.1 has:
  * `ZMod.isCyclic_units_two_pow_iff` — cyclic ↔ `k ≤ 2` (so non-cyclic here);
  * `ZMod.orderOf_five : orderOf (5 : ZMod (2^(n+2))) = 2^n` — order of the
    cyclic generator as a *ring* element;
  * `ZMod.not_isCyclic_units_eight` — the base obstruction;
but it has **no `MulEquiv` decomposing `(ZMod (2^k))ˣ` as a product of cyclic
groups.** Producing it requires, from scratch:
  1. lift `orderOf_five` to the *unit* `5 : (ZMod (2^k))ˣ` (order `2^(k-2)`);
  2. show `-1 ∉ ⟨5⟩` (`-1` is not a power of `5` mod `2^k`);
  3. a cardinality argument that `{±1} × ⟨5⟩` exhausts the order-`2^(k-1)` group;
  4. package (1)-(3) as the `MulEquiv`.
This is a self-contained multi-hundred-line development and is intentionally left
as the documented gap. Once `e` above exists, the proof is
`exact count_of_mulEquiv_prod_cyclic e x y` after rewriting the factor cardinals
`Nat.card (ZMod 2) = 2`, `Nat.card (ZMod (2^(k-2))) = 2^(k-2)`.

The target statement (kept as a comment, NOT a live `sorry`, so this file stays
sorry-free; the counting engine above is what's reusable once the iso lands):

    theorem units_two_pow_count_ge_three (k : ℕ) (hk : 3 ≤ k) (x y : ℕ) :
        Nat.card {p : (ZMod (2 ^ k))ˣ × (ZMod (2 ^ k))ˣ // p.1 ^ x * p.2 ^ y = 1}
          = (2 * Nat.gcd 2 (Nat.gcd x y))
            * (2 ^ (k - 2) * Nat.gcd (2 ^ (k - 2)) (Nat.gcd x y)) := by
      -- obtain e : (ZMod (2^k))ˣ ≃* ZMod 2 × ZMod (2^(k-2)) := <missing mathlib iso>
      -- exact count_of_mulEquiv_prod_cyclic e x y  (after the cardinal rewrites)
-/

end BealTwoDensity
