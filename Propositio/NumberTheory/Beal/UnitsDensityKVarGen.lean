import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Propositio.NumberTheory.Beal.UnitsDensityKVar
import Propositio.NumberTheory.Beal.UnitsDensityGeneral

/-!
# Beal MULTIPLICATIVE unit-group count — k variables, GENERAL modulus

NEW (no LaTTe sibling) — k-variable multiplicative count at general modulus;
completes the density theory (k-variable × any modulus).

This file is the last generalization of the multiplicative unit-group density
theory. The two prior pieces are:

* `BealUnitsDensityKVar.cyclic_lin_solution_count` — **k variables, cyclic group**:
  for a finite cyclic `G` of order `N`,
  `#{A : Fin k → G // ∏ i, Aᵢ^{xᵢ} = 1} = N^(k-1) · gcd(N, gcd xᵢ)`.
* `BealUnitsDensityGeneral.units_pair_solution_count_mul` — **2 variables, general
  modulus**: CRT-multiplicativity of the *pair* count over coprime moduli.

The missing corner is **k variables × general modulus, multiplicative**, which
necessarily leaves cyclic territory (e.g. `(ZMod (p^k'))ˣ` for a composite or even
modulus is non-cyclic). The organising principle is the same as the `k = 2` case
of `BealTwoDensity.prodSolnEquiv`: in a *product* group the condition
`∏ i, Aᵢ^{xᵢ} = 1` holds **componentwise**, so the solution set factors as a
product. Lifting this to `k`-tuples uses `Equiv.arrowProdEquivProdArrow`
(`(Fin k → G × H) ≃ (Fin k → G) × (Fin k → H)`).

## What this file lands (sorry-free, axiom-clean)

1. **k-variable CRT-multiplicativity (units)** — `units_kvar_solution_count_mul`:
   for coprime `m, n` and any `x : Fin k → ℕ`,
   `Nat.card {A : Fin k → (ZMod (m*n))ˣ // ∏ i, Aᵢ^{xᵢ} = 1}
      = Nat.card {… over (ZMod m)ˣ} * Nat.card {… over (ZMod n)ˣ}`.
   Route: the units-CRT `MulEquiv` `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`
   (`BealUnitsDensityGeneral.unitsChineseRemainder`) transported across the
   product factorization `kvarProdSolnEquiv`.

2. **k-variable product-of-two-cyclics explicit count** —
   `prod_cyclic_kvar_solution_count`: for finite cyclic `G`, `H`,
   `#{A : Fin k → G×H // ∏ = 1}
      = (|G|^(k-1)·gcd(|G|, gcd x)) · (|H|^(k-1)·gcd(|H|, gcd x))`
   via the product factorization + `cyclic_lin_solution_count` on each factor.
   (This is the engine for the non-cyclic prime-power case, e.g. `(ZMod 2^a)ˣ`.)

3. **general ODD modulus, k variables** — `units_kvar_solution_count_odd`:
   for odd `n > 0`,
   `#{A : Fin k → (ZMod n)ˣ // ∏ = 1}
      = ∏_{p^a ‖ n} φ(p^a)^(k-1)·gcd(φ(p^a), gcd x)`,
   via `Nat.multiplicative_factorization` from (1) and the odd-prime-power
   cyclic count `BealUnitsDensityKVar.units_lin_solution_count_prime_pow`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealUnitsDensityKVarGen.lean` to typecheck.
-/

namespace BealUnitsDensityKVarGen

open BealUnitsDensityKVar BealUnitsDensityGeneral

/-!
## 0. The k-variable product factorization (the engine)

In a product group `G × H`, a k-tuple `A : Fin k → G × H` satisfies
`∏ i, (A i)^{x i} = 1` iff each component does. This is the k-variable analog of
`BealTwoDensity.prodSolnEquiv`, built on `Equiv.arrowProdEquivProdArrow`.
-/

/-- The k-variable solution-set subtype over a group `G`: tuples `A : Fin k → G`
with `∏ i, (A i)^{x i} = 1`. -/
abbrev KSolSet (G : Type*) [CommGroup G] (k : ℕ) (x : Fin k → ℕ) :=
  {A : Fin k → G // ∏ i, (A i) ^ (x i) = 1}

/-- **Component-wise k-variable solution equivalence.** A k-tuple `A : Fin k → G×H`
of pairs in a product group satisfies `∏ i, (A i)^{x i} = 1` iff each component
does, giving a bijection between the product solution set and the product of the
per-factor solution sets.

This is `BealTwoDensity.prodSolnEquiv` lifted to `k` variables: the tuple split
`(Fin k → G × H) ≃ (Fin k → G) × (Fin k → H)` is
`Equiv.arrowProdEquivProdArrow`, and `∏` in a product is computed componentwise
via `Prod.fst_prod` / `Prod.snd_prod`. -/
def kvarProdSolnEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (k : ℕ) (x : Fin k → ℕ) :
    KSolSet (G × H) k x ≃ KSolSet G k x × KSolSet H k x := by
  refine (Equiv.subtypeEquiv (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => G)
      (fun _ => H)) ?_).trans
    (Equiv.subtypeProdEquivProd
      (p := fun A : Fin k → G => ∏ i, (A i) ^ (x i) = 1)
      (q := fun A : Fin k → H => ∏ i, (A i) ^ (x i) = 1))
  intro A
  -- goal: (∏ i, (A i)^{x i} = 1) ↔ (∏ i, (A i).1^{x i} = 1 ∧ ∏ i, (A i).2^{x i} = 1)
  simp only [Equiv.arrowProdEquivProdArrow_apply]
  -- `c = 1` in `G × H` ↔ `c.1 = 1 ∧ c.2 = 1`; and `(∏)·.1 = ∏ ·.1` componentwise.
  rw [show (1 : G × H) = ((1 : G), (1 : H)) from rfl, Prod.ext_iff,
    Prod.fst_prod, Prod.snd_prod]
  simp only [Prod.pow_fst, Prod.pow_snd]

/-- **k-variable product count factorizes.** For any two finite commutative groups,
the number of k-variable solution tuples over `G × H` is the product of the
per-factor counts. -/
theorem prod_kvar_solution_count {G H : Type*} [CommGroup G] [CommGroup H]
    [Finite G] [Finite H] (k : ℕ) (x : Fin k → ℕ) :
    Nat.card (KSolSet (G × H) k x)
      = Nat.card (KSolSet G k x) * Nat.card (KSolSet H k x) := by
  rw [Nat.card_congr (kvarProdSolnEquiv k x), Nat.card_prod]

/-!
## 1. HEADLINE — k-variable CRT-multiplicativity on units
-/

/-- **CRT bijection on k-variable unit-solution sets.** For coprime `m, n`, the
k-variable unit-solution set over `(ZMod (m*n))ˣ` is in bijection with the product
of the k-variable unit-solution sets over `(ZMod m)ˣ` and `(ZMod n)ˣ`, transported
along the units-CRT isomorphism `BealUnitsDensityGeneral.unitsChineseRemainder`.

The condition `∏ i, (A i)^{x i} = 1` transfers because the CRT map is a `MulEquiv`
(preserves `^`, `*`, `1`, and `∏`), then factors componentwise via
`kvarProdSolnEquiv`. -/
noncomputable def units_kvarHom_chineseRemainder_equiv
    (m n : ℕ) (h : Nat.Coprime m n) (k : ℕ) (x : Fin k → ℕ) :
    KSolSet (ZMod (m * n))ˣ k x
      ≃ KSolSet (ZMod m)ˣ k x × KSolSet (ZMod n)ˣ k x := by
  -- `e : (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.
  let e := unitsChineseRemainder m n h
  -- Step 1: transport the solution set across the MulEquiv `e` pointwise.
  have step1 : KSolSet (ZMod (m * n))ˣ k x
      ≃ KSolSet ((ZMod m)ˣ × (ZMod n)ˣ) k x := by
    refine Equiv.subtypeEquiv (Equiv.piCongrRight (fun _ => e.toEquiv)) ?_
    intro A
    simp only [Equiv.piCongrRight_apply, MulEquiv.toEquiv_eq_coe, Pi.map_apply,
      EquivLike.coe_coe]
    -- (∏ i, (A i)^{x i} = 1) ↔ (∏ i, (e (A i))^{x i} = 1)
    rw [← e.map_eq_one_iff, map_prod]
    simp only [map_pow]
  -- Step 2: factor the product solution set componentwise.
  exact step1.trans (kvarProdSolnEquiv k x)

/-- **HEADLINE #1 (NEW).** The k-variable unit-group Beal count is multiplicative
over coprime moduli. For coprime `m, n` and any `x : Fin k → ℕ`, the number of
k-tuples `A : Fin k → (ZMod (m*n))ˣ` with `∏ i, (A i)^{x i} = 1` equals the
product of the corresponding counts over `(ZMod m)ˣ` and `(ZMod n)ˣ`.

This combines the non-cyclic product structure (`kvarProdSolnEquiv`) with the
k-variable degree of freedom; no LaTTe sibling combined `k` variables with two
moduli on the unit groups. -/
theorem units_kvar_solution_count_mul
    (m n : ℕ) (h : Nat.Coprime m n) (k : ℕ) (x : Fin k → ℕ) :
    Nat.card (KSolSet (ZMod (m * n))ˣ k x)
      = Nat.card (KSolSet (ZMod m)ˣ k x) * Nat.card (KSolSet (ZMod n)ˣ k x) := by
  rw [Nat.card_congr (units_kvarHom_chineseRemainder_equiv m n h k x), Nat.card_prod]

/-!
## 2. k-variable product-of-two-cyclics explicit count

The engine for non-cyclic factors (e.g. `(ZMod (2^a))ˣ ≃ C₂ × C_{2^(a-2)}`): once
a group is described as a product of two cyclic groups, its k-variable count is
the product of the two cyclic k-variable counts of
`BealUnitsDensityKVar.cyclic_lin_solution_count`.
-/

attribute [local instance] IsCyclic.commGroup

/-- **Product of two cyclic factors — explicit k-variable count.** For finite
cyclic `G`, `H` and `k ≥ 1`, the k-variable solution count over `G × H` is

  `(|G|^(k-1)·gcd(|G|, gcd x)) · (|H|^(k-1)·gcd(|H|, gcd x))`.

Proved by the product factorization `prod_kvar_solution_count` plus the cyclic
k-variable headline on each factor. This is the formula a non-cyclic prime power
needs: instantiate `G`, `H` as the two cyclic factors once the structure
isomorphism is supplied. -/
theorem prod_cyclic_kvar_solution_count {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] [IsCyclic G] [IsCyclic H] [Nonempty G] [Nonempty H]
    (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card (KSolSet (G × H) k x)
      = (Nat.card G ^ (k - 1) * Nat.gcd (Nat.card G) (Finset.univ.gcd x))
        * (Nat.card H ^ (k - 1) * Nat.gcd (Nat.card H) (Finset.univ.gcd x)) := by
  rw [prod_kvar_solution_count, cyclic_lin_solution_count k hk x,
    cyclic_lin_solution_count k hk x]

/-- **Transport along any product-of-cyclics description.** If a finite group `G`
is multiplicatively isomorphic to `H₁ × H₂` with both `Hᵢ` finite cyclic, then its
k-variable solution count is the product-of-cyclics formula for `H₁ × H₂`.

For a non-cyclic prime power `G = (ZMod (p^a))ˣ`, supply the structure `MulEquiv e`
(e.g. `BealTwoAdicIso.unitsEquiv` for `p = 2`) and this reads off the count.
The k-variable counting is done here in full; only `e` is group-specific. -/
theorem count_of_mulEquiv_prod_cyclic_kvar
    {G H₁ H₂ : Type*} [CommGroup G] [Group H₁] [Group H₂]
    [Finite H₁] [Finite H₂] [IsCyclic H₁] [IsCyclic H₂] [Nonempty H₁] [Nonempty H₂]
    (e : G ≃* (H₁ × H₂)) (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card (KSolSet G k x)
      = (Nat.card H₁ ^ (k - 1) * Nat.gcd (Nat.card H₁) (Finset.univ.gcd x))
        * (Nat.card H₂ ^ (k - 1) * Nat.gcd (Nat.card H₂) (Finset.univ.gcd x)) := by
  -- transport the k-variable solution set across `e`, then apply the cyclic count.
  have hbij : KSolSet G k x ≃ KSolSet (H₁ × H₂) k x := by
    refine Equiv.subtypeEquiv (Equiv.piCongrRight (fun _ => e.toEquiv)) ?_
    intro A
    simp only [Equiv.piCongrRight_apply, MulEquiv.toEquiv_eq_coe, Pi.map_apply,
      EquivLike.coe_coe]
    rw [← e.map_eq_one_iff, map_prod]
    simp only [map_pow]
  rw [Nat.card_congr hbij, prod_cyclic_kvar_solution_count k hk x]

/-!
## 3. General ODD modulus, k variables

Combining HEADLINE #1 (multiplicativity over coprime moduli) with
`BealUnitsDensityKVar.units_lin_solution_count_prime_pow` (the odd-prime-power
cyclic k-variable count) via `Nat.multiplicative_factorization` gives the full
Beal-LOCAL multiplicative k-variable density over any odd modulus.
-/

/-- `f 1 = 1`: the k-variable unit-solution count over the trivial modulus `ZMod 1`
is `1` (the group `(ZMod 1)ˣ` is trivial, so the solution set is a singleton). -/
theorem units_kvar_solution_count_one (k : ℕ) (x : Fin k → ℕ) :
    Nat.card (KSolSet (ZMod 1)ˣ k x) = 1 := by
  haveI : Nonempty (KSolSet (ZMod 1)ˣ k x) := ⟨⟨fun _ => 1, by simp⟩⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-- **#3 (stretch, LANDED): explicit factorization product for ODD `n`.**
For odd `n > 0`, `k ≥ 1`, and any `x : Fin k → ℕ`, the k-variable unit-group Beal
count over `(ZMod n)ˣ` is the product over the prime factorization of `n`:

  `Nat.card {A : Fin k → (ZMod n)ˣ // ∏ i, (A i)^{x i} = 1}
     = ∏_{p^a ‖ n} φ(p^a)^(k-1) · gcd(φ(p^a), gcd x)`.

This is the full Beal-LOCAL multiplicative k-variable density over any odd modulus,
assembled from HEADLINE #1 (`units_kvar_solution_count_mul`) and the odd-prime-power
cyclic k-variable count
(`BealUnitsDensityKVar.units_lin_solution_count_prime_pow`) via
`Nat.multiplicative_factorization`. Oddness discharges the `p ≠ 2` hypothesis on
every prime factor. -/
theorem units_kvar_solution_count_odd
    (n : ℕ) (hn : Odd n) (hn0 : n ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card (KSolSet (ZMod n)ˣ k x)
      = n.factorization.prod fun p a =>
          Nat.totient (p ^ a) ^ (k - 1)
            * Nat.gcd (Nat.totient (p ^ a)) (Finset.univ.gcd x) := by
  have hmf := Nat.multiplicative_factorization
    (fun m => Nat.card (KSolSet (ZMod m)ˣ k x))
    (fun a b hab => units_kvar_solution_count_mul a b hab k x)
    (units_kvar_solution_count_one k x) hn0
  simp only at hmf
  rw [hmf]
  apply Finsupp.prod_congr
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hn)
      (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  haveI : Fact p.Prime := ⟨hpp⟩
  have hka : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  exact units_lin_solution_count_prime_pow p (n.factorization p) hp2 hka k hk x

end BealUnitsDensityKVarGen
