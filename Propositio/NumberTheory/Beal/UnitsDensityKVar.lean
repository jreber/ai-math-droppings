import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Propositio.NumberTheory.Beal.DensityKVar

/-!
# Beal MULTIPLICATIVE unit-group count — k variables

NEW (no LaTTe sibling) — k-variable multiplicative unit-group count; multiplicative
analog of `BealDensityKVar.lin_solution_count` via discrete log.

`BealDensityKVar.lin_solution_count` counts, in the *additive* exponent space
`Fin k → ZMod n`, the tuples `v` with `∑ i, xᵢ • vᵢ = 0`:

  `Nat.card (linHom n k x).ker = n^(k-1) · gcd(n, gcd of all xᵢ)`.

That is a statement about *exponents*. The Beal-local multiplicative object is a
count of **group elements**: how many `k`-tuples of group elements `A : Fin k → G`
satisfy `∏ i, Aᵢ^{xᵢ} = 1`. This file makes the bridge precise and proves the
unit-group count.

The bridge is the cyclic **discrete logarithm**: a finite cyclic group `G` of
order `N` carries a `MulEquiv` `Multiplicative (ZMod N) ≃* G`
(`zmodCyclicMulEquiv`), whose inverse composed with `Multiplicative.toAdd` is a
log map `φ : G ≃ ZMod N` satisfying `φ(A·B) = φA + φB` and `φ(Aᵏ) = k•φA`.
Under the pointwise log `Φ : (Fin k → G) ≃ (Fin k → ZMod N)`,
`∏ i, Aᵢ^{xᵢ} = 1 ↔ ∑ i, xᵢ•(φ Aᵢ) = 0`, so the multiplicative-solution set
biject with `(linHom N k x).ker`. Transporting the additive count gives:

  **HEADLINE:** for a finite cyclic group `G` of order `N = Nat.card G`,
  `k ≥ 1`, and exponents `x : Fin k → ℕ`,
  `Nat.card { A : Fin k → G // ∏ i, Aᵢ^{xᵢ} = 1 } = N^(k-1) · gcd(N, gcd xᵢ)`.

  **concrete:** for an odd prime `p` and `k' ≥ 1`, taking `G = (ZMod (p^k'))ˣ`
  (cyclic of order `φ(p^k') = p^{k'-1}(p-1)`),
  `Nat.card { A : Fin k → units // ∏ i, Aᵢ^{xᵢ} = 1 }
     = φ(p^k')^(k-1) · gcd(φ(p^k'), gcd xᵢ)`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealUnitsDensityKVar.lean` to typecheck.

This mirrors `BealUnitsDensity.logEquiv` / `cyclic_pair_solution_count`
(the `k = 2` / `prodCongr` case) using `Equiv.piCongrRight` for the `k`-fold log.
-/

namespace BealUnitsDensityKVar

open BealDensityKVar

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

-- A finite cyclic group is commutative, so `∏ i, Aᵢ^{xᵢ}` is well-defined.
-- This local instance supplies the `CommGroup` (hence `CommMonoid`) structure that
-- `Finset.prod` requires, derived from `IsCyclic G` via `IsCyclic.commGroup`.
attribute [local instance] IsCyclic.commGroup

/-!
## 1. The discrete-log bijection (k variables)

For a finite cyclic group `G` of order `N`, the multiplicative-solution set
`{ A : Fin k → G // ∏ i, Aᵢ^{xᵢ} = 1 }` biject with the additive kernel
`(linHom N k x).ker`, via the pointwise discrete logarithm
`φ = Multiplicative.toAdd ∘ (zmodCyclicMulEquiv).symm`.
-/

/-- **Discrete-log bijection (k-variable).** In a finite cyclic group `G` of order
`N = Nat.card G`, the set of `k`-tuples `A : Fin k → G` with `∏ i, Aᵢ^{xᵢ} = 1` is
in bijection with the additive kernel `(linHom N k x).ker`.

This is the multiplicative-to-additive bridge: `φ A := toAdd ((zmodCyclicMulEquiv).symm A)`
is the discrete log, a group iso `G ≃ ZMod N` (additively), and `Φ := Equiv.piCongrRight (fun _ => φ)`
is its pointwise lift, under which `∏ i, Aᵢ^{xᵢ} = 1 ⟺ ∑ i, xᵢ•(φ Aᵢ) = 0`. -/
noncomputable def logPiEquiv (k : ℕ) (x : Fin k → ℕ) [Nonempty G] :
    {A : Fin k → G // ∏ i, (A i) ^ (x i) = 1} ≃ (linHom (Nat.card G) k x).ker := by
  set N := Nat.card G with hN
  set e := zmodCyclicMulEquiv (G := G) inferInstance with he
  -- the discrete log φ : G ≃ ZMod N
  let φ : G ≃ ZMod N := e.symm.toEquiv.trans Multiplicative.toAdd
  have hpow : ∀ (A : G) (j : ℕ), φ (A ^ j) = j • φ A := by
    intro A j; show Multiplicative.toAdd (e.symm (A ^ j)) = _; rw [map_pow]; rfl
  have hone : φ 1 = 0 := by show Multiplicative.toAdd (e.symm 1) = _; rw [map_one]; rfl
  -- φ on a finite product ∏ → ∑
  have hprod : ∀ (A : Fin k → G), φ (∏ i, A i) = ∑ i, φ (A i) := by
    intro A
    show Multiplicative.toAdd (e.symm (∏ i, A i)) = _
    rw [map_prod]
    rfl
  -- the pointwise log Φ : (Fin k → G) ≃ (Fin k → ZMod N)
  refine Equiv.subtypeEquiv (Equiv.piCongrRight (fun _ => φ)) ?_
  intro A
  simp only [AddMonoidHom.mem_ker, linHom_apply, Equiv.piCongrRight_apply, Pi.map_apply]
  -- goal: (∏ i, A i ^ x i = 1) ↔ (∑ i, x i • φ (A i) = 0)
  -- rewrite RHS: ∑ x i • φ (A i) = ∑ φ (A i ^ x i) = φ (∏ A i ^ x i)
  have hrhs : (∑ i, (x i) • φ (A i)) = φ (∏ i, (A i) ^ (x i)) := by
    rw [hprod]
    apply Finset.sum_congr rfl
    intro i _; rw [hpow]
  rw [hrhs]
  constructor
  · intro h; rw [h, hone]
  · intro h; exact φ.injective (by rw [h, hone])

/-!
## 2. Abstract headline — cyclic-group multiplicative k-variable count
-/

/-- **HEADLINE (abstract).** For a finite cyclic group `G` of order
`N = Nat.card G`, `k ≥ 1`, and exponents `x : Fin k → ℕ`, the number of
`k`-tuples `A : Fin k → G` with `∏ i, Aᵢ^{xᵢ} = 1` equals
`N^(k-1) · gcd(N, gcd of all xᵢ)`.

Proof: transport `BealDensityKVar.lin_solution_count` across the pointwise
discrete-log bijection `logPiEquiv`. This is the multiplicative analog of the
additive k-variable count. -/
theorem cyclic_lin_solution_count (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) [Nonempty G] :
    Nat.card {A : Fin k → G // ∏ i, (A i) ^ (x i) = 1}
      = Nat.card G ^ (k - 1) * Nat.gcd (Nat.card G) (Finset.univ.gcd x) := by
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  rw [Nat.card_congr (logPiEquiv k x)]
  exact lin_solution_count (Nat.card G) k hk x

/-!
## 3. k=2 reduction — recovers the pair count
-/

/-- k=2 reduction: the headline at `k = 2` with coefficient vector `![x, y]`
gives `N · gcd(N, gcd x y)`, matching `BealUnitsDensity.cyclic_pair_solution_count`
(modulo the `∏`/`prod` vs `·` phrasing). -/
theorem cyclic_lin_solution_count_two (x y : ℕ) [Nonempty G] :
    Nat.card {A : Fin 2 → G // ∏ i, (A i) ^ ((![x, y] : Fin 2 → ℕ) i) = 1}
      = Nat.card G * Nat.gcd (Nat.card G) (Nat.gcd x y) := by
  rw [cyclic_lin_solution_count 2 (by norm_num) ![x, y]]
  have hg : Finset.univ.gcd (![x, y] : Fin 2 → ℕ) = Nat.gcd x y := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
    rw [Finset.gcd_insert, Finset.gcd_singleton]
    simp [gcd_eq_nat_gcd]
  rw [hg]
  congr 1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]

/-!
## 4. Concrete specialization — the Beal-local unit density `(ZMod (p^k'))ˣ`
-/

/-- **HEADLINE (concrete).** For an odd prime `p` and `k' ≥ 1`, in the unit group
`(ZMod (p^k'))ˣ` — which is cyclic of order `φ(p^k')` — the number of `k`-tuples
`A : Fin k → units` with `∏ i, Aᵢ^{xᵢ} = 1` equals
`φ(p^k')^(k-1) · gcd(φ(p^k'), gcd of all xᵢ)`.

This is the genuine **Beal-local multiplicative density** in `k` variables: the
additive exponent-space count of `BealDensityKVar` realised on the actual
congruence `∏ i, Aᵢ^{xᵢ} ≡ 1 (mod p^k')`. -/
theorem units_lin_solution_count_prime_pow
    (p k' : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (_hk' : k' ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card {A : Fin k → (ZMod (p ^ k'))ˣ // ∏ i, (A i) ^ (x i) = 1}
      = Nat.totient (p ^ k') ^ (k - 1)
        * Nat.gcd (Nat.totient (p ^ k')) (Finset.univ.gcd x) := by
  haveI : NeZero (p ^ k') := ⟨pow_ne_zero k' (Fact.out (p := p.Prime)).ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ k'))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p (Fact.out (p := p.Prime)) hp2 k'
  -- N = Nat.card units = φ(p^k')
  have hcard : Nat.card (ZMod (p ^ k'))ˣ = Nat.totient (p ^ k') := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units_eq_totient (p ^ k')
  have := cyclic_lin_solution_count (G := (ZMod (p ^ k'))ˣ) k hk x
  rwa [hcard] at this

/-- **Explicit closed form.** Same count as `units_lin_solution_count_prime_pow`
written with `φ(p^k')` expanded to `p^{k'-1}·(p-1)`. -/
theorem units_lin_solution_count_prime_pow_explicit
    (p k' : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hk' : k' ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card {A : Fin k → (ZMod (p ^ k'))ˣ // ∏ i, (A i) ^ (x i) = 1}
      = (p ^ (k' - 1) * (p - 1)) ^ (k - 1)
        * Nat.gcd (p ^ (k' - 1) * (p - 1)) (Finset.univ.gcd x) := by
  have htot : Nat.totient (p ^ k') = p ^ (k' - 1) * (p - 1) :=
    Nat.totient_prime_pow (Fact.out (p := p.Prime)) (Nat.pos_of_ne_zero hk')
  rw [units_lin_solution_count_prime_pow p k' hp2 hk' k hk x, htot]

end BealUnitsDensityKVar
