import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Propositio.Beal.Density

/-!
# Beal MULTIPLICATIVE unit-group density

NEW capstone (no LaTTe sibling) — multiplicative unit-group density bridging the
additive exponent count (`BealDensity`) to `A^x·B^y = 1` via the cyclic log iso.

`BealDensity.pair_solution_count` counts, in the *additive* exponent space
`ZMod n × ZMod n`, the pairs `(a,b)` with `x•a + y•b = 0`:

  `Nat.card (pairHom n x y).ker = n · gcd(n, gcd(x, y))`.

That is a statement about the *exponents*. The actual Beal-local object is a
count of **units**: how many pairs of units `(A,B)` satisfy `A^x · B^y = 1` in
`(ZMod (p^k))ˣ`. This file makes the bridge precise and proves the unit-group
count.

The bridge is the cyclic **discrete logarithm**: a finite cyclic group `G` of
order `N` carries a `MulEquiv` `Multiplicative (ZMod N) ≃* G`
(`zmodCyclicMulEquiv`), whose inverse composed with `Multiplicative.toAdd` is a
log map `φ : G ≃ ZMod N` satisfying `φ(A·B) = φA + φB` and `φ(Aᵏ) = k•φA`.
Under `φ`, `A^x · B^y = 1 ↔ x•(φA) + y•(φB) = 0`, so the unit-solution set
biject with `(pairHom N x y).ker`. Transporting the additive count gives:

  **abstract:** for a finite cyclic group `G` of order `N`,
  `Nat.card { (A,B) : G×G // A^x · B^y = 1 } = N · gcd(N, gcd(x,y))`.

  **concrete:** for an odd prime `p` and `k ≥ 1`, taking `G = (ZMod (p^k))ˣ`
  (cyclic, of order `φ(p^k) = p^{k-1}(p-1)`),
  `Nat.card { (A,B) : units² // A^x · B^y = 1 } = φ(p^k) · gcd(φ(p^k), gcd(x,y))`
  — the genuine Beal-local multiplicative density.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealUnitsDensity.lean` to typecheck.

Key mathlib lemmas relied on:
* `zmodCyclicMulEquiv` (`Mathlib.GroupTheory.SpecificGroups.Cyclic`) — the
  `Multiplicative (ZMod (Nat.card G)) ≃* G` for a cyclic group `G` (discrete log).
* `ZMod.isCyclic_units_of_prime_pow` (`Mathlib.RingTheory.ZMod.UnitsCyclic`) —
  `(ZMod (p^n))ˣ` is cyclic for odd prime `p`.
* `ZMod.card_units_eq_totient`, `Nat.totient_prime_pow`.
* `BealDensity.pair_solution_count` — the additive exponent-space count.
-/

namespace BealUnitsDensity

open BealDensity

/-!
## 1. The discrete-log bijection

For a finite cyclic group `G` of order `N`, the unit-solution set
`{ (A,B) // A^x · B^y = 1 }` biject with the additive kernel
`(pairHom N x y).ker ⊆ ZMod N × ZMod N`, via the discrete logarithm
`φ = Multiplicative.toAdd ∘ (zmodCyclicMulEquiv).symm`.
-/

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/-- **Discrete-log bijection.** In a finite cyclic group `G` of order
`N = Nat.card G`, the set of unit-pairs `(A,B)` with `A^x · B^y = 1` is in
bijection with the additive kernel `(pairHom N x y).ker`.

This is the multiplicative-to-additive bridge: `φ A := toAdd ((zmodCyclicMulEquiv).symm A)`
is the discrete log, a group iso `G ≃ ZMod N` (additively), under which
`A^x · B^y = 1 ⟺ x•(φA) + y•(φB) = 0`. -/
noncomputable def logEquiv (x y : ℕ) [Nonempty G] :
    {p : G × G // p.1 ^ x * p.2 ^ y = 1} ≃ (pairHom (Nat.card G) x y).ker := by
  set N := Nat.card G with hN
  set e := zmodCyclicMulEquiv (G := G) inferInstance with he
  -- the discrete log φ : G ≃ ZMod N
  let φ : G ≃ ZMod N := e.symm.toEquiv.trans Multiplicative.toAdd
  -- φ is an additive group hom (transported from the MulEquiv e.symm)
  have hadd : ∀ A B : G, φ (A * B) = φ A + φ B := by
    intro A B; show Multiplicative.toAdd (e.symm (A * B)) = _; rw [map_mul]; rfl
  have hpow : ∀ (A : G) (j : ℕ), φ (A ^ j) = j • φ A := by
    intro A j; show Multiplicative.toAdd (e.symm (A ^ j)) = _; rw [map_pow]; rfl
  have hone : φ 1 = 0 := by show Multiplicative.toAdd (e.symm 1) = _; rw [map_one]; rfl
  refine Equiv.subtypeEquiv (φ.prodCongr φ) ?_
  intro p
  simp only [AddMonoidHom.mem_ker, pairHom_apply, Equiv.prodCongr_apply, Prod.map]
  rw [← hpow, ← hpow, ← hadd]
  constructor
  · intro h; rw [h, hone]
  · intro h; exact φ.injective (by rw [h, hone])

/-!
## 2. Abstract headline — cyclic-group multiplicative count
-/

/-- **HEADLINE (abstract).** For a finite cyclic group `G` of order
`N = Nat.card G` and exponents `x y : ℕ`, the number of unit-pairs `(A,B)`
with `A^x · B^y = 1` equals `N · gcd(N, gcd(x, y))`  (= `N · gcd(x,y,N)`).

Proof: transport `BealDensity.pair_solution_count` across the discrete-log
bijection `logEquiv`. -/
theorem cyclic_pair_solution_count (x y : ℕ) [Nonempty G] :
    Nat.card {p : G × G // p.1 ^ x * p.2 ^ y = 1}
      = Nat.card G * Nat.gcd (Nat.card G) (Nat.gcd x y) := by
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  rw [Nat.card_congr (logEquiv x y)]
  exact pair_solution_count (Nat.card G) x y

/-!
## 3. Concrete specialization — the Beal-local unit density `(ZMod (p^k))ˣ`
-/

/-- **HEADLINE (concrete).** For an odd prime `p` and `k ≥ 1`, in the unit group
`(ZMod (p^k))ˣ` — which is cyclic of order `φ(p^k)` — the number of unit-pairs
`(A,B)` with `A^x · B^y = 1` equals `φ(p^k) · gcd(φ(p^k), gcd(x, y))`.

This is the genuine **Beal-local multiplicative density**: the additive
exponent-space count of `BealDensity` realised on the actual congruence
`A^x · B^y ≡ 1 (mod p^k)`. -/
theorem units_pair_solution_count_prime_pow
    (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (_hk : k ≠ 0) (x y : ℕ) :
    Nat.card {q : (ZMod (p ^ k))ˣ × (ZMod (p ^ k))ˣ // q.1 ^ x * q.2 ^ y = 1}
      = Nat.totient (p ^ k)
        * Nat.gcd (Nat.totient (p ^ k)) (Nat.gcd x y) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ k))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p (Fact.out (p := p.Prime)) hp2 k
  -- N = Nat.card units = φ(p^k)
  have hcard : Nat.card (ZMod (p ^ k))ˣ = Nat.totient (p ^ k) := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units_eq_totient (p ^ k)
  have := cyclic_pair_solution_count (G := (ZMod (p ^ k))ˣ) x y
  rwa [hcard] at this

/-- **Explicit closed form.** Same count as `units_pair_solution_count_prime_pow`
written with `φ(p^k)` expanded to `p^{k-1}·(p-1)`. -/
theorem units_pair_solution_count_prime_pow_explicit
    (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hk : k ≠ 0) (x y : ℕ) :
    Nat.card {q : (ZMod (p ^ k))ˣ × (ZMod (p ^ k))ˣ // q.1 ^ x * q.2 ^ y = 1}
      = p ^ (k - 1) * (p - 1)
        * Nat.gcd (p ^ (k - 1) * (p - 1)) (Nat.gcd x y) := by
  have htot : Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
    Nat.totient_prime_pow (Fact.out (p := p.Prime)) (Nat.pos_of_ne_zero hk)
  rw [units_pair_solution_count_prime_pow p k hp2 hk x y, htot]

end BealUnitsDensity
