import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Propositio.Beal.UnitsDensity

/-!
# Beal unit-group density over a GENERAL modulus (NEW, no LaTTe sibling)

NEW (no LaTTe sibling) — unit-group Beal-local density over a general modulus via
CRT on units; extends `BealUnitsDensity` from prime powers.

`BealUnitsDensity` proves the multiplicative unit-group count over a *prime power*:
for an odd prime `p` and `k ≥ 1`,
`Nat.card {q : (ZMod (p^k))ˣ × (ZMod (p^k))ˣ // q.1^x * q.2^y = 1}
   = φ(p^k) · gcd(φ(p^k), gcd x y)`.

This file lifts that to a **general modulus** by Chinese Remainder on *units*.
The key external input is the units-CRT isomorphism
`(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ` for coprime `m, n`
(`(Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits`).
A `MulEquiv` preserves `^`, `*`, and `1`, so the condition `A^x · B^y = 1`
transfers componentwise, giving an `Equiv` of unit-solution sets whose cardinality
is the product. This mirrors `BealDensityGeneral.pair_solution_count_mul` (the
additive CRT step) but on the genuine multiplicative congruence.

## What is new here

* `unitsChineseRemainder` — the units-CRT `MulEquiv`
  `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`, packaged for reuse.
* `units_pairHom_chineseRemainder_equiv` — the **CRT bijection** on unit-solution
  sets: for coprime `m, n` the set `{q // q.1^x*q.2^y=1}` over `(ZMod (m*n))ˣ` is
  in explicit bijection with the product of the corresponding sets over
  `(ZMod m)ˣ` and `(ZMod n)ˣ`.
* `units_pair_solution_count_mul` (**HEADLINE #1**) — multiplicativity of the
  unit-group count over coprime moduli.
* `units_pair_solution_count_odd` (#2, stretch) — explicit product over the
  factorization for odd `n` (status documented at the theorem).
-/

namespace BealUnitsDensityGeneral

open BealUnitsDensity

/-!
## 0. The units-CRT isomorphism

For coprime `m, n`, lift the ring-CRT iso `ZMod (m*n) ≃+* ZMod m × ZMod n`
to the unit groups: `(ZMod (m*n))ˣ ≃* (ZMod m × ZMod n)ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.
-/

/-- **Units CRT isomorphism (NEW packaging).** For coprime `m, n`,
`(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`, obtained by applying `Units.mapEquiv`
to the ring-CRT `MulEquiv` and then splitting the product units via
`MulEquiv.prodUnits`. -/
noncomputable def unitsChineseRemainder (m n : ℕ) (h : Nat.Coprime m n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-!
## 1. The CRT bijection on unit-solution sets
-/

/-- The unit-solution-set subtype: pairs of units `(A,B)` with `A^x · B^y = 1`. -/
abbrev USolSet (N x y : ℕ) :=
  {q : (ZMod N)ˣ × (ZMod N)ˣ // q.1 ^ x * q.2 ^ y = 1}

/-- **CRT bijection on unit-solution sets (NEW).**
For coprime `m, n`, the unit-solution set over `(ZMod (m*n))ˣ` is in explicit
bijection with the product of the unit-solution sets over `(ZMod m)ˣ` and
`(ZMod n)ˣ`, transported along the units-CRT isomorphism. The condition
`A^x · B^y = 1` transfers componentwise because the iso is a `MulEquiv`
(preserves `^`, `*`, `1`). -/
noncomputable def units_pairHom_chineseRemainder_equiv
    (m n : ℕ) (h : Nat.Coprime m n) (x y : ℕ) :
    USolSet (m * n) x y ≃ USolSet m x y × USolSet n x y := by
  -- `e : (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.
  let e := unitsChineseRemainder m n h
  -- Equiv on the ambient pair space:
  --   ((ZMod (m*n))ˣ)²  ≃  ((ZMod m)ˣ × (ZMod n)ˣ)²  ≃  ((ZMod m)ˣ)² × ((ZMod n)ˣ)².
  let E : ((ZMod (m * n))ˣ × (ZMod (m * n))ˣ)
        ≃ ((ZMod m)ˣ × (ZMod m)ˣ) × ((ZMod n)ˣ × (ZMod n)ˣ) :=
    (e.prodCongr e).toEquiv.trans
      (Equiv.prodProdProdComm (ZMod m)ˣ (ZMod n)ˣ (ZMod m)ˣ (ZMod n)ˣ)
  refine (Equiv.subtypeEquiv E ?_).trans
    (Equiv.subtypeProdEquivProd
      (p := fun q : (ZMod m)ˣ × (ZMod m)ˣ => q.1 ^ x * q.2 ^ y = 1)
      (q := fun q : (ZMod n)ˣ × (ZMod n)ˣ => q.1 ^ x * q.2 ^ y = 1))
  rintro ⟨a, b⟩
  -- LHS condition over `(ZMod (m*n))ˣ`.
  show a ^ x * b ^ y = 1 ↔ _
  -- Apply `e` (a MulEquiv): `c = 1 ↔ e c = 1`, and `e` commutes with `*`, `^`.
  rw [← e.map_eq_one_iff, map_mul, map_pow, map_pow]
  -- Now compare in `(ZMod m)ˣ × (ZMod n)ˣ`, componentwise.
  rw [Prod.ext_iff]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd,
    Prod.fst_one, Prod.snd_one]
  rfl

/-!
## 2. HEADLINE #1 — multiplicativity of the unit-group count
-/

/-- **HEADLINE #1 (NEW).** The unit-group Beal count is multiplicative over
coprime moduli. For coprime `m, n > 0` and any `x, y`, the number of unit-pairs
`(A,B)` with `A^x · B^y = 1` over `(ZMod (m*n))ˣ` equals the product of the
corresponding counts over `(ZMod m)ˣ` and `(ZMod n)ˣ`.

Proved by transporting the unit-solution set along the units-CRT isomorphism
(`units_pairHom_chineseRemainder_equiv`) and reading off cardinalities. No LaTTe
sibling: the LaTTe corpus never combined two moduli on the unit groups. -/
theorem units_pair_solution_count_mul
    (m n : ℕ) (h : Nat.Coprime m n) (x y : ℕ) :
    Nat.card (USolSet (m * n) x y)
      = Nat.card (USolSet m x y) * Nat.card (USolSet n x y) := by
  rw [Nat.card_congr (units_pairHom_chineseRemainder_equiv m n h x y), Nat.card_prod]

/-!
## 3. #2 (stretch) — explicit product over the factorization for ODD `n`

Combining HEADLINE #1 (multiplicativity) with
`BealUnitsDensity.units_pair_solution_count_prime_pow` (the prime-power closed
form, which requires the odd-prime hypothesis `p ≠ 2`) via Nat's
`multiplicative_factorization`, we obtain the full Beal-LOCAL multiplicative
density over any **odd** modulus as a product over its prime factorization.

The base case `f 1 = 1` holds because `(ZMod 1)ˣ` is a subsingleton, so the
unit-solution set over `ZMod 1` is a singleton `{(1,1)}`. Each factor `p^k` in
the factorization has `p` an odd prime (since `n` is odd, every prime factor is
`≠ 2`) and `k = n.factorization p ≠ 0`, so the prime-power closed form applies.
-/

/-- `f 1 = 1`: the unit-solution count over the trivial modulus `ZMod 1` is `1`
(the group `(ZMod 1)ˣ` is trivial, so `{(A,B) // A^x·B^y=1}` is a singleton). -/
theorem units_pair_solution_count_one (x y : ℕ) :
    Nat.card (USolSet 1 x y) = 1 := by
  haveI : Nonempty (USolSet 1 x y) := ⟨⟨(1, 1), by simp⟩⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-- **#2 (stretch, LANDED): explicit factorization product for ODD `n`.**
For odd `n > 0` and any `x, y`, the unit-group Beal count over `(ZMod n)ˣ` is the
product over the prime factorization of `n`:
`Nat.card {q : (ZMod n)ˣ × (ZMod n)ˣ // q.1^x*q.2^y=1}
   = ∏ (p^k) in n.factorization, φ(p^k) · gcd(φ(p^k), gcd x y)`.

This is the full Beal-LOCAL multiplicative density over any odd modulus, assembled
from HEADLINE #1 (`units_pair_solution_count_mul`, multiplicativity over coprime
moduli) and `BealUnitsDensity.units_pair_solution_count_prime_pow` (the
odd-prime-power closed form), via `Nat.multiplicative_factorization`. Oddness is
used exactly to discharge the `p ≠ 2` hypothesis on every prime factor. -/
theorem units_pair_solution_count_odd
    (n : ℕ) (hn : Odd n) (hn0 : n ≠ 0) (x y : ℕ) :
    Nat.card (USolSet n x y)
      = n.factorization.prod fun p k =>
          Nat.totient (p ^ k) * Nat.gcd (Nat.totient (p ^ k)) (Nat.gcd x y) := by
  -- Evaluate the multiplicative function `f m = Nat.card (USolSet m x y)` over
  -- the factorization of `n`.
  have hmf := Nat.multiplicative_factorization
    (fun m => Nat.card (USolSet m x y))
    (fun a b hab => units_pair_solution_count_mul a b hab x y)
    (units_pair_solution_count_one x y) hn0
  simp only at hmf
  rw [hmf]
  -- Rewrite each prime-power factor `f (p^k)` by the prime-power closed form.
  apply Finsupp.prod_congr
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  haveI : Fact p.Prime := ⟨hpp⟩
  have hk : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  exact units_pair_solution_count_prime_pow p (n.factorization p) hp2 hk x y

end BealUnitsDensityGeneral
