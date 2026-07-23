import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Everywhere-local-solubility: where Beal signatures have **no** congruence obstruction

The local-obstruction files (`BealTwoThreeLocal`, `BealThreeFourLocal`,
`BealFifthMixedLocal`, `BealCubeMod9`, …) prove that certain Beal/generalized-Fermat
signatures *miss* a residue at a special prime. This file proves the **dual**: at the
natural small moduli the bare sum `a^x + b^y` is **surjective** onto `ZMod m`, so there is
**no** congruence obstruction there. Each such theorem is a machine-checked
`∀ r, ∃ a b, a^x + b^y = r` (a finite `decide`).

## Why this matters (the Hasse-principle reading)

For the signatures `(2,3,n)`, `(3,4,z)`, `(4,5,z)`, `(3,5,z)` the obstruction found at the
special prime (`a²+b³` needs the `a`-odd refinement; `13 ∣` for `(3,4)`; `11 ∣` for
`(4,5)`; `31 ∣` for `(3,5)`) is **isolated** — the other small moduli below are
surjective, so no single congruence rules the signature out. The conjecture
nonetheless predicts no primitive solution. In other words Beal asserts a (conjectural)
**failure of the Hasse / local-global principle** for these signatures: they are locally
soluble at essentially every modulus yet (conjecturally) globally insoluble. This is
exactly the regime where the global methods — cyclotomic descent, ABC, modularity —
are *unavoidable*; no elementary local sieve can finish.

## The lone genuinely-local signature: `(4,4,z)`

By contrast `(4,4,z)` carries a robust **2-adic** obstruction already in the bare sum: a
fourth power is `0` or `1 (mod 16)`, so `a⁴ + b⁴ ∈ {0,1,2} (mod 16)` and the sum is **not**
surjective mod 16 (`fourfour_not_surjective_mod16`). So `(4,4,z)` is the outlier of this
group — locally restricted at 2 — which is consistent with its unconditional even-`z`
closure (`BealFourthPowerLocal.beal_44z_of_even_z`).

## Discipline

Every statement is a finite `decide` over `ZMod m` (NOT `native_decide`). Surjectivity
was confirmed by `#eval` of the image before assertion. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

Typecheck with `lake env lean BealLocalSolubility.lean`.
-/

namespace BealLocalSolubility

/-! ## 1. `(2,3,n)`: `a² + b³` is surjective (no bare obstruction) -/

/-- `a² + b³` hits every residue mod 8 (the bare sum has no obstruction; the genuine
`(2,3,n)` obstruction needs the `a`-odd refinement, cf. `BealTwoThreeLocal`). -/
theorem twothree_surjective_mod8 : ∀ r : ZMod 8, ∃ a b : ZMod 8, a ^ 2 + b ^ 3 = r := by decide

/-- `a² + b³` is surjective mod 16 as well. -/
theorem twothree_surjective_mod16 : ∀ r : ZMod 16, ∃ a b : ZMod 16, a ^ 2 + b ^ 3 = r := by decide

/-- `a² + b³` is surjective mod 9. -/
theorem twothree_surjective_mod9 : ∀ r : ZMod 9, ∃ a b : ZMod 9, a ^ 2 + b ^ 3 = r := by decide

/-! ## 2. `(3,4,z)`: surjective away from the lone obstruction prime 13 -/

/-- `a³ + b⁴` is surjective mod 16 (no 2-adic obstruction for this signature). -/
theorem threefour_surjective_mod16 : ∀ r : ZMod 16, ∃ a b : ZMod 16, a ^ 3 + b ^ 4 = r := by decide

/-- `a³ + b⁴` is surjective mod 9. -/
theorem threefour_surjective_mod9 : ∀ r : ZMod 9, ∃ a b : ZMod 9, a ^ 3 + b ^ 4 = r := by decide

/-- `a³ + b⁴` is surjective mod 7 — so the `(3,4,z)` obstruction at `13`
(`BealThreeFourLocal`) is isolated among small primes. -/
theorem threefour_surjective_mod7 : ∀ r : ZMod 7, ∃ a b : ZMod 7, a ^ 3 + b ^ 4 = r := by decide

/-! ## 3. `(4,5,z)` and `(3,5,z)`: surjective away from their obstruction primes -/

/-- `a⁴ + b⁵` is surjective mod 25 (the `(4,5,z)` obstruction lives at `11`, cf.
`BealFifthMixedLocal`). -/
theorem fourfive_surjective_mod25 : ∀ r : ZMod 25, ∃ a b : ZMod 25, a ^ 4 + b ^ 5 = r := by decide

/-- `a³ + b⁵` is surjective mod 25; mod 11 it is surjective too (the cube map is already
a bijection there), which is why the `(3,5,z)` obstruction needs the bigger prime `31`. -/
theorem threefive_surjective_mod25 : ∀ r : ZMod 25, ∃ a b : ZMod 25, a ^ 3 + b ^ 5 = r := by decide

/-- `a³ + b⁵` is surjective mod 11. -/
theorem threefive_surjective_mod11 : ∀ r : ZMod 11, ∃ a b : ZMod 11, a ^ 3 + b ^ 5 = r := by decide

/-! ## 4. The contrast: `(4,4,z)` IS locally restricted at 2 -/

/-- **`(4,4,z)` is the outlier: `a⁴ + b⁴` is NOT surjective mod 16.** A fourth power is
`0` or `1 (mod 16)`, so the sum lies in `{0,1,2}` and misses the other thirteen residues
— a genuine bare 2-adic obstruction (unlike the signatures above). -/
theorem fourfour_not_surjective_mod16 :
    ¬ (∀ r : ZMod 16, ∃ a b : ZMod 16, a ^ 4 + b ^ 4 = r) := by decide

/-! ## 5. Axiom checks -/

#print axioms twothree_surjective_mod16
#print axioms threefour_surjective_mod16
#print axioms fourfive_surjective_mod25
#print axioms threefive_surjective_mod25
#print axioms fourfour_not_surjective_mod16

end BealLocalSolubility
