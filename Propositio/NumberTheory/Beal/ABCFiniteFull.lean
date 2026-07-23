import Propositio.NumberTheory.Beal.Radical
import Propositio.NumberTheory.Beal.ABCFinite
import Mathlib.Tactic

/-!
# ABC ⟹ finitely many primitive Beal solutions (per exponent triple, Lean 4)

This file **strengthens** `BealABCFinite` from a bounded *base* to per-exponent-triple
finiteness of the entire primitive Beal **solution set** — the Granville
"ABC ⟹ finitely many Beal solutions (for each fixed large exponent triple)".

`BealABCFinite.beal_base_bounded` gives, under ABC, an exponent threshold `N` and an
absolute constant `M` with `C ≤ M` for every primitive solution `Aˣ + Bʸ = Cᶻ`
(`A, B, C ≥ 2`, `min(x,y,z) ≥ N`).  For a *fixed* exponent triple `(x,y,z)` this bound
on the base immediately bounds the other two components:

* `A ≤ Aˣ ≤ Aˣ + Bʸ = Cᶻ ≤ ⌊M⌋₊ᶻ` (using `1 ≤ A`, `1 ≤ x`, `C ≤ ⌊M⌋₊`), and likewise
  `B ≤ Bʸ ≤ Cᶻ ≤ ⌊M⌋₊ᶻ`.

Hence for fixed `(x,y,z)` the solution triples `(A,B,C)` live in the finite box
`Iic ⌊M⌋₊ᶻ × Iic ⌊M⌋₊ᶻ × Iic ⌊M⌋₊`, so there are only finitely many.

## Contents
* `base_bounds_components` — from `Aˣ + Bʸ = Cᶻ`, `A, B, C ≥ 2`, `1 ≤ x, y`, and
  `C ≤ D` (`D : ℕ`), the crude component bounds `A ≤ Dᶻ` and `B ≤ Dᶻ`.
* `beal_solutions_finite` — **headline**: ABC ⟹ for each fixed exponent triple with
  `min(x,y,z) ≥ N`, the set of primitive Beal solutions `(A,B,C)` is finite.

The genuine uniform statement (finiteness of the full `(A,B,C,x,y,z)` solution set)
is *not* proved here: with the base `C` bounded but `z` unbounded a priori, `Cᶻ`
ranges over arbitrarily large values, so `A, B` are not uniformly bounded and the
exponent `z` is not bounded either.  Per-exponent-triple finiteness is the clean
conditional theorem; see the closing remark.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17).  Use
`lake env lean BealABCFiniteFull.lean` to typecheck.
-/

namespace BealABCFiniteFull

open scoped Real

/-! ## 1. A base bound on `C` bounds the other two components -/

/-- **Component bounds.** In a primitive Beal solution `Aˣ + Bʸ = Cᶻ` with
`A, B, C ≥ 2`, exponents `x, y ≥ 1`, and a base bound `C ≤ D` over `ℕ`, both other
components are bounded by `Dᶻ`: `A ≤ Dᶻ` and `B ≤ Dᶻ`.

Proof (crude, all in `ℕ`): `A ≤ Aˣ` (since `1 ≤ A`, `1 ≤ x`), `Aˣ ≤ Aˣ + Bʸ = Cᶻ`,
and `Cᶻ ≤ Dᶻ` (monotonicity of `· ^ z`); symmetrically for `B`. -/
theorem base_bounds_components {A B C D x y z : ℕ}
    (_hA : 2 ≤ A) (_hB : 2 ≤ B) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hCD : C ≤ D) (hsum : A ^ x + B ^ y = C ^ z) :
    A ≤ D ^ z ∧ B ≤ D ^ z := by
  have hCz : C ^ z ≤ D ^ z := Nat.pow_le_pow_left hCD z
  -- A ≤ Aˣ ≤ Aˣ + Bʸ = Cᶻ ≤ Dᶻ
  have hAx : A ≤ A ^ x := Nat.le_self_pow (by omega) A
  have hAxC : A ^ x ≤ C ^ z := by omega
  -- B ≤ Bʸ ≤ Aˣ + Bʸ = Cᶻ ≤ Dᶻ
  have hBy : B ≤ B ^ y := Nat.le_self_pow (by omega) B
  have hByC : B ^ y ≤ C ^ z := by omega
  exact ⟨le_trans hAx (le_trans hAxC hCz), le_trans hBy (le_trans hByC hCz)⟩

/-! ## 2. Headline: ABC ⟹ finitely many primitive solutions per exponent triple -/

/-- **Headline (conditional Granville theorem, solution-set form).** Assume the ABC
conjecture.  Then there is an exponent threshold `N` such that for **every** fixed
exponent triple `(x, y, z)` with `min(x,y,z) ≥ N`, the set of primitive Beal
solutions `(A, B, C)` of `Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and `gcd(A,B) = 1` is
**finite**.

This strengthens `BealABCFinite.beal_base_bounded` (which bounds only the base `C`)
to honest finiteness of the full primitive solution set, exponent triple by exponent
triple.  The proof: `beal_base_bounded` gives `N` and an absolute `M` with `C ≤ M`,
so `C ≤ ⌊M⌋₊`; then `base_bounds_components` bounds `A, B ≤ ⌊M⌋₊ᶻ`, embedding the
solution set into the finite box `Iic ⌊M⌋₊ᶻ × Iic ⌊M⌋₊ᶻ × Iic ⌊M⌋₊`. -/
theorem beal_solutions_finite (habc : BealRadical.ABCConjecture) :
    ∃ N : ℕ, ∀ x y z : ℕ, N ≤ x → N ≤ y → N ≤ z →
      Set.Finite { p : ℕ × ℕ × ℕ |
        2 ≤ p.1 ∧ 2 ≤ p.2.1 ∧ 2 ≤ p.2.2 ∧ Nat.Coprime p.1 p.2.1 ∧
        p.1 ^ x + p.2.1 ^ y = p.2.2 ^ z } := by
  obtain ⟨N, M, hM⟩ := BealABCFinite.beal_base_bounded habc
  -- The threshold N controls the exponents; ⌊M⌋₊ is the integer base bound.
  refine ⟨max N 1, ?_⟩
  intro x y z hx hy hz
  set D : ℕ := Nat.floor M with hD
  -- Embed the solution set into the finite box  Iic (Dᶻ) × Iic (Dᶻ) × Iic D.
  apply Set.Finite.subset
    ((Set.finite_Iic (D ^ z)).prod
      ((Set.finite_Iic (D ^ z)).prod (Set.finite_Iic D)))
  rintro ⟨A, B, C⟩ ⟨hA, hB, hC, hcop, hsum⟩
  -- Exponent thresholds.
  have hxN : N ≤ x := le_trans (le_max_left N 1) hx
  have hyN : N ≤ y := le_trans (le_max_left N 1) hy
  have hzN : N ≤ z := le_trans (le_max_left N 1) hz
  have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
  have hy1 : 1 ≤ y := le_trans (le_max_right N 1) hy
  -- Base bound: C ≤ M over ℝ, hence C ≤ ⌊M⌋₊.
  have hCM : (C : ℝ) ≤ M := hM A B C x y z hA hB hC hxN hyN hzN hcop hsum
  have hCD : C ≤ D := Nat.le_floor hCM
  -- Component bounds: A, B ≤ Dᶻ.
  obtain ⟨hAD, hBD⟩ := base_bounds_components hA hB hx1 hy1 hCD hsum
  exact ⟨hAD, hBD, hCD⟩

end BealABCFiniteFull
