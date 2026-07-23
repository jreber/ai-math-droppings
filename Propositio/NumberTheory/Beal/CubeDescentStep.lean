import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeDescent
import Propositio.NumberTheory.Beal.EisensteinDescent
import Propositio.NumberTheory.Beal.CubeSynthesis

/-!
# M4: Kummer sign-pinning + integral-basis descent step (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file pushes the M4 step of the
ℤ[ζ₃] Beal cube-sum descent one rung past `BealCubeSynthesis`: from the
power-extraction output `Associated (dᶻ) (A + B·η)` it

  1. **pins the residual unit to a sign** (`unit_pinned_to_sign`): under
     `gcd(z, 3) = 1`, the descent unit `u ∈ {±1, ±η, ±η²}` (`Units.mem`) has its
     `η`-power part absorbed into the base, leaving `A + B·η = ε · d'ᶻ` with
     `ε ∈ {1, −1}`; and

  2. **extracts integral-basis coordinate relations** (`descent_relations_two`,
     `descent_relations_three`, and the coupling `descent_coupling_three`):
     writing `d' = e + f·η` (`e, f ∈ ℤ`) and using `η² = −η − 1`,
     the two sides of `A + B·η = ±(e + f·η)ᶻ` are compared on the integral basis
     `{1, η}` of `𝓞 K`. Coordinate **uniqueness** (`{1, η}` is `ℤ`-linearly
     independent in `𝓞 K`) turns the cyclotomic equation into a *pair* of integer
     equations; the explicit `z = 2` and `z = 3` coordinate forms are computed.

## What is genuinely new here

* **`unit_pinned_to_sign`** — rigorously closes the `η`-absorption half of M4:
  `Associated (dᶻ) (A+B·η)` ∧ `gcd(z,3)=1` ⟹ `∃ d', A + B·η = d'ᶻ ∨ A + B·η = -d'ᶻ`.
  This is the first time the descent unit is reduced all the way to a **sign** in
  this development. It uses `BealCubeSynthesis.kummer_absorb_eta_pow` for the
  absorption and mathlib's `IsCyclotomicExtension.Rat.Three.Units.mem` for the
  classification.

* **`eta_coords_unique`** — `{1, η}` coordinate uniqueness over `ℤ` in `𝓞 K`:
  `e₁ + f₁·η = e₂ + f₂·η ⟹ e₁ = e₂ ∧ f₁ = f₂`. Derived from `ζ` having a degree-2
  minimal polynomial over `ℚ` (the power basis of `K = ℚ(ζ₃)`, `finrank ℚ K = 2`).
  This is the engine that makes "compare coordinates" a theorem.

* **`sq_eta_coords` / `cube_eta_coords`** and **`descent_relations_two` /
  `descent_relations_three`** — the explicit `{1,η}`-coordinate equations
  (`z = 2`, `z = 3`) the sign-pinned descent must satisfy, plus the coupling
  `descent_coupling_three` with the integer descent `A + B = s³`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCubeDescentStep.lean` to typecheck (SLOW, ~90s).
-/

namespace BealCubeDescentStep

open scoped NumberField

/-!
## M4 step 1 — pinning the descent unit to a sign

`eisenstein_power_extraction` (via `beal_cube_structure_three_ndvd_C`) outputs
`Associated (dᶻ) (A + B·η)`, i.e. there is a unit `u : (𝓞 K)ˣ` with
`A + B·η = u · dᶻ`. Mathlib's `IsCyclotomicExtension.Rat.Three.Units.mem`
classifies `u ∈ [1, -1, η, -η, η², -η²]` (here `η` is the *unit* attached to
`hζ.toInteger`). Each case is `±η^k` for `k ∈ {0,1,2}`, so
`A + B·η = ±η^k · dᶻ`. With `gcd(z, 3) = 1` the `η^k` factor is itself a `z`-th
power of a unit (`BealCubeSynthesis.eta_isPow_of_coprime_three`), and
`BealCubeSynthesis.kummer_absorb_eta_pow` absorbs it into the base, collapsing the
unit to the residual sign `±1`.
-/

/-- Mathlib's `Three.Units.mem` is phrased with the unit `η`; its coercion to
`𝓞 K` is `hζ.toInteger`. We record the value form to translate the list
membership into equations in `𝓞 K`. -/
private lemma coe_three_eta {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ((IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit : 𝓞 K)
      = hζ.toInteger := rfl

/-- **M4.1 — `unit_pinned_to_sign`.** From the power-extraction output
`Associated (dᶻ) (A + B·η)` and `gcd(z, 3) = 1`, the descent unit is pinned to a
sign: there is a base `d'` with

  `A + B·η = d'ᶻ`   or   `A + B·η = −d'ᶻ`.

Proof: `Associated` unfolds to `A + B·η = u · dᶻ` for `u : (𝓞 K)ˣ`; `Units.mem`
classifies `(u : 𝓞 K) ∈ {±1, ±η, ±η²}`, i.e. `u · dᶻ = ±η^k · dᶻ` for some
`k ∈ {0,1,2}`. Writing the `+` cases as `η^k · dᶻ` and applying
`kummer_absorb_eta_pow` (which needs `gcd(z,3)=1`) absorbs `η^k` into the base,
giving `A + B·η = d'ᶻ`; the `−` cases give `A + B·η = −(η^k·dᶻ) = −d'ᶻ`. -/
theorem unit_pinned_to_sign {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B d : 𝓞 K} {z : ℕ} (hcop : Nat.Coprime z 3)
    (hassoc : Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) :
    ∃ d' : 𝓞 K,
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ z ∨
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = -(d' ^ z) := by
  classical
  set x : 𝓞 K := (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger with hx
  -- Unfold Associated: x = u * dᶻ.
  obtain ⟨u, hu⟩ := hassoc
  -- u * dᶻ = x, rewrite to x = (u : 𝓞 K) * dᶻ.
  have hxu : x = (u : 𝓞 K) * d ^ z := by rw [← hu]; ring
  -- Classify u via Units.mem.
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  have hce : ((IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit : 𝓞 K)
      = hζ.toInteger := coe_three_eta hζ
  -- Each case gives x = ±η^k · dᶻ; absorb η^k (k ∈ {0,1,2}).
  -- After `fin_cases`, `u` is replaced by the case literal inside `hxu`; we
  -- normalize the unit coercion (`Units.val_pow_eq_pow_val`, `Units.val_neg`,
  -- `hce`) to land on `x = ±η^k · dᶻ`.
  fin_cases hmem <;>
    simp only [Units.val_one, Units.val_neg, Units.val_pow_eq_pow_val, hce,
      one_mul] at hxu
  · -- u = 1 : x = d^z (k = 0)
    exact ⟨d, Or.inl hxu⟩
  · -- u = -1 : x = -(d^z)
    refine ⟨d, Or.inr ?_⟩; rw [hxu]; ring
  · -- u = η : x = η^1 · d^z
    have hxk : x = hζ.toInteger ^ 1 * d ^ z := by rw [hxu]; ring
    obtain ⟨d', hd'⟩ := BealCubeSynthesis.kummer_absorb_eta_pow hζ hcop hxk
    exact ⟨d', Or.inl hd'⟩
  · -- u = -η : x = -(η^1 · d^z)
    have hxk : -x = hζ.toInteger ^ 1 * d ^ z := by rw [hxu]; ring
    obtain ⟨d', hd'⟩ := BealCubeSynthesis.kummer_absorb_eta_pow hζ hcop hxk
    refine ⟨d', Or.inr ?_⟩; rw [← hd']; ring
  · -- u = η² : x = η^2 · d^z
    have hxk : x = hζ.toInteger ^ 2 * d ^ z := by rw [hxu]
    obtain ⟨d', hd'⟩ := BealCubeSynthesis.kummer_absorb_eta_pow hζ hcop hxk
    exact ⟨d', Or.inl hd'⟩
  · -- u = -η² : x = -(η^2 · d^z)
    have hxk : -x = hζ.toInteger ^ 2 * d ^ z := by rw [hxu]; ring
    obtain ⟨d', hd'⟩ := BealCubeSynthesis.kummer_absorb_eta_pow hζ hcop hxk
    refine ⟨d', Or.inr ?_⟩; rw [← hd']; ring

/-!
## M4 step 2 — integral-basis coordinate relations

`𝓞 K = ℤ[ζ₃]` is free of rank `φ(3) = 2` over `ℤ` on `{1, η}` (`η = hζ.toInteger`).
Hence every `y : 𝓞 K` is uniquely `e + f·η` with `e, f ∈ ℤ`, and equality of two
such expressions forces equality of coordinates. We prove this comparison engine
(`eta_coords_unique`) via the degree-2 minimal polynomial of `ζ` over `ℚ`.
-/

/-- **M4.2.a — `{1, η}` coordinate uniqueness over `ℤ` in `𝓞 K`.**
If `e₁ + f₁·η = e₂ + f₂·η` with `eᵢ, fᵢ : ℤ`, then `e₁ = e₂` and `f₁ = f₂`.

This is the linear independence of `{1, η}` over `ℤ` in `𝓞 K = ℤ[ζ₃]`. Proof:
reduce to `a + b·η = 0` (`a = e₁−e₂`, `b = f₁−f₂`) and map to `K`. If `b ≠ 0`
then `ζ = −a/b ∈ range(algebraMap ℚ K)`, forcing `(minpoly ℚ ζ).degree = 1`
(`minpoly.degree_eq_one_iff`); but the power basis of `K = ℚ(ζ₃)` has
`degree (minpoly ℚ ζ) = dim = finrank ℚ K = φ(3) = 2`
(`PowerBasis.degree_minpoly`, `IsCyclotomicExtension.finrank`) — contradiction.
So `b = 0`, whence `a = 0`. -/
theorem eta_coords_unique {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {e₁ f₁ e₂ f₂ : ℤ}
    (h : (e₁ : 𝓞 K) + (f₁ : 𝓞 K) * hζ.toInteger
       = (e₂ : 𝓞 K) + (f₂ : 𝓞 K) * hζ.toInteger) :
    e₁ = e₂ ∧ f₁ = f₂ := by
  -- Reduce to: (e₁-e₂) + (f₁-f₂)·η = 0 ⟹ both coeffs vanish.
  have hsub : ((e₁ - e₂ : ℤ) : 𝓞 K) + ((f₁ - f₂ : ℤ) : 𝓞 K) * hζ.toInteger = 0 := by
    push_cast; linear_combination h
  set a : ℤ := e₁ - e₂ with ha
  set b : ℤ := f₁ - f₂ with hb0
  -- It suffices to show a = 0 and b = 0.
  suffices hab : a = 0 ∧ b = 0 by
    obtain ⟨ha0, hb0'⟩ := hab
    exact ⟨by omega, by omega⟩
  -- Work in K. Map hsub into K (via the subring coercion):
  -- a + b·ζ = 0 with a, b ∈ ℤ ⊆ ℚ.
  have hKeq : (a : K) + (b : K) * ζ = 0 := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hsub
    simpa [IsPrimitiveRoot.coe_toInteger] using this
  -- The power basis of K over ℚ has gen ζ and dim 2; its minpoly has degree 2.
  set pb := hζ.powerBasis ℚ with hpb
  have hgen : pb.gen = ζ := hζ.powerBasis_gen ℚ
  have hdim : pb.dim = 2 := by
    have h1 : Module.finrank ℚ K = pb.dim := pb.finrank
    have h2 : Module.finrank ℚ K = (3 : ℕ).totient :=
      IsCyclotomicExtension.finrank (n := 3) K (Polynomial.cyclotomic.irreducible_rat (by norm_num))
    have h3 : (3 : ℕ).totient = 2 := by decide
    rw [h2, h3] at h1; omega
  -- If b ≠ 0, then ζ = -a/b ∈ range(algebraMap ℚ K), forcing minpoly degree 1,
  -- contradicting degree (minpoly ℚ ζ) = pb.dim = 2.
  have hbzero : b = 0 := by
    by_contra hb
    have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
    -- ζ = (-(a:K)) * (b:K)⁻¹ = algebraMap ℚ K (-(a:ℚ)/b).
    have hζrange : ζ ∈ (algebraMap ℚ K).range := by
      refine ⟨(-(a : ℚ)) / (b : ℚ), ?_⟩
      have hbQ : ((b : ℚ) : K) = (b : K) := by push_cast; ring
      rw [map_div₀, map_neg, map_intCast, map_intCast]
      field_simp
      linear_combination -hKeq
    have hdeg1 : (minpoly ℚ ζ).degree = 1 :=
      (minpoly.degree_eq_one_iff).2 hζrange
    have hdeg2 : (minpoly ℚ pb.gen).degree = (pb.dim : WithBot ℕ) := pb.degree_minpoly
    rw [hgen, hdeg1, hdim] at hdeg2
    norm_num at hdeg2
  -- With b = 0, a = 0 follows.
  refine ⟨?_, hbzero⟩
  rw [hbzero] at hKeq
  simp only [Int.cast_zero, zero_mul, add_zero] at hKeq
  exact_mod_cast hKeq

/-- The cyclotomic relation `η² = −η − 1` in `𝓞 K`, restated for the expansions
below (mathlib `Three.eta_sq`, via `eta_sq_add_eta_add_one`). -/
private lemma eta_sq_eq {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
  have hη : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ
  linear_combination hη

/-- **M4.2.b — `z = 2` coordinate expansion.** With `d' = e + f·η`,

  `(e + f·η)² = (e² − f²) + (2ef − f²)·η`   in `𝓞 K`,

using `η² = −η − 1`. So if `A + B·η = (e + f·η)²` then, by `eta_coords_unique`,
`A = e² − f²` and `B = 2ef − f²` (as integers, once `A, B` are integer-cast). -/
theorem sq_eta_coords {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (e f : 𝓞 K) :
    (e + f * hζ.toInteger) ^ 2
      = (e ^ 2 - f ^ 2) + (2 * e * f - f ^ 2) * hζ.toInteger := by
  have hη := eta_sq_eq hζ
  linear_combination (f ^ 2) * hη

/-- **M4.2.c — `z = 3` coordinate expansion.** With `d' = e + f·η`,

  `(e + f·η)³ = (e³ − 3ef² + f³) + (3e²f − 3ef²)·η`   in `𝓞 K`,

using `η² = −η − 1` and `η³ = 1`. So `A + B·η = (e + f·η)³` gives, via
`eta_coords_unique`, `A = e³ − 3ef² + f³` and `B = 3e²f − 3ef²` (integer-cast). -/
theorem cube_eta_coords {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (e f : 𝓞 K) :
    (e + f * hζ.toInteger) ^ 3
      = (e ^ 3 - 3 * e * f ^ 2 + f ^ 3)
        + (3 * e ^ 2 * f - 3 * e * f ^ 2) * hζ.toInteger := by
  have hη := eta_sq_eq hζ
  -- η³ = η·η² = η·(−η−1) = −η²−η = −(−η−1)−η = 1.
  have hcube : hζ.toInteger ^ 3 = 1 := hζ.toInteger_cube_eq_one
  -- Expand and reduce η³ (hcube) then η² (hη).
  have hexp : (e + f * hζ.toInteger) ^ 3
      = e ^ 3 + 3 * e ^ 2 * f * hζ.toInteger
        + 3 * e * f ^ 2 * hζ.toInteger ^ 2 + f ^ 3 * hζ.toInteger ^ 3 := by ring
  rw [hexp, hcube, hη]; ring

/-!
## M4 step 2 — the descent coordinate relations (`z = 2`, `z = 3`)

Combining the sign-pinned descent `A + B·η = ±d'ᶻ` (`unit_pinned_to_sign`) with
the explicit expansions and `eta_coords_unique`, the integer coordinates `(A, B)`
are pinned to polynomials in `(e, f)` (the `{1,η}`-coordinates of the base `d'`).
We record the `z = 2` and `z = 3` integer relations, where `A, B : ℤ` (or `ℕ`
cast) and `d' = (e : 𝓞 K) + (f : 𝓞 K)·η`. The `+` (sign `ε = 1`) cases are
stated; the `−` cases negate the right-hand sides verbatim.
-/

/-- **M4.2.d — `z = 2` integer descent relations (sign `+`).** If
`(A : 𝓞 K) + B·η = (e + f·η)²` with `A, B, e, f : ℤ`, then

  `A = e² − f²`   and   `B = 2ef − f²`   (in `ℤ`).

Proof: expand the right side via `sq_eta_coords`, then apply coordinate
uniqueness `eta_coords_unique`. -/
theorem descent_relations_two {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B e f : ℤ}
    (h : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
       = ((e : 𝓞 K) + (f : 𝓞 K) * hζ.toInteger) ^ 2) :
    A = e ^ 2 - f ^ 2 ∧ B = 2 * e * f - f ^ 2 := by
  rw [sq_eta_coords hζ] at h
  have h' : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
      = (((e ^ 2 - f ^ 2 : ℤ)) : 𝓞 K)
        + (((2 * e * f - f ^ 2 : ℤ)) : 𝓞 K) * hζ.toInteger := by
    rw [h]; push_cast; ring
  exact eta_coords_unique hζ h'

/-- **M4.2.e — `z = 3` integer descent relations (sign `+`).** If
`(A : 𝓞 K) + B·η = (e + f·η)³` with `A, B, e, f : ℤ`, then

  `A = e³ − 3ef² + f³`   and   `B = 3e²f − 3ef²`   (in `ℤ`).

Proof: expand via `cube_eta_coords`, then `eta_coords_unique`. -/
theorem descent_relations_three {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B e f : ℤ}
    (h : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
       = ((e : 𝓞 K) + (f : 𝓞 K) * hζ.toInteger) ^ 3) :
    A = e ^ 3 - 3 * e * f ^ 2 + f ^ 3 ∧ B = 3 * e ^ 2 * f - 3 * e * f ^ 2 := by
  rw [cube_eta_coords hζ] at h
  have h' : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
      = (((e ^ 3 - 3 * e * f ^ 2 + f ^ 3 : ℤ)) : 𝓞 K)
        + (((3 * e ^ 2 * f - 3 * e * f ^ 2 : ℤ)) : 𝓞 K) * hζ.toInteger := by
    rw [h]; push_cast; ring
  exact eta_coords_unique hζ h'

/-!
## M4 step 3 (STRETCH) — coupling the cyclotomic and integer descents

For the operative exponent `z = 3` (the Beal cube case the whole pipeline
targets), put the two descents side by side:

* integer descent (`BealCubeDescent.cube_sum_descent`): `A + B = s³`;
* cyclotomic descent (`unit_pinned_to_sign` + `descent_relations_three`, sign `+`):
  `A = e³ − 3ef² + f³`, `B = 3e²f − 3ef²`.

Adding the two coordinate relations gives `A + B = e³ + 3e²f − 6ef² + f³`, so the
descent forces the **Diophantine coupling**

  `e³ + 3e²f − 6ef² + f³ = s³`.

This is a genuine constraint relating the *new* (smaller) base coordinates `(e,f)`
to the *old* `z`-th-power root `s`. It is the equation a minimal-counterexample
descent (à la `FermatLastTheoremForThreeGen`) would attack: a nontrivial solution
in `(e,f)` would feed back a strictly smaller cube-sum configuration. We record it
as a clean lemma; assembling the full strict descent on a `λ`-adic size parameter
is the remaining work (see `## REMAINING PLAN`). -/

/-- **M4.3 (STRETCH) — the `z = 3` Diophantine coupling.** If the integer descent
gives `A + B = s³` and the (sign `+`) cyclotomic descent gives
`(A : 𝓞 K) + B·η = (e + f·η)³`, then the base coordinates `(e, f)` and the root
`s` are coupled by

  `e³ + 3e²f − 6ef² + f³ = s³`.

This is the descent equation feeding a minimal-counterexample argument. -/
theorem descent_coupling_three {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B e f s : ℤ}
    (hsum : A + B = s ^ 3)
    (h : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
       = ((e : 𝓞 K) + (f : 𝓞 K) * hζ.toInteger) ^ 3) :
    e ^ 3 + 3 * e ^ 2 * f - 6 * e * f ^ 2 + f ^ 3 = s ^ 3 := by
  obtain ⟨hA, hB⟩ := descent_relations_three hζ h
  rw [← hsum, hA, hB]; ring

end BealCubeDescentStep

-- Axiom audit (remove before finishing): each headline should report
-- `[propext, Classical.choice, Quot.sound]`.
-- #print axioms BealCubeDescentStep.unit_pinned_to_sign
-- #print axioms BealCubeDescentStep.eta_coords_unique
-- #print axioms BealCubeDescentStep.descent_relations_two
-- #print axioms BealCubeDescentStep.descent_relations_three
-- #print axioms BealCubeDescentStep.descent_coupling_three

/-!
## REMAINING PLAN

This file closes the M4 unit step (η-absorption + sign pinning) and turns the
sign-pinned cyclotomic descent into explicit integer coordinate relations. All
declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Proved here:**

  * **`unit_pinned_to_sign`** — from `Associated (dᶻ) (A+B·η)` and `gcd(z,3)=1`,
    the descent unit `u ∈ {±1,±η,±η²}` (`Three.Units.mem`) has its `η`-power part
    absorbed (`BealCubeSynthesis.kummer_absorb_eta_pow`), leaving the sign:
    `A + B·η = d'ᶻ ∨ A + B·η = −d'ᶻ`. **The η-absorption half of M4 is closed.**

  * **`eta_coords_unique`** — `{1, η}` coordinate uniqueness over `ℤ` in `𝓞 K`
    (`e₁+f₁η = e₂+f₂η ⟹ e₁=e₂ ∧ f₁=f₂`), via the degree-2 minimal polynomial of
    `ζ` (`minpoly.degree_eq_one_iff` + `PowerBasis.degree_minpoly`,
    `IsCyclotomicExtension.finrank`). The comparison engine.

  * **`sq_eta_coords` / `cube_eta_coords`** — the `{1,η}`-expansions of
    `(e+f·η)²` and `(e+f·η)³` (using `η²=−η−1`, `η³=1`).

  * **`descent_relations_two` / `descent_relations_three`** — the explicit integer
    coordinate relations the sign-pinned descent forces:
    `z=2`: `A = e²−f²`, `B = 2ef−f²`;
    `z=3`: `A = e³−3ef²+f³`, `B = 3e²f−3ef²`.

  * **`descent_coupling_three`** (STRETCH) — coupling with `A+B = s³`:
    `e³ + 3e²f − 6ef² + f³ = s³`, the descent equation.

### The precise remaining obstruction

1. **Kummer sign-pinning of the residual `±1`.** `unit_pinned_to_sign` already
   reduces the unit to a *sign* (`±1`) unconditionally (given `gcd(z,3)=1`). To
   *eliminate* the `−1` branch one would feed the congruence
   `A + B·η ≡ ℤ (mod λ²)` (from the integer side) into Kummer's lemma
   `eq_one_or_neg_one_of_unit_of_congruent`. That requires the residual unit (here
   already collapsed) — the remaining step is showing the descent base `d'` is
   genuinely an integer-congruent configuration so the `−1` case is excluded or
   handled symmetrically. NOT yet wired: it needs the `λ²`-congruence bookkeeping.

2. **General `z` coordinates.** `descent_relations_{two,three}` are explicit only
   for `z ∈ {2,3}`; for general `z` the closed form is the binomial expansion of
   `(e+f·η)ᶻ` reduced mod `η²+η+1`. The *structural* statement — `(A,B)` are the
   unique `{1,η}`-coordinates of `±(e+f·η)ᶻ` — holds for all `z` via
   `eta_coords_unique` once the right side is written in `{1,η}` form; only the
   coefficient polynomials are `z`-dependent.

3. **Minimal descent.** `descent_coupling_three` (`e³+3e²f−6ef²+f³ = s³`) is the
   Diophantine constraint a `Solution'`/`Solution`-style minimal-counterexample
   descent (`Mathlib/NumberTheory/FLT/Three.lean`,
   `FermatLastTheoremForThreeGen`) would contradict. Assembling the strict descent
   on a `λ`-adic size parameter (`Solution'.multiplicity`) is the remaining work.

### Mathlib declarations used

* `IsCyclotomicExtension.Rat.Three.Units.mem` — `u ∈ {±1,±η,±η²}` (sign pinning).
* `IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one` — `η²+η+1=0`.
* `IsPrimitiveRoot.toInteger_cube_eq_one` — `η³=1`.
* `minpoly.degree_eq_one_iff`, `PowerBasis.degree_minpoly`,
  `IsCyclotomicExtension.finrank` — coordinate uniqueness engine.
* `BealCubeSynthesis.kummer_absorb_eta_pow`,
  `BealCubeSynthesis.eta_isPow_of_coprime_three` — the η-absorption.
-/
