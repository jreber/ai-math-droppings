import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CyclotomicDescent
import Propositio.NumberTheory.Beal.SplitPrimeGeneral

/-!
# Capstone synthesis: the constraints on a primitive Beal `(p, p, z)` counterexample

**NEW — interface check + machine-checked summary.** The `p`-uniform analogue of
`BealCubeCapstone.cube_sum_counterexample_constraints`. This file assembles the
two completed general-`p` results into a single statement listing the
*simultaneous* constraints any primitive Beal `(p, p, z)` counterexample
`A^p + B^p = C^z` (odd prime `p`, `p ∤ (A + B)`) must satisfy. Nothing new is
proved; the value is twofold:

* **Documentation.** It is the project's machine-checked answer to the question
  "what would a primitive `(p, p, z)` Beal counterexample have to look like?":
  `A + B` must descend to a perfect `z`-th power *in `ℤ`*, `A + ζ·B` must be a
  `z`-th power up to a unit *in `ℤ[ζ_p]`*, and (locally) the equation must avoid
  every forbidden split-prime residue.

* **Interface check.** Composing the pieces *forces* their signatures to agree.
  If `beal_ppz_structure_gen` or `beal_ppz_split_obstruction` drifted out of
  alignment, this file would stop typechecking.

## The constraint set

For an odd prime `p` with `𝓞 K = ℤ[ζ_p]` a PID, `Nat.Coprime A B`, `p ∤ (A + B)`,
`z ≠ 0`, and `A^p + B^p = C^z`:

1. **Integer descent** (`BealCyclotomicDescent.beal_ppz_structure_gen`, conjunct 1):
   `A + B` is a perfect `z`-th power, `∃ s, A + B = sᶻ`.

2. **Cyclotomic descent** (`beal_ppz_structure_gen`, conjunct 2): in `𝓞 K`,
   `A + B·ζ` is a `z`-th power up to a unit, `∃ d, Associated (dᶻ) (A + B·ζ)`.

3. **Split-prime local obstruction**
   (`BealSplitPrimeGeneral.beal_ppz_split_obstruction`): at every split prime
   `q ≡ 1 (mod p)` and forbidden residue `f ∉ pthPowerSumImage p q`, the right
   side cannot land on `f`: if `(C : ZMod q)^z = f` the equation is impossible
   mod `q`.

Conjuncts (1) and (2) are universally-true structural facts and form the
**headline** `beal_ppz_counterexample_constraints`. Conjunct (3) is *conditional*
on a concrete `decide`d forbidden residue at a particular split prime, so — as in
`BealCubeCapstone` — it appears as a companion corollary
(`beal_ppz_forbidden_residue`) and a fully-concrete instance for `(p, q) = (7, 29)`
(`beal_seventh_counterexample_mod29`).

The headline is instantiated for `p = 3` (`beal_33z_counterexample_constraints`,
PID via `three_pid`) and `p = 5` (`beal_55z_counterexample_constraints`, PID via
`five_pid`) as one-line corollaries.

Typecheck with `lake env lean BealPPZCapstone.lean` (imports the cyclotomic
development, so it is SLOW).
-/

namespace BealPPZCapstone

open scoped NumberField

/-- **Capstone: the simultaneous structural constraints on a primitive
`(p, p, z)` Beal counterexample (HEADLINE).**

Let `p` be an odd prime with `𝓞 K = ℤ[ζ_p]` a PID (`IsPrincipalIdealRing`),
`ζ` a primitive `p`-th root of unity in `K`. Any primitive `(p, p, z)` Beal
counterexample `A^p + B^p = C^z` with `Nat.Coprime A B`, `p ∤ (A + B)`, and
`z ≠ 0` is forced to satisfy *both*:

* **(integer descent)** `A + B` is a perfect `z`-th power: `∃ s : ℕ, A + B = sᶻ`;
* **(cyclotomic descent)** `A + B·ζ` is a `z`-th power up to a unit in `𝓞 K`:
  `∃ d : 𝓞 K, Associated (dᶻ) ((A : 𝓞 K) + B·ζ)`.

This is exactly `BealCyclotomicDescent.beal_ppz_structure_gen`, repackaged as the
`p`-uniform capstone (the general-`p` analogue of
`BealCubeCapstone.cube_sum_counterexample_constraints`). **NEW.** -/
theorem beal_ppz_counterexample_constraints
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hpAB : ¬ p ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) :=
  BealCyclotomicDescent.beal_ppz_structure_gen hp2 hζ hAB hpAB hz h

/-- **Companion corollary: the right-hand side avoids every forbidden split-prime
residue.**

If a residue `f : ZMod q` is *forbidden* — `f ∉ pthPowerSumImage p q`, i.e. not a
sum of two `p`-th powers mod `q` — then any primitive `(p, p, z)` solution
`A^p + B^p = C^z` cannot have `C^z` reduce to `f` mod `q`. The local constraint
on `C` complementing the global structural constraints of the headline.

This is `BealSplitPrimeGeneral.beal_ppz_split_obstruction`, applied through the
reduction of the equation mod `q`. **NEW.** -/
theorem beal_ppz_forbidden_residue
    {p q : ℕ} [NeZero q] {A B C : ℕ} {z : ℕ}
    {f : ZMod q} (hf : f ∉ BealSplitPrimeGeneral.pthPowerSumImage p q)
    (h : A ^ p + B ^ p = C ^ z) :
    (C : ZMod q) ^ z ≠ f := by
  intro hCf
  -- Reduce the equation mod q: (A:ZMod q)^p + (B:ZMod q)^p = (C:ZMod q)^z.
  have hmod : (A : ZMod q) ^ p + (B : ZMod q) ^ p = (C : ZMod q) ^ z := by
    have := congrArg (Nat.cast : ℕ → ZMod q) h
    push_cast at this
    exact this
  -- Cast A, B, C to ℤ to invoke the integer-typed obstruction.
  have hobstr :
      ((A : ℤ) : ZMod q) ^ p + ((B : ℤ) : ZMod q) ^ p ≠ ((C : ℤ) : ZMod q) ^ z :=
    BealSplitPrimeGeneral.beal_ppz_split_obstruction (A := (A : ℤ)) (B := (B : ℤ))
      (C := (C : ℤ)) hf (by push_cast; rw [hCf])
  apply hobstr
  push_cast
  rw [hmod]

/-- **Concrete seventh-power instance of the split-prime constraint at `q = 29`.**

If `C^z ≡ 3 (mod 29)` then `A^7 + B^7 = C^z` is impossible mod 29 — `3` is one of
the `16` residues forbidden by `BealSplitPrimeGeneral.three_notMem_pthPowerSumImage_29`.
The `(p, q) = (7, 29)` member of the split-prime obstruction family, wiring the
companion corollary to a fully `decide`d non-membership. **NEW.** -/
theorem beal_seventh_counterexample_mod29
    {A B C z : ℕ} (hC : (C : ZMod 29) ^ z = 3)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    False := by
  exact beal_ppz_forbidden_residue
    BealSplitPrimeGeneral.three_notMem_pthPowerSumImage_29 h hC

/-!
## The `p = 3` and `p = 5` instances (one-liners)

The headline subsumes both completed rungs. We instantiate `p = 3` (PID via
`three_pid`) and `p = 5` (PID via `five_pid`); adding any future PID prime `p` is
the same one-line pattern.
-/

/-- **The `p = 3` instance of the capstone.** The cube-sum structural constraints
from the general capstone `beal_ppz_counterexample_constraints`, PID discharged by
`IsCyclotomicExtension.Rat.three_pid`. One line. -/
theorem beal_33z_counterexample_constraints
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h3 : ¬ 3 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  exact beal_ppz_counterexample_constraints (by decide) hζ hAB h3 hz h

/-- **The `p = 5` instance of the capstone.** The `(5, 5, z)` structural
constraints from the general capstone `beal_ppz_counterexample_constraints`, PID
discharged by `IsCyclotomicExtension.Rat.five_pid`. One line. -/
theorem beal_55z_counterexample_constraints
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  exact beal_ppz_counterexample_constraints (by decide) hζ hAB h5 hz h

end BealPPZCapstone
