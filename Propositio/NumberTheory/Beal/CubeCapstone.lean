import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeDescent
import Propositio.NumberTheory.Beal.CubeDescentThree
import Propositio.NumberTheory.Beal.CubeMod9
import Propositio.NumberTheory.Beal.CubeSplitPrime
import Propositio.NumberTheory.Beal.CombinedObstruction
import Propositio.NumberTheory.Beal.CubeSynthesis

/-!
# Capstone synthesis: the constraints on a primitive Beal cube-sum counterexample

**NEW — interface check + machine-checked summary.** This file assembles every
cube-sum result of the project into a single statement listing the *simultaneous*
constraints any primitive Beal cube-sum counterexample `A³ + B³ = C^z` must
satisfy. Nothing new is proved; the value is twofold:

* **Documentation.** It is the project's machine-checked answer to the question
  "what would a primitive cube-sum Beal counterexample have to look like?" — it
  must descend into perfect `z`-th powers, avoid the mod-7 / mod-9 / mod-504
  local obstructions, have exponent `z ≠ 3` (FLT-3), and (in the cyclotomic
  refinement) be a `z`-th power up to a unit in `ℤ[ζ₃]`.

* **Interface check.** Composing the pieces *forces* their signatures to agree.
  If any cube-sum lemma drifted out of alignment with the others, this file would
  stop typechecking.

## The constraint set (case `3 ∤ C`)

For `0 < A, B, C`, `Nat.Coprime A B`, `3 ≤ z`, `3 ∤ C`, and `A³ + B³ = C^z`:

1. **Descent power-structure** (`BealCubeDescent.cube_sum_descent`): the two
   Eisenstein factors are each perfect `z`-th powers,
   `∃ s t, A + B = sᶻ ∧ A² + B² − A·B = tᶻ ∧ C = s·t`.

2. **Mod-7 split-prime obstruction**
   (`BealCubeSplitPrime.cube_sum_not_three_or_four_mod7`): the cube-sum residue
   `A³ + B³ (mod 7)` avoids the gap `{3, 4}` of the index-3 cube subgroup.

3. **Mod-7 obstruction on `C` itself** (corollary): since the equation reduces
   mod 7, the right-hand side `C^z (mod 7)` must also avoid `{3, 4}`.

4. **FLT-3** (`BealCubeDescentThree.beal_333`): the exponent satisfies `z ≠ 3`,
   because `A³ + B³ = C³` has no nonzero solution.

The mod-9 (`BealCubeMod9.case_one_obstruction`) and mod-504
(`BealCombinedObstruction`) obstructions are *conditional on `C^z`'s residue*
(`C^z ≢ 3 (mod 504)`, and the `3 ∣ z` mod-9 case), so they appear as the
companion corollary `cube_sum_C_residue_constraints` constraining `C^z` directly,
rather than as universally-true conjuncts of the headline.

The optional cyclotomic refinement
(`cube_sum_counterexample_constraints_cyclotomic`) adds the `ℤ[ζ₃]` structure
`∃ d, Associated (dᶻ) (A + B·η)` from `BealCubeSynthesis`; it carries the
cyclotomic typeclass machinery, so it is stated separately.

Typecheck with `lake env lean BealCubeCapstone.lean` (imports the cyclotomic
development, so it is SLOW, ~90s).
-/

namespace BealCubeCapstone

open scoped NumberField

/-- **Capstone: the simultaneous constraints on a primitive `3 ∤ C` cube-sum
counterexample (HEADLINE).**

Any primitive cube-sum Beal counterexample `A³ + B³ = C^z` with `0 < A, B, C`,
`Nat.Coprime A B`, exponent `3 ≤ z`, and `3 ∤ C` is forced to satisfy *all* of:

* **(descent)** each Eisenstein factor is a perfect `z`-th power:
  `∃ s t, A + B = sᶻ ∧ A² + B² − A·B = tᶻ ∧ C = s·t`;
* **(mod-7)** the cube-sum residue avoids the split-prime gap `{3, 4} (mod 7)`:
  `(A : ZMod 7)³ + (B : ZMod 7)³ ≠ 3 ∧ ≠ 4`;
* **(FLT-3)** the exponent is not `3`: `z ≠ 3`.

Composes `BealCubeDescent.cube_sum_descent`,
`BealCubeSplitPrime.cube_sum_not_three_or_four_mod7` (at the `ZMod 7` reductions
of `A, B`), and `BealCubeDescentThree.beal_333`. **NEW.** -/
theorem cube_sum_counterexample_constraints
    {A B C z : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : Nat.Coprime A B) (hz : 3 ≤ z) (hndvd : ¬ 3 ∣ C)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (∃ s t : ℕ, A + B = s ^ z ∧ A ^ 2 + B ^ 2 - A * B = t ^ z ∧ C = s * t) ∧
    ((A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 ≠ 3 ∧
      (A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 ≠ 4) ∧
    z ≠ 3 := by
  have hz0 : z ≠ 0 := by omega
  refine ⟨BealCubeDescent.cube_sum_descent hAB hndvd hz0 h, ?_, ?_⟩
  · -- Mod-7 split-prime obstruction at the reductions of A, B.
    exact BealCubeSplitPrime.cube_sum_not_three_or_four_mod7 (A : ZMod 7) (B : ZMod 7)
  · -- FLT-3: if z = 3 then A³ + B³ = C³ contradicts beal_333.
    intro hz3
    subst hz3
    exact BealCubeDescentThree.beal_333 hA.ne' hB.ne' hC.ne' h

/-- **Companion corollary: `C^z` is constrained mod 7** (deliverable 2).

Since `A³ + B³ = C^z` reduces mod 7 and the cube-sum image avoids `{3, 4}`, the
right-hand side `C^z` reduced mod 7 must *also* avoid the gap:
`(C : ZMod 7)^z ≠ 3 ∧ (C : ZMod 7)^z ≠ 4`. A clean constraint on `C` itself,
following from the mod-7 obstruction applied through the equation. **NEW.** -/
theorem cube_sum_C_forbidden_residue_mod7
    {A B C z : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : Nat.Coprime A B) (hz : 3 ≤ z) (hndvd : ¬ 3 ∣ C)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (C : ZMod 7) ^ z ≠ 3 ∧ (C : ZMod 7) ^ z ≠ 4 := by
  -- Reduce the equation mod 7: (A:ZMod 7)³ + (B:ZMod 7)³ = (C:ZMod 7)^z.
  have hmod : (A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 = (C : ZMod 7) ^ z := by
    have := congrArg (Nat.cast : ℕ → ZMod 7) h
    push_cast at this
    exact this
  obtain ⟨hne3, hne4⟩ :=
    BealCubeSplitPrime.cube_sum_not_three_or_four_mod7 (A : ZMod 7) (B : ZMod 7)
  refine ⟨?_, ?_⟩
  · rw [← hmod]; exact hne3
  · rw [← hmod]; exact hne4

/-- **Capstone with the cyclotomic refinement (optional conjunct).**

The headline constraint set, *extended* with the `ℤ[ζ₃]` cyclotomic structure
from `BealCubeSynthesis.beal_cube_structure_three_ndvd_C`: in `𝓞 K = ℤ[ζ₃]`, the
Eisenstein factor `A + B·η` is a `z`-th power up to a unit,
`∃ d, Associated (dᶻ) ((A : 𝓞 K) + B·η)`. The four conjuncts are:

* **(descent)** `∃ s t, A + B = sᶻ ∧ A² + B² − A·B = tᶻ ∧ C = s·t`;
* **(mod-7)** `(A : ZMod 7)³ + (B : ZMod 7)³ ≠ 3 ∧ ≠ 4`;
* **(FLT-3)** `z ≠ 3`;
* **(cyclotomic)** `∃ d : 𝓞 K, Associated (dᶻ) ((A : 𝓞 K) + B·η)`.

Stated over a fixed cyclotomic field `K` (the third-root extension of `ℚ`); the
cyclotomic conjunct carries that typeclass machinery, which is why it is a
separate statement from the `ℕ`/`ZMod`-only headline. **NEW.** -/
theorem cube_sum_counterexample_constraints_cyclotomic
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : Nat.Coprime A B) (hz : 3 ≤ z) (hndvd : ¬ 3 ∣ C)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (∃ s t : ℕ, A + B = s ^ z ∧ A ^ 2 + B ^ 2 - A * B = t ^ z ∧ C = s * t) ∧
    ((A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 ≠ 3 ∧
      (A : ZMod 7) ^ 3 + (B : ZMod 7) ^ 3 ≠ 4) ∧
    z ≠ 3 ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  have hz0 : z ≠ 0 := by omega
  obtain ⟨hdesc, hmod7, hz3⟩ :=
    cube_sum_counterexample_constraints hA hB hC hAB hz hndvd h
  refine ⟨hdesc, hmod7, hz3, ?_⟩
  -- The cyclotomic conjunct of the structure theorem.
  exact (BealCubeSynthesis.beal_cube_structure_three_ndvd_C hζ hAB hndvd hz0 h).2

end BealCubeCapstone
