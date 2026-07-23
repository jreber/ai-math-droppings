/-
Collatz parity-vector (stopping-time) theorems — Bucket 3.

Lean 4 mirror of `src/ai_math/collatz/parity_vector.clj`.

The LaTTe namespace `ai-math.collatz.parity-vector` exposes 10 REAL theorems
(see `parity-vector-theorems-real` in `test/ai_math/theorem_records_test.clj`):

  1. parity-vector-eq-1
  2. pow-two-coprime-three
  3. pv-shift
  4. pv-zero-parity
  5. plus-right-cancel-minus
  6. parity-vector-residue-lemma-nat
  7. density-bounded-by-parity-vector
  8. divides-lt-nat-zero
  9. diff-le-left
  10. parity-vector-classes-disjoint

SEVEN of these are ALREADY ported (and kernel-verified) in `TerrasDensity.lean`,
which is the Bucket-3 home for the Terras C.5/C.6 density argument and reuses
the same `T` / `T_iter` / `PVEq` infrastructure:

  - parity-vector-eq-1                → `TerrasDensity.parity_vector_eq_1`
  - pow-two-coprime-three             → `TerrasDensity.pow_two_coprime_three`
  - parity-vector-residue-lemma-nat   → `TerrasDensity.parity_vector_residue_lemma_nat`
  - density-bounded-by-parity-vector  → `TerrasDensity.density_bounded_by_parity_vector`
  - divides-lt-nat-zero               → `TerrasDensity.divides_lt_nat_zero`
  - diff-le-left                      → `TerrasDensity.diff_le_left_int`
  - parity-vector-classes-disjoint    → `TerrasDensity.parity_vector_classes_disjoint`

This file ports the THREE genuinely-missing LaTTe theorems — the
parity-vector *shift* infrastructure lemmas (C.5/C.6 inductive step) and the
arithmetic cancellation helper:

  - pv-shift                  → `pv_shift`              (here, REAL)
  - pv-zero-parity            → `pv_zero_parity`        (here, REAL)
  - plus-right-cancel-minus   → `plus_right_cancel_minus` (here, REAL)

In `TerrasDensity.parity_vector_residue_lemma_nat` the shift / zero-parity
facts appear *inline* as `h_shift` and `h_par`; here they are extracted as
standalone named theorems faithful to their LaTTe siblings, so each of the 10
LaTTe theorems has an explicit Lean 4 home.

We re-use `TerrasDensity`'s `T`, `T_iter`, and `PVEq` rather than redefining
them, keeping a single source of truth for the parity-vector framework.

House-style doc-comments use `LaTTe sibling: <clj path> :: <name>`.
-/
import Propositio.Collatz.Basic

namespace CollatzParityVector

open TerrasDensity

/--
**pv_shift — parity-vector shift (C.5/C.6 inductive step).**

If `m` and `n` share a length-`(k+1)` parity vector, then `T m` and `T n`
share a length-`k` parity vector.

This is the descent step of the parity-vector residue induction: it strips the
leading parity bit and pushes the remaining `k` bits onto the once-iterated
pair `(T m, T n)`. In `TerrasDensity.parity_vector_residue_lemma_nat` this is
the inline hypothesis `h_shift`.

The LaTTe proof instantiates the `(succ x)`-pv hypothesis at `succ j` and
rewrites `T^{succ j}(m) = T^j(T m)` via `terras-T-iter-succ`. The Lean version
uses the definitional unfolding `T_iter m (j+1) = T_iter (T m) j` (which is
`rfl` for the `T_iter` recursor).

LaTTe sibling: `src/ai_math/collatz/parity_vector.clj` :: `pv-shift` (REAL).
-/
theorem pv_shift (m n k : Nat) (h : PVEq m n (k + 1)) :
    PVEq (T m) (T n) k := by
  intro j hj
  have hstep := h (j + 1) (Nat.succ_lt_succ hj)
  -- T_iter _ (j+1) = T_iter (T _) j definitionally
  simp only [show T_iter m (j + 1) = T_iter (T m) j from rfl,
             show T_iter n (j + 1) = T_iter (T n) j from rfl] at hstep
  exact hstep

/--
**pv_zero_parity — same parity at step 0.**

If `m` and `n` share a length-`(k+1)` parity vector, then `m` and `n` have the
same parity (`m % 2 = n % 2`).

This is the `j = 0` projection of `PVEq m n (k+1)`: since `0 < k+1`, the
hypothesis applies at `j = 0`, and `T^0(m) = m`, `T^0(n) = n` definitionally.
It is the base parity bit consumed by `pv_shift` in the residue induction
(inline hypothesis `h_par` in `TerrasDensity.parity_vector_residue_lemma_nat`).

The LaTTe statement phrases "same parity" as
`(even m ∧ even n) ∨ (odd m ∧ odd n)`; the idiomatic Lean form is the
arithmetic equality `m % 2 = n % 2`, which is equivalent over `Nat`. The
disjunctive form is recovered below as `pv_zero_parity_disj`.

LaTTe sibling: `src/ai_math/collatz/parity_vector.clj` :: `pv-zero-parity` (REAL).
-/
theorem pv_zero_parity (m n k : Nat) (h : PVEq m n (k + 1)) :
    m % 2 = n % 2 := by
  have h0 := h 0 (Nat.zero_lt_succ k)
  simp only [show T_iter m 0 = m from rfl, show T_iter n 0 = n from rfl] at h0
  exact h0

/--
Disjunctive ("both even or both odd") restatement of `pv_zero_parity`,
matching the exact LaTTe conclusion shape.

LaTTe sibling: `src/ai_math/collatz/parity_vector.clj` :: `pv-zero-parity`
(REAL — conclusion form).
-/
theorem pv_zero_parity_disj (m n k : Nat) (h : PVEq m n (k + 1)) :
    (m % 2 = 0 ∧ n % 2 = 0) ∨ (m % 2 = 1 ∧ n % 2 = 1) := by
  have hpar := pv_zero_parity m n k h
  omega

/--
**plus_right_cancel_minus — cancel a common right summand in a difference.**

`(u + c) - (v + c) = u - v`.

A pure integer-arithmetic helper used by the nat-restricted residue lemma. The
LaTTe proof is a 7-step `minus-prop` / `plus-assoc` / `plus-right-cancel`
chain; over `Int` in Lean this is a single `ring` fact.

LaTTe sibling: `src/ai_math/collatz/parity_vector.clj` ::
`plus-right-cancel-minus` (REAL).
-/
theorem plus_right_cancel_minus (u v c : Int) :
    (u + c) - (v + c) = u - v := by
  ring

end CollatzParityVector
