/-
# Sperner door-counting parity lemma

This is the classical "door counting" proof of Sperner's lemma, stripped to
pure combinatorics with **zero geometry**: a finite set `T` of "triangles",
a finite set `E` of "edges", an incidence map `inc : T → Finset E` recording
which edges belong to which triangle, and a fixed subset `door : Finset E` of
marked ("door") edges.

The only combinatorial content used is the standard *boundary/interior*
dichotomy: every edge that is incident to at least one triangle is incident
to **either exactly one** triangle (a *boundary* edge) **or exactly two**
triangles (an *interior* edge). Call a triangle *rainbow* if it has an odd
number of door-edges among its edges.

**Claim (`rainbow_card_parity`).** The number of rainbow triangles is
congruent mod 2 to the number of *boundary* door-edges:
`(rainbow.card : ZMod 2) = (boundary.card : ZMod 2)`.

In particular an odd number of boundary door-edges forces an odd — hence
nonzero — number of rainbow triangles, which is exactly the missing
combinatorial bridge for the Sperner-parity step of Monsky's theorem (the
geometric instantiation, relating `door`/`inc` to a concrete triangulation
and 2-adic colouring, is deliberately out of scope here).

## Proof idea (double counting in `ZMod 2`)

Set `mult e := #{t | e ∈ inc t}` (the multiplicity of edge `e`). Double-count
`M := ∑ t, #(inc t ∩ door)`:

* **By triangle:** `(M : ZMod 2) = (rainbow.card : ZMod 2)`, since a natural
  number is `1` mod 2 exactly when it is odd (and `rainbow` is *defined* as
  the triangles with odd door-edge-count).
* **By edge:** swapping the double sum (`Finset.sum_comm`) shows
  `M = ∑ e ∈ door, mult e`. Splitting `door` into `boundary` (`mult e = 1`)
  and its complement (`mult e = 2`, by hypothesis) gives
  `M = boundary.card + 2 * (interior part).card`, which is `boundary.card`
  mod 2.

Combining the two counts of `M` gives the claim.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

namespace MonskySpernerParity

open Finset

variable {T E : Type*} [Fintype T] [DecidableEq E]

/-- The multiplicity of edge `e`: the number of triangles `t` with `e ∈ inc t`. -/
def mult (inc : T → Finset E) (e : E) : ℕ :=
  (Finset.univ.filter (fun t => e ∈ inc t)).card

@[simp] lemma mult_apply (inc : T → Finset E) (e : E) :
    mult inc e = (Finset.univ.filter (fun t => e ∈ inc t)).card := rfl

/-- The rainbow triangles: those with an odd number of door-edges. -/
def rainbow (inc : T → Finset E) (door : Finset E) : Finset T :=
  Finset.univ.filter (fun t => Odd (inc t ∩ door).card)

@[simp] lemma rainbow_apply (inc : T → Finset E) (door : Finset E) :
    rainbow inc door = Finset.univ.filter (fun t => Odd (inc t ∩ door).card) := rfl

/-- The boundary door-edges: door-edges of multiplicity exactly `1`. -/
def boundary (inc : T → Finset E) (door : Finset E) : Finset E :=
  door.filter (fun e => mult inc e = 1)

@[simp] lemma boundary_apply (inc : T → Finset E) (door : Finset E) :
    boundary inc door = door.filter (fun e => mult inc e = 1) := rfl

/-- Parity helper: casting a natural number to `ZMod 2` matches the
`Odd`/`Even` dichotomy. -/
lemma nat_cast_zmod_two_eq_ite_odd (n : ℕ) :
    (n : ZMod 2) = if Odd n then 1 else 0 := by
  rcases Nat.even_or_odd n with he | ho
  · have hn : ¬ Odd n := Nat.not_odd_iff_even.mpr he
    have hmod : n % 2 = 0 := Nat.not_odd_iff.mp hn
    rw [if_neg hn]
    have h := ZMod.natCast_mod n 2
    rw [hmod] at h
    simpa using h.symm
  · have hmod : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_pos ho]
    have h := ZMod.natCast_mod n 2
    rw [hmod] at h
    simpa using h.symm

/-- **Sperner door-counting parity lemma.**

Let `inc : T → Finset E` assign to each triangle its (door-relevant) edges,
and `door : Finset E` a set of marked edges. Assume every door-edge has
multiplicity `1` (boundary) or `2` (interior) — the hypothesis `hmult`. Then
the number of rainbow triangles (odd door-edge-count) is congruent mod 2 to
the number of boundary door-edges. -/
theorem rainbow_card_parity
    (inc : T → Finset E) (door : Finset E)
    (hmult : ∀ e ∈ door, mult inc e = 1 ∨ mult inc e = 2) :
    ((rainbow inc door).card : ZMod 2) = ((boundary inc door).card : ZMod 2) := by
  classical
  -- `M` is the double-counted incidence sum.
  set M : ℕ := ∑ t : T, (inc t ∩ door).card with hM

  -- Step 1: counting `M` by triangle recovers `rainbow.card` mod 2.
  have step_triangle : (M : ZMod 2) = ((rainbow inc door).card : ZMod 2) := by
    rw [hM, rainbow_apply, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    rw [nat_cast_zmod_two_eq_ite_odd]

  -- Step 2: counting `M` by edge (double-counting swap) recovers
  -- `∑ e ∈ door, mult inc e`.
  have step_swap : M = ∑ e ∈ door, mult inc e := by
    rw [hM]
    calc ∑ t : T, (inc t ∩ door).card
        = ∑ t : T, ∑ e ∈ door, (if e ∈ inc t then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      _ = ∑ e ∈ door, ∑ t : T, (if e ∈ inc t then 1 else 0) := Finset.sum_comm
      _ = ∑ e ∈ door, mult inc e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [mult_apply, Finset.card_filter]

  -- Step 3: split `door` into boundary (multiplicity 1) and interior
  -- (multiplicity 2) edges.
  have step_split :
      ∑ e ∈ door, mult inc e
        = (boundary inc door).card
          + (door.filter (fun e => ¬ mult inc e = 1)).card * 2 := by
    rw [boundary_apply,
      ← Finset.sum_filter_add_sum_filter_not door (fun e => mult inc e = 1) (mult inc)]
    congr 1
    · have h1 : ∑ e ∈ door.filter (fun e => mult inc e = 1), mult inc e
          = ∑ e ∈ door.filter (fun e => mult inc e = 1), 1 :=
        Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2)
      rw [h1, Finset.sum_const, smul_eq_mul, mul_one]
    · have heq : ∀ e ∈ door.filter (fun e => ¬ mult inc e = 1), mult inc e = 2 := by
        intro e he
        obtain ⟨hedoor, hne⟩ := Finset.mem_filter.mp he
        rcases hmult e hedoor with h1 | h2
        · exact absurd h1 hne
        · exact h2
      rw [Finset.sum_congr rfl heq, Finset.sum_const, smul_eq_mul]

  -- Assemble: `M` counted by edge is `boundary.card` mod 2, and `M` counted
  -- by triangle is `rainbow.card` mod 2.
  have step_edge : (M : ZMod 2) = ((boundary inc door).card : ZMod 2) := by
    rw [step_swap, step_split]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, mul_zero, add_zero]

  exact step_triangle.symm.trans step_edge

end MonskySpernerParity
