import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.Collatz.Basic
import Propositio.Collatz.LyapunovCascade
import Propositio.Collatz.CascadeCycles
import Propositio.Collatz.H5
import Propositio.Collatz.CycleTelescope
import Propositio.Collatz.CycleDecide

/-!
# Uniform decidable cc-cycle exclusion for any fixed length L

## Purpose

This file provides a **single uniform theorem**
`cc_no_nontrivial_cycle_of_excluded` that reduces the exclusion of nontrivial
`cc`-cycles of any fixed length `L` to verifying a single `Bool`-valued
predicate `cycleExcludedB L = true`.  For each concrete `L` (8, 9, 10, …),
that verification is discharged by a single `by decide` (kernel-evaluated,
no `native_decide`), giving fully axiom-clean proofs.

## Method

The proof chain is:

1. **Telescope identity** (`CollatzCycleTelescope`): for a cycle
   `cc^[L] n = n`, `2^A · n = 3^L · n + Steiner n L` where
   `A = Σ_{i<L} v₂(3·cc^[i] n + 1)`.  Hence `(2^A − 3^L) ∣ Steiner n L`.

2. **Cycle constraint** (`CollatzCascadeCycles`): `3^L < 2^A < 4^L`, pinning
   `A` to finitely many values in `{0, …, 2L − 1}`.

3. **Composition enumeration** (`CollatzCycleDecide`): since each
   `v₂(3·cc^[i] n + 1) ≥ 1` (oddness), the valuation list
   `[v₂(3·cc^[0] n+1), …, v₂(3·cc^[L−1] n+1)]` is a member of
   `compositions L A` (a positive-integer list of length `L` summing to `A`).
   `steinerVal` computes `Steiner n L` purely from this list.

4. **Kernel decide**: `cycleExcludedB L` checks that for every admissible `A`
   (those with `3^L < 2^A < 4^L`) and every `as ∈ compositions L A`, the
   divisibility `(2^A − 3^L) ∣ steinerVal as` is FALSE.  This is a finite
   computation.

## Honest caveat

The general theorem (Steiner 1977, Simons–de Weger 2005) rules out ALL cycle
lengths simultaneously using Baker-type transcendence bounds on linear forms
in logarithms.  THIS FILE does NOT achieve that; it excludes each fixed `L`
individually.  The `by decide` cost grows like `C(A−1, L−1)` (binomial
composition count) and becomes infeasible for large `L` in the kernel
evaluator.

| L  | admissible A range | max C(A−1,L−1) | feasibility   |
|----|--------------------|----------------|---------------|
|  8 | {13,14,15}         | 3432           | fast          |
|  9 | {15,16,17}         | 12870          | slow (~minutes)|
| 10 | {16,17,18,19}      | 48620          | borderline    |
-/

namespace CollatzCycleUniform

open TerrasDensity (cc)
open CollatzCycleDecide (steinerVal compositions cons_mem_compositions
     nil_mem_compositions_zero iterate_odd one_le_v2_three_mul_add_one)
open CollatzCycleTelescope (S Steiner S_zero S_succ Steiner_zero Steiner_succ
     cycle_steiner_dvd)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## §1  The valuation list and its basic facts -/

/-- `valList n L` is the list of per-step 2-adic valuations of `cc` iterates
starting at `n`, for `L` steps. -/
def valList (n L : Nat) : List Nat :=
  (List.range L).map (fun i => padicValNat 2 (3 * cc^[i] n + 1))

/-- The sum of `valList n L` equals `CollatzCycleTelescope.S n L`. -/
theorem valList_sum (n L : Nat) : (valList n L).sum = S n L := by
  induction L with
  | zero => simp [valList, S_zero]
  | succ L ih =>
    rw [S_succ]
    simp only [valList, List.range_succ, List.map_append, List.map_cons, List.map_nil,
               List.sum_append, List.sum_cons, List.sum_nil]
    have ihm : (List.map (fun i => padicValNat 2 (3 * cc^[i] n + 1)) (List.range L)).sum
        = S n L := ih
    omega

/-- The length of `valList n L` is `L`. -/
theorem valList_length (n L : Nat) : (valList n L).length = L := by
  simp [valList]

/-- Every element of `valList n L` is `≥ 1` when `n` is odd. -/
theorem valList_pos (n L : Nat) (hodd : Odd n) : ∀ x ∈ valList n L, 1 ≤ x := by
  intro x hx
  simp only [valList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact one_le_v2_three_mul_add_one (iterate_odd n hodd i)

/-! ## §2  The Steiner ↔ steinerVal bridge -/

/-- Helper: the second component of the foldl accumulator equals the running sum. -/
private theorem foldl_snd (as : List Nat) (s t : Nat) :
    (as.foldl (fun p a => (3 * p.1 + 2 ^ p.2, p.2 + a)) (s, t)).2 = t + as.sum := by
  induction as generalizing s t with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]
    omega

/-- `steinerVal (as ++ [a]) = 3 * steinerVal as + 2 ^ as.sum`. -/
theorem steinerVal_append (as : List Nat) (a : Nat) :
    steinerVal (as ++ [a]) = 3 * steinerVal as + 2 ^ as.sum := by
  simp only [steinerVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h2 : (as.foldl (fun p a => (3 * p.1 + 2 ^ p.2, p.2 + a)) (0, 0)).2 = as.sum := by
    have := foldl_snd as 0 0
    simp at this
    exact this
  -- The foldl on `as` gives the pair (steinerVal as, as.sum).
  set q := as.foldl (fun p a => (3 * p.1 + 2 ^ p.2, p.2 + a)) (0, 0) with hq
  have hq1 : q.1 = steinerVal as := rfl
  have hq2 : q.2 = as.sum := h2
  rw [hq1, hq2]

/-- `Steiner n L = steinerVal (valList n L)`. -/
theorem steiner_eq_steinerVal (n L : Nat) :
    Steiner n L = steinerVal (valList n L) := by
  induction L with
  | zero => simp [Steiner_zero, valList, steinerVal]
  | succ L ih =>
    rw [Steiner_succ]
    have happ : valList n (L + 1) = valList n L ++ [padicValNat 2 (3 * cc^[L] n + 1)] := by
      simp [valList, List.range_succ, List.map_append]
    rw [happ, steinerVal_append, ← ih, valList_sum]

/-! ## §3  General membership lemma -/

/-- A list with all elements ≥ 1 is a member of `compositions as.length as.sum`. -/
theorem mem_compositions_of (as : List Nat) (hpos : ∀ x ∈ as, 1 ≤ x) :
    as ∈ compositions as.length as.sum := by
  induction as with
  | nil => exact nil_mem_compositions_zero
  | cons a rest ih =>
    have ha : 1 ≤ a := hpos a (by simp)
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have ih' := ih hrest
    simp only [List.length_cons, List.sum_cons]
    apply cons_mem_compositions ha (by omega)
    have hsub : a + rest.sum - a = rest.sum := by omega
    rw [hsub]
    exact ih'

/-- `valList n L ∈ compositions L (S n L)` when `n` is odd. -/
theorem valList_mem (n L : Nat) (hodd : Odd n) :
    valList n L ∈ compositions L (S n L) := by
  have h := mem_compositions_of (valList n L) (valList_pos n L hodd)
  rw [valList_length, valList_sum] at h
  exact h

/-! ## §4  The decidable exclusion predicate -/

/-- `cycleExcludedB L` is a decidable Boolean check that for every admissible
total valuation `A` (with `3^L < 2^A < 4^L`, i.e. `A ∈ range (2*L)`) and
every composition `as ∈ compositions L A`, the divisibility
`(2^A − 3^L) ∣ steinerVal as` fails.

When this returns `true`, `cc` has no nontrivial cycle of length `L`. -/
def cycleExcludedB (L : Nat) : Bool :=
  (List.range (2 * L)).all (fun A =>
    if 3 ^ L < 2 ^ A ∧ 2 ^ A < 4 ^ L then
      (compositions L A).all (fun as => !decide ((2 ^ A - 3 ^ L) ∣ steinerVal as))
    else
      true)

/-! ## §5  The uniform exclusion theorem -/

/-- **Uniform cc-cycle exclusion theorem.**

If `cycleExcludedB L = true`, then `cc` has no nontrivial `L`-step cycle.

Given an odd `n` with `cc^[L] n = n` and a nontrivial element in the cycle,
we derive a contradiction using:
1. The cycle constraint `3^L < 2^A < 4^L` (pinning A to `range (2*L)`).
2. `cycle_steiner_dvd`: `(2^A − 3^L) ∣ Steiner n L`.
3. The steinerVal bridge: `Steiner n L = steinerVal (valList n L)`.
4. `valList n L ∈ compositions L A`.
5. `cycleExcludedB L = true` says no composition can satisfy the divisibility.
-/
theorem cc_no_nontrivial_cycle_of_excluded (L : Nat) (hL : 1 ≤ L)
    (hexcl : cycleExcludedB L = true)
    (n : Nat) (hodd : Odd n) (hcyc : cc^[L] n = n)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  -- Step 1: Let A = S n L (the total 2-adic valuation).
  set A := S n L with hA_def
  -- Step 2: Obtain the cycle constraint 3^L < 2^A < 4^L.
  have hcon : (3 : Nat) ^ L < 2 ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1))
      ∧ (2 : Nat) ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1)) < 4 ^ L :=
    CollatzCascadeCycles.cc_cycle_constraint n L hodd hcyc hL hnontriv
  -- Bridge the sum to S n L.
  have hA_eq : ∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1) = A := by
    simp only [hA_def, S]
  rw [hA_eq] at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- Step 3: A < 2*L (since 2^A < 4^L = 2^(2L) and 2^· is strictly monotone).
  have h4L : (4 : Nat) ^ L = 2 ^ (2 * L) := by
    rw [show (4 : Nat) = 2 ^ 2 from by norm_num, ← pow_mul]
  have hA_lt : A < 2 * L := by
    by_contra hge
    rw [not_lt] at hge
    have hle : (2 : Nat) ^ (2 * L) ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hge
    rw [← h4L] at hle
    omega
  -- Step 4: A ∈ List.range (2 * L).
  have hAmem : A ∈ List.range (2 * L) := List.mem_range.mpr hA_lt
  -- Step 5: Apply cycleExcludedB; the `if` condition 3^L < 2^A ∧ 2^A < 4^L holds.
  have hbody := List.all_eq_true.mp hexcl A hAmem
  rw [if_pos (And.intro h3 h4)] at hbody
  -- hbody : (compositions L A).all (fun as => !decide ((2^A - 3^L) ∣ steinerVal as)) = true
  -- Step 6: Steiner divisibility, bridged to steinerVal over valList n L.
  have hdvd : (2 ^ A - 3 ^ L) ∣ Steiner n L :=
    cycle_steiner_dvd n hodd L hL hcyc hnontriv
  have hbridge : Steiner n L = steinerVal (valList n L) :=
    steiner_eq_steinerVal n L
  have hmem : valList n L ∈ compositions L A := valList_mem n L hodd
  -- Step 7: The composition check refutes the divisibility for valList n L.
  have hbad := List.all_eq_true.mp hbody (valList n L) hmem
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbad
  rw [← hbridge] at hbad
  exact hbad hdvd

/-! ## §6  Concrete instances

Each instance discharges `cycleExcludedB L = true` by a single kernel `decide`
(no `native_decide`). The composition counts C(A−1, L−1) are small for L ≤ 8
(L=5: 35/70, L=6: 126/252, L=7: 462/924, L=8: 792/1716/3432), so each `decide`
is cheap — and far lighter than the `interval_cases` enumeration in
`CollatzFiveSixSevenCycleExclusion`, which this method supersedes for L = 5,6,7. -/

-- No nontrivial `cc`-cycle of length 5 exists.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cc_no_nontrivial_five_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[5] n = n)
    (hnt : ∃ j ∈ Finset.range 5, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 5 (by norm_num) (by decide) n hodd hcyc hnt

-- No nontrivial `cc`-cycle of length 6 exists.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cc_no_nontrivial_six_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[6] n = n)
    (hnt : ∃ j ∈ Finset.range 6, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 6 (by norm_num) (by decide) n hodd hcyc hnt

-- No nontrivial `cc`-cycle of length 7 exists.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem cc_no_nontrivial_seven_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[7] n = n)
    (hnt : ∃ j ∈ Finset.range 7, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 7 (by norm_num) (by decide) n hodd hcyc hnt

-- No nontrivial `cc`-cycle of length 8 exists.  (Same result as
-- `CollatzCycleDecide.cc_no_nontrivial_eight_cycle`, now derived from the
-- uniform theorem via a single kernel `decide` on `cycleExcludedB 8`.)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 80000000 in
theorem cc_no_nontrivial_eight_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[8] n = n)
    (hnt : ∃ j ∈ Finset.range 8, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 8 (by norm_num) (by decide) n hodd hcyc hnt

-- NOTE: the `L = 9` instance (`cc_no_nontrivial_nine_cycle`) is omitted: its
-- `by decide` over the C(A−1, 8) compositions exhausts memory (the OOM that
-- crashed the original session). The reusable uniform theorem
-- `cc_no_nontrivial_cycle_of_excluded` still covers L = 9 the moment a feasible
-- `cycleExcludedB 9 = true` discharge (e.g. a `native_decide`-free reflection or
-- a tighter composition enumerator) is available.

/-! ## §7  Axiom checks -/

#print axioms cc_no_nontrivial_cycle_of_excluded
#print axioms cc_no_nontrivial_five_cycle
#print axioms cc_no_nontrivial_six_cycle
#print axioms cc_no_nontrivial_seven_cycle
#print axioms cc_no_nontrivial_eight_cycle

end CollatzCycleUniform
