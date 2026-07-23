import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.LyapunovCascade
import Propositio.NumberTheory.Collatz.CascadeCycles
import Propositio.NumberTheory.Collatz.H5

/-!
# Exclusion of `cc`-cycles of length 8 via kernel `decide` over compositions

## Method and scaling advantage

This file proves there is no nontrivial cycle of length **L = 8** for the
fully-compressed odd Collatz map `cc n = (3n+1)/2^{v₂(3n+1)}`.

The **key scaling improvement** over `CollatzFiveSixSevenCycleExclusion.lean` is the
**decide-over-compositions** method:

*Old method (`interval_cases`):* For L=7 we `interval_cases` over 6 free valuation
variables, each up to A. For L=8, A=15, this would generate ≈ 8^7 ≈ 2 million
branches — completely infeasible for `interval_cases` or `omega`.

*New method (L=8):* For each admissible total valuation A (the constraint
`3^L < 2^A < 4^L` pins A to finitely many values), we `decide` over
`compositions L A` — all lists of L positive naturals summing to A.
The RHS of the telescoped identity depends on the valuation list only through a
pure recursive formula (`steinerVal`), so the check is a single kernel `decide`
over C(A−1, L−1) compositions:

| (L, A) | C(A−1, L−1) | Old `interval_cases` bound |
|--------|-------------|---------------------------|
| (8,13) | 792         | ≫ 10^6                   |
| (8,14) | 1716        | ≫ 10^6                   |
| (8,15) | 3432        | ≫ 10^6                   |

*Crucial axiom hygiene:* we use `decide` only (kernel-checked), NEVER
`native_decide` (which would introduce `Lean.ofReduceBool`). All main theorems
depend only on `[propext, Classical.choice, Quot.sound]`.

## Honesty caveat

This is a genuine L=8 exclusion. The general theorem (Steiner 1977,
Simons–de Weger 2005) — ruling out ALL cycle lengths simultaneously — requires
Baker-type transcendence bounds on linear forms in logarithms, far beyond this file.
The decide-composition method applies for each fixed L, but the composition count
C(A−1, L−1) grows with L, making arbitrarily large L eventually infeasible for the
kernel. L=8 is well within reach.
-/

namespace CollatzCycleDecide

open TerrasDensity (cc)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## Pure list machinery: `steinerVal` and `compositions` -/

/-- `steinerVal as` computes the Steiner numerator for the valuation list `as`.
The foldl accumulator is `(steiner_so_far, partial_sum_so_far)`:

* Initially `(0, 0)`.
* Step: `(s, t) ↦ (3·s + 2^t, t + aᵢ)` encodes
  `Steiner n (i+1) = 3·Steiner n i + 2^(S n i)`.

For `as = [a₀,…,a_{L−1}]` with `aᵢ = v₂(3·cc^[i] n + 1)`,
`steinerVal as = CollatzCycleTelescope.Steiner n L`. -/
def steinerVal (as : List Nat) : Nat :=
  (as.foldl (fun p a => (3 * p.1 + 2 ^ p.2, p.2 + a)) (0, 0)).1

/-- `compositions parts total` enumerates all lists of exactly `parts` positive
naturals summing to `total`.  Each member `as` satisfies `∀ x ∈ as, 1 ≤ x` and
`as.length = parts` and `as.sum = total`. -/
def compositions : Nat → Nat → List (List Nat)
  | 0,        t => if t = 0 then [[]] else []
  | parts + 1, t =>
    (List.range t).flatMap (fun i =>
      let a := i + 1
      (compositions parts (t - a)).map (a :: ·))

/-! ## Sanity checks via `#eval` -/

-- steinerVal [] = 0 (Steiner n 0 = 0)
#eval steinerVal []          -- 0
-- steinerVal [any] = 1 (Steiner n 1 = 2^0 = 1)
#eval steinerVal [3]         -- 1
-- steinerVal [a0, a1] = 3 + 2^a0
#eval steinerVal [1, 2]      -- 5  (= 3 + 2^1)
#eval steinerVal [2, 1]      -- 7  (= 3 + 2^2)
-- Composition count C(14,7) = 3432 for L=8, A=15
#eval (compositions 8 15).length  -- 3432
-- Pipeline verification: L=5, A=8, modulus 13
#eval (compositions 5 8).all (fun as => ¬ (13 : Nat) ∣ steinerVal as)  -- true

/-! ## `steinerVal` expansion lemma -/

/-- Explicit expansion of `steinerVal [a0,…,a7]`.

Proof: `simp` unfolds the 8-step `foldl`; the initial `2^0 = 1` and `Nat.zero_add`
simplify; the partial sums `t_i = a0+…+a_{i−1}` appear as-is in the formula;
`ring` closes the remaining algebraic identity. -/
theorem steinerVal_8 (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) :
    steinerVal [a0, a1, a2, a3, a4, a5, a6, a7]
    = 2187 + 729 * 2 ^ a0 + 243 * 2 ^ (a0 + a1)
      + 81 * 2 ^ (a0 + a1 + a2) + 27 * 2 ^ (a0 + a1 + a2 + a3)
      + 9 * 2 ^ (a0 + a1 + a2 + a3 + a4) + 3 * 2 ^ (a0 + a1 + a2 + a3 + a4 + a5)
      + 2 ^ (a0 + a1 + a2 + a3 + a4 + a5 + a6) := by
  simp only [steinerVal, List.foldl, Nat.zero_add, Nat.mul_zero, pow_zero, Nat.mul_one]
  ring

/-! ## Membership in `compositions` -/

/-- Appending a positive `a ≤ total` to a composition of `total - a` into `L` parts
gives a composition of `total` into `L+1` parts. -/
theorem cons_mem_compositions {a total L : Nat} {as : List Nat}
    (ha : 1 ≤ a) (ha_le : a ≤ total) (hmem : as ∈ compositions L (total - a)) :
    a :: as ∈ compositions (L + 1) total := by
  simp only [compositions, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨a - 1, by omega, as, ?_, by simp; omega⟩
  have heq : a - 1 + 1 = a := by omega
  rwa [heq]

/-- The empty list is a composition of 0 into 0 parts. -/
theorem nil_mem_compositions_zero : ([] : List Nat) ∈ compositions 0 0 := by
  simp [compositions]

/-! ## Pinning `A` for L = 8 -/

/-- For L=8: `3^8 = 6561 < 2^A < 4^8 = 65536` forces `A ∈ {13, 14, 15}`.

Bounds: `2^12 = 4096 < 6561` and `2^16 = 65536`. -/
theorem pow_two_in_6561_65536 (A : Nat) (hlo : 6561 < 2 ^ A) (hhi : 2 ^ A < 65536) :
    A = 13 ∨ A = 14 ∨ A = 15 := by
  rcases Nat.lt_or_ge A 13 with hA | hA
  · have : (2 : Nat) ^ A ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rcases Nat.lt_or_ge A 16 with hA16 | hA16
    · omega
    · have : (2 : Nat) ^ 16 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA16
      omega

/-! ## Oddness along the cycle -/

/-- Every iterate `cc^[i] n` of an odd start is odd. -/
theorem iterate_odd (n : Nat) (hodd : Odd n) (i : Nat) : Odd (cc^[i] n) := by
  cases i with
  | zero => simpa using hodd
  | succ j => rw [Function.iterate_succ_apply']; exact CollatzH5.cc_odd _

/-- For odd `m`, `v₂(3m+1) ≥ 1`: `3m+1 = 2(3k+2)` when `m = 2k+1`. -/
theorem one_le_v2_three_mul_add_one {m : Nat} (hm : Odd m) :
    1 ≤ padicValNat 2 (3 * m + 1) := by
  obtain ⟨k, hk⟩ := hm
  have hdvd : (2 : Nat) ^ 1 ∣ (3 * m + 1) := ⟨3 * k + 2, by omega⟩
  have hne : (3 * m + 1) ≠ 0 := by omega
  exact (padicValNat_dvd_iff_le hne).mp hdvd

/-! ## Kernel `decide` checks for L = 8

For L=8, A∈{13,14,15}, the divisibility moduli are:
* A=13: 2^13 − 3^8 = 8192 − 6561 = 1631  (792 compositions)
* A=14: 2^14 − 3^8 = 16384 − 6561 = 9823  (1716 compositions)
* A=15: 2^15 − 3^8 = 32768 − 6561 = 26207  (3432 compositions)
-/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- No positive composition of 13 into 8 parts yields `1631 ∣ steinerVal`.
(792 compositions checked by kernel `decide`.) -/
theorem check8_13 :
    (compositions 8 13).all (fun as => ¬ (1631 : Nat) ∣ steinerVal as) = true := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- No positive composition of 14 into 8 parts yields `9823 ∣ steinerVal`.
(1716 compositions checked by kernel `decide`.) -/
theorem check8_14 :
    (compositions 8 14).all (fun as => ¬ (9823 : Nat) ∣ steinerVal as) = true := by
  decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
/-- No positive composition of 15 into 8 parts yields `26207 ∣ steinerVal`.
(3432 compositions checked by kernel `decide`.) -/
theorem check8_15 :
    (compositions 8 15).all (fun as => ¬ (26207 : Nat) ∣ steinerVal as) = true := by
  decide

/-! ## Main exclusion theorem for L = 8 -/

set_option maxHeartbeats 4000000 in
/-- **`cc_no_nontrivial_eight_cycle`.**

No nontrivial `cc`-cycle of length 8 exists.

**Proof (decide-over-compositions method):**

1. Derive the L=8 telescoped exact relation (one more step than L=7):
   for `nᵢ = cc^[i] n`, `aᵢ = v₂(3nᵢ+1)`, `A = Σ aᵢ`:
   `2^A · n₀ = 3^8 · n₀ + steinerVal [a₀,…,a₇]`.

2. `cc_cycle_constraint` gives `6561 < 2^A < 65536`, so A ∈ {13,14,15}.

3. For each A: `(2^A − 3^8) · n₀ = steinerVal [a₀,…,a₇]`, giving divisibility.

4. Each aᵢ ≥ 1 (from oddness) and Σaᵢ = A, so `[a₀,…,a₇] ∈ compositions 8 A`.

5. `check8_A` (kernel `decide`) rules out `(2^A−3^8) ∣ steinerVal` for all members
   of `compositions 8 A` — contradiction. -/
theorem cc_no_nontrivial_eight_cycle (n : Nat) (hodd : Odd n)
    (hcyc : cc^[8] n = n) (hnontriv : ∃ j ∈ Finset.range 8, 1 < cc^[j] n) :
    False := by
  -- Name cycle elements and per-step valuations.
  set n0 := cc^[0] n with hn0
  set n1 := cc^[1] n with hn1
  set n2 := cc^[2] n with hn2
  set n3 := cc^[3] n with hn3
  set n4 := cc^[4] n with hn4
  set n5 := cc^[5] n with hn5
  set n6 := cc^[6] n with hn6
  set n7 := cc^[7] n with hn7
  set a0 := padicValNat 2 (3 * cc^[0] n + 1) with ha0
  set a1 := padicValNat 2 (3 * cc^[1] n + 1) with ha1
  set a2 := padicValNat 2 (3 * cc^[2] n + 1) with ha2
  set a3 := padicValNat 2 (3 * cc^[3] n + 1) with ha3
  set a4 := padicValNat 2 (3 * cc^[4] n + 1) with ha4
  set a5 := padicValNat 2 (3 * cc^[5] n + 1) with ha5
  set a6 := padicValNat 2 (3 * cc^[6] n + 1) with ha6
  set a7 := padicValNat 2 (3 * cc^[7] n + 1) with ha7
  -- Per-step exact identities: 2^aᵢ · nᵢ₊₁ = 3·nᵢ + 1.
  have h0 : 2 ^ a0 * n1 = 3 * n0 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 0; simpa [hn0, hn1, ha0] using this
  have h1 : 2 ^ a1 * n2 = 3 * n1 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 1; simpa [hn1, hn2, ha1] using this
  have h2 : 2 ^ a2 * n3 = 3 * n2 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 2; simpa [hn2, hn3, ha2] using this
  have h3 : 2 ^ a3 * n4 = 3 * n3 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 3; simpa [hn3, hn4, ha3] using this
  have h4 : 2 ^ a4 * n5 = 3 * n4 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 4; simpa [hn4, hn5, ha4] using this
  have h5 : 2 ^ a5 * n6 = 3 * n5 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 5; simpa [hn5, hn6, ha5] using this
  have h6 : 2 ^ a6 * n7 = 3 * n6 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 6; simpa [hn6, hn7, ha6] using this
  have h7 : 2 ^ a7 * n0 = 3 * n7 + 1 := by
    have hh := CollatzCascadeCycles.pow_v2_mul_iterate n 7
    rw [show (7 : Nat) + 1 = 8 from rfl, hcyc] at hh
    simpa [hn0, hn7, ha7] using hh
  -- Telescoped exact relation (innermost to outermost).
  have hI6 : 2 ^ a6 * (2 ^ a7 * n0) = 9 * n6 + 3 + 2 ^ a6 := by
    have : 2 ^ a6 * (2 ^ a7 * n0) = 3 * (2 ^ a6 * n7) + 2 ^ a6 := by rw [h7]; ring
    rw [this, h6]; ring
  have hI5 : 2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0))
      = 27 * n5 + 9 + 3 * 2 ^ a5 + 2 ^ a5 * 2 ^ a6 := by
    rw [hI6]
    have : 2 ^ a5 * (9 * n6 + 3 + 2 ^ a6)
        = 9 * (2 ^ a5 * n6) + 3 * 2 ^ a5 + 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h5]; ring
  have hI4 : 2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))
      = 81 * n4 + 27 + 9 * 2 ^ a4 + 3 * (2 ^ a4 * 2 ^ a5)
        + 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by
    rw [hI5]
    have : 2 ^ a4 * (27 * n5 + 9 + 3 * 2 ^ a5 + 2 ^ a5 * 2 ^ a6)
        = 27 * (2 ^ a4 * n5) + 9 * 2 ^ a4 + 3 * (2 ^ a4 * 2 ^ a5)
          + 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h4]; ring
  have hI3 : 2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0))))
      = 243 * n3 + 81 + 27 * 2 ^ a3 + 9 * (2 ^ a3 * 2 ^ a4)
        + 3 * (2 ^ a3 * 2 ^ a4 * 2 ^ a5)
        + 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by
    rw [hI4]
    have : 2 ^ a3 * (81 * n4 + 27 + 9 * 2 ^ a4 + 3 * (2 ^ a4 * 2 ^ a5)
            + 2 ^ a4 * 2 ^ a5 * 2 ^ a6)
        = 81 * (2 ^ a3 * n4) + 27 * 2 ^ a3 + 9 * (2 ^ a3 * 2 ^ a4)
          + 3 * (2 ^ a3 * 2 ^ a4 * 2 ^ a5)
          + 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h3]; ring
  have hI2 : 2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))))
      = 729 * n2 + 243 + 81 * 2 ^ a2 + 27 * (2 ^ a2 * 2 ^ a3)
        + 9 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4)
        + 3 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
        + 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by
    rw [hI3]
    have : 2 ^ a2 * (243 * n3 + 81 + 27 * 2 ^ a3 + 9 * (2 ^ a3 * 2 ^ a4)
            + 3 * (2 ^ a3 * 2 ^ a4 * 2 ^ a5) + 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6)
        = 243 * (2 ^ a2 * n3) + 81 * 2 ^ a2 + 27 * (2 ^ a2 * 2 ^ a3)
          + 9 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4)
          + 3 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
          + 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h2]; ring
  have hI1 : 2 ^ a1 * (2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0))))))
      = 2187 * n1 + 729 + 243 * 2 ^ a1 + 81 * (2 ^ a1 * 2 ^ a2)
        + 27 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3)
        + 9 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4)
        + 3 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
        + 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by
    rw [hI2]
    have : 2 ^ a1 * (729 * n2 + 243 + 81 * 2 ^ a2 + 27 * (2 ^ a2 * 2 ^ a3)
            + 9 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4)
            + 3 * (2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
            + 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6)
        = 729 * (2 ^ a1 * n2) + 243 * 2 ^ a1 + 81 * (2 ^ a1 * 2 ^ a2)
          + 27 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3)
          + 9 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4)
          + 3 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
          + 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h1]; ring
  -- Full telescoped relation (outermost step, using h0 and hI1).
  have htel : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))))))
      = 6561 * n0 + 2187 + 729 * 2 ^ a0 + 243 * (2 ^ a0 * 2 ^ a1)
        + 81 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2)
        + 27 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3)
        + 9 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4)
        + 3 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
        + 2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by
    rw [hI1]
    have : 2 ^ a0 * (2187 * n1 + 729 + 243 * 2 ^ a1 + 81 * (2 ^ a1 * 2 ^ a2)
            + 27 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3)
            + 9 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4)
            + 3 * (2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
            + 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6)
        = 2187 * (2 ^ a0 * n1) + 729 * 2 ^ a0 + 243 * (2 ^ a0 * 2 ^ a1)
          + 81 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2)
          + 27 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3)
          + 9 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4)
          + 3 * (2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5)
          + 2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * 2 ^ a5 * 2 ^ a6 := by ring
    rw [this, h0]; ring
  -- Normalize all power-products to single powers via simp [← pow_add].
  simp only [← pow_add] at htel
  -- Cycle constraint: 3^8 < 2^A < 4^8.
  have hcon := CollatzCascadeCycles.cc_cycle_constraint n 8 hodd hcyc (by omega) hnontriv
  obtain ⟨hlo, hhi⟩ := hcon
  have hAsum : (∑ i ∈ Finset.range 8, padicValNat 2 (3 * cc^[i] n + 1))
      = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [← ha0, ← ha1, ← ha2, ← ha3, ← ha4, ← ha5, ← ha6, ← ha7]; ring
  rw [hAsum] at hlo hhi
  -- 3^8 = 6561, 4^8 = 65536.
  norm_num at hlo hhi
  -- Valuation lower bounds: each aᵢ ≥ 1.
  have ho0 : 1 ≤ a0 := one_le_v2_three_mul_add_one (iterate_odd n hodd 0)
  have ho1 : 1 ≤ a1 := one_le_v2_three_mul_add_one (iterate_odd n hodd 1)
  have ho2 : 1 ≤ a2 := one_le_v2_three_mul_add_one (iterate_odd n hodd 2)
  have ho3 : 1 ≤ a3 := one_le_v2_three_mul_add_one (iterate_odd n hodd 3)
  have ho4 : 1 ≤ a4 := one_le_v2_three_mul_add_one (iterate_odd n hodd 4)
  have ho5 : 1 ≤ a5 := one_le_v2_three_mul_add_one (iterate_odd n hodd 5)
  have ho6 : 1 ≤ a6 := one_le_v2_three_mul_add_one (iterate_odd n hodd 6)
  have ho7 : 1 ≤ a7 := one_le_v2_three_mul_add_one (iterate_odd n hodd 7)
  -- steinerVal [a0,...,a7] equals the telescoped RHS.
  have hst := steinerVal_8 a0 a1 a2 a3 a4 a5 a6 a7
  -- Case split on A ∈ {13, 14, 15}.
  rcases pow_two_in_6561_65536 _ hlo hhi with hA | hA | hA
  · -- A = 13.  LHS = 2^13 · n0 = 8192 · n0.
    have hlhs : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))))))
        = 8192 * n0 := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hA]
      norm_num
    rw [hlhs] at htel
    -- 1631 * n0 = steinerVal [a0,...,a7]
    have heq : 1631 * n0 = steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      rw [hst]; omega
    -- Membership: [a0,...,a7] ∈ compositions 8 13.
    have hmem : [a0, a1, a2, a3, a4, a5, a6, a7] ∈ compositions 8 13 := by
      apply cons_mem_compositions ho0 (by omega)
      apply cons_mem_compositions ho1 (by omega)
      apply cons_mem_compositions ho2 (by omega)
      apply cons_mem_compositions ho3 (by omega)
      apply cons_mem_compositions ho4 (by omega)
      apply cons_mem_compositions ho5 (by omega)
      apply cons_mem_compositions ho6 (by omega)
      apply cons_mem_compositions ho7 (by omega)
      have : 13 - a0 - a1 - a2 - a3 - a4 - a5 - a6 - a7 = 0 := by omega
      rw [this]; exact nil_mem_compositions_zero
    -- check8_13 says ¬ 1631 ∣ steinerVal for all such lists.
    have hbad : ¬ (1631 : Nat) ∣ steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      have hcheck := List.all_eq_true.mp check8_13 _ hmem
      simpa [decide_eq_true_eq] using hcheck
    exact hbad ⟨n0, heq.symm⟩
  · -- A = 14.  LHS = 2^14 · n0 = 16384 · n0.
    have hlhs : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))))))
        = 16384 * n0 := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hA]
      norm_num
    rw [hlhs] at htel
    have heq : 9823 * n0 = steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      rw [hst]; omega
    have hmem : [a0, a1, a2, a3, a4, a5, a6, a7] ∈ compositions 8 14 := by
      apply cons_mem_compositions ho0 (by omega)
      apply cons_mem_compositions ho1 (by omega)
      apply cons_mem_compositions ho2 (by omega)
      apply cons_mem_compositions ho3 (by omega)
      apply cons_mem_compositions ho4 (by omega)
      apply cons_mem_compositions ho5 (by omega)
      apply cons_mem_compositions ho6 (by omega)
      apply cons_mem_compositions ho7 (by omega)
      have : 14 - a0 - a1 - a2 - a3 - a4 - a5 - a6 - a7 = 0 := by omega
      rw [this]; exact nil_mem_compositions_zero
    have hbad : ¬ (9823 : Nat) ∣ steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      have hcheck := List.all_eq_true.mp check8_14 _ hmem
      simpa [decide_eq_true_eq] using hcheck
    exact hbad ⟨n0, heq.symm⟩
  · -- A = 15.  LHS = 2^15 · n0 = 32768 · n0.
    have hlhs : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * (2 ^ a4 * (2 ^ a5 * (2 ^ a6 * (2 ^ a7 * n0)))))))
        = 32768 * n0 := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hA]
      norm_num
    rw [hlhs] at htel
    have heq : 26207 * n0 = steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      rw [hst]; omega
    have hmem : [a0, a1, a2, a3, a4, a5, a6, a7] ∈ compositions 8 15 := by
      apply cons_mem_compositions ho0 (by omega)
      apply cons_mem_compositions ho1 (by omega)
      apply cons_mem_compositions ho2 (by omega)
      apply cons_mem_compositions ho3 (by omega)
      apply cons_mem_compositions ho4 (by omega)
      apply cons_mem_compositions ho5 (by omega)
      apply cons_mem_compositions ho6 (by omega)
      apply cons_mem_compositions ho7 (by omega)
      have : 15 - a0 - a1 - a2 - a3 - a4 - a5 - a6 - a7 = 0 := by omega
      rw [this]; exact nil_mem_compositions_zero
    have hbad : ¬ (26207 : Nat) ∣ steinerVal [a0, a1, a2, a3, a4, a5, a6, a7] := by
      have hcheck := List.all_eq_true.mp check8_15 _ hmem
      simpa [decide_eq_true_eq] using hcheck
    exact hbad ⟨n0, heq.symm⟩

end CollatzCycleDecide

#print axioms CollatzCycleDecide.cc_no_nontrivial_eight_cycle
