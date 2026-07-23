import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.LyapunovCascade
import Propositio.NumberTheory.Collatz.H5

/-!
# The Collatz cycle multiplicative constraint — Lean 4 (NEW extension)

This file formalizes the **exact multiplicative constraint** that any cycle of the
fully-compressed odd Collatz map `cc n = (3n+1)/2^{v₂(3n+1)}` must satisfy. This is
the analytic heart of every modern Collatz cycle-exclusion result (Steiner 1977,
Simons–de Weger 2005): a hypothetical cycle of length `L` with total 2-adic
valuation `A := Σ_{i<L} v₂(3·cc^[i] n + 1)` is pinned by

    2^A · ∏_{i<L} cc^[i] n = ∏_{i<L} (3·cc^[i] n + 1)              (exact identity)

and, dividing factorwise through by `∏ cc^[i] n` (all factors ≥ 1) using
`3m < 3m+1 ≤ 4m`:

    3^L < 2^A < 4^L              (equivalently  L·log₂3 < A < 2L).

## Reuse — no map is redefined

  * `TerrasDensity.cc` — the compressed odd Collatz step.
  * `TerrasDensity.Odd n = ∃ k, n = 2k+1`.
  * `LyapunovCascade.pow_v2_mul_cc n : 2^{v₂(3n+1)} · cc n = 3n+1` — the per-step
    exact-division identity (the single load-bearing arithmetic fact).
  * `CollatzH5.cc_odd n : Odd (cc n)` — unconditional oddness of one `cc` step
    (hence positivity of every cycle element after the first).

## What is new

  1. `cc_cycle_prod_identity` — the **exact cyclic identity** above. This holds for
     *any* cycle, with no regime hypothesis (unlike `cascade_mult_exact`, which is
     restricted to the single-spine cascade regime `v₂(n+1) = L+2`).
  2. `cc_cycle_three_pow_lt` — the **lower bound** `3^L < 2^A` (factorwise `3m < 3m+1`).
  3. `cc_cycle_pow_lt_four` — the **upper bound** `2^A < 4^L` for a nontrivial cycle.
     Combined with (2): the fundamental constraint `3^L < 2^A < 4^L`.

## Honesty caveats

Full cycle-exclusion is NOT claimed and is NOT required by the task. These results
are the *necessary multiplicative constraint* every cc-cycle obeys; ruling out the
constraint for all `L` (Steiner/Simons–de Weger) requires transcendence theory
(Baker's bounds on linear forms in logarithms) and is far beyond this file.
-/

namespace CollatzCascadeCycles

open TerrasDensity (cc)
open scoped BigOperators

/-- Local abbreviation for the project's `Odd` (`∃ k, n = 2k+1`), distinct from
mathlib's `_root_.Odd`. -/
local notation "Odd" => TerrasDensity.Odd

/-! ## Per-step exact identity and positivity bookkeeping -/

/-- **Per-step exact identity.** For every `m`,
`2^{v₂(3m+1)} · cc m = 3m+1`. This is `LyapunovCascade.pow_v2_mul_cc`, restated
for local use. Holds with no hypothesis on `m` (`cc` is the odd part of `3m+1`). -/
theorem pow_v2_mul_cc (m : Nat) :
    2 ^ padicValNat 2 (3 * m + 1) * cc m = 3 * m + 1 :=
  LyapunovCascade.pow_v2_mul_cc m

/-- Every iterate `cc^[i] n` of an odd start is `≥ 1`: for `i = 0` it is `n` (odd,
hence positive); for `i ≥ 1` it is `cc (cc^[i-1] n)`, odd by `CollatzH5.cc_odd`. -/
theorem one_le_iterate (n : Nat) (hodd : Odd n) (i : Nat) : 1 ≤ cc^[i] n := by
  cases i with
  | zero => obtain ⟨k, hk⟩ := hodd; simp [hk]
  | succ j =>
    rw [Function.iterate_succ_apply']
    obtain ⟨k, hk⟩ := CollatzH5.cc_odd (cc^[j] n)
    omega

/-- Convenience: the per-step identity rewritten on a cycle iterate, exposing the
"next" element `cc^[i+1] n` via `Function.iterate_succ_apply'`. -/
theorem pow_v2_mul_iterate (n i : Nat) :
    2 ^ padicValNat 2 (3 * cc^[i] n + 1) * cc^[i + 1] n = 3 * cc^[i] n + 1 := by
  rw [Function.iterate_succ_apply']
  exact pow_v2_mul_cc (cc^[i] n)

/-! ## 1. The exact cyclic identity -/

/-- **`cc_cycle_prod_identity` — the exact cycle constraint (NEW).**

Let `n` be odd with `cc^[L] n = n` (an `L`-step cycle of the compressed map).
Set the total 2-adic valuation around the cycle

    A := Σ_{i<L} v₂(3·cc^[i] n + 1).

Then the **exact multiplicative identity** holds:

    2^A · ∏_{i<L} cc^[i] n = ∏_{i<L} (3·cc^[i] n + 1).

Proof. Per step, `2^{a_i} · cc^[i+1] n = 3·cc^[i] n + 1` (`pow_v2_mul_iterate`).
Taking `∏_{i<L}` and splitting the product, the RHS becomes
`(∏ 2^{a_i}) · (∏ cc^[i+1] n) = 2^A · ∏ cc^[i+1] n`. The cyclic product
`∏_{i<L} cc^[i+1] n` reindexes to `∏_{i<L} cc^[i] n` because the orbit closes:
`Finset.prod_range_succ'` and `Finset.prod_range_succ` both expand
`∏_{i<L+1} cc^[i] n`, equating `(∏_{i<L} cc^[i+1] n)·(cc^[0] n)` with
`(∏_{i<L} cc^[i] n)·(cc^[L] n)`; with `cc^[0] n = n = cc^[L] n ≠ 0` the trailing
factors cancel.

This is the unconditional, full-generality form of the cascade landing identity:
no `v₂(n+1)` spine hypothesis is needed (unlike `cascade_mult_exact`). -/
theorem cc_cycle_prod_identity (n L : Nat) (hodd : Odd n) (hcyc : cc^[L] n = n) :
    2 ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1))
        * ∏ i ∈ Finset.range L, cc^[i] n
      = ∏ i ∈ Finset.range L, (3 * cc^[i] n + 1) := by
  -- RHS = ∏ (2^{a_i} · cc^[i+1] n) via the per-step identity.
  have hrhs :
      (∏ i ∈ Finset.range L, (3 * cc^[i] n + 1))
        = ∏ i ∈ Finset.range L,
            (2 ^ padicValNat 2 (3 * cc^[i] n + 1) * cc^[i + 1] n) := by
    apply Finset.prod_congr rfl
    intro i _
    exact (pow_v2_mul_iterate n i).symm
  -- Split the product of products.
  rw [hrhs, Finset.prod_mul_distrib]
  -- ∏ 2^{a_i} = 2^{Σ a_i}.
  rw [← Finset.prod_pow_eq_pow_sum]
  -- Reindex the shifted cyclic product:  ∏_{i<L} cc^[i+1] n = ∏_{i<L} cc^[i] n.
  have hshift :
      (∏ i ∈ Finset.range L, cc^[i + 1] n)
        = ∏ i ∈ Finset.range L, cc^[i] n := by
    -- Both expansions of ∏_{i<L+1} cc^[i] n, with the trailing factors
    -- cc^[0] n = n and cc^[L] n = n cancelled (n ≠ 0).
    have hsucc' :
        (∏ i ∈ Finset.range (L + 1), cc^[i] n)
          = (∏ i ∈ Finset.range L, cc^[i + 1] n) * cc^[0] n :=
      Finset.prod_range_succ' (fun i => cc^[i] n) L
    have hsucc :
        (∏ i ∈ Finset.range (L + 1), cc^[i] n)
          = (∏ i ∈ Finset.range L, cc^[i] n) * cc^[L] n :=
      Finset.prod_range_succ (fun i => cc^[i] n) L
    rw [Function.iterate_zero_apply] at hsucc'
    rw [hcyc] at hsucc
    have hn0 : n ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
    have hmul : (∏ i ∈ Finset.range L, cc^[i + 1] n) * n
            = (∏ i ∈ Finset.range L, cc^[i] n) * n := by
      rw [← hsucc', ← hsucc]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) hmul
  rw [hshift]

/-! ## 2 & 3. The fundamental bounds  3^L < 2^A < 4^L  -/

/-- **`cc_cycle_three_pow_lt` — the lower bound `3^L < 2^A` (NEW).**

With the hypotheses of `cc_cycle_prod_identity` (and `L ≥ 1`), the cleaner
factorwise inequality `3m < 3m+1` (for `m ≥ 1`) gives

    3^L · ∏ cc^[i] n  <  ∏ (3·cc^[i] n + 1)  =  2^A · ∏ cc^[i] n,

and cancelling the positive `∏ cc^[i] n` yields `3^L < 2^A`. -/
theorem cc_cycle_three_pow_lt (n L : Nat) (hodd : Odd n) (hcyc : cc^[L] n = n)
    (hL : 1 ≤ L) :
    (3 : Nat) ^ L < 2 ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1)) := by
  set A := ∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1) with hA
  set P := ∏ i ∈ Finset.range L, cc^[i] n with hP
  -- Positivity of the cycle product.
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun i _ => one_le_iterate n hodd i)
  -- ∏ (3 · cc^[i] n) = 3^L · P.
  have hfactor :
      (∏ i ∈ Finset.range L, (3 * cc^[i] n)) = (3 : Nat) ^ L * P := by
    rw [Finset.prod_mul_distrib, hP, Finset.prod_const, Finset.card_range]
  -- 2^A · P = ∏ (3·cc^[i] n + 1)  (the exact identity).
  have hident := cc_cycle_prod_identity n L hodd hcyc
  rw [← hA, ← hP] at hident
  -- ∏ (3·cc^[i] n)  <  ∏ (3·cc^[i] n + 1)  factorwise (strict, nonempty).
  have hstrict :
      (∏ i ∈ Finset.range L, (3 * cc^[i] n))
        < ∏ i ∈ Finset.range L, (3 * cc^[i] n + 1) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      have := one_le_iterate n hodd i; omega
    · intro i _; omega
    · exact Finset.nonempty_range_iff.mpr (by omega)
  -- Chain:  3^L · P  <  2^A · P,  then cancel P.
  rw [hfactor, ← hident] at hstrict
  exact Nat.lt_of_mul_lt_mul_right hstrict

set_option linter.unusedVariables false in
/-- **`cc_cycle_pow_lt_four` — the upper bound `2^A < 4^L` (NEW).**

With the hypotheses of `cc_cycle_prod_identity`, `L ≥ 1`, and the cycle being
**nontrivial** — some element exceeds `1`, i.e. `∃ j < L, 1 < cc^[j] n` — the
factorwise inequality `3m+1 ≤ 4m` (for `m ≥ 1`, strict when `m > 1`) gives

    ∏ (3·cc^[i] n + 1)  <  ∏ (4·cc^[i] n)  =  4^L · ∏ cc^[i] n,

and, with `2^A · ∏ cc^[i] n = ∏ (3·cc^[i] n + 1)`, cancelling the positive
`∏ cc^[i] n` yields `2^A < 4^L`.

Combined with `cc_cycle_three_pow_lt`, this is the **fundamental cycle
constraint** `3^L < 2^A < 4^L`. The nontriviality hypothesis is necessary: a
cycle in which every element equals `1` would be the degenerate fixed point
`cc 1 = 1` (`3·1+1 = 4 = 2^2`, `cc 1 = 1`), for which `3m+1 = 4m` holds with
equality and the upper bound is not strict. -/
theorem cc_cycle_pow_lt_four (n L : Nat) (hodd : Odd n) (hcyc : cc^[L] n = n)
    (hL : 1 ≤ L) (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    (2 : Nat) ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1)) < 4 ^ L := by
  set A := ∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1) with hA
  set P := ∏ i ∈ Finset.range L, cc^[i] n with hP
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun i _ => one_le_iterate n hodd i)
  -- ∏ (4 · cc^[i] n) = 4^L · P.
  have hfactor :
      (∏ i ∈ Finset.range L, (4 * cc^[i] n)) = (4 : Nat) ^ L * P := by
    rw [Finset.prod_mul_distrib, hP, Finset.prod_const, Finset.card_range]
  have hident := cc_cycle_prod_identity n L hodd hcyc
  rw [← hA, ← hP] at hident
  -- ∏ (3·cc^[i] n + 1)  <  ∏ (4·cc^[i] n)  (≤ everywhere, strict at the witness).
  obtain ⟨j, hjmem, hj1⟩ := hnontriv
  have hstrict :
      (∏ i ∈ Finset.range L, (3 * cc^[i] n + 1))
        < ∏ i ∈ Finset.range L, (4 * cc^[i] n) := by
    apply Finset.prod_lt_prod
    · intro i _; omega
    · intro i _
      have := one_le_iterate n hodd i; omega
    · exact ⟨j, hjmem, by omega⟩
  -- Chain:  2^A · P  <  4^L · P,  then cancel P.
  rw [hfactor, ← hident] at hstrict
  exact Nat.lt_of_mul_lt_mul_right hstrict

/-- **`cc_cycle_constraint` — the combined fundamental constraint (NEW).**

Packaging `cc_cycle_three_pow_lt` and `cc_cycle_pow_lt_four`: for a nontrivial
`L`-step cc-cycle (`L ≥ 1`, some element `> 1`),

    3^L  <  2^A  <  4^L,        A := Σ_{i<L} v₂(3·cc^[i] n + 1).

Equivalently `L·log₂3 < A < 2L`: the total 2-adic valuation `A` is squeezed into
a window of width `(2 − log₂3)·L ≈ 0.415·L`. This is the multiplicative
constraint underlying Steiner (1977) and Simons–de Weger (2005). -/
theorem cc_cycle_constraint (n L : Nat) (hodd : Odd n) (hcyc : cc^[L] n = n)
    (hL : 1 ≤ L) (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    (3 : Nat) ^ L < 2 ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1))
      ∧ (2 : Nat) ^ (∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1)) < 4 ^ L :=
  ⟨cc_cycle_three_pow_lt n L hodd hcyc hL, cc_cycle_pow_lt_four n L hodd hcyc hL hnontriv⟩

end CollatzCascadeCycles
