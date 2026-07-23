import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.LyapunovCascade
import Propositio.NumberTheory.Collatz.CascadeCycles
import Propositio.NumberTheory.Collatz.H5

/-!
# Exclusion of `cc`-cycles of length 3 and 4 — Lean 4 (NEW extension)

This file proves, **unconditionally** and axiom-clean, that the fully-compressed
odd Collatz map

    cc n = (3n+1)/2^{v₂(3n+1)}

has **no nontrivial cycle of length 3 or 4**.  This genuinely *goes beyond* the
length-`1,2` exclusion of `CollatzShortCycleExclusion.lean`: for `L = 3, 4` the
open interval `(3^L, 4^L)` *does* contain a power of `2` (namely `2^5 = 32` and
`2^7 = 128`), so the multiplicative constraint `3^L < 2^A < 4^L` alone is *not*
contradictory.  We close the gap with a **Steiner-type finite valuation check**:
a telescoped exact relation around the cycle, evaluated against the now-pinned
total valuation `A`, yields a divisibility that fails for *every* admissible
valuation pattern.

## The arithmetic for `L = 3`

Write `nᵢ = cc^[i] n`, `aᵢ = v₂(3nᵢ+1)`, `A = a₀+a₁+a₂`.  The per-step identity
`2^{aᵢ}·n_{i+1} = 3nᵢ+1` (`pow_v2_mul_iterate`), telescoped around the 3-cycle
(`n₃ = n₀`), gives the **exact relation**

    2^A · n₀ = 27·n₀ + (9 + 3·2^{a₀} + 2^{a₀+a₁}).

The constraint `cc_cycle_constraint` (L=3) gives `27 < 2^A < 64`; the only power
of `2` there is `2^5 = 32`, so `A = 5`.  Substituting `2^A = 32`:

    5·n₀ = 9 + 3·2^{a₀} + 2^{a₀+a₁}.

Each `nᵢ` is odd (start odd, `cc` preserves oddness), so each `aᵢ ≥ 1`; with
`a₂ = 5 − a₀ − a₁ ≥ 1` we get `a₀ ∈ {1,2,3}`, `a₁ ≥ 1`, `a₀+a₁ ≤ 4`.  Over this
finite set the RHS takes the values `{19,23,29,31,37,49}` — **none divisible by
5**.  But `5 ∣ 5·n₀`.  Contradiction.  No nontrivial 3-cycle.

## The arithmetic for `L = 4`

`nᵢ`, `aᵢ` analogously, `A = a₀+a₁+a₂+a₃`.  Telescoping the 4-cycle:

    2^A · n₀ = 81·n₀ + (27 + 9·2^{a₀} + 3·2^{a₀+a₁} + 2^{a₀+a₁+a₂}).

Constraint (L=4): `81 < 2^A < 256`, only `2^7 = 128`, so `A = 7`.  Then

    47·n₀ = 27 + 9·2^{a₀} + 3·2^{a₀+a₁} + 2^{a₀+a₁+a₂},

with `a₀,a₁,a₂ ≥ 1` and `a₀+a₁+a₂ ≤ 6`.  A finite check shows `47 ∤ RHS` for
**every** admissible pattern (verified by `decide` over the bounded set).  No
nontrivial 4-cycle.

## Honesty caveat

This is a true `L = 3, 4` exclusion.  It does **not** extend to all `L`: ruling
out every cycle length (Steiner 1977, Simons–de Weger 2005) needs Baker-type
transcendence bounds on linear forms in logarithms and is far beyond this file.
-/

namespace CollatzThreeCycleExclusion

open TerrasDensity (cc)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## Pinning the total valuation `A` from the interval constraint. -/

/-- The only power of `2` strictly between `27` and `64` is `2^5 = 32`, so
`27 < 2^A < 64` forces `A = 5`.  (`A ≤ 4 ⟹ 2^A ≤ 16 < 27`; `A ≥ 6 ⟹ 2^A ≥ 64`.) -/
theorem pow_two_eq_five_of_in_27_64 (A : Nat) (hlo : 27 < 2 ^ A) (hhi : 2 ^ A < 64) :
    A = 5 := by
  rcases Nat.lt_or_ge A 5 with hA | hA
  · -- A ≤ 4 ⟹ 2^A ≤ 2^4 = 16 < 27.
    have : (2 : Nat) ^ A ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rcases Nat.lt_or_ge A 6 with hA6 | hA6
    · omega
    · -- A ≥ 6 ⟹ 2^A ≥ 2^6 = 64.
      have : (2 : Nat) ^ 6 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA6
      omega

/-- The only power of `2` strictly between `81` and `256` is `2^7 = 128`, so
`81 < 2^A < 256` forces `A = 7`.  (`A ≤ 6 ⟹ 2^A ≤ 64 < 81`; `A ≥ 8 ⟹ 2^A ≥ 256`.) -/
theorem pow_two_eq_seven_of_in_81_256 (A : Nat) (hlo : 81 < 2 ^ A) (hhi : 2 ^ A < 256) :
    A = 7 := by
  rcases Nat.lt_or_ge A 7 with hA | hA
  · have : (2 : Nat) ^ A ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rcases Nat.lt_or_ge A 8 with hA8 | hA8
    · omega
    · have : (2 : Nat) ^ 8 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA8
      omega

/-! ## Oddness along the cycle ⟹ each per-step valuation is `≥ 1`. -/

/-- Every iterate `cc^[i] n` of an odd start is odd: `i = 0` is `n`; `i ≥ 1` is a
`cc`-image, odd by `CollatzH5.cc_odd`. -/
theorem iterate_odd (n : Nat) (hodd : Odd n) (i : Nat) : Odd (cc^[i] n) := by
  cases i with
  | zero => simpa using hodd
  | succ j => rw [Function.iterate_succ_apply']; exact CollatzH5.cc_odd _

/-- For odd `m`, `3m+1` is even, so `v₂(3m+1) ≥ 1`. -/
theorem one_le_v2_three_mul_add_one {m : Nat} (hm : Odd m) :
    1 ≤ padicValNat 2 (3 * m + 1) := by
  obtain ⟨k, hk⟩ := hm
  -- 3m+1 = 6k+4 = 2*(3k+2), so 2 ∣ 3m+1 and 3m+1 ≠ 0.
  have hdvd : (2 : Nat) ^ 1 ∣ (3 * m + 1) := ⟨3 * k + 2, by omega⟩
  have hne : (3 * m + 1) ≠ 0 := by omega
  exact (padicValNat_dvd_iff_le hne).mp hdvd

/-! ## 1. No nontrivial 3-cycle. -/

/-- **`cc_no_nontrivial_three_cycle` (NEW).**

There is no nontrivial `cc` 3-cycle: for odd `n` with `cc^[3] n = n` and a
nontriviality witness `∃ j ∈ Finset.range 3, 1 < cc^[j] n`, `False`.

Proof outline (Steiner-type finite valuation check):

* Per-step identities `2^{aᵢ}·n_{i+1} = 3nᵢ+1` for `i = 0,1,2`
  (`CollatzCascadeCycles.pow_v2_mul_iterate`), where `nᵢ = cc^[i] n`,
  `aᵢ = v₂(3nᵢ+1)`, and `cc^[3] n = n` closes the cycle.
* Telescoping (`linear_combination`) gives the exact relation
  `2^{a₀}·2^{a₁}·2^{a₂}·n₀ = 27·n₀ + 9 + 3·2^{a₀} + 2^{a₀}·2^{a₁}`.
* `cc_cycle_constraint` (L=3) gives `27 < 2^A < 64` with `A = a₀+a₁+a₂`, forcing
  `A = 5` (`pow_two_eq_five_of_in_27_64`); so `2^{a₀}·2^{a₁}·2^{a₂} = 32`.
* Each `nᵢ` is odd, so `aᵢ ≥ 1`; with `a₀+a₁+a₂ = 5` we get `a₀ ≤ 3`, `a₁ ≤ 3`.
* Substituting `32·n₀ = 27·n₀ + …` gives `5·n₀ = 9 + 3·2^{a₀} + 2^{a₀+a₁}`.
  Over `1 ≤ a₀, a₁` with `a₀+a₁ ≤ 4`, the RHS ∈ {19,23,29,31,37,49}, none
  divisible by `5` — contradiction (`interval_cases` + `omega`). -/
theorem cc_no_nontrivial_three_cycle (n : Nat) (hodd : Odd n)
    (hcyc : cc^[3] n = n) (hnontriv : ∃ j ∈ Finset.range 3, 1 < cc^[j] n) :
    False := by
  -- Names for cycle elements and per-step valuations.
  set n0 := cc^[0] n with hn0
  set n1 := cc^[1] n with hn1
  set n2 := cc^[2] n with hn2
  set a0 := padicValNat 2 (3 * cc^[0] n + 1) with ha0
  set a1 := padicValNat 2 (3 * cc^[1] n + 1) with ha1
  set a2 := padicValNat 2 (3 * cc^[2] n + 1) with ha2
  -- Per-step exact identities.
  have h0 : 2 ^ a0 * n1 = 3 * n0 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 0; simpa [hn0, hn1, ha0] using this
  have h1 : 2 ^ a1 * n2 = 3 * n1 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 1; simpa [hn1, hn2, ha1] using this
  have h2 : 2 ^ a2 * n0 = 3 * n2 + 1 := by
    have hh := CollatzCascadeCycles.pow_v2_mul_iterate n 2
    -- hh : 2^a2 * cc^[2+1] n = 3 * cc^[2] n + 1.  Rewrite cc^[2+1] n = cc^[3] n = n = n0.
    rw [show (2 : Nat) + 1 = 3 from rfl, hcyc] at hh
    simpa [hn0, hn2, ha2] using hh
  -- Telescoped exact relation over ℕ:
  --   2^a0·(2^a1·(2^a2·n0)) = 27 n0 + 9 + 3·2^a0 + 2^a0·2^a1.
  -- Generalize the powers to opaque naturals p0,p1,p2 and substitute h0,h1,h2.
  have htel : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * n0))
      = 27 * n0 + 9 + 3 * 2 ^ a0 + 2 ^ a0 * 2 ^ a1 := by
    -- Inner: 2^a1·(2^a2·n0) = 9 n1 + 3 + 2^a1.
    have hin : 2 ^ a1 * (2 ^ a2 * n0) = 9 * n1 + 3 + 2 ^ a1 := by
      have : 2 ^ a1 * (2 ^ a2 * n0) = 3 * (2 ^ a1 * n2) + 2 ^ a1 := by
        rw [h2]; ring
      rw [this, h1]; ring
    rw [hin]
    -- Outer: 2^a0·(9 n1 + 3 + 2^a1) = 9·(2^a0·n1) + 3·2^a0 + 2^a0·2^a1.
    have : 2 ^ a0 * (9 * n1 + 3 + 2 ^ a1) = 9 * (2 ^ a0 * n1) + 3 * 2 ^ a0 + 2 ^ a0 * 2 ^ a1 := by
      ring
    rw [this, h0]; ring
  -- Pull total valuation A from the cycle constraint and pin A = 5.
  have hcon := CollatzCascadeCycles.cc_cycle_constraint n 3 hodd hcyc (by omega) hnontriv
  obtain ⟨hlo, hhi⟩ := hcon
  -- A = a0 + a1 + a2 as the range-3 sum.
  have hAsum : (∑ i ∈ Finset.range 3, padicValNat 2 (3 * cc^[i] n + 1)) = a0 + a1 + a2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
    rw [← ha0, ← ha1, ← ha2]; ring
  rw [hAsum] at hlo hhi
  -- 3^3 = 27, 4^3 = 64.
  norm_num at hlo hhi
  have hA : a0 + a1 + a2 = 5 := pow_two_eq_five_of_in_27_64 _ hlo hhi
  -- LHS of htel: 2^a0 * (2^a1 * (2^a2 * n0)) = 2^(a0+a1+a2) * n0 = 32 * n0.
  have hlhs : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * n0)) = 32 * n0 := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_add, ← pow_add, hA]; norm_num
  rw [hlhs] at htel
  -- 32 n0 = 27 n0 + 9 + 3*2^a0 + 2^a0*2^a1  ⟹  5 n0 = 9 + 3*2^a0 + 2^(a0+a1).
  have hpow01 : 2 ^ a0 * 2 ^ a1 = 2 ^ (a0 + a1) := (pow_add 2 a0 a1).symm
  rw [hpow01] at htel
  have hfive : 5 * n0 = 9 + 3 * 2 ^ a0 + 2 ^ (a0 + a1) := by omega
  -- Valuation bounds: each aᵢ ≥ 1, and a0+a1+a2 = 5 forces a0 ≤ 3, a1 ≤ 3, a0+a1 ≤ 4.
  have ho0 : 1 ≤ a0 := one_le_v2_three_mul_add_one (iterate_odd n hodd 0)
  have ho1 : 1 ≤ a1 := one_le_v2_three_mul_add_one (iterate_odd n hodd 1)
  have ho2 : 1 ≤ a2 := one_le_v2_three_mul_add_one (iterate_odd n hodd 2)
  -- Reduce to a finite divisibility check: 5 ∣ RHS is false for all (a0, a1).
  have hb0 : a0 ≤ 3 := by omega
  have hb1 : a1 ≤ 3 := by omega
  have hsum01 : a0 + a1 ≤ 4 := by omega
  -- Case on a0 and a1; in each case 2^(a0+a1) and 2^a0 are concrete, so omega closes
  -- (5 ∤ RHS ∈ {19,23,29,31,37,49}); the a0+a1 > 4 cases are vacuous by hsum01.
  interval_cases a0 <;> interval_cases a1 <;> norm_num at hfive <;> omega

/-! ## 2. No nontrivial 4-cycle. -/

/-- **`cc_no_nontrivial_four_cycle` (NEW).**

There is no nontrivial `cc` 4-cycle: for odd `n` with `cc^[4] n = n` and a
nontriviality witness `∃ j ∈ Finset.range 4, 1 < cc^[j] n`, `False`.

Same Steiner-type finite valuation check.  With `nᵢ = cc^[i] n`,
`aᵢ = v₂(3nᵢ+1)`, `A = a₀+a₁+a₂+a₃`, the telescoped exact relation is

    2^{a₀}·(2^{a₁}·(2^{a₂}·(2^{a₃}·n₀)))
      = 81·n₀ + 27 + 9·2^{a₀} + 3·2^{a₀+a₁} + 2^{a₀+a₁+a₂}.

`cc_cycle_constraint` (L=4) gives `81 < 2^A < 256`, forcing `A = 7`
(`pow_two_eq_seven_of_in_81_256`); so the LHS is `128·n₀`.  Hence

    47·n₀ = 27 + 9·2^{a₀} + 3·2^{a₀+a₁} + 2^{a₀+a₁+a₂},

with each `aᵢ ≥ 1` and `a₀+a₁+a₂ ≤ 6` (`a₃ = 7−a₀−a₁−a₂ ≥ 1`).  A finite check
over all admissible `(a₀,a₁,a₂)` shows `47 ∤ RHS` in every case — contradiction.
(The check `47 ∤ RHS` was confirmed exhaustively before the proof: no admissible
valuation pattern yields a multiple of `47`.) -/
theorem cc_no_nontrivial_four_cycle (n : Nat) (hodd : Odd n)
    (hcyc : cc^[4] n = n) (hnontriv : ∃ j ∈ Finset.range 4, 1 < cc^[j] n) :
    False := by
  set n0 := cc^[0] n with hn0
  set n1 := cc^[1] n with hn1
  set n2 := cc^[2] n with hn2
  set n3 := cc^[3] n with hn3
  set a0 := padicValNat 2 (3 * cc^[0] n + 1) with ha0
  set a1 := padicValNat 2 (3 * cc^[1] n + 1) with ha1
  set a2 := padicValNat 2 (3 * cc^[2] n + 1) with ha2
  set a3 := padicValNat 2 (3 * cc^[3] n + 1) with ha3
  have h0 : 2 ^ a0 * n1 = 3 * n0 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 0; simpa [hn0, hn1, ha0] using this
  have h1 : 2 ^ a1 * n2 = 3 * n1 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 1; simpa [hn1, hn2, ha1] using this
  have h2 : 2 ^ a2 * n3 = 3 * n2 + 1 := by
    have := CollatzCascadeCycles.pow_v2_mul_iterate n 2; simpa [hn2, hn3, ha2] using this
  have h3 : 2 ^ a3 * n0 = 3 * n3 + 1 := by
    have hh := CollatzCascadeCycles.pow_v2_mul_iterate n 3
    rw [show (3 : Nat) + 1 = 4 from rfl, hcyc] at hh
    simpa [hn0, hn3, ha3] using hh
  -- Telescoped exact relation over ℕ.
  have htel : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * n0)))
      = 81 * n0 + 27 + 9 * 2 ^ a0 + 3 * (2 ^ a0 * 2 ^ a1) + 2 ^ a0 * 2 ^ a1 * 2 ^ a2 := by
    -- innermost: 2^a2·(2^a3·n0) = 9 n2 + 3 + 2^a2
    have hI2 : 2 ^ a2 * (2 ^ a3 * n0) = 9 * n2 + 3 + 2 ^ a2 := by
      have : 2 ^ a2 * (2 ^ a3 * n0) = 3 * (2 ^ a2 * n3) + 2 ^ a2 := by rw [h3]; ring
      rw [this, h2]; ring
    -- next: 2^a1·(9 n2 + 3 + 2^a2) = 27 n1 + 9 + 3·2^a1 + 2^a1·2^a2
    have hI1 : 2 ^ a1 * (2 ^ a2 * (2 ^ a3 * n0))
        = 27 * n1 + 9 + 3 * 2 ^ a1 + 2 ^ a1 * 2 ^ a2 := by
      rw [hI2]
      have : 2 ^ a1 * (9 * n2 + 3 + 2 ^ a2)
          = 9 * (2 ^ a1 * n2) + 3 * 2 ^ a1 + 2 ^ a1 * 2 ^ a2 := by ring
      rw [this, h1]; ring
    -- outer: multiply by 2^a0 and substitute h0.
    rw [hI1]
    have : 2 ^ a0 * (27 * n1 + 9 + 3 * 2 ^ a1 + 2 ^ a1 * 2 ^ a2)
        = 27 * (2 ^ a0 * n1) + 9 * 2 ^ a0 + 3 * (2 ^ a0 * 2 ^ a1)
          + 2 ^ a0 * 2 ^ a1 * 2 ^ a2 := by ring
    rw [this, h0]; ring
  -- Constraint ⟹ A = 7.
  have hcon := CollatzCascadeCycles.cc_cycle_constraint n 4 hodd hcyc (by omega) hnontriv
  obtain ⟨hlo, hhi⟩ := hcon
  have hAsum : (∑ i ∈ Finset.range 4, padicValNat 2 (3 * cc^[i] n + 1))
      = a0 + a1 + a2 + a3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
    rw [← ha0, ← ha1, ← ha2, ← ha3]; ring
  rw [hAsum] at hlo hhi
  -- 3^4 = 81, 4^4 = 256.
  norm_num at hlo hhi
  have hA : a0 + a1 + a2 + a3 = 7 := pow_two_eq_seven_of_in_81_256 _ hlo hhi
  -- LHS = 2^(a0+a1+a2+a3) * n0 = 128 * n0.
  have hlhs : 2 ^ a0 * (2 ^ a1 * (2 ^ a2 * (2 ^ a3 * n0))) = 128 * n0 := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
        ← pow_add, ← pow_add, ← pow_add, hA]; norm_num
  rw [hlhs] at htel
  -- Rewrite the power products as single powers.
  have hp01 : 2 ^ a0 * 2 ^ a1 = 2 ^ (a0 + a1) := (pow_add 2 a0 a1).symm
  rw [hp01] at htel
  -- now htel has `2 ^ (a0 + a1) * 2 ^ a2`; fold to 2^(a0+a1+a2).
  have hp012 : 2 ^ (a0 + a1) * 2 ^ a2 = 2 ^ (a0 + a1 + a2) := (pow_add 2 (a0 + a1) a2).symm
  rw [hp012] at htel
  -- 128 n0 = 81 n0 + 27 + 9·2^a0 + 3·2^(a0+a1) + 2^(a0+a1+a2)
  --   ⟹  47 n0 = 27 + 9·2^a0 + 3·2^(a0+a1) + 2^(a0+a1+a2).
  have hseven : 47 * n0
      = 27 + 9 * 2 ^ a0 + 3 * 2 ^ (a0 + a1) + 2 ^ (a0 + a1 + a2) := by omega
  -- Valuation bounds.
  have ho0 : 1 ≤ a0 := one_le_v2_three_mul_add_one (iterate_odd n hodd 0)
  have ho1 : 1 ≤ a1 := one_le_v2_three_mul_add_one (iterate_odd n hodd 1)
  have ho2 : 1 ≤ a2 := one_le_v2_three_mul_add_one (iterate_odd n hodd 2)
  have ho3 : 1 ≤ a3 := one_le_v2_three_mul_add_one (iterate_odd n hodd 3)
  have hb0 : a0 ≤ 4 := by omega
  have hb1 : a1 ≤ 4 := by omega
  have hb2 : a2 ≤ 4 := by omega
  -- Finite check: 47 ∤ RHS for every admissible (a0, a1, a2).
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;>
    norm_num at hseven <;> omega

end CollatzThreeCycleExclusion
