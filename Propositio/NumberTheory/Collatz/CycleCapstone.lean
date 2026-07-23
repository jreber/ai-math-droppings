import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ShortCycleExclusion
import Propositio.NumberTheory.Collatz.ThreeCycleExclusion
import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.NineCycle
import Propositio.NumberTheory.Collatz.TenCycle
import Propositio.NumberTheory.Collatz.ElevenCycle
import Propositio.NumberTheory.Collatz.TwelveCycle
import Propositio.NumberTheory.Collatz.ThirteenCycle
import Propositio.NumberTheory.Collatz.CascadeCycles
import Propositio.NumberTheory.Collatz.H5
import Propositio.NumberTheory.Collatz.FourteenCycle
import Propositio.NumberTheory.Collatz.FifteenCycle
import Propositio.NumberTheory.Collatz.SixteenCycle

/-!
# Capstone: no nontrivial `cc`-cycle of length 1 through 8

This file unifies the per-length cycle-exclusion results into two capstone
theorems (pure assembly — no new mathematics):

* `cc_no_nontrivial_cycle_le_eight`: odd `n`, `cc^[L] n = n`, `1 ≤ L ≤ 8`,
  nontrivial ⟹ `False`.
* `cc_cycle_le_eight_trivial`: every odd `cc`-cycle of length `1..8` is the
  trivial fixed point `n = 1`.

Dispatch:
* `L = 1, 2` → `CollatzShortCycleExclusion`.
* `L = 3, 4` → `CollatzThreeCycleExclusion`.
* `L = 5, 6, 7, 8` → `CollatzCycleUniform` (the scalable decide-over-compositions
  method, instantiated per length). This supersedes the older `interval_cases`
  route of `CollatzFiveSixSevenCycleExclusion` for L = 5,6,7 and extends to L = 8.

The underlying per-length proofs all run the Steiner finite divisibility check
under the fundamental constraint `3^L < 2^A < 4^L` (`CollatzCascadeCycles`).
-/

namespace CollatzCycleCapstone

open TerrasDensity (cc)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## Main capstone theorem. -/

/-- **`cc_no_nontrivial_cycle_le_eight`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 8`
is impossible.  Proof by `interval_cases L`, each branch dispatching to the
corresponding per-length exclusion theorem. -/
theorem cc_no_nontrivial_cycle_le_eight (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL8 : L ≤ 8)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  interval_cases L
  · -- L = 1
    have hfix : cc n = n := by simpa using hcyc
    obtain ⟨j, hj_mem, hj_gt⟩ := hnontriv
    simp only [Finset.mem_range] at hj_mem
    have hj0 : j = 0 := by omega
    subst hj0; simp only [Function.iterate_zero, id_eq] at hj_gt
    exact CollatzShortCycleExclusion.cc_no_nontrivial_one_cycle n hodd hfix hj_gt
  · -- L = 2
    have hcyc2 : cc (cc n) = n := by
      have : cc^[2] n = n := hcyc
      simpa [Function.iterate_succ, Function.iterate_one] using this
    exact CollatzShortCycleExclusion.cc_no_nontrivial_two_cycle n hodd hcyc2 hnontriv
  · exact CollatzThreeCycleExclusion.cc_no_nontrivial_three_cycle n hodd hcyc hnontriv
  · exact CollatzThreeCycleExclusion.cc_no_nontrivial_four_cycle n hodd hcyc hnontriv
  · exact CollatzCycleUniform.cc_no_nontrivial_five_cycle n hodd hcyc hnontriv
  · exact CollatzCycleUniform.cc_no_nontrivial_six_cycle n hodd hcyc hnontriv
  · exact CollatzCycleUniform.cc_no_nontrivial_seven_cycle n hodd hcyc hnontriv
  · exact CollatzCycleUniform.cc_no_nontrivial_eight_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_eight_trivial`.**

Every odd `cc`-cycle of length `1..8` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_eight_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL8 : L ≤ 8) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_eight n L hodd hcyc hL1 hL8 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 9` (via `CollatzNineCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_nine`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 9` is
impossible.  Extends `cc_no_nontrivial_cycle_le_eight` by the `L = 9` case
(`CollatzNineCycle.cc_no_nontrivial_nine_cycle`). -/
theorem cc_no_nontrivial_cycle_le_nine (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL9 : L ≤ 9)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 9 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_eight n L hodd hcyc hL1 (by omega) hnontriv
  · have hL9' : L = 9 := by omega
    subst hL9'
    exact CollatzNineCycle.cc_no_nontrivial_nine_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_nine_trivial`.**

Every odd `cc`-cycle of length `1..9` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_nine_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL9 : L ≤ 9) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_nine n L hodd hcyc hL1 hL9 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 10` (via `CollatzTenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_ten`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 10` is
impossible.  Extends `cc_no_nontrivial_cycle_le_nine` by the `L = 10` case
(`CollatzTenCycle.cc_no_nontrivial_ten_cycle`). -/
theorem cc_no_nontrivial_cycle_le_ten (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL10 : L ≤ 10)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 10 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_nine n L hodd hcyc hL1 (by omega) hnontriv
  · have hL10' : L = 10 := by omega
    subst hL10'
    exact CollatzTenCycle.cc_no_nontrivial_ten_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_ten_trivial`.**

Every odd `cc`-cycle of length `1..10` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_ten_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL10 : L ≤ 10) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_ten n L hodd hcyc hL1 hL10 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 11` (via `CollatzElevenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_eleven`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 11` is
impossible.  Extends `cc_no_nontrivial_cycle_le_ten` by the `L = 11` case
(`CollatzElevenCycle.cc_no_nontrivial_eleven_cycle`). -/
theorem cc_no_nontrivial_cycle_le_eleven (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL11 : L ≤ 11)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 11 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_ten n L hodd hcyc hL1 (by omega) hnontriv
  · have hL11' : L = 11 := by omega
    subst hL11'
    exact CollatzElevenCycle.cc_no_nontrivial_eleven_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_eleven_trivial`.**

Every odd `cc`-cycle of length `1..11` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_eleven_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL11 : L ≤ 11) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_eleven n L hodd hcyc hL1 hL11 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 12` (via `CollatzTwelveCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_twelve`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 12` is
impossible.  Extends `cc_no_nontrivial_cycle_le_eleven` by the `L = 12` case
(`CollatzTwelveCycle.cc_no_nontrivial_twelve_cycle`). -/
theorem cc_no_nontrivial_cycle_le_twelve (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL12 : L ≤ 12)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 12 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_eleven n L hodd hcyc hL1 (by omega) hnontriv
  · have hL12' : L = 12 := by omega
    subst hL12'
    exact CollatzTwelveCycle.cc_no_nontrivial_twelve_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_twelve_trivial`.**

Every odd `cc`-cycle of length `1..12` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_twelve_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL12 : L ≤ 12) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_twelve n L hodd hcyc hL1 hL12 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 13` (via `CollatzThirteenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_thirteen`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 13` is
impossible.  Extends `cc_no_nontrivial_cycle_le_twelve` by the `L = 13` case
(`CollatzThirteenCycle.cc_no_nontrivial_thirteen_cycle`). -/
theorem cc_no_nontrivial_cycle_le_thirteen (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL13 : L ≤ 13)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 13 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_twelve n L hodd hcyc hL1 (by omega) hnontriv
  · have hL13' : L = 13 := by omega
    subst hL13'
    exact CollatzThirteenCycle.cc_no_nontrivial_thirteen_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_thirteen_trivial`.**

Every odd `cc`-cycle of length `1..13` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_thirteen_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL13 : L ≤ 13) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_thirteen n L hodd hcyc hL1 hL13 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 14` (via `CollatzFourteenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_fourteen`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 14` is
impossible.  Extends `cc_no_nontrivial_cycle_le_thirteen` by the `L = 14` case
(`CollatzFourteenCycle.cc_no_nontrivial_fourteen_cycle`, proved via the cheap
element-bound route rather than composition enumeration). -/
theorem cc_no_nontrivial_cycle_le_fourteen (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL14 : L ≤ 14)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 14 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_thirteen n L hodd hcyc hL1 (by omega) hnontriv
  · have hL14' : L = 14 := by omega
    subst hL14'
    exact CollatzFourteenCycle.cc_no_nontrivial_fourteen_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_fourteen_trivial`.**

Every odd `cc`-cycle of length `1..14` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_fourteen_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL14 : L ≤ 14) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_fourteen n L hodd hcyc hL1 hL14 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 15` (via `CollatzFifteenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_fifteen`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 15` is
impossible.  Extends `cc_no_nontrivial_cycle_le_fourteen` by the `L = 15` case
(`CollatzFifteenCycle.cc_no_nontrivial_fifteen_cycle`, proved via the same
cheap element-bound route, generic in `L`, that closed `L = 14`). -/
theorem cc_no_nontrivial_cycle_le_fifteen (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL15 : L ≤ 15)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 15 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_fourteen n L hodd hcyc hL1 (by omega) hnontriv
  · have hL15' : L = 15 := by omega
    subst hL15'
    exact CollatzFifteenCycle.cc_no_nontrivial_fifteen_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_fifteen_trivial`.**

Every odd `cc`-cycle of length `1..15` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_fifteen_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL15 : L ≤ 15) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_fifteen n L hodd hcyc hL1 hL15 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Extension to `L ≤ 16` (via `CollatzSixteenCycle`). -/

/-- **`cc_no_nontrivial_cycle_le_sixteen`.**

For odd `n`, a nontrivial `cc`-cycle `cc^[L] n = n` of any length `1 ≤ L ≤ 16` is
impossible.  Extends `cc_no_nontrivial_cycle_le_fifteen` by the `L = 16` case
(`CollatzSixteenCycle.cc_no_nontrivial_sixteen_cycle`, proved via the same cheap
element-bound route, generic in `L`, that closed `L = 15` — the element-bound
quality is non-monotone in `L`, and `L = 16` happens to be cheaper than `L = 15`). -/
theorem cc_no_nontrivial_cycle_le_sixteen (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL16 : L ≤ 16)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) : False := by
  rcases Nat.lt_or_ge L 16 with hlt | hge
  · exact cc_no_nontrivial_cycle_le_fifteen n L hodd hcyc hL1 (by omega) hnontriv
  · have hL16' : L = 16 := by omega
    subst hL16'
    exact CollatzSixteenCycle.cc_no_nontrivial_sixteen_cycle n hodd hcyc hnontriv

/-- **`cc_cycle_le_sixteen_trivial`.**

Every odd `cc`-cycle of length `1..16` is the trivial fixed point `n = 1`. -/
theorem cc_cycle_le_sixteen_trivial (n L : Nat) (hodd : Odd n)
    (hcyc : cc^[L] n = n) (hL1 : 1 ≤ L) (hL16 : L ≤ 16) : n = 1 := by
  by_cases hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n
  · exact absurd (cc_no_nontrivial_cycle_le_sixteen n L hodd hcyc hL1 hL16 hnt) (by simp)
  · simp only [not_exists, not_and, not_lt] at hnt
    have h0mem : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
    have hle : cc^[0] n ≤ 1 := hnt 0 h0mem
    simp only [Function.iterate_zero, id_eq] at hle
    obtain ⟨k, hk⟩ := hodd
    omega

end CollatzCycleCapstone

#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_eight
#print axioms CollatzCycleCapstone.cc_cycle_le_eight_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_nine
#print axioms CollatzCycleCapstone.cc_cycle_le_nine_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_ten
#print axioms CollatzCycleCapstone.cc_cycle_le_ten_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_eleven
#print axioms CollatzCycleCapstone.cc_cycle_le_eleven_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_twelve
#print axioms CollatzCycleCapstone.cc_cycle_le_twelve_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_thirteen
#print axioms CollatzCycleCapstone.cc_cycle_le_thirteen_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_fourteen
#print axioms CollatzCycleCapstone.cc_cycle_le_fourteen_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_fifteen
#print axioms CollatzCycleCapstone.cc_cycle_le_fifteen_trivial
#print axioms CollatzCycleCapstone.cc_no_nontrivial_cycle_le_sixteen
#print axioms CollatzCycleCapstone.cc_cycle_le_sixteen_trivial
