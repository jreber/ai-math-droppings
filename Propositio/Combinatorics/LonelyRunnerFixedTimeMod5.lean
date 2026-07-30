/-
# Lonely Runner: Fixed time t = 1/5 for all speeds not divisible by 5

**Conjecture conj-2026-07-29-008:** For any nonzero integer speed v such that 5 does NOT
divide v, the fixed time t = 1/5 gives nid(v · 1/5) ≥ 1/5.

**Proof:** For v ≢ 0 (mod 5), we have v % 5 ∈ {1, 2, 3, 4}. The general residue lemma
nid_ge_of_residue from LonelyRunnerSmallK (which gives nid ≥ 1/3) applies to residues 2,3.
For residues 1,4, we give direct proofs.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerSmallK

namespace LonelyRunnerFixedTimeMod5

/-- For residue 2: nid ≥ 1/5 (via 1/3 from the general lemma). -/
lemma nid_residue_two (v : ℤ) (h_mod : v % 5 = 2) :
    (1 : ℝ) / 5 ≤ LonelyRunnerSmallK.nid ((v : ℝ) / 5) := by
  have h1 : (5 : ℝ) ≤ 3 * (2 : ℝ) := by norm_num
  have h2 : 3 * (2 : ℝ) ≤ 2 * (5 : ℝ) := by norm_num
  have := LonelyRunnerSmallK.nid_ge_of_residue v 5 (by norm_num) 2 h_mod h1 h2
  linarith

/-- For residue 3: nid ≥ 1/5 (via 1/3 from the general lemma). -/
lemma nid_residue_three (v : ℤ) (h_mod : v % 5 = 3) :
    (1 : ℝ) / 5 ≤ LonelyRunnerSmallK.nid ((v : ℝ) / 5) := by
  have h1 : (5 : ℝ) ≤ 3 * (3 : ℝ) := by norm_num
  have h2 : 3 * (3 : ℝ) ≤ 2 * (5 : ℝ) := by norm_num
  have := LonelyRunnerSmallK.nid_ge_of_residue v 5 (by norm_num) 3 h_mod h1 h2
  linarith

/-- For residue 1: direct proof that nid(v/5) = 1/5. -/
lemma nid_residue_one (v : ℤ) (h_mod : v % 5 = 1) :
    (1 : ℝ) / 5 ≤ LonelyRunnerSmallK.nid ((v : ℝ) / 5) := by
  -- v ≡ 1 (mod 5) means v = 5k + 1 for some k
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v = 5 * k + 1 := ⟨(v - 1) / 5, by omega⟩
  rw [hk]
  push_cast
  ring_nf
  -- Now: 1 / 5 ≤ nid (1 / 5 + k)
  -- fract(1/5 + k) = fract(1/5) by peeling off integer part k
  rw [LonelyRunnerSmallK.nid_eq]
  have fract_eq : Int.fract ((1 : ℝ) / 5 + ↑k) = Int.fract ((1 : ℝ) / 5) := by
    have : (1 : ℝ) / 5 + ↑k = ↑k + (1 : ℝ) / 5 := by ring
    simp [this]
  rw [fract_eq]
  -- Int.fract(1/5) = 1/5 and nid = min(1/5, 4/5) = 1/5
  norm_num [Int.fract]

/-- For residue 4: direct proof that nid(v/5) = 1/5. -/
lemma nid_residue_four (v : ℤ) (h_mod : v % 5 = 4) :
    (1 : ℝ) / 5 ≤ LonelyRunnerSmallK.nid ((v : ℝ) / 5) := by
  -- v ≡ 4 (mod 5) means v = 5k + 4 for some k
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v = 5 * k + 4 := ⟨(v - 4) / 5, by omega⟩
  rw [hk]
  push_cast
  ring_nf
  -- Now: 1 / 5 ≤ nid (4 / 5 + k)
  -- fract(4/5 + k) = fract(4/5) by peeling off integer part k
  rw [LonelyRunnerSmallK.nid_eq]
  have fract_eq : Int.fract ((4 : ℝ) / 5 + ↑k) = Int.fract ((4 : ℝ) / 5) := by
    have : (4 : ℝ) / 5 + ↑k = ↑k + (4 : ℝ) / 5 := by ring
    simp [this]
  rw [fract_eq]
  -- Int.fract(4/5) = 4/5 and nid = min(4/5, 1/5) = 1/5
  norm_num [Int.fract]

/-- Main theorem: nid(v/5) ≥ 1/5 for all v ≢ 0 (mod 5). -/
theorem nid_fifth_time (v : ℤ) (hv : v ≠ 0) (hdiv : ¬(5 ∣ v)) :
    (1 : ℝ) / 5 ≤ LonelyRunnerSmallK.nid ((v : ℝ) * (1 / 5)) := by
  have eq : (v : ℝ) * (1 / 5) = (v : ℝ) / 5 := by ring
  rw [eq]
  have hmod : v % 5 ≠ 0 := by
    intro h_eq_zero
    exact hdiv (Int.dvd_of_emod_eq_zero h_eq_zero)
  have h1 : 0 ≤ v % 5 := Int.emod_nonneg v (by norm_num)
  have h2 : v % 5 < 5 := Int.emod_lt_of_pos v (by norm_num)
  have : v % 5 = 1 ∨ v % 5 = 2 ∨ v % 5 = 3 ∨ v % 5 = 4 := by omega
  rcases this with h | h | h | h
  · exact nid_residue_one v h
  · exact nid_residue_two v h
  · exact nid_residue_three v h
  · exact nid_residue_four v h

end LonelyRunnerFixedTimeMod5
