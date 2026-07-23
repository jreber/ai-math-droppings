import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.CycleTelescope
import Propositio.NumberTheory.Collatz.CycleElementBound
import Propositio.NumberTheory.Collatz.AdmissibleACount
import Propositio.NumberTheory.Collatz.FourteenCycle

/-!
# No nontrivial `cc`-cycle of length 15

## Method (cheap route, extending `CollatzFourteenCycle`)

This file is the `L = 15` rung of the same element-bound route used for `L = 14`
(`CollatzFourteenCycle`): `CollatzCycleElementBound.cc_cycle_element_bound_mul`
is **already generic in `L`**, so no new element-bound mathematics is needed.

For `L = 15`, the fundamental cycle window `3^15 < 2^A < 4^15`
(`CollatzAdmissibleACount.admissibleA`) pins `A ∈ {24, 25, 26, 27, 28, 29}`
(check: `3^15 = 14348907 < 2^24 = 16777216`, and `4^15 = 2^30`), and for each
such `A` the element-bound formula gives an explicit numeric cap on `n`
(worst case `n ≤ 3018` at `A = 24`). So instead of enumerating cycle-length-15
compositions (~76M, previously abandoned as impractical), we only need: for
each admissible `A`, no odd `n` in a small range (`< 3020`, uniformly)
satisfies `cc^[15] n = n`.

We reuse the fueled two-adic valuation `v2fuel`/`ccFuel` and the generic growth
bound (`cc_iter_bound`) from `CollatzFourteenCycle` verbatim (both are already
stated generically in the iteration count, so no re-proof is needed there
either) and only re-derive the `L = 15`-specific numeric bridge (fuel margin
for `n < 3020`, 15 iterations) and the final finite kernel-`decide` check.

All results are axiom-clean: no `sorry`, no `axiom`, no `native_decide`.
-/

namespace CollatzFifteenCycle

open TerrasDensity (cc)
open CollatzCycleTelescope (S)
open CollatzFourteenCycle (v2fuel ccFuel ccFuel_eq_cc cc_iter_bound cc_iter_one)
local notation "Odd" => TerrasDensity.Odd

/-! ## §1  Numeric margin: fuel 48 is enough for `n < 3020`, 15 iterations -/

/-- Global numeric margin: for any `m` reachable within `4^15 * 3020` steps'
worth of growth, `3m+1` is safely under `2^48`, so the fuel-48 bridge
(`CollatzFourteenCycle.ccFuel_eq_cc`) applies. -/
theorem hbig_3020_48 : ∀ m : Nat, m + 1 ≤ 4 ^ 15 * 3020 → 3 * m + 1 < 2 ^ 48 := by
  have hlt : 3 * (4 ^ 15 * 3020) + 1 < 2 ^ 48 := by norm_num
  intro m hm
  omega

/-- **Iterated bridge.** For `n < 3020` and `j ≤ 15`, the real `cc`-iterate
agrees with the fueled `ccFuel 48`-iterate. -/
theorem cc_iter_eq_ccFuel_iter (n : Nat) (hn : n < 3020) :
    ∀ j, j ≤ 15 → cc^[j] n = (ccFuel 48)^[j] n := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hb : cc^[j] n + 1 ≤ 4 ^ 15 * 3020 := by
        have hb0 := cc_iter_bound n j
        have hp : (4 : Nat) ^ j ≤ 4 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc cc^[j] n + 1 ≤ 4 ^ j * (n + 1) := hb0
          _ ≤ 4 ^ 15 * (n + 1) := Nat.mul_le_mul_right _ hp
          _ ≤ 4 ^ 15 * 3020 := Nat.mul_le_mul_left _ (by omega)
      have hbound : 3 * cc^[j] n + 1 < 2 ^ 48 := hbig_3020_48 (cc^[j] n) hb
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ihj,
        ← ccFuel_eq_cc 48 (cc^[j] n) hbound]

/-! ## §2  The finite kernel-`decide` check -/

/-- `check15B` is the decidable Boolean check that no odd `n`, `1 < n < 3020`,
is a fixed point of the fueled 15-fold `cc`-iterate. Kernel-`decide`-friendly:
`ccFuel` never invokes well-founded recursion. -/
def check15B : Bool :=
  (List.range 3020).all (fun n =>
    if n % 2 = 1 ∧ 1 < n then !decide ((ccFuel 48)^[15] n = n) else true)

set_option maxRecDepth 20000 in
theorem check15B_true : check15B = true := by decide

/-- **Finite exclusion, real `cc`.** No odd `n` with `1 < n < 3020` satisfies
`cc^[15] n = n`. -/
theorem cc15_ne_of_range (n : Nat) (hoddmod : n % 2 = 1) (h1 : 1 < n) (h2 : n < 3020) :
    cc^[15] n ≠ n := by
  intro heq
  have hmem : n ∈ List.range 3020 := List.mem_range.mpr h2
  have hbody := List.all_eq_true.mp check15B_true n hmem
  rw [if_pos ⟨hoddmod, h1⟩] at hbody
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbody
  apply hbody
  rw [← cc_iter_eq_ccFuel_iter n h2 15 (le_refl 15)]
  exact heq

/-! ## §3  Admissible `A` for `L = 15` -/

/-- For `L = 15`, the admissible total valuation `A` is one of `{24,...,29}`
(kernel-`decide`, cheap: only 30 candidates). -/
theorem admissibleA15_eq :
    ∀ A ∈ CollatzAdmissibleACount.admissibleA 15,
      A = 24 ∨ A = 25 ∨ A = 26 ∨ A = 27 ∨ A = 28 ∨ A = 29 := by decide

/-! ## §4  Capstone -/

/-- **No nontrivial `cc`-cycle of length 15.** -/
theorem cc_no_nontrivial_fifteen_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[15] n = n)
    (hnt : ∃ j ∈ Finset.range 15, 1 < cc^[j] n) : False := by
  have h3 : (3 : Nat) ^ 15 < 2 ^ S n 15 :=
    CollatzCycleElementBound.three_pow_lt_of_cycle n 15 hodd (by norm_num) hcyc
  have h4 : (2 : Nat) ^ S n 15 < 4 ^ 15 :=
    CollatzCycleElementBound.pow_lt_four_of_cycle n 15 hodd (by norm_num) hcyc hnt
  have hmemA : S n 15 ∈ CollatzAdmissibleACount.admissibleA 15 :=
    (CollatzAdmissibleACount.mem_admissibleA_iff 15 (S n 15)).mpr ⟨h3, h4⟩
  have hval := admissibleA15_eq (S n 15) hmemA
  have hbound :=
    CollatzCycleElementBound.cc_cycle_element_bound n 15 hodd (by norm_num) hcyc
  have hn3020 : n < 3020 := by
    rcases hval with hA | hA | hA | hA | hA | hA <;>
      · rw [hA] at hbound; norm_num at hbound; omega
  -- Exclude the trivial cycle `n = 1` using `hnt`.
  obtain ⟨k, hk⟩ := hodd
  have hoddmod : n % 2 = 1 := by omega
  have hne1 : n ≠ 1 := by
    intro hn1
    obtain ⟨j, _hjr, hj1⟩ := hnt
    rw [hn1, cc_iter_one] at hj1
    omega
  have h1lt : 1 < n := by omega
  exact cc15_ne_of_range n hoddmod h1lt hn3020 hcyc

#print axioms cc_no_nontrivial_fifteen_cycle

end CollatzFifteenCycle
