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
# No nontrivial `cc`-cycle of length 16

## Method (cheap route, extending `CollatzFifteenCycle`)

This file is the `L = 16` rung of the same element-bound route used for
`L = 14` (`CollatzFourteenCycle`) and `L = 15` (`CollatzFifteenCycle`):
`CollatzCycleElementBound.cc_cycle_element_bound_mul` is **already generic in
`L`**, so no new element-bound mathematics is needed.

For `L = 16`, the fundamental cycle window `3^16 < 2^A < 4^16`
(`CollatzAdmissibleACount.admissibleA`) pins `A ∈ {26, 27, 28, 29, 30, 31}`
(check: `3^16 = 43046721`, `2^25 = 33554432 < 3^16 < 2^26 = 67108864`, and
`4^16 = 2^32`), and for each such `A` the element-bound formula gives an explicit
numeric cap on `n`:

  * `A = 26`: `n ≤ 1829`   (worst case)
  * `A = 27`: `n ≤ 965`
  * `A = 28`: `n ≤ 781`
  * `A = 29`: `n ≤ 713`
  * `A = 30`: `n ≤ 683`
  * `A = 31`: `n ≤ 669`

Notably the worst-case bound `1829` is **smaller** than the `L = 15` worst case
(`3018`): the element-bound quality is governed by the Diophantine quality of
`A − L` versus `2^A − 3^L`, which is non-monotone in `L`, and `L = 16` happens to
be a cheaper rung than `L = 15`. So instead of enumerating cycle-length-16
compositions (previously assumed to be ~4× the L=15 cost), we only need: for each
admissible `A`, no odd `n` in a small range (`< 1830`, uniformly) satisfies
`cc^[16] n = n`.

We reuse the fueled two-adic valuation `v2fuel`/`ccFuel` and the generic growth
bound (`cc_iter_bound`) from `CollatzFourteenCycle` verbatim (both are already
stated generically in the iteration count) and only re-derive the `L = 16`-specific
numeric bridge (fuel margin for `n < 1830`, 16 iterations) and the final finite
kernel-`decide` check.

All results are axiom-clean: no `sorry`, no `axiom`, no `native_decide`.
-/

namespace CollatzSixteenCycle

open TerrasDensity (cc)
open CollatzCycleTelescope (S)
open CollatzFourteenCycle (v2fuel ccFuel ccFuel_eq_cc cc_iter_bound cc_iter_one)
local notation "Odd" => TerrasDensity.Odd

/-! ## §1  Numeric margin: fuel 48 is enough for `n < 1830`, 16 iterations -/

/-- Global numeric margin: for any `m` reachable within `4^16 * 1830` steps'
worth of growth, `3m+1` is safely under `2^48`, so the fuel-48 bridge
(`CollatzFourteenCycle.ccFuel_eq_cc`) applies. -/
theorem hbig_1830_48 : ∀ m : Nat, m + 1 ≤ 4 ^ 16 * 1830 → 3 * m + 1 < 2 ^ 48 := by
  have hlt : 3 * (4 ^ 16 * 1830) + 1 < 2 ^ 48 := by norm_num
  intro m hm
  omega

/-- **Iterated bridge.** For `n < 1830` and `j ≤ 16`, the real `cc`-iterate
agrees with the fueled `ccFuel 48`-iterate. -/
theorem cc_iter_eq_ccFuel_iter (n : Nat) (hn : n < 1830) :
    ∀ j, j ≤ 16 → cc^[j] n = (ccFuel 48)^[j] n := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hb : cc^[j] n + 1 ≤ 4 ^ 16 * 1830 := by
        have hb0 := cc_iter_bound n j
        have hp : (4 : Nat) ^ j ≤ 4 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc cc^[j] n + 1 ≤ 4 ^ j * (n + 1) := hb0
          _ ≤ 4 ^ 16 * (n + 1) := Nat.mul_le_mul_right _ hp
          _ ≤ 4 ^ 16 * 1830 := Nat.mul_le_mul_left _ (by omega)
      have hbound : 3 * cc^[j] n + 1 < 2 ^ 48 := hbig_1830_48 (cc^[j] n) hb
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ihj,
        ← ccFuel_eq_cc 48 (cc^[j] n) hbound]

/-! ## §2  The finite kernel-`decide` check -/

/-- `check16B` is the decidable Boolean check that no odd `n`, `1 < n < 1830`,
is a fixed point of the fueled 16-fold `cc`-iterate. Kernel-`decide`-friendly:
`ccFuel` never invokes well-founded recursion. -/
def check16B : Bool :=
  (List.range 1830).all (fun n =>
    if n % 2 = 1 ∧ 1 < n then !decide ((ccFuel 48)^[16] n = n) else true)

set_option maxRecDepth 20000 in
theorem check16B_true : check16B = true := by decide

/-- **Finite exclusion, real `cc`.** No odd `n` with `1 < n < 1830` satisfies
`cc^[16] n = n`. -/
theorem cc16_ne_of_range (n : Nat) (hoddmod : n % 2 = 1) (h1 : 1 < n) (h2 : n < 1830) :
    cc^[16] n ≠ n := by
  intro heq
  have hmem : n ∈ List.range 1830 := List.mem_range.mpr h2
  have hbody := List.all_eq_true.mp check16B_true n hmem
  rw [if_pos ⟨hoddmod, h1⟩] at hbody
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbody
  apply hbody
  rw [← cc_iter_eq_ccFuel_iter n h2 16 (le_refl 16)]
  exact heq

/-! ## §3  Admissible `A` for `L = 16` -/

/-- For `L = 16`, the admissible total valuation `A` is one of `{26,...,31}`
(kernel-`decide`, cheap: only 32 candidates). -/
theorem admissibleA16_eq :
    ∀ A ∈ CollatzAdmissibleACount.admissibleA 16,
      A = 26 ∨ A = 27 ∨ A = 28 ∨ A = 29 ∨ A = 30 ∨ A = 31 := by decide

/-! ## §4  Capstone -/

/-- **No nontrivial `cc`-cycle of length 16.** -/
theorem cc_no_nontrivial_sixteen_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[16] n = n)
    (hnt : ∃ j ∈ Finset.range 16, 1 < cc^[j] n) : False := by
  have h3 : (3 : Nat) ^ 16 < 2 ^ S n 16 :=
    CollatzCycleElementBound.three_pow_lt_of_cycle n 16 hodd (by norm_num) hcyc
  have h4 : (2 : Nat) ^ S n 16 < 4 ^ 16 :=
    CollatzCycleElementBound.pow_lt_four_of_cycle n 16 hodd (by norm_num) hcyc hnt
  have hmemA : S n 16 ∈ CollatzAdmissibleACount.admissibleA 16 :=
    (CollatzAdmissibleACount.mem_admissibleA_iff 16 (S n 16)).mpr ⟨h3, h4⟩
  have hval := admissibleA16_eq (S n 16) hmemA
  have hbound :=
    CollatzCycleElementBound.cc_cycle_element_bound n 16 hodd (by norm_num) hcyc
  have hn1830 : n < 1830 := by
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
  exact cc16_ne_of_range n hoddmod h1lt hn1830 hcyc

#print axioms cc_no_nontrivial_sixteen_cycle

end CollatzSixteenCycle
