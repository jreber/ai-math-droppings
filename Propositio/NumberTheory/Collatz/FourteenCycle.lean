import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.CycleTelescope
import Propositio.NumberTheory.Collatz.CycleElementBound
import Propositio.NumberTheory.Collatz.AdmissibleACount

/-!
# No nontrivial `cc`-cycle of length 14

## Method (cheap route, NOT the composition/`steinerVal` enumeration)

`CollatzCycleElementBound.cc_cycle_element_bound_mul` (already proven, axiom-clean)
bounds every element `n` of a hypothetical `cc`-cycle of length `L` in terms of the
total 2-adic valuation `A = S n L`:

    n * (2^A - 3^L) ≤ 2^(A - L) * (3^L - 2^L).

For `L = 14`, the fundamental cycle window `3^14 < 2^A < 4^14`
(`CollatzAdmissibleACount.admissibleA`) pins `A ∈ {23, 24, 25, 26, 27}`, and for
each such `A` the bound formula gives an explicit numeric cap on `n`
(worst case `n ≤ 676` at `A = 23`). So instead of enumerating cycle-length-14
compositions (~20M, previously abandoned as infeasible), we only need: for each
admissible `A`, no odd `n` in a small range (`< 678`, uniformly) satisfies
`cc^[14] n = n`.

The catch: `cc` is built on `padicValNat`, whose mathlib implementation
(`Nat.maxPowDvdDiv`) uses well-founded recursion and does **not** kernel-reduce
under `decide` (confirmed empirically: `decide` gets stuck even on
`padicValNat 2 12 = 2`). This file introduces a **fueled** two-adic valuation
`v2fuel` — plain structural recursion on the fuel argument, so it *does*
kernel-reduce — proves it agrees with `padicValNat 2` whenever the fuel exceeds
the argument's size, and bridges `cc` to a fueled `ccFuel` on the finite range
that matters (`n < 678`, 14 iterations, using the trivial growth bound
`cc m ≤ 3m + 1`). The final finite check is then a single kernel `decide` over
odd `n < 678` on the *fueled*, directly-computable map.

All results are axiom-clean: no `sorry`, no `axiom`, no `native_decide`.
-/

namespace CollatzFourteenCycle

open TerrasDensity (cc)
open CollatzCycleTelescope (S)
local notation "Odd" => TerrasDensity.Odd

/-! ## §1  Fueled two-adic valuation (kernel-`decide`-friendly) -/

/-- Fueled two-adic valuation: strips factors of 2 from `n`, structurally
recursing on the fuel argument (never on `n` itself), so this reduces cleanly
under kernel `decide` — unlike `padicValNat`/`Nat.maxPowDvdDiv`, which use
well-founded recursion and get stuck. -/
def v2fuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then v2fuel fuel (n / 2) + 1 else 0

/-- **Bridge.** `v2fuel fuel w = padicValNat 2 w` whenever the fuel exceeds `w`
(so it never runs out before hitting the odd core). -/
theorem v2fuel_eq (fuel : Nat) :
    ∀ w : Nat, w ≠ 0 → w < 2 ^ fuel → v2fuel fuel w = padicValNat 2 w := by
  induction fuel with
  | zero =>
      intro w hw hbound
      simp only [pow_zero] at hbound
      exact absurd (by omega : w = 0) hw
  | succ fuel ih =>
      intro w hw hbound
      simp only [v2fuel]
      by_cases heven : w % 2 = 0
      · rw [if_pos heven]
        obtain ⟨w', hw'⟩ : ∃ w', w = 2 * w' := ⟨w / 2, by omega⟩
        have hw'nz : w' ≠ 0 := by omega
        have hpow : (2 : Nat) ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
        have hbound' : w' < 2 ^ fuel := by
          rw [hpow] at hbound; omega
        have hwdiv : w / 2 = w' := by omega
        rw [hwdiv, ih w' hw'nz hbound']
        have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
        rw [hw', padicValNat.mul htwo_ne hw'nz, padicValNat_self]
        omega
      · rw [if_neg heven]
        symm
        rw [padicValNat.eq_zero_iff]
        right; right
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        omega

/-! ## §2  Fueled `cc` and its bridge to the real `cc` -/

/-- Fueled `cc`: computes `(3n+1) / 2^(v2fuel fuel (3n+1))`, kernel-`decide`-friendly. -/
def ccFuel (fuel n : Nat) : Nat := (3 * n + 1) / 2 ^ v2fuel fuel (3 * n + 1)

/-- **Bridge.** `ccFuel fuel n = cc n` whenever the fuel exceeds `3n+1`. -/
theorem ccFuel_eq_cc (fuel n : Nat) (hbound : 3 * n + 1 < 2 ^ fuel) :
    ccFuel fuel n = cc n := by
  unfold ccFuel TerrasDensity.cc
  rw [v2fuel_eq fuel (3 * n + 1) (by omega) hbound]

/-! ## §3  Trivial growth bound: `cc` grows by at most a factor of 4 -/

theorem cc_le (m : Nat) : cc m ≤ 3 * m + 1 := by
  unfold TerrasDensity.cc
  exact Nat.div_le_self _ _

theorem cc_succ_bound (m : Nat) : cc m + 1 ≤ 4 * (m + 1) := by
  have h := cc_le m; omega

theorem cc_iter_bound (n : Nat) : ∀ j, cc^[j] n + 1 ≤ 4 ^ j * (n + 1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hstep := cc_succ_bound (cc^[j] n)
      calc cc (cc^[j] n) + 1 ≤ 4 * (cc^[j] n + 1) := hstep
        _ ≤ 4 * (4 ^ j * (n + 1)) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (j + 1) * (n + 1) := by ring

/-! ## §4  Iterated bridge, for `n` bounded and `j ≤ 14` -/

/-- **Fixed point at 1.** `cc 1 = 1`, established via the fueled bridge (`decide`
cannot see this through `padicValNat` directly). -/
theorem cc_one : cc 1 = 1 := by
  rw [← ccFuel_eq_cc 48 1 (by norm_num)]
  decide

theorem cc_iter_one (j : Nat) : cc^[j] 1 = 1 := Function.iterate_fixed cc_one j

/-- Global numeric margin: for any `m` reachable within `4^14 * 678` steps'
worth of growth, `3m+1` is safely under `2^48`, so the fuel-48 bridge applies. -/
theorem hbig_678_48 : ∀ m : Nat, m + 1 ≤ 4 ^ 14 * 678 → 3 * m + 1 < 2 ^ 48 := by
  have hlt : 3 * (4 ^ 14 * 678) + 1 < 2 ^ 48 := by norm_num
  intro m hm
  omega

/-- **Iterated bridge.** For `n < 678` and `j ≤ 14`, the real `cc`-iterate agrees
with the fueled `ccFuel 48`-iterate. -/
theorem cc_iter_eq_ccFuel_iter (n : Nat) (hn : n < 678) :
    ∀ j, j ≤ 14 → cc^[j] n = (ccFuel 48)^[j] n := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hb : cc^[j] n + 1 ≤ 4 ^ 14 * 678 := by
        have hb0 := cc_iter_bound n j
        have hp : (4 : Nat) ^ j ≤ 4 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc cc^[j] n + 1 ≤ 4 ^ j * (n + 1) := hb0
          _ ≤ 4 ^ 14 * (n + 1) := Nat.mul_le_mul_right _ hp
          _ ≤ 4 ^ 14 * 678 := Nat.mul_le_mul_left _ (by omega)
      have hbound : 3 * cc^[j] n + 1 < 2 ^ 48 := hbig_678_48 (cc^[j] n) hb
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ihj,
        ← ccFuel_eq_cc 48 (cc^[j] n) hbound]

/-! ## §5  The finite kernel-`decide` check -/

/-- `check14B` is the decidable Boolean check that no odd `n`, `1 < n < 678`,
is a fixed point of the fueled 14-fold `cc`-iterate. Kernel-`decide`-friendly:
`ccFuel` never invokes well-founded recursion. -/
def check14B : Bool :=
  (List.range 678).all (fun n =>
    if n % 2 = 1 ∧ 1 < n then !decide ((ccFuel 48)^[14] n = n) else true)

set_option maxRecDepth 4000 in
theorem check14B_true : check14B = true := by decide

/-- **Finite exclusion, real `cc`.** No odd `n` with `1 < n < 678` satisfies
`cc^[14] n = n`. -/
theorem cc14_ne_of_range (n : Nat) (hoddmod : n % 2 = 1) (h1 : 1 < n) (h2 : n < 678) :
    cc^[14] n ≠ n := by
  intro heq
  have hmem : n ∈ List.range 678 := List.mem_range.mpr h2
  have hbody := List.all_eq_true.mp check14B_true n hmem
  rw [if_pos ⟨hoddmod, h1⟩] at hbody
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbody
  apply hbody
  rw [← cc_iter_eq_ccFuel_iter n h2 14 (le_refl 14)]
  exact heq

/-! ## §6  Admissible `A` for `L = 14` -/

/-- For `L = 14`, the admissible total valuation `A` is one of `{23,...,27}`
(kernel-`decide`, cheap: only 28 candidates). -/
theorem admissibleA14_eq :
    ∀ A ∈ CollatzAdmissibleACount.admissibleA 14,
      A = 23 ∨ A = 24 ∨ A = 25 ∨ A = 26 ∨ A = 27 := by decide

/-! ## §7  Capstone -/

/-- **No nontrivial `cc`-cycle of length 14.** -/
theorem cc_no_nontrivial_fourteen_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[14] n = n)
    (hnt : ∃ j ∈ Finset.range 14, 1 < cc^[j] n) : False := by
  have h3 : (3 : Nat) ^ 14 < 2 ^ S n 14 :=
    CollatzCycleElementBound.three_pow_lt_of_cycle n 14 hodd (by norm_num) hcyc
  have h4 : (2 : Nat) ^ S n 14 < 4 ^ 14 :=
    CollatzCycleElementBound.pow_lt_four_of_cycle n 14 hodd (by norm_num) hcyc hnt
  have hmemA : S n 14 ∈ CollatzAdmissibleACount.admissibleA 14 :=
    (CollatzAdmissibleACount.mem_admissibleA_iff 14 (S n 14)).mpr ⟨h3, h4⟩
  have hval := admissibleA14_eq (S n 14) hmemA
  have hbound :=
    CollatzCycleElementBound.cc_cycle_element_bound n 14 hodd (by norm_num) hcyc
  have hn678 : n < 678 := by
    rcases hval with hA | hA | hA | hA | hA <;>
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
  exact cc14_ne_of_range n hoddmod h1lt hn678 hcyc

#print axioms cc_no_nontrivial_fourteen_cycle

end CollatzFourteenCycle
