import Mathlib.Tactic

/-!
# A machine-checked Collatz convergence certificate for small `n`

The corpus attacks Collatz two ways: *cycle exclusion* (`CollatzNineCycle` etc. — no
nontrivial cycle of length `≤ 9`) and *density* (`TerrasDensity`, `CollatzAlmostAllDescend`
— almost all `n` descend). This file adds the third, most literal flavor: a **kernel-checked
exhaustive verification** that every `n` in an explicit range reaches `1` under the
standard Collatz map, by a single `decide` (no `native_decide`).

It uses the **standard** Collatz map `T n = n/2` (`n` even) `= 3n+1` (`n` odd) rather than
the corpus's 2-adically-compressed `cc`, precisely because `T` is directly
kernel-reducible — `cc` routes through `padicValNat`, which the kernel `decide` cannot
evaluate. The statement `T^[k] n = 1` is the standard form of "the Collatz trajectory of
`n` reaches `1`".

## Result

> **`collatz_reaches_one_le_100`** : for every `1 ≤ n ≤ 100` there is `k ≤ 130` with
> `T^[k] n = 1`.

discharged from `allReachT 100 130 = true` (`reachesOneT`, a single-pass fuel checker)
via the bridge `reachesOneT_iff`. The kernel `decide` runs ≈6 s / ≈3.6 GB — build through
`scripts/safe-lean.sh`.

## Honesty about the bound

A *method demonstration*, not a record: Collatz is computationally verified to about
`2⁶⁸`. The value here is a fully kernel-checked, axiom-clean certificate
(`[propext, Classical.choice, Quot.sound]`, no `native_decide`/`ofReduceBool`) and the
reusable `allReachT` / `reachesOneT_iff` pair — a larger range is just a bigger `decide`
(cost grows like `N · K`).

Typecheck/​build with `scripts/safe-lean.sh --build CollatzConvergence`.
-/

namespace CollatzConvergence

/-- The standard Collatz map: `n/2` if `n` is even, `3n+1` if odd. -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Single-pass fuel checker: `true` iff `n` reaches `1` within `fuel` applications of `T`. -/
def reachesOneT (n fuel : Nat) : Bool :=
  match fuel with
  | 0 => n == 1
  | f + 1 => n == 1 || reachesOneT (T n) f

/-- `true` iff every `1 ≤ n ≤ N` reaches `1` within `K` Collatz steps. -/
def allReachT (N K : Nat) : Bool :=
  (List.range (N + 1)).all (fun n => if 1 ≤ n then reachesOneT n K else true)

/-- **Bridge.** `reachesOneT n fuel = true` iff the trajectory of `n` hits `1` within
`fuel` steps, i.e. `∃ k ≤ fuel, T^[k] n = 1`. Induction on `fuel`, using
`Function.iterate_succ_apply : T^[k+1] n = T^[k] (T n)`. -/
theorem reachesOneT_iff (n fuel : Nat) :
    reachesOneT n fuel = true ↔ ∃ k ≤ fuel, T^[k] n = 1 := by
  induction fuel generalizing n with
  | zero =>
    simp only [reachesOneT, beq_iff_eq]
    constructor
    · intro h; exact ⟨0, le_refl 0, by simpa using h⟩
    · rintro ⟨k, hk, hk1⟩
      interval_cases k; simpa using hk1
  | succ f ih =>
    simp only [reachesOneT, Bool.or_eq_true, beq_iff_eq]
    rw [ih (T n)]
    constructor
    · rintro (rfl | ⟨k, hk, hk1⟩)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · exact ⟨k + 1, Nat.succ_le_succ hk, by rw [Function.iterate_succ_apply]; exact hk1⟩
    · rintro ⟨k, hk, hk1⟩
      cases k with
      | zero => left; simpa using hk1
      | succ j =>
        right
        exact ⟨j, Nat.le_of_succ_le_succ hk, by rw [Function.iterate_succ_apply] at hk1; exact hk1⟩

/-- The `N = 100`, `K = 130` certificate value (kernel `decide`). -/
theorem allReachT_hundred : allReachT 100 130 = true := by decide

/-- **Every `1 ≤ n ≤ 100` reaches `1` under the Collatz map within `130` steps.**
Machine-checked exhaustive verification (`allReachT_hundred`) bridged through
`reachesOneT_iff`. -/
theorem collatz_reaches_one_le_100 {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 100) :
    ∃ k ≤ 130, T^[k] n = 1 := by
  have hm : n ∈ List.range 101 := List.mem_range.mpr (by omega)
  have hb := List.all_eq_true.mp allReachT_hundred n hm
  rw [if_pos h1] at hb
  exact (reachesOneT_iff n 130).mp hb

#print axioms reachesOneT_iff
#print axioms collatz_reaches_one_le_100

end CollatzConvergence
