import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Propositio.Collatz.Basic
import Propositio.Collatz.CascadeCycles
import Propositio.Collatz.CycleTelescope
import Propositio.Collatz.CycleDecide

/-!
# Simons–de Weger-style element bound for nontrivial cc-cycles

## Purpose

For a `cc`-cycle of length `L` through an odd `n` (so `cc^[L] n = n`), with
total 2-adic valuation `A = S n L = Σ_{i<L} v₂(3·cc^[i] n + 1)`, the telescoped
cycle equation (`CollatzCycleTelescope.cycle_telescope_identity`) reads

    n · (2^A − 3^L) = Steiner n L,       Steiner n L = Σ_{i<L} 3^{L−1−i} · 2^{S n i}.

This file adds the **explicit element bound**: since every per-step valuation is
`≥ 1` (oddness), the partial sums satisfy `S n i ≤ A − (L − i)`, whence

    Steiner n L ≤ 2^{A−L} · (3^L − 2^L)          (sharp: geometric-sum bound)

and therefore every element `n` of the cycle satisfies

    n · (2^A − 3^L) ≤ 2^{A−L} · (3^L − 2^L),
    n ≤ 2^{A−L} · (3^L − 2^L) / (2^A − 3^L)      (Nat division, exact form).

Combined with the fundamental cycle constraint `3^L < 2^A < 4^L`
(`CollatzCascadeCycles.cc_cycle_constraint`), which pins `A ≤ 2L − 1`, this
gives the fully explicit absolute bound

    n < 6^L        (every element of a nontrivial L-cycle),

so testing cycle length `L` reduces to a finite search over odd `n < 6^L`
(`cc_cycle_length_finite_test`).

## Method

The key inductive inequality is proved in the subtraction-free form

    Steiner n L · 2^L + 2^(S n L + L) ≤ 3^L · 2^(S n L)      (`steiner_key_bound`)

whose inductive step is pure semiring arithmetic (`step_arith`): with
`st·p2 + s·p2 ≤ p3·s`, `p2 ≤ p3`, `1 ≤ g`,

    (3·st + s)·2p2 + 2s·g·2p2 ≤ 3p3·2sg.

All results are axiom-clean: no `sorry`, no `axiom`, no `native_decide`.

## Honest caveat

This bounds the elements of a hypothetical nontrivial cycle of a FIXED length
`L`; it does not by itself exclude any cycle length (that is the ladder
`CollatzCycleUniform` / Simons–de Weger territory). Its value is that the
finite search implied by `cc_cycle_length_finite_test` is now an explicitly
bounded statement composable with the existing L ≤ 13 exclusion ladder.
-/

namespace CollatzCycleElementBound

open TerrasDensity (cc)
open CollatzCycleTelescope (S Steiner S_zero S_succ Steiner_zero Steiner_succ
     cycle_telescope_identity)
open CollatzCycleDecide (iterate_odd one_le_v2_three_mul_add_one)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## §1  Bridges to the cascade-cycle constraints -/

/-- Bridge: `3^L < 2^(S n L)` for an odd `L`-cycle (`L ≥ 1`), restating
`CollatzCascadeCycles.cc_cycle_three_pow_lt` through the `S` abbreviation. -/
theorem three_pow_lt_of_cycle (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) : 3 ^ L < 2 ^ S n L := by
  have h := CollatzCascadeCycles.cc_cycle_three_pow_lt n L hodd hcyc hL
  simpa only [S] using h

/-- Bridge: `2^(S n L) < 4^L` for a nontrivial odd `L`-cycle, restating
`CollatzCascadeCycles.cc_cycle_pow_lt_four` through the `S` abbreviation. -/
theorem pow_lt_four_of_cycle (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    2 ^ S n L < 4 ^ L := by
  have h := CollatzCascadeCycles.cc_cycle_pow_lt_four n L hodd hcyc hL hnt
  simpa only [S] using h

/-! ## §2  Lower bound on the total valuation -/

/-- For odd `n`, the total valuation over `L` steps is at least `L`
(each per-step valuation is `≥ 1`). -/
theorem le_S (n L : Nat) (hodd : Odd n) : L ≤ S n L := by
  have h : ∀ j ∈ Finset.range L, 1 ≤ padicValNat 2 (3 * cc^[j] n + 1) :=
    fun j _ => one_le_v2_three_mul_add_one (iterate_odd n hodd j)
  have hsum := Finset.sum_le_sum h
  simpa [S] using hsum

/-! ## §3  The key Steiner-sum bound -/

/-- Pure-arithmetic inductive step for `steiner_key_bound`: a semiring
inequality in five natural variables, proved by an explicit `calc`. -/
private theorem step_arith (st s p2 p3 g : Nat) (hg : 1 ≤ g) (hp : p2 ≤ p3)
    (hih : st * p2 + s * p2 ≤ p3 * s) :
    (3 * st + s) * (p2 * 2) + s * g * 2 * (p2 * 2) ≤ p3 * 3 * (s * (g * 2)) := by
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 1 := ⟨g - 1, by omega⟩
  calc (3 * st + s) * (p2 * 2) + s * (h + 1) * 2 * (p2 * 2)
      = 6 * (st * p2 + s * p2) + 4 * (s * h * p2) := by ring
    _ ≤ 6 * (p3 * s) + 4 * (s * h * p3) :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.le_refl 6) hih)
          (Nat.mul_le_mul (Nat.le_refl 4) (Nat.mul_le_mul (Nat.le_refl (s * h)) hp))
    _ ≤ 6 * (p3 * s) + 6 * (s * h * p3) :=
        Nat.add_le_add_left (Nat.mul_le_mul (by norm_num) (Nat.le_refl (s * h * p3))) _
    _ = p3 * 3 * (s * ((h + 1) * 2)) := by ring

/-- **Key Steiner bound (subtraction-free form).** For odd `n` and every `L`:

    Steiner n L · 2^L + 2^(S n L + L) ≤ 3^L · 2^(S n L).

Equivalently `Steiner n L ≤ 2^{A−L}·(3^L − 2^L)` with `A = S n L`: the Steiner
sum is dominated by the geometric sum with every remaining halving spent as
late as possible. The only arithmetic input is that each per-step valuation is
`≥ 1` for odd starting values. -/
theorem steiner_key_bound (n : Nat) (hodd : Odd n) (L : Nat) :
    Steiner n L * 2 ^ L + 2 ^ (S n L + L) ≤ 3 ^ L * 2 ^ S n L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have ha : 1 ≤ padicValNat 2 (3 * cc^[L] n + 1) :=
      one_le_v2_three_mul_add_one (iterate_odd n hodd L)
    rw [Steiner_succ, S_succ]
    rw [pow_add] at ih
    obtain ⟨b, hb⟩ : ∃ b, padicValNat 2 (3 * cc^[L] n + 1) = b + 1 :=
      ⟨padicValNat 2 (3 * cc^[L] n + 1) - 1, by omega⟩
    rw [hb]
    have hp : (2 : Nat) ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by norm_num) L
    have hL1 : (3 * Steiner n L + 2 ^ S n L) * 2 ^ (L + 1)
          + 2 ^ (S n L + (b + 1) + (L + 1))
        = (3 * Steiner n L + 2 ^ S n L) * (2 ^ L * 2)
          + 2 ^ S n L * 2 ^ b * 2 * (2 ^ L * 2) := by ring
    have hR1 : (3 : Nat) ^ (L + 1) * 2 ^ (S n L + (b + 1))
        = 3 ^ L * 3 * (2 ^ S n L * (2 ^ b * 2)) := by ring
    rw [hL1, hR1]
    exact step_arith (Steiner n L) (2 ^ S n L) (2 ^ L) (3 ^ L) (2 ^ b)
      Nat.one_le_two_pow hp ih

/-- Subtracted form of the key bound:
`Steiner n L · 2^L ≤ (3^L − 2^L) · 2^(S n L)`. -/
theorem steiner_le (n : Nat) (hodd : Odd n) (L : Nat) :
    Steiner n L * 2 ^ L ≤ (3 ^ L - 2 ^ L) * 2 ^ S n L := by
  have hkey := steiner_key_bound n hodd L
  calc Steiner n L * 2 ^ L
      ≤ 3 ^ L * 2 ^ S n L - 2 ^ (S n L + L) := Nat.le_sub_of_add_le hkey
    _ = (3 ^ L - 2 ^ L) * 2 ^ S n L := by
        rw [Nat.sub_mul, pow_add, mul_comm (2 ^ S n L) (2 ^ L)]

/-! ## §4  The exact cycle equation and the element bound -/

/-- **Exact cycle equation.** For an odd `L`-cycle (`L ≥ 1`) through `n`:

    n · (2^(S n L) − 3^L) = Steiner n L.

This is `cycle_telescope_identity` rearranged over `Nat` (the subtraction is
genuine since `3^L < 2^(S n L)`). -/
theorem cc_cycle_element_equation (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) :
    n * (2 ^ S n L - 3 ^ L) = Steiner n L := by
  have hid := cycle_telescope_identity n hodd L hL hcyc
  have h1 : n * (2 ^ S n L - 3 ^ L) = 2 ^ S n L * n - 3 ^ L * n := by
    rw [mul_comm, Nat.sub_mul]
  rw [h1, hid]
  exact Nat.add_sub_cancel_left _ _

/-- **Element bound (product form) — the main theorem.**

Every element `n` of an odd `cc`-cycle of length `L ≥ 1`, with total valuation
`A = S n L`, satisfies

    n · (2^A − 3^L) ≤ 2^(A − L) · (3^L − 2^L).

This is the Simons–de Weger-style bound: the cycle equation forces
`n = Steiner/(2^A − 3^L)`, and the Steiner sum is at most
`2^{A−L}·(3^L − 2^L)`. -/
theorem cc_cycle_element_bound_mul (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) :
    n * (2 ^ S n L - 3 ^ L) ≤ 2 ^ (S n L - L) * (3 ^ L - 2 ^ L) := by
  have heq := cc_cycle_element_equation n L hodd hL hcyc
  have hst := steiner_le n hodd L
  have hAL : L ≤ S n L := le_S n L hodd
  have hsplit : (2 : Nat) ^ (S n L - L) * 2 ^ L = 2 ^ S n L := by
    rw [← pow_add]
    congr 1
    omega
  have hmulL : n * (2 ^ S n L - 3 ^ L) * 2 ^ L
      ≤ 2 ^ (S n L - L) * (3 ^ L - 2 ^ L) * 2 ^ L := by
    calc n * (2 ^ S n L - 3 ^ L) * 2 ^ L
        = Steiner n L * 2 ^ L := by rw [heq]
      _ ≤ (3 ^ L - 2 ^ L) * 2 ^ S n L := hst
      _ = 2 ^ (S n L - L) * (3 ^ L - 2 ^ L) * 2 ^ L := by
          rw [mul_comm (2 ^ (S n L - L)) (3 ^ L - 2 ^ L), mul_assoc, hsplit]
  exact Nat.le_of_mul_le_mul_right hmulL (Nat.two_pow_pos L)

/-- **Element bound (division form).**

    n ≤ 2^(A − L) · (3^L − 2^L) / (2^A − 3^L),      A = S n L,

with exact `Nat` division (the divisor is positive since `3^L < 2^A`). -/
theorem cc_cycle_element_bound (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) :
    n ≤ 2 ^ (S n L - L) * (3 ^ L - 2 ^ L) / (2 ^ S n L - 3 ^ L) := by
  have hlt := three_pow_lt_of_cycle n L hodd hL hcyc
  have hd : 0 < 2 ^ S n L - 3 ^ L := by omega
  rw [Nat.le_div_iff_mul_le hd]
  exact cc_cycle_element_bound_mul n L hodd hL hcyc

/-! ## §5  Absolute bound and finite-search corollary -/

/-- **Absolute element bound.** Every element of a **nontrivial** odd
`cc`-cycle of length `L ≥ 1` is `< 6^L`: the constraint `2^A < 4^L` pins
`A − L ≤ L − 1`, so `n ≤ 2^{L−1}·(3^L − 2^L) < 2^L·3^L = 6^L`. -/
theorem cc_cycle_element_lt_six_pow (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hnt : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    n < 6 ^ L := by
  have hmul := cc_cycle_element_bound_mul n L hodd hL hcyc
  have hlt := three_pow_lt_of_cycle n L hodd hL hcyc
  have h4 := pow_lt_four_of_cycle n L hodd hL hcyc hnt
  -- A < 2L from 2^A < 4^L = 2^(2L).
  have h4L : (4 : Nat) ^ L = 2 ^ (2 * L) := by
    rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]
  have hA2 : S n L < 2 * L := by
    by_contra hge
    rw [not_lt] at hge
    have hle : (2 : Nat) ^ (2 * L) ≤ 2 ^ S n L := Nat.pow_le_pow_right (by norm_num) hge
    rw [← h4L] at hle
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h4 hle)
  have hd : 1 ≤ 2 ^ S n L - 3 ^ L := by omega
  have h2exp : (2 : Nat) ^ (S n L - L) ≤ 2 ^ (L - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3sub : (3 : Nat) ^ L - 2 ^ L < 3 ^ L := by
    have h2pos : 0 < (2 : Nat) ^ L := Nat.two_pow_pos L
    have hple : (2 : Nat) ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by norm_num) L
    omega
  calc n = n * 1 := (mul_one n).symm
    _ ≤ n * (2 ^ S n L - 3 ^ L) := Nat.mul_le_mul (Nat.le_refl n) hd
    _ ≤ 2 ^ (S n L - L) * (3 ^ L - 2 ^ L) := hmul
    _ ≤ 2 ^ (L - 1) * (3 ^ L - 2 ^ L) := Nat.mul_le_mul h2exp (Nat.le_refl _)
    _ < 2 ^ (L - 1) * 3 ^ L :=
        Nat.mul_lt_mul_of_pos_left h3sub (Nat.two_pow_pos (L - 1))
    _ ≤ 2 ^ L * 3 ^ L :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.le_refl _)
    _ = 6 ^ L := by rw [show (6 : Nat) = 2 * 3 by norm_num, mul_pow]

/-- **Finite-search corollary.** If no odd `m < 6^L` carries a nontrivial
`L`-cycle, then NO nontrivial `L`-cycle of `cc` exists at all: testing cycle
length `L` reduces to a finite search below `6^L`. -/
theorem cc_cycle_length_finite_test (L : Nat) (hL : 1 ≤ L)
    (hsearch : ∀ m, Odd m → m < 6 ^ L → cc^[L] m = m →
      ¬∃ j ∈ Finset.range L, 1 < cc^[j] m) :
    ∀ n, Odd n → cc^[L] n = n → ¬∃ j ∈ Finset.range L, 1 < cc^[j] n := by
  intro n hodd hcyc hnt
  exact hsearch n hodd (cc_cycle_element_lt_six_pow n L hodd hL hcyc hnt) hcyc hnt

end CollatzCycleElementBound
