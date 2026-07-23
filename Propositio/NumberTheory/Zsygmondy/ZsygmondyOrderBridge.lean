/-
Zsygmondy order bridge.

The bridge between the "primitive prime divisor of `a^n - 1`" language and the
multiplicative-order language of `orderOf` in `ZMod p`.  For a prime `p` and an
integer `a` with `p ∤ a`:

  (1) `orderOf (a : ZMod p) ∣ m ↔ (p : ℤ) ∣ a ^ m - 1`     (for `m ≥ 1`)
  (2) the classical "primitive prime divisor" characterization: `p` divides
      `a ^ n - 1` but none of `a ^ m - 1` for `0 < m < n` iff
      `orderOf (a : ZMod p) = n`                            (for `n ≥ 1`)

Proof strategy:
1. `(a : ZMod p) ≠ 0` since `p ∤ a` (`ZMod.intCast_zmod_eq_zero_iff_dvd`).
2. `orderOf_dvd_iff_pow_eq_one` turns divisibility of the order into the
   equation `(a : ZMod p) ^ m = 1`, which is the same statement as
   `(p : ℤ) ∣ a ^ m - 1` after `push_cast` through
   `ZMod.intCast_zmod_eq_zero_iff_dvd`. This is (1).
3. `(a : ZMod p)` has finite order (witnessed by Fermat's little theorem,
   `ZMod.pow_card_sub_one_eq_one`), so `orderOf (a : ZMod p) > 0`.
4. (2) follows from (1) by an order-comparison argument: the order itself is a
   valid witness for "some `m` with `p ∣ a^m - 1`", so minimality forces
   `orderOf = n`; conversely `orderOf = n` immediately gives both the
   divisibility at `n` and the non-divisibility below `n` via (1).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-- **(1) Order-divisibility bridge.** For a prime `p`, an integer `a`, and `m ≥ 1`,
the multiplicative order of `a` mod `p` divides `m` iff `p ∣ a^m - 1`. -/
theorem orderOf_dvd_iff {p : ℕ} [Fact p.Prime] (a : ℤ) {m : ℕ} (_hm : 1 ≤ m) :
    orderOf (a : ZMod p) ∣ m ↔ (p : ℤ) ∣ a ^ m - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    ring
  · intro h
    have hzero : ((a ^ m - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have hcast : ((a ^ m - 1 : ℤ) : ZMod p) = (a : ZMod p) ^ m - 1 := by push_cast; ring
    rw [hcast] at hzero
    linear_combination hzero

/-- The order of `a` mod `p` is positive when `p ∤ a`, via Fermat's little theorem
(`a^(p-1) = 1` witnesses finite order). -/
theorem orderOf_pos_of_not_dvd {p : ℕ} [Fact p.Prime] {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) :
    0 < orderOf (a : ZMod p) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hpa
  have hfin : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out (p := p.Prime)).one_lt
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, hp1, hfin⟩).orderOf_pos

/-- **(2) Primitive prime divisor characterization.** For a prime `p`, an integer `a`
with `p ∤ a`, and `n ≥ 1`:  `p` is a *primitive* prime divisor of `a^n - 1` — i.e. it
divides `a^n - 1` but none of `a^m - 1` for `0 < m < n` — iff the multiplicative order
of `a` mod `p` equals `n`. -/
theorem primitive_iff_orderOf_eq {p : ℕ} [Fact p.Prime] (a : ℤ) {n : ℕ} (hn : 1 ≤ n)
    (hpa : ¬ (p : ℤ) ∣ a) :
    ((p : ℤ) ∣ a ^ n - 1 ∧ ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1) ↔
      orderOf (a : ZMod p) = n := by
  constructor
  · rintro ⟨hdvdn, hmin⟩
    have hdn : orderOf (a : ZMod p) ∣ n := (orderOf_dvd_iff a hn).mpr hdvdn
    have hpos : 0 < orderOf (a : ZMod p) := orderOf_pos_of_not_dvd hpa
    have hle : orderOf (a : ZMod p) ≤ n := Nat.le_of_dvd hn hdn
    -- the order itself is a witness for "`p ∣ a^d - 1`", via `pow_orderOf_eq_one`
    have hdvd_ord : (p : ℤ) ∣ a ^ orderOf (a : ZMod p) - 1 :=
      (orderOf_dvd_iff a hpos).mp dvd_rfl
    by_contra hne
    have hlt : orderOf (a : ZMod p) < n := lt_of_le_of_ne hle hne
    exact hmin (orderOf (a : ZMod p)) hpos hlt hdvd_ord
  · intro heq
    refine ⟨?_, ?_⟩
    · have : orderOf (a : ZMod p) ∣ n := heq ▸ dvd_rfl
      exact (orderOf_dvd_iff a hn).mp this
    · intro m hm0 hmn hcontra
      have hdvd : orderOf (a : ZMod p) ∣ m := (orderOf_dvd_iff a hm0).mpr hcontra
      rw [heq] at hdvd
      have := Nat.le_of_dvd hm0 hdvd
      omega
