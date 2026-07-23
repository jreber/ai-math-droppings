/-
Zsygmondy order bridge — general-`b` port.

The two-variable generalization of `ZsygmondyOrderBridge`: the bridge between the
"primitive prime divisor of `a^n - b^n`" language and the multiplicative-order
language of `orderOf` in `ZMod p`, for coprime-style hypotheses where `p ∤ b`.

Since `ZMod p` is a field for prime `p`, the natural substitution for the `b = 1`
statements `orderOf (a : ZMod p)` is `orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)`
(well-defined precisely when `p ∤ b`, which is exactly the side condition every
downstream lemma already carries). For a prime `p`, integers `a b` with `p ∤ b`:

  (1) `orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ m ↔ (p : ℤ) ∣ a ^ m - b ^ m`  (`m ≥ 1`)
  (2) the classical "primitive prime divisor" characterization: `p` divides
      `a ^ n - b ^ n` but none of `a ^ m - b ^ m` for `0 < m < n` iff
      `orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n`                          (`n ≥ 1`)

Proof strategy: identical in shape to `ZsygmondyOrderBridge`, with `r := a * b⁻¹`
playing the role `a` played there. The only new ingredient is clearing the `b⁻¹`
factor: `r ^ m = 1 ↔ (a : ZMod p) ^ m = (b : ZMod p) ^ m`, obtained by multiplying
through by `(b : ZMod p) ^ m ≠ 0`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-- `r ^ m = 1` for `r = a * b⁻¹` iff `a ^ m = b ^ m`, given `b ≠ 0`. Pure field algebra,
the one new ingredient beyond the `b = 1` order bridge. -/
private theorem mul_inv_pow_eq_one_iff {p : ℕ} [Fact p.Prime] {a b : ZMod p} (hb : b ≠ 0)
    {m : ℕ} : (a * b⁻¹) ^ m = 1 ↔ a ^ m = b ^ m := by
  rw [mul_pow, inv_pow]
  constructor
  · intro h
    have hbm : b ^ m ≠ 0 := pow_ne_zero m hb
    field_simp at h
    exact h
  · intro h
    rw [h]
    field_simp

/-- **(1) Order-divisibility bridge, general `b`.** For a prime `p`, integers `a b` with
`p ∤ b`, and `m ≥ 1`, the multiplicative order of `a * b⁻¹` mod `p` divides `m` iff
`p ∣ a^m - b^m`. -/
theorem orderOf_dvd_iff_general {p : ℕ} [Fact p.Prime] (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b)
    {m : ℕ} (_hm : 1 ≤ m) :
    orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ m ↔ (p : ℤ) ∣ a ^ m - b ^ m := by
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb
  rw [orderOf_dvd_iff_pow_eq_one, mul_inv_pow_eq_one_iff hb0]
  constructor
  · intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    ring
  · intro h
    have hzero : ((a ^ m - b ^ m : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have hcast : ((a ^ m - b ^ m : ℤ) : ZMod p) = (a : ZMod p) ^ m - (b : ZMod p) ^ m := by
      push_cast; ring
    rw [hcast] at hzero
    linear_combination hzero

/-- The order of `a * b⁻¹` mod `p` is positive when `p ∤ a` and `p ∤ b`, via Fermat's
little theorem (the element is nonzero, hence has finite order). -/
theorem orderOf_pos_of_not_dvd_general {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
  have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
  have hfin : ((a : ZMod p) * (b : ZMod p)⁻¹) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hr0
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out (p := p.Prime)).one_lt
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, hp1, hfin⟩).orderOf_pos

/-- **(2) Primitive prime divisor characterization, general `b`.** For a prime `p`,
integers `a b` with `p ∤ a`, `p ∤ b`, and `n ≥ 1`: `p` is a *primitive* prime divisor of
`a^n - b^n` — i.e. it divides `a^n - b^n` but none of `a^m - b^m` for `0 < m < n` — iff
the multiplicative order of `a * b⁻¹` mod `p` equals `n`. -/
theorem primitive_iff_orderOf_eq_general {p : ℕ} [Fact p.Prime] (a b : ℤ) {n : ℕ}
    (hn : 1 ≤ n) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    ((p : ℤ) ∣ a ^ n - b ^ n ∧ ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m) ↔
      orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  constructor
  · rintro ⟨hdvdn, hmin⟩
    have hdn : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ n :=
      (orderOf_dvd_iff_general a b hpb hn).mpr hdvdn
    have hpos : 0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
      orderOf_pos_of_not_dvd_general hpa hpb
    have hle : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ≤ n := Nat.le_of_dvd hn hdn
    have hdvd_ord : (p : ℤ) ∣ a ^ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) -
        b ^ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
      (orderOf_dvd_iff_general a b hpb hpos).mp dvd_rfl
    by_contra hne
    have hlt : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) < n := lt_of_le_of_ne hle hne
    exact hmin (orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)) hpos hlt hdvd_ord
  · intro heq
    refine ⟨?_, ?_⟩
    · have : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ n := heq ▸ dvd_rfl
      exact (orderOf_dvd_iff_general a b hpb hn).mp this
    · intro m hm0 hmn hcontra
      have hdvd : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ m :=
        (orderOf_dvd_iff_general a b hpb hm0).mpr hcontra
      rw [heq] at hdvd
      have := Nat.le_of_dvd hm0 hdvd
      omega
