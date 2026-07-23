import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Erdős–Straus multiplicativity brick

If `4/n = 1/a + 1/b + 1/c` (a positive-denominator Erdős–Straus representation for `n`),
then scaling every denominator by a positive `k` yields a representation for `k * n`:

`4/(k*n) = 1/(k*a) + 1/(k*b) + 1/(k*c)`.

This is a pure field identity: multiply both sides of `h` by `1/k`.
-/

theorem erdosStraus_scale (n a b c k : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (h : (4 : ℚ) / n = 1 / a + 1 / b + 1 / c) :
    (4 : ℚ) / (k * n) = 1 / (k * a) + 1 / (k * b) + 1 / (k * c) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hscaled : (4 : ℚ) / (k * n) = (1 / (k : ℚ)) * (1 / a + 1 / b + 1 / c) := by
    rw [← h]
    field_simp
  rw [hscaled]
  field_simp
