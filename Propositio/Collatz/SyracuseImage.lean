import Propositio.Collatz.SyracuseThreeAdicBias

/-!
# The image of the Syracuse map — surjectivity onto the odds not divisible by 3

The companion file `SyracuseThreeAdicBias.lean` proves that the Syracuse map
`Syr N = (3N+1)/2^{v₂(3N+1)}` never lands on a multiple of `3` (`Syr_not_dvd_three`),
and one checks easily that `Syr` of an odd number is odd.  This file proves the
matching **surjectivity** direction: every odd `t` with `3 ∤ t` is hit by `Syr`
on some odd input.  Together these pin the image of `Syr` (restricted to odds)
to be *exactly* the odd numbers not divisible by `3`.

## Construction

Given odd `t` with `3 ∤ t`, we want an odd `m` with `Syr m = t`.  We look for `m`
with `3m+1 = t · 2^v`; since `t` is odd, `v₂(t · 2^v) = v`, so `Syr m = t`
automatically.  The valuation `v` is chosen by the residue of `t` mod `3`:

  * `t ≡ 1 (mod 3)`  ⟹  `v = 2`,  `m = (4t-1)/3`   (so `3m+1 = 4t`),
  * `t ≡ 2 (mod 3)`  ⟹  `v = 1`,  `m = (2t-1)/3`   (so `3m+1 = 2t`).

In each case `3 ∣ (t·2^v - 1)`, `m` is a natural number, and `m` is odd because
`3m = t·2^v - 1` is odd.
-/

namespace SyracuseThreeAdicBias

/-- **Key valuation/cancellation step.** If `t` is odd and `3·m+1 = t·2^v`, then
`Syr m = t`.  Because `t` is odd, `v₂(t·2^v) = v`, so the `2^v` in `Syr_mul_pow`
cancels exactly. -/
private theorem syr_eq_of_eq {m t v : ℕ} (ht : Odd t) (h : 3 * m + 1 = t * 2 ^ v) :
    Syr m = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htmod : t % 2 = 1 := Nat.odd_iff.mp ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at h
  have hpow : (2 : ℕ) ^ v ≠ 0 := pow_ne_zero _ (by norm_num)
  have hv2 : ¬ (2 ∣ t) := by omega
  -- The 2-adic valuation of `3m+1 = t·2^v` is exactly `v`.
  have hval : padicValNat 2 (3 * m + 1) = v := by
    rw [h, padicValNat.mul ht0 hpow, padicValNat.eq_zero_of_not_dvd hv2,
      padicValNat.prime_pow, zero_add]
  -- Cancel `2^v` in `Syr m · 2^v = 3m+1 = t·2^v`.
  have hmul := Syr_mul_pow m
  rw [hval, h] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpow) hmul

/-- **Surjectivity of the Syracuse map onto the odds not divisible by 3.**
Every odd `t` with `3 ∤ t` is the image under `Syr` of some odd `m`. -/
theorem Syr_surjective_on_odd_not_three {t : ℕ} (ht : Odd t) (h3 : ¬ (3 ∣ t)) :
    ∃ m : ℕ, Odd m ∧ Syr m = t := by
  have ht2 : t % 2 = 1 := Nat.odd_iff.mp ht
  have ht3 : t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases ht3 with h1 | h2
  · -- `t ≡ 1 (mod 3)`: take `v = 2`, `m = (4t-1)/3`, so `3m+1 = 4t`.
    refine ⟨(4 * t - 1) / 3, Nat.odd_iff.mpr (by omega), ?_⟩
    refine syr_eq_of_eq (v := 2) ht ?_
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]; omega
  · -- `t ≡ 2 (mod 3)`: take `v = 1`, `m = (2t-1)/3`, so `3m+1 = 2t`.
    refine ⟨(2 * t - 1) / 3, Nat.odd_iff.mpr (by omega), ?_⟩
    refine syr_eq_of_eq (v := 1) ht ?_
    have h2' : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2']; omega

end SyracuseThreeAdicBias
