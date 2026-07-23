import Propositio.Collatz.SyracuseThreeAdicBias
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic

/-!
# The Syracuse map has no 2-cycle other than the fixed point `1`

The Syracuse map `Syr` (the odd part of `3N+1`) is defined in
`SyracuseThreeAdicBias.lean`.  Here we prove that the only odd `n` with
`Syr (Syr n) = n` is `n = 1`; equivalently, the Syracuse dynamics have no
nontrivial 2-cycle on the odd numbers.

The argument is purely elementary.  Writing `m = Syr n`, the exact-division
identity `Syr_mul_pow` gives, with `a = v₂(3n+1)`, `b = v₂(3m+1)`,

    m · 2^a = 3n+1   and   n · 2^b = 3m+1.

Multiplying and using `3n+1 ≤ 4n`, `3m+1 ≤ 4m` (valid since `n,m ≥ 1`) forces
`2^{a+b} ≤ 16`, hence `a+b ≤ 4`.  Both `a,b ≥ 1` (since `n,m` odd make `3n+1`,
`3m+1` even), so a finite case analysis on `(a,b)` closes the goal: the only
positive solution is `n = m = 1`.
-/

namespace SyracuseNoTwoCycle

open SyracuseThreeAdicBias

/-- The Syracuse map always outputs an odd number: `Syr N` is the *odd part* of
`3N+1`, so it carries no factor of `2`. -/
theorem Syr_odd (N : ℕ) : Odd (Syr N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd]
  rintro ⟨k, hk⟩
  set v := padicValNat 2 (3 * N + 1) with hvdef
  have hmul := Syr_mul_pow N
  rw [hk] at hmul
  -- hmul : (k + k) * 2 ^ v = 3 * N + 1
  have hdvd : 2 ^ (v + 1) ∣ (3 * N + 1) :=
    ⟨k, by rw [← hmul, pow_succ]; ring⟩
  exact pow_succ_padicValNat_not_dvd (p := 2) (by omega) hdvd

/-- **No nontrivial 2-cycle.** For odd `n`, `Syr (Syr n) = n` iff `n = 1`. -/
theorem Syr_two_cycle_iff_one {n : ℕ} (hn : Odd n) : Syr (Syr n) = n ↔ n = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    -- Set up the second iterate and its data.
    set m := Syr n with hm
    have hm_odd : Odd m := Syr_odd n
    have hn1 : 1 ≤ n := hn.pos
    have hm1 : 1 ≤ m := hm_odd.pos
    set a := padicValNat 2 (3 * n + 1) with ha_def
    set b := padicValNat 2 (3 * m + 1) with hb_def
    -- The two exact-division identities.
    have eqI : m * 2 ^ a = 3 * n + 1 := Syr_mul_pow n
    have eqII : n * 2 ^ b = 3 * m + 1 := by
      have := Syr_mul_pow m
      rw [h] at this
      exact this
    -- Both valuations are ≥ 1 (3n+1 and 3m+1 are even).
    have hda : (2 : ℕ) ∣ (3 * n + 1) := by
      rcases hn with ⟨t, rfl⟩; exact ⟨3 * t + 2, by ring⟩
    have hdb : (2 : ℕ) ∣ (3 * m + 1) := by
      rcases hm_odd with ⟨t, ht⟩; exact ⟨3 * t + 2, by rw [ht]; ring⟩
    have ha1 : 1 ≤ a := by
      rw [ha_def]; exact one_le_padicValNat_of_dvd (by omega) hda
    have hb1 : 1 ≤ b := by
      rw [hb_def]; exact one_le_padicValNat_of_dvd (by omega) hdb
    -- Multiply the two identities.
    have key : m * n * 2 ^ (a + b) = (3 * n + 1) * (3 * m + 1) := by
      rw [pow_add]
      calc m * n * (2 ^ a * 2 ^ b)
          = (m * 2 ^ a) * (n * 2 ^ b) := by ring
        _ = (3 * n + 1) * (3 * m + 1) := by rw [eqI, eqII]
    -- The product is bounded by 16·m·n, forcing 2^(a+b) ≤ 16.
    have hbound : (3 * n + 1) * (3 * m + 1) ≤ m * n * 16 := by nlinarith [hn1, hm1]
    have hcancel : m * n * 2 ^ (a + b) ≤ m * n * 16 := by rw [key]; exact hbound
    have hpos : 0 < m * n := by positivity
    have hle16 : 2 ^ (a + b) ≤ 16 := Nat.le_of_mul_le_mul_left hcancel hpos
    have hab : a + b ≤ 4 := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16] at hle16
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hle16
    -- Finite case analysis: a,b ≥ 1, a+b ≤ 4 ⇒ only n = 1 survives.
    have ha3 : a ≤ 3 := by omega
    have hb3 : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> omega
  · intro h
    subst h
    -- Compute Syr 1 = 1.
    have hv : padicValNat 2 (3 * 1 + 1) = 2 := by
      rw [show (3 * 1 + 1) = 2 ^ 2 from by norm_num]
      exact padicValNat.prime_pow (p := 2) 2
    have hmp := Syr_mul_pow 1
    rw [hv] at hmp
    have hSyr1 : Syr 1 = 1 := by
      have : Syr 1 * 4 = 4 := by norm_num at hmp ⊢; exact hmp
      omega
    rw [hSyr1, hSyr1]

end SyracuseNoTwoCycle
