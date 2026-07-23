/-
Zsygmondy exceptional-case CAPSTONE — general `b`, consecutive integers `a = b + 1`.

This file assembles items (1)–(3) (`ZsygmondyPrimitiveExistsGeneral`,
`ZsygmondyLTEGeneral`) with the two case-elimination theorems of
`ZsygmondyExceptionalEndgameGeneral` (`no_k_ge_two_general`,
`k_eq_one_impossible_of_b_ge_two`) into a CLOSED primitive-divisor existence theorem for
the worst-margin family `a = b + 1`, `b ≥ 2`:

  `primitive_prime_exists_succ_of_b_ge_two`: for `b ≥ 2` and `n ≥ 2`, the number
  `(b+1)^n - b^n` has a primitive prime divisor (no exceptions — the classical `(6,2,1)`
  exception is `b = 1` only, and the `n = 2` exception `a + b = 2b + 1` a power of two never
  occurs for `b ≥ 1`).

## The key structural finding of this file: item (4) is VACUOUS for `a = b + 1`

The frontier note and `ZsygmondyExceptionalEndgameGeneral`'s docstring flagged item (4) —
the `p = 2` branch for even `b` — as the one piece likely to need genuinely new work
(mirroring `ZsygmondyEvenPrime`'s difficulty in the `b = 1` corpus). That framing is
CORRECT for the general-`a` theorem (any `a > b`), but it is UNNECESSARY for the
exceptional endgame, whose only object is `a = b + 1` (consecutive integers): the height
lower bound `(a - b)^φ(n) < Phi n a b` degenerates to `1 < Phi n a b` precisely when
`a - b = 1`, so `a = b + 1` is exactly the family the size-route cannot reach and the
self-bound endgame must handle. For consecutive `a = b + 1`, `2` divides EXACTLY ONE of
`a, b`, so by `not_dvd_base_of_dvd_Phi` (which forces `p ∤ a` AND `p ∤ b` for any prime
`p ∣ Phi n a b`) the prime `2` can never divide `Phi n a b` — hence the intrinsic prime is
automatically ODD, and only the odd-prime LTE (item (2)) is needed. `two_not_dvd_Phi_succ`
below makes this precise. So the full `a = b + 1` endgame closes with items (1)–(3) alone;
`ZsygmondyEvenPrime`-style `p = 2` LTE is not required here.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExistsGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyLTEGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExceptionalEndgameGeneral
import Mathlib.Algebra.IsPrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyExceptionalCapstoneGeneral

/-- **`p = 2` is excluded for consecutive integers.** For `a = b + 1` (`1 ≤ b`) and any
`n ≥ 1`, `2 ∤ Phi n (b+1) b`. Proof: if `2 ∣ Phi n (b+1) b`, then by
`not_dvd_base_of_dvd_Phi` (with `IsCoprime (b+1) b`), `2 ∤ (b+1)` and `2 ∤ b`. But `b` and
`b + 1` are consecutive, so exactly one is even — contradiction. This makes the whole
`p = 2` branch (item (4)) vacuous for the `a = b + 1` endgame. -/
theorem two_not_dvd_Phi_succ {n : ℕ} (hn : 0 < n) {b : ℤ} (_hb : 1 ≤ b) :
    ¬ ((2 : ℕ) : ℤ) ∣ Phi n (b + 1) b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  have hcop : IsCoprime (b + 1) b := ⟨1, -1, by ring⟩
  obtain ⟨hpa, hpb⟩ :=
    ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi hn hcop h2
  have h2b : ¬ (2 : ℤ) ∣ b := by simpa using hpb
  have h2a : ¬ (2 : ℤ) ∣ (b + 1) := by simpa using hpa
  rcases Int.even_or_odd b with hbe | hbo
  · exact h2b hbe.two_dvd
  · exact h2a (hbo.add_one).two_dvd

/-- **Zsygmondy exceptional-case capstone, `a = b + 1`, `b ≥ 2`.** For `b ≥ 2` and `n ≥ 2`,
`(b+1)^n - b^n` has a *primitive* prime divisor: a prime `p` with `p ∣ (b+1)^n - b^n` and
`p ∤ (b+1)^m - b^m` for every `0 < m < n`.

This closes the general-`b` exceptional (`a = b + 1`) case of Zsygmondy's theorem for all
`b ≥ 2`, with NO exceptions. Proof structure (mirrors `primitive_prime_exists_base_two`):
if there is no primitive prime divisor, `(Phi n (b+1) b).natAbs` is a prime power `p^t`
(item (1), `primitive_prime_exists_of_not_isPrimePow_general`); `p ∣ n` (else `p` is itself
a primitive prime divisor); `p ≠ 2` (`two_not_dvd_Phi_succ`), so `p` is odd; the odd-prime
LTE (item (2), `padicValInt_Phi_intrinsic_le_one`) forces `t = 1`, i.e. `Phi n (b+1) b = p`;
the intrinsic decomposition `n = e·p^k` (`intrinsic_order_dvd_general`) has `e ≥ 2` (item
(3), `prime_power_case_impossible_of_succ` rules out `e = 1` / prime-power `n`), and both
`k ≥ 2` (`no_k_ge_two_general`) and `k = 1` (`k_eq_one_impossible_of_b_ge_two`, using `b ≥ 2`
and the odd prime `p ≥ 3`) are impossible — contradiction. -/
theorem primitive_prime_exists_succ_of_b_ge_two {n : ℕ} (hn : 1 < n) {b : ℤ} (hb2 : 2 ≤ b) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (b + 1) ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ (b + 1) ^ m - b ^ m := by
  by_contra hcon
  push_neg at hcon
  set a : ℤ := b + 1 with hadef
  have hb1 : 1 ≤ b := by omega
  have hab : b < a := by omega
  have hcop : IsCoprime a b := ⟨1, -1, by rw [hadef]; ring⟩
  have hn0 : 0 < n := by omega
  -- No primitive prime divisor ⇒ (Phi n a b).natAbs is a prime power.
  have hpp : IsPrimePow (Phi n a b).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_exists_of_not_isPrimePow_general
        hn hb1 hab hcop h
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, t, hp, ht, hpt⟩ := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  set M := (Phi n a b).natAbs with hMdef
  have hpM : p ∣ M := hpt ▸ dvd_pow_self p (by omega : t ≠ 0)
  have hpc : (p : ℤ) ∣ Phi n a b :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM)
  -- p ∣ n: otherwise p is a primitive prime divisor.
  have hpn : p ∣ n := by
    by_contra hpn
    obtain ⟨h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_divisor_of_dvd_Phi hn hcop hpc hpn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  -- p ≠ 2 (consecutive integers), hence odd.
  have hp2ne : p ≠ 2 := by
    rintro rfl
    exact two_not_dvd_Phi_succ hn0 hb1 (hadef ▸ hpc)
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2ne
  -- LTE pins t = 1, so Phi n a b = p.
  have hval_le : padicValInt p (Phi n a b) ≤ 1 :=
    ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one hn hpodd hb1 hab hcop hpn hpc
  have hvalM : padicValInt p (Phi n a b) = t := by
    have h1 : padicValInt p (Phi n a b) = padicValNat p M := by rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by rw [hvalM] at hval_le; omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hPhipos : (0 : ℤ) < Phi n a b := by
    have hlb := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound hn hb1 hab
    have hab1 : (1 : ℤ) ≤ a - b := by omega
    have hpow1 : (1 : ℤ) ≤ (a - b) ^ Nat.totient n := one_le_pow₀ hab1
    linarith
  have hMeq : Phi n a b = (p : ℤ) := by
    have hna := Int.natAbs_of_nonneg hPhipos.le
    rw [← hMdef, hMp] at hna
    exact hna.symm
  -- intrinsic decomposition n = e * p^k, e = ord_p(a·b⁻¹), with e ≥ 2 (not prime-power).
  obtain ⟨hpa, hpb⟩ :=
    ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi hn0 hcop hpc
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 a b hpb hpc
  set e := orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) with he
  have hepos : 0 < e := orderOf_pos_of_not_dvd_general hpa hpb
  have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := by
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hbz : (b : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
    exact mul_ne_zero ha0 (inv_ne_zero hbz)
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hr0
  have hpe_not : ¬ p ∣ e := by
    intro hdvd
    have hle1 : e ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) he_dvd
    have hle2 : p ≤ e := Nat.le_of_dvd hepos hdvd
    have := hp.one_lt
    omega
  -- e ≠ 1: else n = p^k is a prime power (item (3) vacuity).
  have he_ne1 : e ≠ 1 := by
    intro he1
    have hnp : IsPrimePow n := by
      rw [he1, one_mul] at hk
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h
        · exfalso; rw [h0, pow_zero] at hk; omega
        · exact h
      exact ⟨p, k, hp.prime, hkpos, hk.symm⟩
    exact ZsygmondyLTEGeneral.prime_power_case_impossible_of_succ hn hb1 hnp hpn
      (hadef ▸ hpc)
  have he2 : 2 ≤ e := by omega
  -- k ≥ 1 since p ∣ n.
  have hk1 : 1 ≤ k := by
    by_contra hklt
    push_neg at hklt
    interval_cases k
    rw [pow_zero, mul_one] at hk
    rw [hk] at hpn
    exact hpe_not hpn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- k = 1: n = e * p, use the b ≥ 2 uniform margin.
    subst hj0
    simp only [pow_one] at hk
    have he1lt : 1 < e := by omega
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hMeqq : Phi (e * p) a b = (p : ℤ) := by rw [← hk]; exact hMeq
    rw [hadef] at hMeqq
    exact ZsygmondyExceptionalEndgameGeneral.k_eq_one_impossible_of_b_ge_two
      hb2 he1lt hp hp3 hpe_not hMeqq
  · -- k ≥ 2: p² ∣ n, use no_k_ge_two_general.
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hp2dvdn : p * p ∣ n := by
      refine ⟨e * p ^ i, ?_⟩
      rw [hk, pow_succ, pow_succ]; ring
    have hMeq' : Phi n a b = (p : ℤ) := hMeq
    rw [hadef] at hMeq'
    exact ZsygmondyExceptionalEndgameGeneral.no_k_ge_two_general hb1 hn hp hp2dvdn hMeq'

end ZsygmondyExceptionalCapstoneGeneral
