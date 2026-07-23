/-
Zsygmondy: the `p = 2` intrinsic valuation bound, and Zsygmondy existence for ALL `n ≥ 2`
outside the classical exceptions.

This file supplies the final missing ingredient of the Zsygmondy primitive-prime-divisor
theorem: the even-prime companion of `padicValInt_cyclotomic_intrinsic_le_one`
(in `ZsygmondyHeightBound`, which handles all ODD intrinsic primes).

## The p = 2 phenomenology (why n = 2 is genuinely special)

Suppose `2 ∣ Φ_n(a)` (`n ≥ 2`, integer `a ≥ 2`).  Then `2 ∤ a` (`not_dvd_base_of_dvd_cyclotomic`),
so `a` is odd, hence `(a : ZMod 2) = 1` and `e := ord_2(a) = 1`.  The structure lemma
`intrinsic_order_dvd` then forces

    n = e · 2^k = 2^k,

so `2 ∣ Φ_n(a)` can only happen when **n is a power of 2**.  Writing `n = 2^k`:

  * `k = 1` (n = 2):  `Φ_2(a) = a + 1`, and `v_2(a+1)` is *unbounded* (e.g. `a = 2^t - 1`
    gives `v_2(a+1) = t`).  **The clean `≤ 1` bound is FALSE here.**  This is exactly the
    source of the classical `(n, a) = (2, 2^t - 1)` Zsygmondy exception.
  * `k ≥ 2` (4 ∣ n):  `Φ_{2^k}(a) = a^{2^{k-1}} + 1 ≡ 2 (mod 8)` (an odd square is `≡ 1`
    mod 8), so `v_2(Φ_n(a)) = 1` **exactly** — the clean bound holds.

So the correct even-prime intrinsic bound is `v_2(Φ_n(a)) ≤ 1` **for `n ≠ 2`** (the `k ≥ 2`
regime).  The `n = 2` case is not a defect of the proof; it is the genuine classical exception.

## TARGET A — `padicValInt_cyclotomic_intrinsic_two_le`

For `n ≥ 2`, `n ≠ 2`, integer `a ≥ 2`, and `2 ∣ Φ_n(a)`:  `v_2(Φ_n(a)) ≤ 1`.

Proof mirrors the odd-prime `padicValInt_cyclotomic_intrinsic_le_one`, but replaces the
odd-prime LTE by the **2-adic even LTE** `Zsygmondy2adicLTE.v2_pow_sub_pow_even`.  With
`e = 1` the structure lemma gives `n = 2^k`; `n ≠ 2` forces `k ≥ 2`, so with `m = 2^{k-1} = n/2`
both `n` and `m` are *even* and the even-case LTE applies to the odd base `a`:

    v_2(aⁿ - 1) = v_2(a-1) + v_2(a+1) + k   - 1,
    v_2(aᵐ - 1) = v_2(a-1) + v_2(a+1) + (k-1) - 1,

whence `v_2(aⁿ-1) = v_2(aᵐ-1) + 1`.  Since `(aᵐ - 1)·Φ_n(a) ∣ aⁿ - 1`, additivity of `v_2`
under products gives `v_2(aᵐ-1) + v_2(Φ_n(a)) ≤ v_2(aⁿ-1) = v_2(aᵐ-1) + 1`, i.e.
`v_2(Φ_n(a)) ≤ 1`.

## TARGET B — `primitive_prime_exists_of_size`

Zsygmondy existence for ALL `n ≥ 2`, `a ≥ 2`, with the same size hypothesis
`n ≤ (a-1)^φ(n)` as the odd-n theorem, and the single explicit carve-out

    ¬ (n = 2 ∧ ∃ t, (a + 1).natAbs = 2^t)

(the `n = 2`, `a + 1` a power of two exception).  The other two "classical" exceptions
(`n = 1`; `(n, a) = (6, 2)`) are *automatically* excluded: `n = 1` by `1 < n`, and `a = 2`
(hence `(6,2)`) by the size hypothesis itself — `(a-1)^φ(n) = 1 < n` when `a = 2`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHeightBound
import Propositio.NumberTheory.Zsygmondy.Zsygmondy2adicLTE
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Polynomial

/-- **TARGET A — even-prime intrinsic valuation bound.**  For `n ≥ 2` with `n ≠ 2`, an
integer `a ≥ 2`, and `2 ∣ Φ_n(a)`, the 2-adic valuation of `Φ_n(a)` is at most `1`.

The hypothesis `2 ∣ Φ_n(a)` already forces `a` odd and `n` a power of two (see the file
header); `n ≠ 2` excludes the classical `Φ_2(a) = a + 1` exception where `v_2` is unbounded.
In the remaining `4 ∣ n` regime one has in fact `v_2(Φ_n(a)) = 1` exactly. -/
theorem padicValInt_cyclotomic_intrinsic_two_le
    {n : ℕ} (hn : 1 < n) (hn2 : n ≠ 2) {a : ℤ} (ha : 2 ≤ a)
    (hpc : (2 : ℤ) ∣ (cyclotomic n ℤ).eval a) :
    padicValInt 2 ((cyclotomic n ℤ).eval a) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : 0 < n := by omega
  have hone_lt_a : 1 < a := by omega
  have hpa : ¬ (2 : ℤ) ∣ a := not_dvd_base_of_dvd_cyclotomic hn0 a hpc
  -- a strictly-greater-than-one bound on any positive power of `a`
  have hpow_gt : ∀ s : ℕ, 1 ≤ s → (1 : ℤ) < a ^ s := by
    intro s
    induction s with
    | zero => intro h; omega
    | succ t ih =>
      intro _
      rw [pow_succ]
      rcases Nat.eq_zero_or_pos t with ht0 | htp
      · subst ht0; simpa using hone_lt_a
      · have h1 := ih htp
        nlinarith [h1, ha]
  -- `q = a.toNat` as an odd natural ≥ 2
  set q : ℕ := a.toNat with hq
  have hqa : (q : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hq2 : 2 ≤ q := by omega
  have hqlt1 : (1 : ℕ) < q := by omega
  have hq_ndvd : ¬ (2 ∣ q) := by
    intro h
    exact hpa (by rw [← hqa]; exact_mod_cast h)
  have hqodd : Odd q := by rw [Nat.odd_iff]; omega
  -- order of `a` mod `2` is `1` (units of `ZMod 2` are trivial)
  have ha0 : (a : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
  have he1 : orderOf (a : ZMod 2) = 1 :=
    Nat.dvd_one.mp (by simpa using ZMod.orderOf_dvd_card_sub_one ha0)
  -- structure: `n = 2 ^ k`
  obtain ⟨k, hk⟩ := intrinsic_order_dvd (p := 2) hn0 a hpa hpc
  rw [he1, one_mul] at hk
  -- `n ≠ 2` and `n > 1` force `k ≥ 2`
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k
    · rw [pow_zero] at hk; omega
    · rw [pow_one] at hk; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  -- the proper divisor `m = 2 ^ (j+1) = n / 2`
  set m : ℕ := 2 ^ (j + 1) with hm
  have hmpos : 0 < m := pow_pos (by norm_num) _
  have hmn : n = m * 2 := by rw [hk, hm]; ring
  have hn_ne : n ≠ 0 := by omega
  have hm_ne : m ≠ 0 := by omega
  have hn_even : Even n := ⟨m, by omega⟩
  have hm_even : Even m := ⟨2 ^ j, by rw [hm]; ring⟩
  -- 2-adic valuations of `n` and `m`
  have hpv_n : padicValNat 2 n = j + 2 := by rw [hk, padicValNat.prime_pow]
  have hpv_m : padicValNat 2 m = j + 1 := by rw [hm, padicValNat.prime_pow]
  -- bridge: `v_2` on `ℤ` of `aᵉ - 1` matches `v_2` on `ℕ` of `qᵉ - 1`
  have bridge : ∀ e : ℕ, 1 ≤ e →
      padicValInt 2 (a ^ e - 1) = padicValNat 2 (q ^ e - 1) := by
    intro e he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have hcast : a ^ e - 1 = ((q ^ e - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hqe, Nat.cast_pow, Nat.cast_one, hqa]
    rw [hcast]
    exact padicValInt.of_nat
  -- 2-adic even LTE for exponents `n` and `m`
  have hVn : padicValNat 2 (q ^ n - 1)
      = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) + padicValNat 2 n - 1 := by
    have h := Zsygmondy2adicLTE.v2_pow_sub_pow_even hqodd odd_one hqlt1 hn_ne hn_even
    rwa [one_pow] at h
  have hVm : padicValNat 2 (q ^ m - 1)
      = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) + padicValNat 2 m - 1 := by
    have h := Zsygmondy2adicLTE.v2_pow_sub_pow_even hqodd odd_one hqlt1 hm_ne hm_even
    rwa [one_pow] at h
  have hbn : padicValInt 2 (a ^ n - 1) = padicValNat 2 (q ^ n - 1) := bridge n (by omega)
  have hbm : padicValInt 2 (a ^ m - 1) = padicValNat 2 (q ^ m - 1) := bridge m hmpos
  -- divisibility `(aᵐ - 1) · Φ_n(a) ∣ aⁿ - 1`
  have hmem : m ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨⟨2, hmn⟩, ?_⟩
    rw [hmn]; exact (Nat.lt_mul_iff_one_lt_right hmpos).mpr (by norm_num)
  have hdvd_poly : ((X : ℤ[X]) ^ m - 1) * cyclotomic n ℤ ∣ (X : ℤ[X]) ^ n - 1 :=
    X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hmem
  have hdvd_eval : (a ^ m - 1) * (cyclotomic n ℤ).eval a ∣ a ^ n - 1 := by
    have h := Polynomial.eval_dvd (x := a) hdvd_poly
    simpa [eval_mul, eval_sub, eval_pow, eval_X, eval_one] using h
  -- non-vanishing
  have hxne : a ^ m - 1 ≠ 0 := sub_ne_zero.mpr (hpow_gt m hmpos).ne'
  have hyne : a ^ n - 1 ≠ 0 := sub_ne_zero.mpr (hpow_gt n (by omega)).ne'
  have hCne : (cyclotomic n ℤ).eval a ≠ 0 := by
    intro h0
    have hpos := one_lt_natAbs_cyclotomic_eval hn ha
    rw [h0] at hpos; simp at hpos
  -- additivity and monotonicity of `v_2`
  have hval_mul : padicValInt 2 ((a ^ m - 1) * (cyclotomic n ℤ).eval a)
      = padicValInt 2 (a ^ m - 1) + padicValInt 2 ((cyclotomic n ℤ).eval a) :=
    padicValInt.mul hxne hCne
  have hmono : padicValInt 2 ((a ^ m - 1) * (cyclotomic n ℤ).eval a)
      ≤ padicValInt 2 (a ^ n - 1) := by
    have hd : (2 : ℤ) ^ padicValInt 2 ((a ^ m - 1) * (cyclotomic n ℤ).eval a) ∣ a ^ n - 1 :=
      (padicValInt_dvd _).trans hdvd_eval
    rcases (padicValInt_dvd_iff _ _).mp hd with h | h
    · exact absurd h hyne
    · exact h
  omega

/-- **TARGET B — Zsygmondy existence for all `n ≥ 2`, minus the classical exceptions.**
For `n ≥ 2`, an integer `a ≥ 2`, the size hypothesis `n ≤ (a-1)^φ(n)`, and the explicit
carve-out `¬ (n = 2 ∧ a + 1` is a power of two`)`, the number `a^n - 1` has a *primitive*
prime divisor: a prime `p` dividing `a^n - 1` but none of `a^m - 1` for `0 < m < n`.

This drops the `Odd n` hypothesis of `primitive_prime_exists_of_odd_of_size`.  The remaining
two classical exceptions are automatically excluded: `n = 1` by `1 < n`; and `a = 2` (hence
`(n,a) = (6,2)`) by the size hypothesis, since `(a-1)^φ(n) = 1 < n` when `a = 2`.  The single
genuine even-`n` exception, `n = 2` with `a + 1` a power of two, is the stated carve-out.

Proof mirrors `primitive_prime_exists_of_odd_of_size`, dispatching the intrinsic prime `p`
by parity: odd `p` via `padicValInt_cyclotomic_intrinsic_le_one`, and `p = 2` (which forces
`n` a power of two) via TARGET A when `n > 2`, or the carve-out when `n = 2`. -/
theorem primitive_prime_exists_of_size {n : ℕ} (hn : 1 < n)
    {a : ℤ} (ha : 2 ≤ a) (hsize : (n : ℤ) ≤ (a - 1) ^ Nat.totient n)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, (a + 1).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  by_contra hcon
  push_neg at hcon
  -- No primitive prime divisor ⇒ |Φ_n(a)| is a prime power.
  have hpp : IsPrimePow ((cyclotomic n ℤ).eval a).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ := primitive_prime_exists_of_not_isPrimePow hn ha h
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, t, hp, ht, hpt⟩ := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  set M := ((cyclotomic n ℤ).eval a).natAbs with hMdef
  -- p divides Φ_n(a)
  have hpM : p ∣ M := hpt ▸ dvd_pow_self p (by omega : t ≠ 0)
  have hpc : (p : ℤ) ∣ (cyclotomic n ℤ).eval a :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM)
  -- p ∣ n: otherwise p is itself a primitive prime divisor (contradiction).
  have hpn : p ∣ n := by
    by_contra hpn
    obtain ⟨h1, h2⟩ := primitive_prime_divisor_of_dvd_cyclotomic hn a hpc hpn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  -- v_p(Φ_n(a)) = t (since |Φ_n(a)| = p^t)
  have hvalM : padicValInt p ((cyclotomic n ℤ).eval a) = t := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : padicValInt p ((cyclotomic n ℤ).eval a) = padicValNat p M := by
      rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  -- the intrinsic valuation bound: `t ≤ 1`, split on `p = 2` vs `p` odd.
  have ht1 : t = 1 := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · -- p = 2 : the even-prime case
      subst hp2
      -- when n = 2 the value is `Φ_2(a) = a + 1`, giving the excluded configuration
      by_cases hn2 : n = 2
      · exfalso
        apply hexc
        refine ⟨hn2, t, ?_⟩
        -- |Φ_2(a)| = (a+1).natAbs = 2^t
        have hΦ : (cyclotomic n ℤ).eval a = a + 1 := by
          rw [hn2, cyclotomic_two]; simp
        rw [hMdef, hΦ] at hpt
        exact hpt.symm
      · -- n ≠ 2 : TARGET A gives v_2 ≤ 1
        have hval_le : padicValInt 2 ((cyclotomic n ℤ).eval a) ≤ 1 :=
          padicValInt_cyclotomic_intrinsic_two_le hn hn2 ha hpc
        rw [hvalM] at hval_le
        omega
    · -- p odd : the odd-prime intrinsic bound
      have hval_le : padicValInt p ((cyclotomic n ℤ).eval a) ≤ 1 :=
        padicValInt_cyclotomic_intrinsic_le_one hn hpodd ha hpn hpc
      rw [hvalM] at hval_le
      omega
  -- so |Φ_n(a)| = p ≤ n, contradicting the totient lower bound + size hypothesis.
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hpn_le : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hlb : (a - 1) ^ Nat.totient n < (M : ℤ) := by
    rw [hMdef]; exact cyclotomic_eval_totient_lower_bound hn ha
  have hMpZ : (M : ℤ) = (p : ℤ) := by rw [hMp]
  have hpnZ : (p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hpn_le
  rw [hMpZ] at hlb
  linarith [hsize, hlb, hpnZ]
