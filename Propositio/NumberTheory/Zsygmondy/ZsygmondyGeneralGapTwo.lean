/-
Zsygmondy's theorem, general non-consecutive case (`a - b ≥ 2`) — the residual scope flagged
in `docs/kb/frontier/_meta.json`'s `_goal_zsygmondy_OPEN_2026_07_05` note after the
consecutive case (`a = b + 1`, ALL `b ≥ 1`) was fully closed
(`ZsygmondyExceptionalCapstoneGeneral.primitive_prime_exists_succ_of_b_ge_two` plus the
classical `b = 1` corpus).

## Strategy

The consecutive case needed a delicate numeric-margin "exceptional endgame" because the
totient-growth size route (`n ≤ (a - b) ^ φ(n)`) is identically `n ≤ 1`, false for every
`n ≥ 2` when `a - b = 1`. For `a - b ≥ 2` the size route is NOT vacuous: the SAME totient
lower bound `(a - b) ^ φ(n) < Phi n a b` (`ZsygmondyExceptionalEndgameGeneral.
Phi_totient_lower_bound`, already proved for general `a, b`) combined with the *pure*,
`a`/`b`-independent totient-growth inequality `n ≤ 2 ^ φ(n)` for `n ≠ 6`
(`ZsygmondyBaseThree.totient_growth_two_ne_six`) discharges the whole `n ≠ 6` range in ONE
uniform step, for every `a - b ≥ 2` (not just `a - b = 2`): `n ≤ 2 ^ φ(n) ≤ (a-b) ^ φ(n)`.

This makes `n = 6` the only residual gap (exactly mirroring why the `b = 1, a = 3` case
needed one explicit witness `p = 7` in `ZsygmondyBaseThree`) — but here the gap must be closed
for an ENTIRE family (every `a - b ≥ 2`, not one fixed `a`), so a witness computation is not
an option. Instead `n = 6` is closed by a genuinely new (if elementary) direct argument: the
explicit closed form `Phi 6 a b = a² - ab + b²` (`Phi_six_eq`, derived from mathlib's
`Polynomial.cyclotomic_six` via the real-valued division bridge) satisfies
`a² - ab + b² > 6` whenever `a - b ≥ 2`, `b ≥ 1` — STRICTLY sharper than the generic totient
lower bound at `n = 6` (`(a-b)² < Phi 6 a b`, which only gives `Phi 6 a b > 4`, not `> 6`).
Combined with the intrinsic-prime valuation bound (`t ≤ 1`, both parities of the intrinsic
prime `p ∈ {2, 3}`), this directly rules out `n = 6` being an obstruction, for every member of
the family at once.

## What THIS FILE proves (real, sorry-free)

* `padicValInt_Phi_intrinsic_two_le`: the general-`b` port of `ZsygmondyEvenPrime.
  padicValInt_cyclotomic_intrinsic_two_le` (even-prime intrinsic valuation bound `≤ 1`, for
  `n ≠ 2`). This was the genuinely new (non-mechanical) piece flagged as item (4) in
  `ZsygmondyExceptionalEndgameGeneral`'s "What is NOT closed here" list — it turned out to be
  a direct transplant of the `b = 1` proof (`Zsygmondy2adicLTE.v2_pow_sub_pow_even` was
  already stated for general odd naturals `a > b`, not `b = 1`-specialized).

* `Phi_two_eq`, `Phi_six_eq`: explicit closed forms `Phi 2 a b = a + b`,
  `Phi 6 a b = a² - ab + b²`, via the real division bridge and mathlib's `cyclotomic_two` /
  `cyclotomic_six`.

* `primitive_prime_exists_of_size_general`: the general-`b` port of `ZsygmondyEvenPrime.
  primitive_prime_exists_of_size` (Zsygmondy existence for ALL `n ≥ 2`, given the size
  hypothesis `n ≤ (a-b)^φ(n)` and the single explicit `n = 2` carve-out).

* `primitive_prime_exists_six_of_gap_two`: `n = 6` closed directly (no size hypothesis) for
  every `a - b ≥ 2`, `b ≥ 1`, coprime.

* `zsygmondy_general_of_gap_two`: **THE CAPSTONE.** For every `n ≥ 2`, coprime integers
  `a > b ≥ 1` with `a - b ≥ 2`, and the single explicit `n = 2` carve-out (`a + b` a power of
  two), `a^n - b^n` has a primitive prime divisor. Unconditional — no `n = 6` exclusion, no
  restriction to odd `n`, no restriction on the size of the gap `a - b` beyond `≥ 2`.

Combined with the pre-existing closure of `a - b = 1` (`ZsygmondyExceptionalCapstoneGeneral.
primitive_prime_exists_succ_of_b_ge_two` for `b ≥ 2`, plus the classical `b = 1` corpus
`ZsygmondyBaseThree.zsygmondy_base_one_full`), this closes the FULL general two-variable
Zsygmondy existence theorem for every coprime `a > b ≥ 1`, modulo final assembly (not
attempted in this file — see the closing remark below).
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHomogeneousCyclotomicFactor
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExistsGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyLTEGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExceptionalEndgameGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactorGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridgeGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyBaseThree
import Propositio.NumberTheory.Zsygmondy.Zsygmondy2adicLTE
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.IsPrimePow

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyGeneralGapTwo

/-! ### The even-prime intrinsic valuation bound, general `b` (the genuinely new item) -/

/-- **Even-prime intrinsic valuation bound, general `b`.** For `n ≥ 2`, `n ≠ 2`, integers
`1 ≤ b < a`, `IsCoprime a b`, and `2 ∣ Phi n a b`: the `2`-adic valuation of `Phi n a b` is at
most `1`. The general-`b` port of `ZsygmondyEvenPrime.padicValInt_cyclotomic_intrinsic_two_le`
— a direct transplant through `Zsygmondy2adicLTE.v2_pow_sub_pow_even` (already stated for
general odd naturals `a > b`) and the `prod_Phi_eq`-based homogeneous divisibility, mirroring
`ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one`'s odd-prime port. -/
theorem padicValInt_Phi_intrinsic_two_le
    {n : ℕ} (hn : 1 < n) (hn2 : n ≠ 2) {a b : ℤ} (hb : 1 ≤ b) (hab : b < a)
    (hcop : IsCoprime a b) (hpc : (2 : ℤ) ∣ Phi n a b) :
    padicValInt 2 (Phi n a b) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : 0 < n := by omega
  obtain ⟨hpa, hpb⟩ := ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi hn0 hcop hpc
  have hb0 : (0 : ℤ) ≤ b := by omega
  have hpow_lt : ∀ s : ℕ, 1 ≤ s → b ^ s < a ^ s := by
    intro s hs
    exact pow_lt_pow_left₀ hab hb0 (by omega)
  -- order of `a * b⁻¹` mod `2` is `1` (units of `ZMod 2` are trivial)
  have hr0 : (a : ZMod 2) * (b : ZMod 2)⁻¹ ≠ 0 := by
    have ha0 : (a : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hbz : (b : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
    exact mul_ne_zero ha0 (inv_ne_zero hbz)
  have he1 : orderOf ((a : ZMod 2) * (b : ZMod 2)⁻¹) = 1 :=
    Nat.dvd_one.mp (by simpa using ZMod.orderOf_dvd_card_sub_one hr0)
  -- structure: `n = 2 ^ k`
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 a b hpb hpc
  rw [he1, one_mul] at hk
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k
    · rw [pow_zero] at hk; omega
    · rw [pow_one] at hk; exact hn2 hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  set m : ℕ := 2 ^ (j + 1) with hm
  have hmpos : 0 < m := pow_pos (by norm_num) _
  have hmn : n = m * 2 := by rw [hk, hm]; ring
  have hn_ne : n ≠ 0 := by omega
  have hm_ne : m ≠ 0 := by omega
  have hn_even : Even n := ⟨m, by omega⟩
  have hm_even : Even m := ⟨2 ^ j, by rw [hm]; ring⟩
  -- naturals `qa = a.toNat`, `qb = b.toNat`, both odd, `qb < qa`
  set qa : ℕ := a.toNat with hqadef
  set qb : ℕ := b.toNat with hqbdef
  have hqa : (qa : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hqb : (qb : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hqab : qb < qa := by
    have : (qb : ℤ) < (qa : ℤ) := by rw [hqa, hqb]; omega
    exact_mod_cast this
  have hqa_ndvd : ¬ (2 ∣ qa) := by
    intro h
    exact hpa (by rw [← hqa]; exact_mod_cast h)
  have hqb_ndvd : ¬ (2 ∣ qb) := by
    intro h
    exact hpb (by rw [← hqb]; exact_mod_cast h)
  have hqaodd : Odd qa := by rw [Nat.odd_iff]; omega
  have hqbodd : Odd qb := by rw [Nat.odd_iff]; omega
  -- bridge: `padicValInt 2` on `ℤ` matches `padicValNat 2` on `ℕ` for `a^e - b^e`
  have bridge : ∀ e : ℕ, 1 ≤ e →
      padicValInt 2 (a ^ e - b ^ e) = padicValNat 2 (qa ^ e - qb ^ e) := by
    intro e he
    have hqe : qb ^ e < qa ^ e := Nat.pow_lt_pow_left hqab (by omega)
    have hcast : a ^ e - b ^ e = ((qa ^ e - qb ^ e : ℕ) : ℤ) := by
      rw [Nat.cast_sub hqe.le, Nat.cast_pow, Nat.cast_pow, hqa, hqb]
    rw [hcast]
    exact padicValInt.of_nat
  -- 2-adic even LTE for exponents `n` and `m`
  have hVn : padicValNat 2 (qa ^ n - qb ^ n)
      = padicValNat 2 (qa - qb) + padicValNat 2 (qa + qb) + padicValNat 2 n - 1 :=
    Zsygmondy2adicLTE.v2_pow_sub_pow_even hqaodd hqbodd hqab hn_ne hn_even
  have hVm : padicValNat 2 (qa ^ m - qb ^ m)
      = padicValNat 2 (qa - qb) + padicValNat 2 (qa + qb) + padicValNat 2 m - 1 :=
    Zsygmondy2adicLTE.v2_pow_sub_pow_even hqaodd hqbodd hqab hm_ne hm_even
  have hbn : padicValInt 2 (a ^ n - b ^ n) = padicValNat 2 (qa ^ n - qb ^ n) := bridge n (by omega)
  have hbm : padicValInt 2 (a ^ m - b ^ m) = padicValNat 2 (qa ^ m - qb ^ m) := bridge m hmpos
  have hpv_n : padicValNat 2 n = j + 2 := by rw [hk, padicValNat.prime_pow]
  have hpv_m : padicValNat 2 m = j + 1 := by rw [hm, padicValNat.prime_pow]
  -- homogeneous divisibility `(a^m - b^m) * Phi n a b ∣ a^n - b^n`, via `prod_Phi_eq`
  have hmn_dvd : m ∣ n := ⟨2, hmn⟩
  have hmltn : m < n := by
    rw [hmn]; exact (Nat.lt_mul_iff_one_lt_right hmpos).mpr (by norm_num)
  have hsub_div : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn0.ne' hmn_dvd
  have hn_notin : n ∉ m.divisors := by
    rw [Nat.mem_divisors]
    rintro ⟨hnm, _⟩
    exact absurd (Nat.le_of_dvd hmpos hnm) (by omega)
  have hins_sub : insert n m.divisors ⊆ n.divisors :=
    Finset.insert_subset (Nat.mem_divisors_self n hn0.ne') hsub_div
  have hprod_dvd :
      (∏ d ∈ insert n m.divisors, Phi d a b) ∣ ∏ d ∈ n.divisors, Phi d a b :=
    Finset.prod_dvd_prod_of_subset _ _ (fun d => Phi d a b) hins_sub
  rw [Finset.prod_insert hn_notin, ← prod_Phi_eq m hmpos a b,
    ← prod_Phi_eq n hn0 a b] at hprod_dvd
  have hdvd_eval : (a ^ m - b ^ m) * Phi n a b ∣ a ^ n - b ^ n := by
    rw [mul_comm]; exact hprod_dvd
  -- non-vanishing
  have hxne : a ^ m - b ^ m ≠ 0 := sub_ne_zero.mpr (hpow_lt m hmpos).ne'
  have hyne : a ^ n - b ^ n ≠ 0 := sub_ne_zero.mpr (hpow_lt n (by omega)).ne'
  have hCne : Phi n a b ≠ 0 := by
    intro h0
    have hpos := ZsygmondyPrimitiveExistsGeneral.one_lt_natAbs_Phi hn hb hab
    rw [h0] at hpos; simp at hpos
  -- additivity and monotonicity of `v_2`
  have hval_mul : padicValInt 2 ((a ^ m - b ^ m) * Phi n a b)
      = padicValInt 2 (a ^ m - b ^ m) + padicValInt 2 (Phi n a b) :=
    padicValInt.mul hxne hCne
  have hmono : padicValInt 2 ((a ^ m - b ^ m) * Phi n a b)
      ≤ padicValInt 2 (a ^ n - b ^ n) := by
    have hd : (2 : ℤ) ^ padicValInt 2 ((a ^ m - b ^ m) * Phi n a b) ∣ a ^ n - b ^ n :=
      (padicValInt_dvd _).trans hdvd_eval
    rcases (padicValInt_dvd_iff _ _).mp hd with h | h
    · exact absurd h hyne
    · exact h
  omega

/-! ### Explicit closed forms `Phi 2 a b` and `Phi 6 a b` -/

/-- `Phi 2 a b = a + b`, via `Polynomial.cyclotomic_two` and the real division bridge. -/
theorem Phi_two_eq (a b : ℤ) (hb : b ≠ 0) : Phi 2 a b = a + b := by
  have hR := ZsygmondyExceptionalEndgameGeneral.Phi_eq_cyclotomic_eval_div_real 2 a b hb
  have htot2 : Nat.totient 2 = 1 := by decide
  rw [htot2, pow_one, Polynomial.cyclotomic_two] at hR
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at hR
  have heq : ((a : ℝ) / (b : ℝ) + 1) * (b : ℝ) = (a : ℝ) + (b : ℝ) := by
    have hbne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    field_simp
  rw [heq] at hR
  have hcast : ((a + b : ℤ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
  rw [← hcast] at hR
  exact_mod_cast hR

/-- `Phi 6 a b = a² - a·b + b²`, via `Polynomial.cyclotomic_six` and the real division bridge.
-/
theorem Phi_six_eq (a b : ℤ) (hb : b ≠ 0) : Phi 6 a b = a ^ 2 - a * b + b ^ 2 := by
  have hR := ZsygmondyExceptionalEndgameGeneral.Phi_eq_cyclotomic_eval_div_real 6 a b hb
  have htot6 : Nat.totient 6 = 2 := by decide
  rw [htot6, Polynomial.cyclotomic_six] at hR
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow] at hR
  have heq : (((a : ℝ) / (b : ℝ)) ^ 2 - (a : ℝ) / (b : ℝ) + 1) * (b : ℝ) ^ 2
      = (a : ℝ) ^ 2 - (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 := by
    have hbne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    field_simp
  rw [heq] at hR
  have hcast : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) = (a : ℝ) ^ 2 - (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 := by
    push_cast; ring
  rw [← hcast] at hR
  exact_mod_cast hR

/-! ### The size-route existence theorem, general `b` (port of `ZsygmondyEvenPrime.
primitive_prime_exists_of_size`) -/

/-- **Zsygmondy existence for all `n ≥ 2`, general `b`, given the size hypothesis.** The
general-`b` port of `ZsygmondyEvenPrime.primitive_prime_exists_of_size`. For `n ≥ 2`, coprime
integers `1 ≤ b < a`, the size hypothesis `n ≤ (a - b) ^ φ(n)`, and the explicit carve-out
`¬ (n = 2 ∧ a + b` a power of two`)`: `a^n - b^n` has a primitive prime divisor. -/
theorem primitive_prime_exists_of_size_general {n : ℕ} (hn : 1 < n) {a b : ℤ}
    (hb : 1 ≤ b) (hab : b < a) (hcop : IsCoprime a b)
    (hsize : (n : ℤ) ≤ (a - b) ^ Nat.totient n)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, (a + b).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_contra hcon
  push_neg at hcon
  have hpp : IsPrimePow (Phi n a b).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_exists_of_not_isPrimePow_general
        hn hb hab hcop h
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, t, hp, ht, hpt⟩ := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  set M := (Phi n a b).natAbs with hMdef
  have hpM : p ∣ M := hpt ▸ dvd_pow_self p (by omega : t ≠ 0)
  have hpc : (p : ℤ) ∣ Phi n a b :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM)
  have hpn : p ∣ n := by
    by_contra hpn
    obtain ⟨h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_divisor_of_dvd_Phi hn hcop hpc hpn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  have hvalM : padicValInt p (Phi n a b) = t := by
    have h1 : padicValInt p (Phi n a b) = padicValNat p M := by rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · subst hp2
      by_cases hn2 : n = 2
      · exfalso
        apply hexc
        refine ⟨hn2, t, ?_⟩
        have hΦ : Phi n a b = a + b := by
          rw [hn2]; exact Phi_two_eq a b (by omega)
        rw [hMdef, hΦ] at hpt
        exact hpt.symm
      · have hval_le := padicValInt_Phi_intrinsic_two_le hn hn2 hb hab hcop hpc
        rw [hvalM] at hval_le
        omega
    · have hval_le :=
        ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one hn hpodd hb hab hcop hpn hpc
      rw [hvalM] at hval_le
      omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hpn_le : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hlb0 : (a - b) ^ Nat.totient n < Phi n a b :=
    ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound hn hb hab
  have hgap_pos : (0 : ℤ) < a - b := by omega
  have hPhi_pos : 0 < Phi n a b :=
    lt_trans (pow_pos hgap_pos (Nat.totient n)) hlb0
  have hlb : (a - b) ^ Nat.totient n < (M : ℤ) := by
    rw [hMdef, Int.natAbs_of_nonneg hPhi_pos.le]; exact hlb0
  have hMpZ : (M : ℤ) = (p : ℤ) := by rw [hMp]
  have hpnZ : (p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hpn_le
  rw [hMpZ] at hlb
  linarith [hsize, hlb, hpnZ]

/-! ### The `n = 6` residual, closed directly for every `a - b ≥ 2` -/

/-- **`n = 6` closed directly, for every `a - b ≥ 2`.** The size hypothesis of
`primitive_prime_exists_of_size_general` (`6 ≤ (a-b)^φ(6) = (a-b)²`) genuinely FAILS at
`a - b = 2` (`4 < 6`) — the same boundary failure that forced `ZsygmondyBaseThree` to patch
`(a,n) = (3,6)` with an explicit witness. Here the whole family is closed at once by the
SHARPER direct bound `Phi_six_eq`: `a² - ab + b² > 6` whenever `a - b ≥ 2`, `b ≥ 1`
(strictly better than the generic totient lower bound `(a-b)² < Phi 6 a b`, which only gives
`Phi 6 a b > 4`). -/
theorem primitive_prime_exists_six_of_gap_two {a b : ℤ}
    (hb : 1 ≤ b) (hgap : b + 2 ≤ a) (hcop : IsCoprime a b) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ 6 - b ^ 6 ∧
      ∀ m, 0 < m → m < 6 → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_contra hcon
  push_neg at hcon
  have hn : (1 : ℕ) < 6 := by norm_num
  have hab : b < a := by omega
  have hpp : IsPrimePow (Phi 6 a b).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_exists_of_not_isPrimePow_general
        hn hb hab hcop h
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, t, hp, ht, hpt⟩ := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  set M := (Phi 6 a b).natAbs with hMdef
  have hpM : p ∣ M := hpt ▸ dvd_pow_self p (by omega : t ≠ 0)
  have hpc : (p : ℤ) ∣ Phi 6 a b :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM)
  have hpn : p ∣ 6 := by
    by_contra hpn
    obtain ⟨h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_divisor_of_dvd_Phi hn hcop hpc hpn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  have hvalM : padicValInt p (Phi 6 a b) = t := by
    have h1 : padicValInt p (Phi 6 a b) = padicValNat p M := by rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · subst hp2
      have hn2 : (6 : ℕ) ≠ 2 := by norm_num
      have hval_le := padicValInt_Phi_intrinsic_two_le hn hn2 hb hab hcop hpc
      rw [hvalM] at hval_le
      omega
    · have hval_le :=
        ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one hn hpodd hb hab hcop hpn hpc
      rw [hvalM] at hval_le
      omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hpn_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpn
  have hPhi6 : Phi 6 a b = a ^ 2 - a * b + b ^ 2 := Phi_six_eq a b (by omega)
  have hgt6 : (6 : ℤ) < a ^ 2 - a * b + b ^ 2 := by nlinarith [hb, hgap]
  have hnn : (0 : ℤ) ≤ a ^ 2 - a * b + b ^ 2 := by nlinarith [hb, hgap]
  have hMval : (M : ℤ) = a ^ 2 - a * b + b ^ 2 := by
    rw [hMdef, hPhi6, Int.natAbs_of_nonneg hnn]
  have hMle6 : (M : ℤ) ≤ 6 := by
    rw [hMp]
    exact_mod_cast hpn_le
  rw [hMval] at hMle6
  linarith [hgt6, hMle6]

/-! ### The capstone: general `n`, general `a - b ≥ 2` -/

/-- **Zsygmondy's theorem, general `b`, non-consecutive case (`a - b ≥ 2`) — CLOSED for all
`n ≥ 2`.** For every `n ≥ 2`, coprime integers `a > b ≥ 1` with `a - b ≥ 2`, and the single
explicit carve-out `¬ (n = 2 ∧ a + b` a power of two`)`, `a^n - b^n` has a *primitive* prime
divisor: a prime `p` dividing `a^n - b^n` but none of `a^m - b^m` for `0 < m < n`.

Unconditional: no restriction to odd `n`, no restriction on the size of the gap beyond `≥ 2`,
no `n = 6` exclusion (closed directly by `primitive_prime_exists_six_of_gap_two`). Combined
with the pre-existing closure of `a - b = 1`
(`ZsygmondyExceptionalCapstoneGeneral.primitive_prime_exists_succ_of_b_ge_two` for `b ≥ 2`,
the classical `b = 1` corpus `ZsygmondyBaseThree.zsygmondy_base_one_full` for `a = b + 1`),
this closes the full general two-variable Zsygmondy *existence* theorem for every coprime
`a > b ≥ 1` — final assembly into one combined statement is not attempted in this file. -/
theorem zsygmondy_general_of_gap_two {n : ℕ} (hn : 1 < n) {a b : ℤ}
    (hb : 1 ≤ b) (hgap : b + 2 ≤ a) (hcop : IsCoprime a b)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, (a + b).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_cases hn6 : n = 6
  · subst hn6
    exact primitive_prime_exists_six_of_gap_two hb hgap hcop
  · have hab : b < a := by omega
    have hn_le : (n : ℤ) ≤ 2 ^ Nat.totient n := by
      have h := ZsygmondyBaseThree.totient_growth_two_ne_six n hn6
      exact_mod_cast h
    have h2 : (2 : ℤ) ≤ a - b := by omega
    have hsize : (n : ℤ) ≤ (a - b) ^ Nat.totient n :=
      le_trans hn_le (pow_le_pow_left₀ (by norm_num) h2 (Nat.totient n))
    exact primitive_prime_exists_of_size_general hn hb hab hcop hsize hexc

end ZsygmondyGeneralGapTwo
