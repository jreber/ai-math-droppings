/-
Zsygmondy's theorem, the general (non-consecutive) two-variable case, for ODD `n`.

## Task

Per `docs/kb/conjectures/conj-2026-07-12-006.json`: the full two-variable Zsygmondy theorem's
*consecutive* case (`a = b + 1`) is already fully closed for all `b ≥ 1`
(`ZsygmondyExceptionalEndgameGeneral` + `ZsygmondyPrimitiveExistsGeneral` +
`ZsygmondyLTEGeneral`, assembled implicitly the same way `ZsygmondyBaseTwoEndgame` assembles
the `a = 2, b = 1` case). The genuinely open gap is the *general* case: coprime `a > b ≥ 1`
with `a - b ≥ 2`.

## What THIS FILE finds and proves

**Key finding**: the `a = b + 1` endgame's numeric margins (`ZsygmondyExceptionalEndgameGeneral`'s
Layers 3–4, `no_k_ge_two_general` / `margin_ge_two` / `k_eq_one_impossible_of_b_ge_two`) do
*not* use `a = b + 1` in any essential way — they generalize to ANY gap `a - b ≥ 1` (Layer 3)
or `a - b ≥ 2` (Layer 4), and in fact become STRICTLY SIMPLER once the gap is `≥ 2`: Layer 4's
`b ≥ 2` side-restriction (needed at gap `1` to avoid the classical `n = 6` exception) is no
longer needed at all, and the item flagged in `ZsygmondyExceptionalEndgameGeneral`'s "what is
NOT closed" list as "the genuine, needs the real geometric-sum bound" `e = 1` / prime-power-`n`
case (`ratio_ne_one_of_succ` is FALSE for gap `≥ 2`, since primes dividing `a - b` give `e = 1`)
turns out to be the ONE genuinely new piece needed here — but it too closes cleanly for
gap `≥ 2`, via the *generic* totient/height lower bound `Phi_totient_lower_bound` (no
delicate geometric-sum evaluation needed, because `(a-b)^φ(n) ≥ 2^φ(n)` is already a real,
nonvacuous bound once `a - b ≥ 2`, unlike the gap-`1` case where `(a-b)^φ(n) = 1^φ(n) = 1` is
useless and forced the much harder `ZsygmondyBaseTwoEndgame`/`ZsygmondyBaseTwo` geometric-sum
route).

Restricting to ODD `n ≥ 3` sidesteps the one remaining hard piece of the *even*-`n` theory
(the bivariate/general-`b` port of the `p = 2` intrinsic-valuation LTE bound,
`ZsygmondyEvenPrime.padicValInt_cyclotomic_intrinsic_two_le`, NOT attempted here — see the
docstring of `primitive_prime_exists_gap_two_odd` below): for odd `n`, every prime dividing
`n` is odd, so the odd-prime LTE bound (`ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one`,
already general in `a, b` with no `a = b+1` restriction) is all that is needed.

**Result**: `primitive_prime_exists_gap_two_odd` — for coprime integers `a > b ≥ 1` with
`a - b ≥ 2`, and ODD `n ≥ 3`, `a^n - b^n` has a primitive prime divisor, UNCONDITIONALLY (no
exceptions at all — matching the classical fact that every Zsygmondy exception has either
`a - b = 1` or `n` even).

## What is NOT closed here

The EVEN-`n` case, which needs the general-`b` bivariate port of the `p = 2` intrinsic LTE
bound (flagged as "the piece most likely to need genuinely new work" in
`ZsygmondyExceptionalEndgameGeneral`'s docstring, item 4) — this file does not attempt it.
Combined with the (separately closed) `a = b + 1` case, the full general-`b` Zsygmondy theorem
now has ONLY the even-`n` gap remaining, for every value of `a - b` (both `= 1` and `≥ 2`).
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExceptionalEndgameGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExistsGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyLTEGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactorGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridgeGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHomogeneousCyclotomicFactor
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.IsPrimePow

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyGapTwoOddCase

/-! ### Step 0: the general-gap numeric margin, replacing `a = b + 1` -/

/-- **General-gap power bound.** For ANY integers `a > b ≥ 1` (any gap `a - b ≥ 1`, not just
`a = b + 1`) and any `p : ℕ`: `p ≤ a^p - b^p`. Generalizes
`ZsygmondyExceptionalEndgameGeneral.pow_sub_pow_ge_of_succ` (specific to `a = b + 1`) via
monotonicity of `x ↦ x^p` in the base: since `a ≥ b + 1 > 0`, `a^p ≥ (b+1)^p`. -/
theorem pow_sub_pow_ge_general {a b : ℤ} (hb : 1 ≤ b) (hab : b + 1 ≤ a) (p : ℕ) :
    (p : ℤ) ≤ a ^ p - b ^ p := by
  have hmono : (b + 1) ^ p ≤ a ^ p := pow_le_pow_left₀ (by linarith) hab p
  have hbase := ZsygmondyExceptionalEndgameGeneral.pow_sub_pow_ge_of_succ hb p
  linarith

/-! ### Layer 3, generalized off `a = b + 1` to ANY gap `a - b ≥ 1` -/

/-- **Layer 3, generalized.** For ANY coprime-gap pair `a > b ≥ 1` (not just `a = b + 1`),
`n ≥ 2`, `p` prime with `p² ∣ n`: `Phi n a b = p` is impossible. Same proof shape as
`ZsygmondyExceptionalEndgameGeneral.no_k_ge_two_general`, with the numeric margin replaced by
the general-gap version `pow_sub_pow_ge_general`. -/
theorem no_k_ge_two_gap {n p : ℕ} {a b : ℤ} (hb : 1 ≤ b) (hab : b + 1 ≤ a) (hn : 1 < n)
    (hp : p.Prime) (hp2 : p * p ∣ n) (hMeq : Phi n a b = (p : ℤ)) : False := by
  obtain ⟨m, hm⟩ := hp2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso; rw [h0, Nat.mul_zero] at hm; omega
    · exact h
  set n' : ℕ := p * m with hn'def
  have hnn' : n = n' * p := by rw [hn'def, hm]; ring
  have hpn' : p ∣ n' := ⟨m, hn'def⟩
  have hn'gt1 : 1 < n' := by
    rw [hn'def]
    have hple : p ≤ p * m := Nat.le_mul_of_pos_right p hmpos
    have := hp.one_lt
    omega
  have hbne : b ≠ 0 := by omega
  have heq : Phi n a b = Phi n' (a ^ p) (b ^ p) := by
    rw [hnn']; exact ZsygmondyExceptionalEndgameGeneral.Phi_expand_eq_of_dvd hp hpn' a b hbne
  have hMeq' : Phi n' (a ^ p) (b ^ p) = (p : ℤ) := by rw [← heq]; exact hMeq
  have hab' : b ^ p < a ^ p := by
    have hab2 : b < a := by omega
    have hb0 : (0 : ℤ) ≤ b := by omega
    exact pow_lt_pow_left₀ hab2 hb0 hp.ne_zero
  have hb1' : (1 : ℤ) ≤ b ^ p := one_le_pow₀ hb
  have hlb := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound (n := n') hn'gt1 hb1' hab'
  rw [hMeq'] at hlb
  have hmargin : (p : ℤ) ≤ a ^ p - b ^ p := pow_sub_pow_ge_general hb hab p
  have hn'pos : 0 < n' := Nat.zero_lt_one.trans hn'gt1
  have hexpge1 : 1 ≤ Nat.totient n' := Nat.totient_pos.mpr hn'pos
  have hbase_pos : (1 : ℤ) ≤ a ^ p - b ^ p := by omega
  have hpowge : a ^ p - b ^ p ≤ (a ^ p - b ^ p) ^ (Nat.totient n') :=
    le_self_pow₀ hbase_pos (by omega)
  have hfin : (p : ℤ) ≤ (a ^ p - b ^ p) ^ (Nat.totient n') := le_trans hmargin hpowge
  linarith [hlb, hfin]

/-! ### Layer 4, generalized to gap ≥ 2 — SIMPLER than the `a = b + 1` case (no `b ≥ 2`
side-condition needed at all). -/

/-- **Uniform gap-≥-2 margin.** For any integers `a ≥ b + 2` (`b ≥ 1`), and `p ≥ 3`:
`(a + b) * p < a^p - b^p`. Generalizes `ZsygmondyExceptionalEndgameGeneral.margin_ge_two`
(the `a = b + 1` file's margin, which needed `b ≥ 2`) to any base gap `a - b ≥ 2` — and,
the key finding of this file, needs NO restriction on `b` at all: `b = 1` is fine here,
unlike the gap-`1` case where `b = 1` is exactly the classical `n = 6` exception. -/
theorem margin_gap_two {a b : ℤ} (hb : 1 ≤ b) (hab : b + 2 ≤ a) :
    ∀ p : ℕ, 3 ≤ p → (a + b) * (p : ℤ) < a ^ p - b ^ p := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
    have hfact : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    have hab2 : (2 : ℤ) ≤ a - b := by omega
    have hann : (0 : ℤ) ≤ a := by omega
    have hbnn : (0 : ℤ) ≤ b := by omega
    have hXnn : (0 : ℤ) ≤ a ^ 2 + a * b + b ^ 2 := by positivity
    have hprod : (0 : ℤ) ≤ (a - b - 2) * (a ^ 2 + a * b + b ^ 2) :=
      mul_nonneg (by linarith) hXnn
    have hstep1 : (2 : ℤ) * a ^ 2 ≤ a ^ 3 - b ^ 3 := by
      rw [hfact]
      nlinarith [hprod, mul_nonneg hann hbnn, sq_nonneg b]
    have hble : b ≤ a - 2 := by omega
    have ha3 : (3 : ℤ) ≤ a := by omega
    have hstep2 : (a + b) * 3 ≤ (2 * a - 2) * 3 := by nlinarith [hble]
    have hstep3 : (2 * a - 2) * 3 < 2 * a ^ 2 := by nlinarith [ha3]
    have hc3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
    rw [hc3]
    linarith [hstep1, hstep2, hstep3]
  | succ n hn ih =>
    have hrec : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    have hapos : (0 : ℤ) < a := by omega
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast, hrec]
    have hstep : a * ((a + b) * (n : ℤ)) < a * (a ^ n - b ^ n) :=
      mul_lt_mul_of_pos_left ih hapos
    have hn3 : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have han1 : (2 : ℤ) ≤ a - 1 := by omega
    have hgoal_reduce : (a + b) * ((n : ℤ) + 1) ≤ a * ((a + b) * (n : ℤ)) := by
      have hfactor : a * ((a + b) * (n : ℤ)) - (a + b) * ((n : ℤ) + 1)
          = (a + b) * ((n : ℤ) * (a - 1) - 1) := by ring
      have hprod2 : (6 : ℤ) ≤ (n : ℤ) * (a - 1) := by nlinarith [hn3, han1]
      have hnonneg1 : (0 : ℤ) ≤ (n : ℤ) * (a - 1) - 1 := by linarith
      have hnonneg2 : (0 : ℤ) ≤ a + b := by omega
      have hmul := mul_nonneg hnonneg2 hnonneg1
      linarith [hfactor, hmul]
    have habnn : (0 : ℤ) ≤ (a - b) * b ^ n := mul_nonneg (by omega) (pow_nonneg (by omega) n)
    linarith [hstep, hgoal_reduce, habnn]

/-- **The `k = 1` case is impossible for gap ≥ 2.** For `a ≥ b + 2` (`b ≥ 1`), `q > 1`, `p`
prime with `p ∤ q` and `p ≥ 3`: `Phi (q*p) a b = p` is impossible. Direct generalization of
`ZsygmondyExceptionalEndgameGeneral.k_eq_one_impossible_of_b_ge_two`, replacing
`margin_ge_two` by `margin_gap_two` and `b + 1` by a general `a`. -/
theorem k_eq_one_impossible_gap {q p : ℕ} {a b : ℤ} (hb : 1 ≤ b) (hab : b + 2 ≤ a)
    (hq1 : 1 < q) (hp : p.Prime) (hp3 : 3 ≤ p) (hqp : ¬ p ∣ q)
    (hMeq : Phi (q * p) a b = (p : ℤ)) : False := by
  have hbne : b ≠ 0 := by omega
  have hexpand : Phi (q * p) a b * Phi q a b = Phi q (a ^ p) (b ^ p) :=
    ZsygmondyExceptionalEndgameGeneral.Phi_expand_eval_eq_mul_of_not_dvd hp hqp a b hbne
  rw [hMeq] at hexpand
  have hab' : b < a := by omega
  have hPhiqab_pos : 0 < Phi q a b := by
    have hlbq := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound (n := q) hq1 hb hab'
    have hnn : (0 : ℤ) ≤ (a - b) ^ Nat.totient q := pow_nonneg (by omega) (Nat.totient q)
    linarith
  have hubq : Phi q a b ≤ (a + b) ^ Nat.totient q :=
    ZsygmondyExceptionalEndgameGeneral.Phi_totient_upper_bound q hb hab'
  have hab'' : b ^ p < a ^ p := by
    have hb0 : (0 : ℤ) ≤ b := by omega
    exact pow_lt_pow_left₀ hab' hb0 hp.ne_zero
  have hb1' : (1 : ℤ) ≤ b ^ p := one_le_pow₀ hb
  have hlbqp := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound (n := q) hq1 hb1' hab''
  rw [← hexpand] at hlbqp
  have hchain : (a ^ p - b ^ p) ^ Nat.totient q < (p : ℤ) * (a + b) ^ Nat.totient q := by
    have hpnn : (0 : ℤ) ≤ (p : ℤ) := by positivity
    calc (a ^ p - b ^ p) ^ Nat.totient q < (p : ℤ) * Phi q a b := hlbqp
      _ ≤ (p : ℤ) * (a + b) ^ Nat.totient q := mul_le_mul_of_nonneg_left hubq hpnn
  have hmargin : (a + b) * (p : ℤ) < a ^ p - b ^ p := margin_gap_two hb hab p hp3
  have hqe1 : Nat.totient q ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
  have hab_pos : (0 : ℤ) ≤ (a + b) * (p : ℤ) := by
    have : (0 : ℤ) < a + b := by omega
    positivity
  have hpowlt : ((a + b) * (p : ℤ)) ^ Nat.totient q < (a ^ p - b ^ p) ^ Nat.totient q :=
    pow_lt_pow_left₀ hmargin hab_pos hqe1
  have hpoweq : ((a + b) * (p : ℤ)) ^ Nat.totient q =
      (a + b) ^ Nat.totient q * (p : ℤ) ^ Nat.totient q := by rw [mul_pow]
  rw [hpoweq] at hpowlt
  have hchain2 : (a + b) ^ Nat.totient q * (p : ℤ) ^ Nat.totient q <
      (p : ℤ) * (a + b) ^ Nat.totient q := lt_trans hpowlt hchain
  have habpos : (0 : ℤ) < (a + b) ^ Nat.totient q := by
    have : (0 : ℤ) < a + b := by omega
    positivity
  have hpcancel : (p : ℤ) ^ Nat.totient q < (p : ℤ) := by
    have hcomm : (p : ℤ) * (a + b) ^ Nat.totient q = (a + b) ^ Nat.totient q * (p : ℤ) := by ring
    rw [hcomm] at hchain2
    exact lt_of_mul_lt_mul_left hchain2 habpos.le
  have hp1lt : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hiff := pow_lt_pow_iff_right₀ (a := (p : ℤ)) (n := Nat.totient q) (m := 1) hp1lt
  rw [pow_one] at hiff
  have hlt1 : Nat.totient q < 1 := hiff.mp hpcancel
  omega

/-! ### The NEW piece: the `e = 1` / prime-power-`n` case, for gap ≥ 2

For `a = b + 1` this case never arises (`ratio_ne_one_of_succ`): no prime can divide the gap
`a - b = 1`. For gap `≥ 2` it is a genuinely live case (any prime dividing `a - b` forces
`e = 1`), but it closes cleanly via the GENERIC totient/height lower bound — no delicate
geometric-sum evaluation is needed, unlike the `a = 2, b = 1` case (`ZsygmondyBaseTwo`),
because `(a - b) ≥ 2` already makes `Phi_totient_lower_bound` a nonvacuous bound. -/

/-- **The prime-power-`n` case, gap ≥ 2.** For `a ≥ b + 2` (`b ≥ 1`), an odd prime `p`, and
`k ≥ 1`: `Phi (p^k) a b ≠ p`. This is the gap-`≥ 2` replacement for the `e = 1` branch that
`ZsygmondyExceptionalEndgameGeneral.prime_power_case_impossible_of_succ` closed (vacuously,
via `ratio_ne_one_of_succ`) for `a = b + 1` specifically. -/
theorem Phi_prime_power_ne_gap {p k : ℕ} {a b : ℤ} (hb : 1 ≤ b) (hab : b + 2 ≤ a)
    (hp : p.Prime) (hk : 1 ≤ k) : Phi (p ^ k) a b ≠ (p : ℤ) := by
  intro hMeq
  have hn2 : 1 < p ^ k :=
    calc 1 < p := hp.one_lt
      _ ≤ p ^ k := Nat.le_self_pow (by omega) p
  have hab' : b < a := by omega
  have hlb := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound (n := p ^ k) hn2 hb hab'
  rw [hMeq] at hlb
  have hd2 : (2 : ℤ) ≤ a - b := by omega
  have htot : Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) := Nat.totient_prime_pow hp (by omega)
  have htot_ge : p - 1 ≤ Nat.totient (p ^ k) := by
    rw [htot]
    have h1 : 1 ≤ p ^ (k - 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
    calc p - 1 = 1 * (p - 1) := by ring
      _ ≤ p ^ (k - 1) * (p - 1) := Nat.mul_le_mul_right _ h1
  have hpnat : p ≤ 2 ^ (p - 1) := by
    have hlt := Nat.lt_two_pow_self (n := p - 1)
    have := hp.one_lt
    omega
  have h2pow : (p : ℤ) ≤ (2 : ℤ) ^ (p - 1) := by exact_mod_cast hpnat
  have hpow_mono1 : (2 : ℤ) ^ (p - 1) ≤ (a - b) ^ (p - 1) := pow_le_pow_left₀ (by norm_num) hd2 _
  have hpow_mono2 : (a - b : ℤ) ^ (p - 1) ≤ (a - b) ^ (Nat.totient (p ^ k)) :=
    pow_le_pow_right₀ (by omega) htot_ge
  have hchain : (p : ℤ) ≤ (a - b) ^ (Nat.totient (p ^ k)) :=
    le_trans h2pow (le_trans hpow_mono1 hpow_mono2)
  linarith [hlb, hchain]

/-! ### The final assembly: unconditional existence for gap ≥ 2, odd `n` -/

/-- **Zsygmondy, general (non-consecutive) case, ODD `n`.** For coprime integers `a > b ≥ 1`
with gap `a - b ≥ 2`, and ODD `n ≥ 3`, the number `a^n - b^n` has a *primitive* prime
divisor — UNCONDITIONALLY, no exceptions (matching the classical fact that every Zsygmondy
exception has either `a - b = 1` or `n` even).

Restricting to odd `n` sidesteps the one remaining hard piece of the general theory: the
bivariate/general-`b` port of the `p = 2` intrinsic-valuation LTE bound
(`ZsygmondyEvenPrime.padicValInt_cyclotomic_intrinsic_two_le`), NOT attempted in this file —
for odd `n`, every prime dividing `n` is odd, so only the already-general odd-prime LTE bound
(`ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one`) is needed. -/
theorem primitive_prime_exists_gap_two_odd {a b : ℤ} (hb : 1 ≤ b) (hab : b + 2 ≤ a)
    (hcop : IsCoprime a b) {n : ℕ} (hn_odd : Odd n) (hn3 : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_contra hcon
  push_neg at hcon
  have hn : 1 < n := by omega
  have hab' : b < a := by omega
  have hpp : IsPrimePow (Phi n a b).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ :=
      ZsygmondyPrimitiveExistsGeneral.primitive_prime_exists_of_not_isPrimePow_general
        hn hb hab' hcop h
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
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · exfalso
      rw [hp2] at hpn
      have heven : Even n := even_iff_two_dvd.mpr hpn
      exact (Nat.not_odd_iff_even.mpr heven) hn_odd
    · exact hpodd
  obtain ⟨hpa, hpb⟩ :=
    ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi (by omega) hcop hpc
  have hval_le : padicValInt p (Phi n a b) ≤ 1 :=
    ZsygmondyLTEGeneral.padicValInt_Phi_intrinsic_le_one hn hpodd hb hab' hcop hpn hpc
  have hvalM : padicValInt p (Phi n a b) = t := by
    have h1 : padicValInt p (Phi n a b) = padicValNat p M := by rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by rw [hvalM] at hval_le; omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hpos : (0 : ℤ) < Phi n a b := by
    have hlb := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound hn hb hab'
    have hd0 : (0 : ℤ) < a - b := by omega
    have hpw : (0 : ℤ) < (a - b) ^ Nat.totient n := pow_pos hd0 _
    linarith
  have hMeq : Phi n a b = (p : ℤ) := by
    have hna := Int.natAbs_of_nonneg hpos.le
    rw [← hMdef, hMp] at hna
    linarith [hna]
  -- structure: n = e * p ^ k, e = ord_p(a * b⁻¹), p ∤ e
  obtain ⟨k, hk⟩ :=
    intrinsic_order_dvd_general (n := n) (p := p) (by omega)
      a b hpb hpc
  set e := orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) with hedef
  have hepos : 0 < e := orderOf_pos_of_not_dvd_general hpa hpb
  have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := by
    have ha0 : (a : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hb0z : (b : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
    exact mul_ne_zero ha0 (inv_ne_zero hb0z)
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hr0
  have hpe_not : ¬ p ∣ e := by
    intro hdvd
    have hle1 : e ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) he_dvd
    have hle2 : p ≤ e := Nat.le_of_dvd hepos hdvd
    have := hp.one_lt
    omega
  by_cases he1 : e = 1
  · -- n = p ^ k : the new prime-power case
    rw [he1, one_mul] at hk
    have hk1 : 1 ≤ k := by
      by_contra hklt
      push_neg at hklt
      interval_cases k
      rw [pow_zero] at hk
      omega
    have hMeq' : Phi (p ^ k) a b = (p : ℤ) := by rw [← hk]; exact hMeq
    exact Phi_prime_power_ne_gap hb hab hp hk1 hMeq'
  · -- e ≥ 2
    have he2 : 2 ≤ e := by omega
    have hk1 : 1 ≤ k := by
      by_contra hklt
      push_neg at hklt
      interval_cases k
      rw [pow_zero, mul_one] at hk
      rw [hk] at hpn
      exact hpe_not hpn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- k = 1 : Layer 4
      subst hj0
      simp only [pow_one] at hk
      have hMeq' : Phi (e * p) a b = (p : ℤ) := by rw [← hk]; exact hMeq
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases hpodd with ⟨m, hm⟩
        omega
      exact k_eq_one_impossible_gap hb hab (by omega : 1 < e) hp hp3 hpe_not hMeq'
    · -- k ≥ 2 : Layer 3
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hp2dvdn : p * p ∣ n := by
        clear_value e
        refine ⟨e * p ^ i, ?_⟩
        rw [hk, pow_succ, pow_succ]; ring
      exact no_k_ge_two_gap hb (by omega : b + 1 ≤ a) hn hp hp2dvdn hMeq

end ZsygmondyGapTwoOddCase
