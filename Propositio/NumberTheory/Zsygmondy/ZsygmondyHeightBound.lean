/-
Zsygmondy height / prime-power bound — the remaining analytic ingredients that feed
`primitive_prime_exists_of_not_isPrimePow` (in `ZsygmondyPrimitiveExists`).

The whole remaining gap of Zsygmondy's theorem was isolated there into the single
hypothesis `¬ IsPrimePow |Φ_n(a)|`.  This file supplies the two classical ingredients
that discharge that hypothesis, and chains them into a genuine, *unconditional*
existence theorem for odd `n` in an explicit size range.

* **(2a) Totient lower bound (integer form).** `cyclotomic_eval_totient_lower_bound`:
  for `n ≥ 2`, `a ≥ 2` (integer), `(a - 1) ^ φ(n) < |Φ_n(a)|`.  A direct integer
  repackaging of mathlib's `sub_one_pow_totient_lt_natAbs_cyclotomic_eval`.

* **(2b) Intrinsic prime valuation bound.** `padicValInt_cyclotomic_intrinsic_le_one`:
  for an ODD prime `p` with `p ∣ n` and `p ∣ Φ_n(a)` (`n ≥ 2`, `a ≥ 2`), the `p`-adic
  valuation `v_p(Φ_n(a)) ≤ 1`.  This is the height brick: the intrinsic part of `Φ_n(a)`
  carries a single factor of its (odd) intrinsic prime.  Proof: with `e = ord_p(a)`,
  the structure lemma gives `n = e·p^{j+1}`; lifting-the-exponent (`lte_odd_prime`) on
  the base `a^e` gives `v_p(a^n-1) = v_p(a^e-1) + (j+1)` and
  `v_p(a^{e p^j}-1) = v_p(a^e-1) + j`, while
  `(a^{e p^j}-1)·Φ_n(a) ∣ a^n-1`
  (`X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd`), so
  `v_p(a^{e p^j}-1) + v_p(Φ_n(a)) ≤ v_p(a^n-1)`, forcing `v_p(Φ_n(a)) ≤ 1`.

* **(3) Unconditional existence for odd `n` in a size range.**
  `primitive_prime_exists_of_odd_of_size`: for `n ≥ 2` odd, `a ≥ 2`, and
  `n ≤ (a - 1) ^ φ(n)`, the number `a^n - 1` has a primitive prime divisor.
  Proof: if not, `|Φ_n(a)|` is a prime power `p^t`.  Either `p ∤ n` — then `p` is itself
  a primitive prime divisor (contradiction) — or `p ∣ n`; since `n` is odd, `p` is odd, so
  (2b) gives `t = v_p(Φ_n(a)) ≤ 1`, whence `|Φ_n(a)| = p ≤ n`, contradicting the lower
  bound `(a-1)^φ(n) < |Φ_n(a)|` from (2a) together with the size hypothesis.

Scope note: the only ingredient left for the *full* Zsygmondy theorem (all `n ≥ 2`,
`a ≥ 2` outside the three classical exceptions) is the intrinsic valuation bound for the
prime `p = 2` (the even-intrinsic case, which is exactly where the `a = 2` and
`(n,a) = (6,2)` exceptions live and needs the 2-adic LTE analysis).  (2b) here covers all
odd intrinsic primes; the odd-`n` existence theorem is therefore genuinely unconditional.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExists
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactor
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridge
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOddPrimeLTE
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.IsPrimePow

open Polynomial

/-- **(2a) Totient lower bound, integer form.** For `n ≥ 2` and an integer `a ≥ 2`,
`(a - 1) ^ φ(n) < |Φ_n(a)|`.  Integer repackaging of mathlib's
`sub_one_pow_totient_lt_natAbs_cyclotomic_eval`. -/
theorem cyclotomic_eval_totient_lower_bound {n : ℕ} (hn : 1 < n) {a : ℤ} (ha : 2 ≤ a) :
    (a - 1) ^ Nat.totient n < (((cyclotomic n ℤ).eval a).natAbs : ℤ) := by
  set q : ℕ := a.toNat with hq
  have hqa : (q : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hqne : q ≠ 1 := by omega
  have hbnd := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn hqne
  have hbndZ : (((q - 1) ^ Nat.totient n : ℕ) : ℤ)
      < (((cyclotomic n ℤ).eval (↑q : ℤ)).natAbs : ℤ) := by exact_mod_cast hbnd
  rw [Nat.cast_pow, Nat.cast_sub (by omega : (1 : ℕ) ≤ q), Nat.cast_one, hqa] at hbndZ
  exact hbndZ

/-- **(2b) Intrinsic prime valuation bound (odd prime).** For an odd prime `p` with
`p ∣ n` and `p ∣ Φ_n(a)` (where `n ≥ 2`, `a ≥ 2`), the `p`-adic valuation of `Φ_n(a)` is
at most `1`.  So the intrinsic (odd) prime enters the cyclotomic value with a single
factor. -/
theorem padicValInt_cyclotomic_intrinsic_le_one
    {n p : ℕ} (hn : 1 < n) (hpodd : Odd p) [Fact p.Prime] {a : ℤ} (ha : 2 ≤ a)
    (hpn : p ∣ n) (hpc : (p : ℤ) ∣ (cyclotomic n ℤ).eval a) :
    padicValInt p ((cyclotomic n ℤ).eval a) ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn0 : 0 < n := by omega
  have hone_lt_a : 1 < a := by omega
  have hpa : ¬ (p : ℤ) ∣ a := not_dvd_base_of_dvd_cyclotomic hn0 a hpc
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
  -- order of `a` mod `p` and the structural factorization `n = e * p^k`
  set e := orderOf (a : ZMod p) with he
  have hepos : 0 < e := orderOf_pos_of_not_dvd hpa
  obtain ⟨k, hk⟩ := intrinsic_order_dvd hn0 a hpa hpc
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  -- since `p ∣ n`, the `p`-part exponent `k` is at least `1`
  have hk1 : 1 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    rw [pow_zero, mul_one] at hk
    rw [hk] at hpn
    have hle1 : e ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) he_dvd
    have hle2 : p ≤ e := Nat.le_of_dvd hepos hpn
    have := hp.one_lt
    omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- LTE base facts on `a^e`
  have hAne : a ^ e ≠ 1 := (hpow_gt e hepos).ne'
  have hpApos : ¬ (p : ℤ) ∣ a ^ e := fun h => hpa (hpZ.dvd_of_dvd_pow h)
  have hAsub : (p : ℤ) ∣ (a ^ e - 1) := (orderOf_dvd_iff a hepos).mp dvd_rfl
  -- valuation of `a^n - 1` via LTE with exponent `p^(j+1)`
  have hval_n : padicValInt p (a ^ n - 1) = padicValInt p (a ^ e - 1) + (j + 1) := by
    have hlte := ZsygmondyOddPrimeLTE.lte_odd_prime hp hpodd hAne hpApos hAsub (n := p ^ (j + 1))
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne'))
    rw [one_pow, padicValNat.prime_pow, ← pow_mul, ← hk] at hlte
    exact hlte
  -- the proper divisor `m = e * p^j`
  set m := e * p ^ j with hm
  have hmpos : 0 < m := Nat.mul_pos hepos (pow_pos hp.pos j)
  have hmn : n = m * p := by rw [hk, hm, pow_succ]; ring
  have hval_m : padicValInt p (a ^ m - 1) = padicValInt p (a ^ e - 1) + j := by
    have hlte := ZsygmondyOddPrimeLTE.lte_odd_prime hp hpodd hAne hpApos hAsub (n := p ^ j)
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne'))
    rw [one_pow, padicValNat.prime_pow, ← pow_mul] at hlte
    exact hlte
  -- divisibility `(a^m - 1) * Φ_n(a) ∣ a^n - 1`
  have hmem : m ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨⟨p, hmn⟩, ?_⟩
    rw [hmn]; exact (Nat.lt_mul_iff_one_lt_right hmpos).mpr hp.one_lt
  have hdvd_poly : ((X : ℤ[X]) ^ m - 1) * cyclotomic n ℤ ∣ (X : ℤ[X]) ^ n - 1 :=
    X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hmem
  have hdvd_eval : (a ^ m - 1) * (cyclotomic n ℤ).eval a ∣ a ^ n - 1 := by
    have h := Polynomial.eval_dvd (x := a) hdvd_poly
    simpa [eval_mul, eval_sub, eval_pow, eval_X, eval_one] using h
  -- non-vanishing of the relevant integers
  have hxne : a ^ m - 1 ≠ 0 := sub_ne_zero.mpr (hpow_gt m hmpos).ne'
  have hyne : a ^ n - 1 ≠ 0 := sub_ne_zero.mpr (hpow_gt n (by omega)).ne'
  have hCne : (cyclotomic n ℤ).eval a ≠ 0 := by
    intro h0
    have hpos := one_lt_natAbs_cyclotomic_eval hn ha
    rw [h0] at hpos; simp at hpos
  -- valuation of the product and monotonicity under divisibility
  have hval_mul : padicValInt p ((a ^ m - 1) * (cyclotomic n ℤ).eval a)
      = padicValInt p (a ^ m - 1) + padicValInt p ((cyclotomic n ℤ).eval a) :=
    padicValInt.mul hxne hCne
  have hmono : padicValInt p ((a ^ m - 1) * (cyclotomic n ℤ).eval a)
      ≤ padicValInt p (a ^ n - 1) := by
    have hd : (p : ℤ) ^ padicValInt p ((a ^ m - 1) * (cyclotomic n ℤ).eval a) ∣ a ^ n - 1 :=
      (padicValInt_dvd _).trans hdvd_eval
    rcases (padicValInt_dvd_iff _ _).mp hd with h | h
    · exact absurd h hyne
    · exact h
  -- combine: v_p(a^e-1)+j + v_p(Φ) ≤ v_p(a^e-1)+(j+1)
  have hchain : padicValInt p (a ^ e - 1) + j + padicValInt p ((cyclotomic n ℤ).eval a)
      ≤ padicValInt p (a ^ e - 1) + (j + 1) := by
    calc padicValInt p (a ^ e - 1) + j + padicValInt p ((cyclotomic n ℤ).eval a)
        = padicValInt p (a ^ m - 1) + padicValInt p ((cyclotomic n ℤ).eval a) := by rw [hval_m]
      _ = padicValInt p ((a ^ m - 1) * (cyclotomic n ℤ).eval a) := hval_mul.symm
      _ ≤ padicValInt p (a ^ n - 1) := hmono
      _ = padicValInt p (a ^ e - 1) + (j + 1) := hval_n
  omega

/-- **(3) Unconditional Zsygmondy existence for odd `n` in a size range.** For `n ≥ 2`
odd, an integer `a ≥ 2`, and `n ≤ (a - 1) ^ φ(n)`, the number `a^n - 1` has a *primitive*
prime divisor: a prime `p` dividing `a^n - 1` but none of `a^m - 1` for `0 < m < n`.

This is unconditional (no `¬ IsPrimePow` hypothesis): the only intrinsic prime dividing an
odd `n` is odd, and the intrinsic valuation bound (2b) handles all odd primes, collapsing a
hypothetical prime-power value of `Φ_n(a)` to `≤ n`, which the totient lower bound (2a) plus
the size hypothesis rule out. -/
theorem primitive_prime_exists_of_odd_of_size {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    {a : ℤ} (ha : 2 ≤ a) (hsize : (n : ℤ) ≤ (a - 1) ^ Nat.totient n) :
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
  -- p is odd since n is odd and p ∣ n
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hpn
    rw [Nat.odd_iff] at hodd
    omega
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  -- intrinsic valuation bound: v_p(Φ_n(a)) ≤ 1
  have hval_le : padicValInt p ((cyclotomic n ℤ).eval a) ≤ 1 :=
    padicValInt_cyclotomic_intrinsic_le_one hn hpodd ha hpn hpc
  -- but v_p(Φ_n(a)) = t (since |Φ_n(a)| = p^t)
  have hvalM : padicValInt p ((cyclotomic n ℤ).eval a) = t := by
    have h1 : padicValInt p ((cyclotomic n ℤ).eval a) = padicValNat p M := by
      rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by rw [hvalM] at hval_le; omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hpn_le : p ≤ n := Nat.le_of_dvd (by omega) hpn
  -- lower bound from (2a) and the final contradiction
  have hlb : (a - 1) ^ Nat.totient n < (M : ℤ) := by
    rw [hMdef]; exact cyclotomic_eval_totient_lower_bound hn ha
  have hMpZ : (M : ℤ) = (p : ℤ) := by rw [hMp]
  have hpnZ : (p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hpn_le
  rw [hMpZ] at hlb
  linarith [hsize, hlb, hpnZ]
