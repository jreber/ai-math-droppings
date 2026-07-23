/-
Zsygmondy base-2 endgame: the correct closure of the `a = 2` case, via the classical
Birkhoff–Vandiver / Bang argument as reformulated by Bart Michels
(https://pommetatin.be/files/zsigmondy_en.pdf, Section 2, "Case 3").

This SUPERSEDES the wrong `conj-2026-07-08-004` target (blanket `n < Φ_n(2)` for all
`n ≠ 6`, which needs a genuine base-2 Mahler-measure-flavoured estimate and is a dead end
— see `docs/kb/failed/2026-07-08__conj-2026-07-08-004__general-base2-cyclotomic-bound.json`).
The classical proof never proves that blanket inequality. Instead, assuming `Φ_n(2)` is a
prime power `p^t` with intrinsic prime `p ∣ n` (the only way a primitive prime divisor can
fail to exist, `primitive_prime_exists_of_not_isPrimePow`), it derives a SELF-BOUND on `p`
by applying the totient/height lower bound one level down — to `Φ_q(2^p)` rather than to
`Φ_n(2)` directly, where `n = q · p^k` is the intrinsic-order decomposition
(`intrinsic_order_dvd`, `q = ord_p(2)`, `p ∤ q`) — and combines it with the classical
congruence `q ∣ p - 1` for primitive divisors of `Φ_q` (`primitive_prime_congr_one`) to pin
down `n` exactly.

## Why `p = 2` never happens here

For `a = 2` specifically, `not_dvd_base_of_dvd_cyclotomic` gives `p ∤ 2` whenever
`p ∣ Φ_n(2)`, so the intrinsic prime `p` is automatically odd — the whole `p = 2`
phenomenology of `ZsygmondyEvenPrime` (needed for general `a`) never arises for `a = 2`.
This also means the general-`a` machinery's `hsize : n ≤ (a - 1) ^ φ(n)` route is entirely
useless here (it degenerates to `n ≤ 1`), which is exactly why this file exists: it replaces
that route with the self-bound / congruence pincer instead.

## The self-bound argument (Michels Case 3, specialised to `a = 2, b = 1`)

Write `n = q · p^k` via `intrinsic_order_dvd` (`q := ord_p(2)`, `p ∤ q`, and `p ∣ n` forces
`k ≥ 1`). If `n` is a prime power then `q = 1` and `ZsygmondyBaseTwo` already gives
`n < Φ_n(2) = p ≤ n`, a direct contradiction — so this file only needs the non-prime-power
branch (`q ≥ 2`).

* **`k ≥ 2` is impossible.** Since `p ∣ n / p` in this case, the cyclotomic *expand*
  identity `cyclotomic_expand_eq_cyclotomic` gives the EQUALITY `Φ_n(2) = Φ_{n/p}(2^p)`
  (no quotient factor). The totient lower bound applied to the RHS at index `n/p > 1`
  gives `(2^p - 1)^{φ(n/p)} < Φ_{n/p}(2^p) = Φ_n(2) = p`, but `2^p - 1 ≥ p` always
  (`Nat.lt_two_pow_self`), a contradiction.

* **`k = 1` forces `p = 3`.** Now `p ∤ q`, so `cyclotomic_expand_eq_cyclotomic_mul` gives
  the EQUALITY `Φ_q(2^p) = Φ_n(2) · Φ_q(2) = p · Φ_q(2)`. Sandwiching:
  `(2^p - 1)^{φ(q)} < Φ_q(2^p) = p · Φ_q(2) ≤ p · 3^{φ(q)}` (upper bound: an integer
  repackaging of mathlib's `cyclotomic_eval_le_add_one_pow_totient`). For `p ≥ 5` one has
  `(2^p - 1) ≥ 3p` (elementary), forcing `(2^p-1)^{φ(q)} ≥ (3p)^{φ(q)} ≥ 3^{φ(q)} · p`,
  contradicting strictness. So `p ≤ 4`; combined with `p` an odd prime, `p = 3`.

* **`q < p` pins `n = 6`.** Fermat (`ZMod.pow_card`) gives `2^p ≡ 2 (mod p)`, so evaluating
  the polynomial identity mod `p` gives `Φ_q(2^p) ≡ Φ_q(2) (mod p)`; combined with
  `Φ_q(2^p) = p · Φ_q(2) ≡ 0 (mod p)` this gives `p ∣ Φ_q(2)`. Since `p ∤ q` and `p ∤ 2`,
  `primitive_prime_congr_one` gives `q ∣ (p - 1)`, so `q ≤ p - 1 < p`. With `p = 3`: `q < 3`
  and `q ≥ 2` (non-prime-power branch) forces `q = 2`, i.e. `n = q · p^1 = 6` — exactly the
  classical exception, contradicting the hypothesis `n ≠ 6`.

No asymptotic / equidistribution content is used anywhere; every step is an elementary
integer inequality or a single Fermat/cyclotomic-expand identity.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExists
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHeightBound
import Propositio.NumberTheory.Zsygmondy.ZsygmondyBaseTwo
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitivePrimeCongr
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactor
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.IsPrimePow

open Polynomial

namespace ZsygmondyBaseTwoEndgame

/-- Integer repackaging of mathlib's `cyclotomic_eval_le_add_one_pow_totient`: for any
`n` and integer `a ≥ 2`, `Φ_n(a) ≤ (a+1)^φ(n)`. -/
theorem cyclotomic_eval_totient_upper_bound (n : ℕ) {a : ℤ} (ha : 2 ≤ a) :
    (cyclotomic n ℤ).eval a ≤ (a + 1) ^ Nat.totient n := by
  have hq' : (1 : ℝ) < (a : ℝ) := by
    have : (1 : ℤ) < a := by omega
    exact_mod_cast this
  have hR : (cyclotomic n ℝ).eval (a : ℝ) ≤ ((a : ℝ) + 1) ^ Nat.totient n :=
    cyclotomic_eval_le_add_one_pow_totient hq' n
  have heq : (cyclotomic n ℝ).eval (a : ℝ) = (((cyclotomic n ℤ).eval a : ℤ) : ℝ) := by
    have h := cyclotomic.eval_apply a n (Int.castRingHom ℝ)
    simpa using h
  rw [heq] at hR
  have hcast : (((a + 1) ^ Nat.totient n : ℤ) : ℝ) = ((a : ℝ) + 1) ^ Nat.totient n := by
    push_cast; ring
  rw [← hcast] at hR
  exact_mod_cast hR

/-- Elementary numeric bound: `3 * p < 2 ^ p` for `p ≥ 5`. -/
private theorem three_mul_lt_two_pow {p : ℕ} (hp5 : 5 ≤ p) : 3 * p < 2 ^ p := by
  induction p, hp5 using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h3 : (3 : ℕ) < 2 ^ n := by
      calc (3 : ℕ) ≤ 3 * n := by nlinarith
        _ < 2 ^ n := ih
    calc 3 * (n + 1) = 3 * n + 3 := by ring
      _ < 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **The self-bound on the intrinsic prime, `k ≥ 2` case.** If `Φ_n(2) = p` (`n ≥ 2`,
`p` prime, `p ∣ n`, `p^2 ∣ n`), this is impossible. -/
private theorem no_k_ge_two {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    (hMeq : (cyclotomic n ℤ).eval (2 : ℤ) = (p : ℤ)) (hp2 : p * p ∣ n) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := hp2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso; rw [h0, Nat.mul_zero] at hm; omega
    · exact h
  set n' : ℕ := p * m with hn'def
  have hnn' : n = n' * p := by rw [hn'def, hm]; ring
  have hpn' : p ∣ n' := ⟨m, hn'def⟩
  have hexp : expand ℤ p (cyclotomic n' ℤ) = cyclotomic n ℤ := by
    rw [cyclotomic_expand_eq_cyclotomic hp hpn' ℤ, ← hnn']
  have heval : (cyclotomic n' ℤ).eval ((2 : ℤ) ^ p) = (p : ℤ) := by
    have h := expand_eval p (cyclotomic n' ℤ) (2 : ℤ)
    rw [hexp] at h
    rw [← h, hMeq]
  have hn'gt1 : 1 < n' := by
    rw [hn'def]
    have hple : p ≤ p * m := Nat.le_mul_of_pos_right p hmpos
    have := hp.one_lt
    omega
  have hn'pos : 0 < n' := by omega
  have ha2 : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
    calc (2:ℤ) = 2^1 := by ring
      _ ≤ 2 ^ p := by
        apply pow_le_pow_right₀ (by norm_num)
        exact hp.pos
  have hlb := cyclotomic_eval_totient_lower_bound hn'gt1 ha2
  rw [heval] at hlb
  have hnatabs : ((p:ℤ)).natAbs = p := Int.natAbs_natCast p
  rw [hnatabs] at hlb
  have hlt : ((2:ℤ) ^ p - 1) ^ Nat.totient n' < (p : ℤ) := hlb
  have hp_lt : p < 2 ^ p := Nat.lt_two_pow_self
  have hexpge1 : 1 ≤ Nat.totient n' := Nat.totient_pos.mpr hn'pos
  have hbase_pos : (1:ℤ) ≤ (2:ℤ)^p - 1 := by
    have : (2:ℤ) ≤ 2^p := ha2
    omega
  have hpowge : (2:ℤ)^p - 1 ≤ ((2:ℤ)^p - 1)^(Nat.totient n') :=
    le_self_pow₀ hbase_pos (by omega)
  have hfin : (2:ℤ)^p - 1 < (p:ℤ) := lt_of_le_of_lt hpowge hlt
  have hp_ltZ : (p : ℤ) < (2:ℤ) ^ p := by exact_mod_cast hp_lt
  omega

/-- **The self-bound on the intrinsic prime, `k = 1` case.** If `n = q * p` (`q > 1`,
`p ∤ q`) and `Φ_n(2) = p`, then `p ≤ 4`. -/
private theorem p_le_four_of_k_eq_one {q p : ℕ} (hq1 : 1 < q) [Fact p.Prime]
    (hpq : ¬ p ∣ q) (hMeq : (cyclotomic (q * p) ℤ).eval (2 : ℤ) = (p : ℤ)) : p ≤ 4 := by
  by_contra hgt
  push_neg at hgt
  have hp5 : 5 ≤ p := by omega
  have hp : p.Prime := Fact.out
  set Cq : ℤ := (cyclotomic q ℤ).eval (2 : ℤ) with hCqdef
  have hexp : expand ℤ p (cyclotomic q ℤ) = cyclotomic (q * p) ℤ * cyclotomic q ℤ :=
    cyclotomic_expand_eq_cyclotomic_mul hp hpq ℤ
  have heval : (cyclotomic q ℤ).eval ((2 : ℤ) ^ p) = (p : ℤ) * Cq := by
    have h := expand_eval p (cyclotomic q ℤ) (2 : ℤ)
    rw [hexp] at h
    simp only [eval_mul] at h
    rw [← h, hMeq]
  have hCqpos : (0 : ℤ) < Cq := cyclotomic_pos' q (by norm_num)
  have hprodnonneg : (0 : ℤ) ≤ (p : ℤ) * Cq := by positivity
  have ha2 : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
    calc (2:ℤ) = 2^1 := by ring
      _ ≤ 2 ^ p := by
        apply pow_le_pow_right₀ (by norm_num)
        exact hp.pos
  have hlb := cyclotomic_eval_totient_lower_bound hq1 ha2
  rw [heval, Int.natAbs_of_nonneg hprodnonneg] at hlb
  -- hlb : (2^p - 1)^φ(q) < p * Cq
  have hub : Cq ≤ (2 + 1 : ℤ) ^ Nat.totient q :=
    cyclotomic_eval_totient_upper_bound q (by norm_num)
  have hub' : Cq ≤ (3 : ℤ) ^ Nat.totient q := by
    have : (2 + 1 : ℤ) = 3 := by norm_num
    rwa [this] at hub
  have hpnn : (0:ℤ) ≤ (p:ℤ) := by positivity
  have hchain : ((2:ℤ)^p - 1)^(Nat.totient q) < (p:ℤ) * (3:ℤ)^(Nat.totient q) :=
    lt_of_lt_of_le hlb (mul_le_mul_of_nonneg_left hub' hpnn)
  -- numeric contradiction for p ≥ 5
  have hnatlt : 3 * p < 2 ^ p := three_mul_lt_two_pow hp5
  have hzlt : (3 * p : ℤ) < (2:ℤ) ^ p := by exact_mod_cast hnatlt
  have hstep : (3 * (p:ℤ)) ≤ (2:ℤ) ^ p - 1 := by omega
  have h3pnn : (0:ℤ) ≤ 3 * (p:ℤ) := by positivity
  have hpowle : (3 * (p:ℤ))^(Nat.totient q) ≤ ((2:ℤ)^p - 1)^(Nat.totient q) :=
    pow_le_pow_left₀ h3pnn hstep _
  have hexpand : (3 * (p:ℤ))^(Nat.totient q) = (3:ℤ)^(Nat.totient q) * (p:ℤ)^(Nat.totient q) := by
    rw [mul_pow]
  have hqe1 : Nat.totient q ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
  have hple : (p:ℤ) ≤ (p:ℤ)^(Nat.totient q) := le_self_pow₀ (by exact_mod_cast hp.one_le) hqe1
  have h3enn : (0:ℤ) ≤ (3:ℤ)^(Nat.totient q) := by positivity
  have hfin : (p:ℤ) * (3:ℤ)^(Nat.totient q) ≤ (3 * (p:ℤ))^(Nat.totient q) := by
    rw [hexpand, mul_comm ((3:ℤ)^(Nat.totient q)) ((p:ℤ)^(Nat.totient q))]
    exact mul_le_mul_of_nonneg_right hple h3enn
  linarith [hchain, hpowle, hfin]

/-- **The congruence pin, `k = 1` case.** If `n = q * p` (`q > 1`, `p ∤ q`, `p ≠ 2`) and
`Φ_n(2) = p`, then `q ∣ (p - 1)`. -/
private theorem q_dvd_p_sub_one_of_k_eq_one {q p : ℕ} (hq1 : 1 < q) [Fact p.Prime]
    (hpq : ¬ p ∣ q) (hp2ne : p ≠ 2)
    (hMeq : (cyclotomic (q * p) ℤ).eval (2 : ℤ) = (p : ℤ)) : q ∣ (p - 1) := by
  have hp : p.Prime := Fact.out
  set Cq : ℤ := (cyclotomic q ℤ).eval (2 : ℤ) with hCqdef
  have hexp : expand ℤ p (cyclotomic q ℤ) = cyclotomic (q * p) ℤ * cyclotomic q ℤ :=
    cyclotomic_expand_eq_cyclotomic_mul hp hpq ℤ
  have heval : (cyclotomic q ℤ).eval ((2 : ℤ) ^ p) = (p : ℤ) * Cq := by
    have h := expand_eval p (cyclotomic q ℤ) (2 : ℤ)
    rw [hexp] at h
    simp only [eval_mul] at h
    rw [← h, hMeq]
  -- Fermat: 2^p ≡ 2 (mod p)
  have hferm : (((2:ℤ) ^ p : ℤ) : ZMod p) = ((2:ℤ) : ZMod p) := by
    push_cast
    exact ZMod.pow_card (2 : ZMod p)
  have hcong1 := cyclotomic.eval_apply ((2:ℤ) ^ p) q (Int.castRingHom (ZMod p))
  have hcong2 := cyclotomic.eval_apply (2:ℤ) q (Int.castRingHom (ZMod p))
  simp only [Int.coe_castRingHom] at hcong1 hcong2
  rw [hferm, heval] at hcong1
  rw [← hCqdef] at hcong2
  rw [hcong2] at hcong1
  -- hcong1 : (Cq : ZMod p) = (((p:ℤ) * Cq : ℤ) : ZMod p)
  have hp0 : ((p:ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hcong1' : (Cq : ZMod p) = 0 := by
    rw [hcong1]
    push_cast
    rw [hp0]
    ring
  have hpdvdCq : (p:ℤ) ∣ Cq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcong1'
  have hpa2 : ¬ (p:ℤ) ∣ (2:ℤ) := by
    intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    exact hp2ne this
  exact primitive_prime_congr_one hq1 (2:ℤ) hpdvdCq hpq hpa2

/-- **Zsygmondy base-2 endgame.** For `n ≥ 2`, `n ≠ 6`, the number `2^n - 1` has a
*primitive* prime divisor: a prime `p` with `p ∣ 2^n - 1` and `p ∤ 2^m - 1` for every
`0 < m < n`. This closes the base-`a = 2` case of Zsygmondy's theorem completely (the
only classical exceptions for `a = 2` are `n = 1`, excluded by `1 < n`, and `n = 6`,
excluded by hypothesis). -/
theorem primitive_prime_exists_base_two {n : ℕ} (hn : 1 < n) (hn6 : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (2 : ℤ) ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ (2 : ℤ) ^ m - 1 := by
  by_contra hcon
  push_neg at hcon
  have ha : (2 : ℤ) ≤ 2 := le_refl 2
  have hn0 : 0 < n := by omega
  have hpp : IsPrimePow ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs := by
    by_contra h
    obtain ⟨p, hp, h1, h2⟩ := primitive_prime_exists_of_not_isPrimePow hn ha h
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, t, hp, ht, hpt⟩ := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  set M := ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs with hMdef
  have hpM : p ∣ M := hpt ▸ dvd_pow_self p (by omega : t ≠ 0)
  have hpc : (p : ℤ) ∣ (cyclotomic n ℤ).eval (2 : ℤ) :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpM)
  have hpn : p ∣ n := by
    by_contra hpn
    obtain ⟨h1, h2⟩ := primitive_prime_divisor_of_dvd_cyclotomic hn (2 : ℤ) hpc hpn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon p hp h1
    exact h2 m hm0 hmn hmd
  have hpa : ¬ (p : ℤ) ∣ (2 : ℤ) := not_dvd_base_of_dvd_cyclotomic hn0 (2 : ℤ) hpc
  have hp2ne : p ≠ 2 := by
    intro h; subst h; exact hpa (by norm_num)
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2ne
  have hval_le : padicValInt p ((cyclotomic n ℤ).eval (2 : ℤ)) ≤ 1 :=
    padicValInt_cyclotomic_intrinsic_le_one hn hpodd ha hpn hpc
  have hvalM : padicValInt p ((cyclotomic n ℤ).eval (2 : ℤ)) = t := by
    have h1 : padicValInt p ((cyclotomic n ℤ).eval (2 : ℤ)) = padicValNat p M := by
      rw [hMdef]; rfl
    rw [h1, ← hpt, padicValNat.prime_pow]
  have ht1 : t = 1 := by rw [hvalM] at hval_le; omega
  have hMp : M = p := by rw [← hpt, ht1, pow_one]
  have hMeq : (cyclotomic n ℤ).eval (2 : ℤ) = (p : ℤ) := by
    have hpos : (0 : ℤ) < (cyclotomic n ℤ).eval (2 : ℤ) := cyclotomic_pos' n (by norm_num)
    have hna := Int.natAbs_of_nonneg hpos.le
    rw [← hMdef, hMp] at hna
    linarith [hna]
  -- structure: n = e * p ^ k, e = ord_p(2), p ∤ e
  obtain ⟨k, hk⟩ := intrinsic_order_dvd hn0 (2 : ℤ) hpa hpc
  set e := orderOf ((2 : ℤ) : ZMod p) with he
  have hepos : 0 < e := orderOf_pos_of_not_dvd hpa
  have ha0 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  have hpe_not : ¬ p ∣ e := by
    intro hdvd
    have hle1 : e ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) he_dvd
    have hle2 : p ≤ e := Nat.le_of_dvd hepos hdvd
    have := hp.one_lt
    omega
  by_cases hnpp : IsPrimePow n
  · have hlt := ZsygmondyBaseTwo.cyclotomic_eval_two_gt_of_isPrimePow hnpp
    rw [hMeq] at hlt
    have hple : p ≤ n := Nat.le_of_dvd hn0 hpn
    have hpleZ : (p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hple
    linarith [hlt, hpleZ]
  · have he_ne1 : e ≠ 1 := by
      intro he1
      apply hnpp
      rw [he1, one_mul] at hk
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h
        · exfalso; rw [h0, pow_zero] at hk; omega
        · exact h
      exact ⟨p, k, hp.prime, hkpos, hk.symm⟩
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
    · subst hj0
      simp only [pow_one] at hk
      have he1lt : 1 < e := by omega
      have hMeqq : (cyclotomic (e * p) ℤ).eval (2 : ℤ) = (p : ℤ) := by
        rw [← hk]; exact hMeq
      have hple4 : p ≤ 4 := p_le_four_of_k_eq_one he1lt hpe_not hMeqq
      have hp3 : p = 3 := by
        have hp2le : 2 ≤ p := hp.two_le
        have hp234 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases hp234 with h2 | h3 | h4
        · exact absurd h2 hp2ne
        · exact h3
        · exfalso; rw [h4] at hp; exact absurd hp (by decide)
      have hqdvd : e ∣ (p - 1) :=
        q_dvd_p_sub_one_of_k_eq_one he1lt hpe_not hp2ne hMeqq
      rw [hp3] at hqdvd
      norm_num at hqdvd
      have hele2 : e ≤ 2 := Nat.le_of_dvd (by norm_num) hqdvd
      have he_eq2 : e = 2 := by omega
      have hn6' : n = 6 := by rw [hk, he_eq2, hp3]
      exact hn6 hn6'
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hp2dvdn : p * p ∣ n := by
        clear_value e
        refine ⟨e * p ^ i, ?_⟩
        rw [hk, pow_succ, pow_succ]; ring
      exact no_k_ge_two hn hMeq hp2dvdn

end ZsygmondyBaseTwoEndgame
