/-
Zsygmondy intrinsic-prime valuation bound (LTE for `Phi`) — general-`b` port, plus the
`a = b + 1` prime-power (`e = 1`) case.

This file supplies items (2) and (3) of the "What is NOT closed here" list in
`ZsygmondyExceptionalEndgameGeneral`:

## Item (2): LTE for `Phi` (odd prime), general `b`

`padicValInt_Phi_intrinsic_le_one`: the two-variable generalization of
`ZsygmondyHeightBound.padicValInt_cyclotomic_intrinsic_le_one`. For an ODD prime `p` with
`p ∣ n` and `p ∣ Phi n a b` (`n ≥ 2`, `IsCoprime a b`, `1 ≤ b < a`), the `p`-adic valuation
`v_p(Phi n a b) ≤ 1`. This pins `t = 1` exactly (`Phi n a b = p`, not just `p^t`) once
`Phi n a b` is known to be a prime power.

The proof is a direct transplant of the `b = 1` proof, with:
  * the base pair `(a^e, b^e)` in place of `(a^e, 1)`, `e = ord_p(a·b⁻¹)`
    (`intrinsic_order_dvd_general`), driving `ZsygmondyOddPrimeLTE.lte_odd_prime` (which is
    already stated for general `a, b`);
  * the homogeneous divisibility `(a^m - b^m) · Phi n a b ∣ a^n - b^n` obtained directly
    from the product factorization `prod_Phi_eq` (`a^n - b^n = ∏_{d ∣ n} Phi d a b`) by the
    subset `insert n m.divisors ⊆ n.divisors` (`m = e·p^j` a proper divisor), replacing the
    `b = 1` file's `X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd`.

## Item (3): the `e = 1` / prime-power `n` case, for `a = b + 1`

KEY SIMPLIFICATION: for `a = b + 1` (the only case the exceptional endgame cares about),
the `e = 1` branch is VACUOUS, so the geometric-sum size bound literally asked for in item
(3) (the general-`b` analogue of `ZsygmondyBaseTwo.cyclotomic_eval_two_gt_of_isPrimePow`,
`Φ_n(2) > n`) is NOT NEEDED for the endgame. Indeed
`e = ord_p(a·b⁻¹) = 1 ⟺ a·b⁻¹ = 1 in ZMod p ⟺ p ∣ (a - b) = p ∣ 1`, impossible for a
prime `p`. Hence:
  * `ratio_ne_one_of_succ`: `(b+1)·b⁻¹ ≠ 1` in `ZMod p` (whenever `p ∤ b`), so `e ≠ 1`.
  * `prime_power_case_impossible_of_succ`: for `a = b + 1`, if `n` is a prime power, `p ∣ n`
    and `p ∣ Phi n (b+1) b`, then `False` — the `e = 1` branch never arises.

This is strictly simpler than the `b = 1` base-2 file, which went through the explicit
geometric-sum evaluation `cyclotomic_eval_two_gt_of_isPrimePow` to derive `n < p ≤ n`; the
`a - b = 1` shortcut sidesteps that entirely. (For general `a > b` NOT of the form `b + 1`,
the `e = 1` case is genuine and would need the real geometric-sum bound; that generality is
orthogonal to the exceptional endgame, whose worst-margin object is always `a = b + 1`.)
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveExistsGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridgeGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactorGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOddPrimeLTE
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.GCD.Basic

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyLTEGeneral

/-- **Item (2): LTE for `Phi`, odd prime.** For an odd prime `p` with `p ∣ n` and
`p ∣ Phi n a b` (`n ≥ 2`, `IsCoprime a b`, `1 ≤ b < a`), the `p`-adic valuation of
`Phi n a b` is at most `1`. So the intrinsic (odd) prime enters `Phi n a b` with a single
factor — the general-`b` analogue of `padicValInt_cyclotomic_intrinsic_le_one`. -/
theorem padicValInt_Phi_intrinsic_le_one
    {n p : ℕ} (hn : 1 < n) (hpodd : Odd p) [Fact p.Prime] {a b : ℤ}
    (hb : 1 ≤ b) (hab : b < a) (hcop : IsCoprime a b)
    (hpn : p ∣ n) (hpc : (p : ℤ) ∣ Phi n a b) :
    padicValInt p (Phi n a b) ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn0 : 0 < n := by omega
  obtain ⟨hpa, hpb⟩ :=
    ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi hn0 hcop hpc
  -- powers of `a` (and `b`) grow strictly, all comparisons are clean since `a > b ≥ 1`
  have hb0 : (0 : ℤ) ≤ b := by omega
  have hpow_lt : ∀ s : ℕ, 1 ≤ s → b ^ s < a ^ s := by
    intro s hs
    exact pow_lt_pow_left₀ hab hb0 (by omega)
  -- order of `a·b⁻¹` mod `p` and the structural factorization `n = e * p^k`
  set e := orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) with he
  have hepos : 0 < e := orderOf_pos_of_not_dvd_general hpa hpb
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 a b hpb hpc
  have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := by
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hbz : (b : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
    exact mul_ne_zero ha0 (inv_ne_zero hbz)
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hr0
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
  -- LTE base facts on the pair `(a^e, b^e)`
  have hAne : a ^ e ≠ b ^ e := (hpow_lt e hepos).ne'
  have hpApos : ¬ (p : ℤ) ∣ a ^ e := fun h => hpa (hpZ.dvd_of_dvd_pow h)
  have hAsub : (p : ℤ) ∣ (a ^ e - b ^ e) :=
    (orderOf_dvd_iff_general a b hpb hepos).mp dvd_rfl
  -- valuation of `a^n - b^n` via LTE with exponent `p^(j+1)`
  have hae_n : (a ^ e) ^ p ^ (j + 1) = a ^ n := by rw [← pow_mul, ← hk]
  have hbe_n : (b ^ e) ^ p ^ (j + 1) = b ^ n := by rw [← pow_mul, ← hk]
  have hval_n : padicValInt p (a ^ n - b ^ n) = padicValInt p (a ^ e - b ^ e) + (j + 1) := by
    have hlte := ZsygmondyOddPrimeLTE.lte_odd_prime hp hpodd hAne hpApos hAsub
      (n := p ^ (j + 1)) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne'))
    rw [hae_n, hbe_n, padicValNat.prime_pow] at hlte
    exact hlte
  -- the proper divisor `m = e * p^j`
  set m := e * p ^ j with hm
  have hmpos : 0 < m := Nat.mul_pos hepos (pow_pos hp.pos j)
  have hmn : n = m * p := by rw [hk, hm, pow_succ]; ring
  have hae_m : (a ^ e) ^ p ^ j = a ^ m := by rw [← pow_mul, ← hm]
  have hbe_m : (b ^ e) ^ p ^ j = b ^ m := by rw [← pow_mul, ← hm]
  have hval_m : padicValInt p (a ^ m - b ^ m) = padicValInt p (a ^ e - b ^ e) + j := by
    have hlte := ZsygmondyOddPrimeLTE.lte_odd_prime hp hpodd hAne hpApos hAsub
      (n := p ^ j) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne'))
    rw [hae_m, hbe_m, padicValNat.prime_pow] at hlte
    exact hlte
  -- homogeneous divisibility `(a^m - b^m) * Phi n a b ∣ a^n - b^n`, via `prod_Phi_eq`
  have hmn_dvd : m ∣ n := ⟨p, hmn⟩
  have hmltn : m < n := by
    rw [hmn]; exact (Nat.lt_mul_iff_one_lt_right hmpos).mpr hp.one_lt
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
  -- hprod_dvd : Phi n a b * (a^m - b^m) ∣ a^n - b^n
  have hdvd_eval : (a ^ m - b ^ m) * Phi n a b ∣ a ^ n - b ^ n := by
    rw [mul_comm]; exact hprod_dvd
  -- non-vanishing of the relevant integers
  have hxne : a ^ m - b ^ m ≠ 0 := sub_ne_zero.mpr (hpow_lt m hmpos).ne'
  have hyne : a ^ n - b ^ n ≠ 0 := sub_ne_zero.mpr (hpow_lt n (by omega)).ne'
  have hCne : Phi n a b ≠ 0 := by
    intro h0
    have hpos := ZsygmondyPrimitiveExistsGeneral.one_lt_natAbs_Phi hn hb hab
    rw [h0] at hpos; simp at hpos
  -- valuation of the product and monotonicity under divisibility
  have hval_mul : padicValInt p ((a ^ m - b ^ m) * Phi n a b)
      = padicValInt p (a ^ m - b ^ m) + padicValInt p (Phi n a b) :=
    padicValInt.mul hxne hCne
  have hmono : padicValInt p ((a ^ m - b ^ m) * Phi n a b)
      ≤ padicValInt p (a ^ n - b ^ n) := by
    have hd : (p : ℤ) ^ padicValInt p ((a ^ m - b ^ m) * Phi n a b) ∣ a ^ n - b ^ n :=
      (padicValInt_dvd _).trans hdvd_eval
    rcases (padicValInt_dvd_iff _ _).mp hd with h | h
    · exact absurd h hyne
    · exact h
  -- combine: v_p(a^e-b^e)+j + v_p(Φ) ≤ v_p(a^e-b^e)+(j+1)
  have hchain : padicValInt p (a ^ e - b ^ e) + j + padicValInt p (Phi n a b)
      ≤ padicValInt p (a ^ e - b ^ e) + (j + 1) := by
    calc padicValInt p (a ^ e - b ^ e) + j + padicValInt p (Phi n a b)
        = padicValInt p (a ^ m - b ^ m) + padicValInt p (Phi n a b) := by rw [hval_m]
      _ = padicValInt p ((a ^ m - b ^ m) * Phi n a b) := hval_mul.symm
      _ ≤ padicValInt p (a ^ n - b ^ n) := hmono
      _ = padicValInt p (a ^ e - b ^ e) + (j + 1) := hval_n
  omega

/-! ### Item (3): the `e = 1` / prime-power `n` case for `a = b + 1` -/

/-- **Item (3) core.** For `a = b + 1` and a prime `p ∤ b`, the ratio `(b+1)·b⁻¹` is not `1`
in `ZMod p`. Consequently `ord_p((b+1)·b⁻¹) ≠ 1`. Reason: `(b+1)·b⁻¹ = 1 ⟺ (b+1) = b`, i.e.
`1 = 0` in `ZMod p`, impossible. This is exactly why the prime-power (`e = 1`) branch of the
intrinsic decomposition is vacuous for `a = b + 1`, so the geometric-sum size bound (the
literal item (3), `Φ_n(2) > n`) is unneeded for the endgame. -/
theorem ratio_ne_one_of_succ {p : ℕ} [Fact p.Prime] {b : ℤ} (hpb : ¬ (p : ℤ) ∣ b) :
    ((b + 1 : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹ ≠ 1 := by
  intro h
  have hbz : ((b : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
  have hcast : ((b + 1 : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) := by
    have h2 := congrArg (· * ((b : ℤ) : ZMod p)) h
    simp only [one_mul] at h2
    rw [mul_assoc, inv_mul_cancel₀ hbz, mul_one] at h2
    exact h2
  have h3 : ((b : ℤ) : ZMod p) + 1 = ((b : ℤ) : ZMod p) := by
    rw [show ((b + 1 : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) + 1 from by push_cast; ring] at hcast
    exact hcast
  have h4 : (1 : ZMod p) = 0 := by linear_combination h3
  exact one_ne_zero h4

/-- **Item (3).** For `a = b + 1` (`1 ≤ b`), the prime-power (`e = 1`) branch of the
intrinsic decomposition is impossible: if `n` is a prime power, `p ∣ n` and
`p ∣ Phi n (b+1) b`, then `False`. Proof: `intrinsic_order_dvd_general` gives
`n = e·p^k` with `e = ord_p((b+1)·b⁻¹)`; `ratio_ne_one_of_succ` gives `e ≠ 1`; Fermat gives
`p ∤ e`; but a prime power `n` with `p ∣ n` is `p^k'`, forcing `e ∣ p^k'` coprime to `p`,
hence `e = 1` — contradiction. -/
theorem prime_power_case_impossible_of_succ {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    {b : ℤ} (_hb : 1 ≤ b) (hpp : IsPrimePow n) (hpn : p ∣ n)
    (hpc : (p : ℤ) ∣ Phi n (b + 1) b) : False := by
  have hp : p.Prime := Fact.out
  have hn0 : 0 < n := by omega
  have hcop : IsCoprime (b + 1) b := ⟨1, -1, by ring⟩
  obtain ⟨hpa, hpb⟩ :=
    ZsygmondyPrimitiveExistsGeneral.not_dvd_base_of_dvd_Phi hn0 hcop hpc
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 (b + 1) b hpb hpc
  set e := orderOf (((b + 1 : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹) with he
  have hepos : 0 < e := orderOf_pos_of_not_dvd_general hpa hpb
  have hene : e ≠ 1 := fun h1 => ratio_ne_one_of_succ hpb (orderOf_eq_one_iff.mp h1)
  have hr0 : ((b + 1 : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹ ≠ 0 := by
    have ha0 : ((b + 1 : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hbz : ((b : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
    exact mul_ne_zero ha0 (inv_ne_zero hbz)
  have he_dvd : e ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hr0
  have hpe : ¬ p ∣ e := by
    intro hd
    have h1 : e ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) he_dvd
    have h2 : p ≤ e := Nat.le_of_dvd hepos hd
    have := hp.one_lt
    omega
  -- `n` a prime power dividing by `p` must be a power of `p`
  obtain ⟨q, k', hq, hk'pos, hqk⟩ := (isPrimePow_nat_iff n).mp hpp
  have hpq : p = q := by
    have hpdvd : p ∣ q ^ k' := hqk ▸ hpn
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd)
  subst hpq
  -- now `n = p^k'`, and `n = e * p^k`, so `e ∣ p^k'`; coprimality forces `e = 1`
  have hen : e * p ^ k = p ^ k' := by rw [← hk]; exact hqk.symm
  have hedvd : e ∣ p ^ k' := ⟨p ^ k, hen.symm⟩
  have hcop2 : Nat.Coprime e (p ^ k') :=
    (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpe)).pow_right k'
  have hgcd : Nat.gcd e (p ^ k') = 1 := hcop2
  have hedvd1 : e ∣ Nat.gcd e (p ^ k') := Nat.dvd_gcd dvd_rfl hedvd
  rw [hgcd] at hedvd1
  exact hene (Nat.dvd_one.mp hedvd1)

end ZsygmondyLTEGeneral
