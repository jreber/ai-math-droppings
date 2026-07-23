import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# A standalone `p`-adic polynomial-coefficient toolkit for the oSALIKHOV denominator proof

This file is **self-contained** (no project imports).  It develops the Apéry-style coefficient
divisibility facts for products of *linear* factors `(C c + X)`, culminating in the divisibility of
the coefficients of the oSALIKHOV key polynomial

  `Gpoly n = (C 15 + X)^(2n) · (C 12 + X)^n · (C 18 + X)^n · (C 10 + X)^n · (C 20 + X)^n   : ℤ[X]`.

The numbers `12 = 2²·3`, `18 = 2·3²`, `10 = 2·5`, `20 = 2²·5`, `15 = 3·5` make the *low* coefficients
of `Gpoly n` highly divisible by `2, 3, 5`: the low coefficient `(C c + X)^a |> .coeff i` equals
`C(a,i)·c^(a−i)`, hence is divisible by `c^(a−i)` (low coefficients are MOST divisible).

## Contents

1. `coeff_linfac_dvd`     : `c^(a−i) ∣ ((C c + X)^a).coeff i`            (the single-factor engine).
2. `coeff_mul_linfac_dvd` : `c^(a−m) ∣ ((C c + X)^a * H).coeff m`        (convolution corollary).
3. `coeff_listprod_linfac_dvd` : the general finite-product divisibility, and
   `Gpoly_coeff_dvd`          : `(15·12·18·10·20)^(n−i) ∣ (Gpoly n).coeff i` for `i ≤ n`,
   `Gpoly_coeff_dvd_15`       : `15^(2n−i) ∣ (Gpoly n).coeff i`                  (per-factor sharp form).

All lemmas are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only; no `native_decide`,
no `sorry`).
-/

namespace OSalikhovGCoeff

open Polynomial

/-! ### 1. The single-factor engine -/

/-- **Every coefficient of `(C c + X)^a` of index `i` is divisible by `c^(a−i)`.**
The `+X` analogue of the proven `(C c − X)^n` template; the induction
`(C c + X)^(a+1) = C c·(C c+X)^a + X·(C c+X)^a` gives `coeff i = c·p.coeff i + (X·p).coeff i`, the
only `c`-specific step being `c·c^a = c^(a+1)`. -/
theorem coeff_linfac_dvd (c : ℤ) (a i : ℕ) :
    c ^ (a - i) ∣ ((C c + X : ℤ[X]) ^ a).coeff i := by
  induction a generalizing i with
  | zero => rcases i with _ | i <;> simp
  | succ a ih =>
    set p : ℤ[X] := (C c + X : ℤ[X]) ^ a with hp
    have hrec : ((C c + X : ℤ[X]) ^ (a + 1)).coeff i = c * p.coeff i + (X * p).coeff i := by
      rw [pow_succ, mul_comm ((C c + X : ℤ[X]) ^ a) (C c + X), ← hp, add_mul,
        Polynomial.coeff_add, Polynomial.coeff_C_mul]
    rw [hrec]
    rcases i with _ | i
    · rw [Polynomial.coeff_X_mul_zero, add_zero, Nat.sub_zero]
      have h1 : c ^ (a - 0) ∣ p.coeff 0 := by simpa using ih 0
      calc c ^ (a + 1) = c * c ^ a := by ring
        _ ∣ c * p.coeff 0 := by rw [Nat.sub_zero] at h1; exact mul_dvd_mul_left c h1
    · rw [Polynomial.coeff_X_mul]
      have hA : c ^ (a + 1 - (i + 1)) ∣ c * p.coeff (i + 1) := by
        by_cases hjn : i + 1 ≤ a
        · have he : a + 1 - (i + 1) = (a - (i + 1)) + 1 := by omega
          rw [he, pow_succ, mul_comm]
          exact mul_dvd_mul (dvd_refl c) (ih (i + 1))
        · have : a + 1 - (i + 1) = 0 := by omega
          rw [this, pow_zero]; exact one_dvd _
      have hB : c ^ (a + 1 - (i + 1)) ∣ p.coeff i := by
        have he : a + 1 - (i + 1) = a - i := by omega
        rw [he]; exact ih i
      exact dvd_add hA hB

/-! ### 2. The convolution corollary -/

/-- **Convolution corollary.**  For any `H`, the factor `(C c + X)^a` contributes
`c^(a−m)`-divisibility to `((C c + X)^a * H).coeff m`.  Each antidiagonal split `(u,v)`, `u+v=m`,
has `u ≤ m`, so `c^(a−m) ∣ c^(a−u) ∣ coeff_u((C c + X)^a)`. -/
theorem coeff_mul_linfac_dvd (c : ℤ) (a m : ℕ) (H : ℤ[X]) :
    c ^ (a - m) ∣ ((C c + X : ℤ[X]) ^ a * H).coeff m := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
  have hpow : c ^ (a - m) ∣ c ^ (a - u) := pow_dvd_pow c (Nat.sub_le_sub_left (by omega) a)
  exact Dvd.dvd.mul_right (hpow.trans (coeff_linfac_dvd c a u)) _

/-! ### 3. The general finite product and the `Gpoly n` assembly -/

/-- **General finite-product divisibility.**  If `e + m ≤ a_k` for every factor `(c_k, a_k)` in the
list `L`, then `(∏ c_k)^e` divides the `m`-th coefficient of `∏ (C c_k + X)^{a_k}`.

Proof: peel the head factor by `coeff_mul`; the antidiagonal split `(u,v)` gives `c^e ∣ coeff_u`
(since `u ≤ m`, hence `e ≤ a − u`) and the induction hypothesis applies at index `v ≤ m` (since the
budget `e + v ≤ e + m ≤ a_k` is preserved). -/
theorem coeff_listprod_linfac_dvd (e : ℕ) :
    ∀ (L : List (ℤ × ℕ)) (m : ℕ), (∀ p ∈ L, e + m ≤ p.2) →
      ((L.map (fun p => p.1)).prod) ^ e ∣
        ((L.map (fun p => (C p.1 + X : ℤ[X]) ^ p.2)).prod).coeff m := by
  intro L
  induction L with
  | nil => intro m _; simp
  | cons hd tl ih =>
    intro m hm
    obtain ⟨c, a⟩ := hd
    simp only [List.map_cons, List.prod_cons]
    rw [mul_pow, Polynomial.coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨u, v⟩ huv
    have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
    have hc : (c : ℤ) ^ e ∣ ((C c + X : ℤ[X]) ^ a).coeff u := by
      have hle : e ≤ a - u := by
        have hmem : e + m ≤ a := hm (c, a) (by simp)
        omega
      exact (pow_dvd_pow c hle).trans (coeff_linfac_dvd c a u)
    have htail :
        ((tl.map (fun p => p.1)).prod) ^ e ∣
          ((tl.map (fun p => (C p.1 + X : ℤ[X]) ^ p.2)).prod).coeff v := by
      apply ih v
      intro p hp
      have hmem : e + m ≤ p.2 := hm p (by simp [hp])
      omega
    exact mul_dvd_mul hc htail

/-- The oSALIKHOV key polynomial. -/
noncomputable def Gpoly (n : ℕ) : ℤ[X] :=
  (C 15 + X) ^ (2 * n) * (C 12 + X) ^ n * (C 18 + X) ^ n * (C 10 + X) ^ n * (C 20 + X) ^ n

/-- The factor list `[(15,2n),(12,n),(18,n),(10,n),(20,n)]` underlying `Gpoly n`. -/
def Gfac (n : ℕ) : List (ℤ × ℕ) := [(15, 2 * n), (12, n), (18, n), (10, n), (20, n)]

/-- **Assembled `Gpoly`-coefficient divisibility.**  For `i ≤ n`,
`(15·12·18·10·20)^(n−i) = 648000^(n−i)` divides `(Gpoly n).coeff i`.
This is the uniform-exponent combined `2,3,5`-divisibility of the *low* coefficients. -/
theorem Gpoly_coeff_dvd (n i : ℕ) (hi : i ≤ n) :
    (648000 : ℤ) ^ (n - i) ∣ (Gpoly n).coeff i := by
  have hyp : ∀ p ∈ Gfac n, (n - i) + i ≤ p.2 := by
    intro p hp
    fin_cases hp <;> dsimp only <;> omega
  have key := coeff_listprod_linfac_dvd (n - i) (Gfac n) i hyp
  have h1 : ((Gfac n).map (fun p => p.1)).prod = (648000 : ℤ) := by
    unfold Gfac
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    norm_num
  have h2 : ((Gfac n).map (fun p => (C p.1 + X : ℤ[X]) ^ p.2)).prod = Gpoly n := by
    unfold Gfac Gpoly
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  rw [h1, h2] at key
  exact key

/-- **Per-factor sharp form.**  The leading factor `(C 15 + X)^(2n)` gives the strongest single-base
divisibility `15^(2n−i) ∣ (Gpoly n).coeff i` (no constraint on `i`). -/
theorem Gpoly_coeff_dvd_15 (n i : ℕ) :
    (15 : ℤ) ^ (2 * n - i) ∣ (Gpoly n).coeff i := by
  have hG : Gpoly n =
      (C 15 + X : ℤ[X]) ^ (2 * n) *
        ((C 12 + X) ^ n * (C 18 + X) ^ n * (C 10 + X) ^ n * (C 20 + X) ^ n) := by
    rw [Gpoly]; ring
  rw [hG]
  exact coeff_mul_linfac_dvd 15 (2 * n) i _

/-! ### 4. Sharp per-prime divisibility

The uniform `Gpoly_coeff_dvd` (`648000^(n−i)`, `i ≤ n`) is too weak per prime.  The sharp statement
tracks a single prime `p` dividing the bases of a *sublist* of the factors and uses the *full*
exponent budget of that sublist, absorbing all the other factors into an unconstrained `H`. -/

/-- **Per-prime convolution engine.**  If `p` divides the base `c_k` of *every* factor in `L`, then
for any polynomial `H`, `p^{(Σ a_k) − m}` divides the `m`-th coefficient of
`(∏ (C c_k + X)^{a_k}) · H`.

This is the sharp per-prime refinement of `coeff_listprod_linfac_dvd`: instead of the uniform
`(∏ c_k)^e` it tracks the single prime `p` and the full exponent budget `Σ a_k`, absorbing the
non-`p` factors into the unconstrained `H`.  The math: `coeff m (∏(C c_k+X)^{a_k}·H) =
∑ ∏ C(a_k,s_k) c_k^{a_k−s_k}·H_…`, and `v_p(∏ c_k^{a_k−s_k}) ≥ Σ(a_k−s_k) = (Σ a_k) − Σ s_k ≥
(Σ a_k) − m`. -/
theorem coeff_listprod_perprime_mul_dvd (p : ℤ) :
    ∀ (L : List (ℤ × ℕ)) (m : ℕ) (H : ℤ[X]), (∀ q ∈ L, p ∣ q.1) →
      p ^ ((L.map Prod.snd).sum - m) ∣
        ((L.map (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod * H).coeff m := by
  intro L
  induction L with
  | nil => intro m H _; simp
  | cons hd tl ih =>
    intro m H hp
    obtain ⟨c, a⟩ := hd
    have hpc : p ∣ c := hp (c, a) (by simp)
    have hsumeq : (((c, a) :: tl).map Prod.snd).sum = a + (tl.map Prod.snd).sum := by simp
    rw [hsumeq]
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, Polynomial.coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨u, v⟩ huv
    have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
    have h1 : p ^ (a - u) ∣ ((C c + X : ℤ[X]) ^ a).coeff u :=
      (pow_dvd_pow_of_dvd hpc (a - u)).trans (coeff_linfac_dvd c a u)
    have h2 : p ^ ((tl.map Prod.snd).sum - v) ∣
        ((tl.map (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod * H).coeff v := by
      apply ih v H
      intro q hq; exact hp q (by simp [hq])
    have hle : a + (tl.map Prod.snd).sum - m ≤ (a - u) + ((tl.map Prod.snd).sum - v) := by omega
    refine (pow_dvd_pow p hle).trans ?_
    rw [pow_add]
    exact mul_dvd_mul h1 h2

/-- **Per-prime divisibility (no `H`).**  If `p` divides the base of every factor in `L`, then
`p^{(Σ a_k) − m}` divides the `m`-th coefficient of `∏ (C c_k + X)^{a_k}`.  (Apply with the *sublist*
of `p`-bearing factors; the convolution version absorbs the remaining factors.) -/
theorem coeff_listprod_perprime_dvd (p : ℤ) (L : List (ℤ × ℕ)) (m : ℕ)
    (hp : ∀ q ∈ L, p ∣ q.1) :
    p ^ ((L.map Prod.snd).sum - m) ∣
      ((L.map (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod).coeff m := by
  have h := coeff_listprod_perprime_mul_dvd p L m 1 hp
  simpa using h

/-- **Sharp `5`-adic bound.**  `5^(4n−i) ∣ (Gpoly n).coeff i` (all `i`).
The `5`-bearing factors are `15,10,20` with exponents `2n,n,n`, total `4n`. -/
theorem Gpoly_coeff_dvd_5 (n i : ℕ) :
    (5 : ℤ) ^ (4 * n - i) ∣ (Gpoly n).coeff i := by
  have hp : ∀ q ∈ ([(15, 2 * n), (10, n), (20, n)] : List (ℤ × ℕ)), (5 : ℤ) ∣ q.1 := by
    intro q hq; fin_cases hq <;> norm_num
  have key := coeff_listprod_perprime_mul_dvd 5 [(15, 2 * n), (10, n), (20, n)] i
    ((C 12 + X) ^ n * (C 18 + X) ^ n) hp
  have hsum :
      (([(15, 2 * n), (10, n), (20, n)] : List (ℤ × ℕ)).map Prod.snd).sum = 4 * n := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have hprod :
      (([(15, 2 * n), (10, n), (20, n)] : List (ℤ × ℕ)).map
          (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod * ((C 12 + X) ^ n * (C 18 + X) ^ n)
        = Gpoly n := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Gpoly]; ring
  rw [hsum, hprod] at key
  exact key

/-- **Sharp `2`-adic bound.**  `2^(4n−i) ∣ (Gpoly n).coeff i` (all `i`).
The `2`-bearing factors are `12,18,10,20` with exponents `n,n,n,n`, total `4n`. -/
theorem Gpoly_coeff_dvd_2 (n i : ℕ) :
    (2 : ℤ) ^ (4 * n - i) ∣ (Gpoly n).coeff i := by
  have hp : ∀ q ∈ ([(12, n), (18, n), (10, n), (20, n)] : List (ℤ × ℕ)), (2 : ℤ) ∣ q.1 := by
    intro q hq; fin_cases hq <;> norm_num
  have key := coeff_listprod_perprime_mul_dvd 2 [(12, n), (18, n), (10, n), (20, n)] i
    ((C 15 + X) ^ (2 * n)) hp
  have hsum :
      (([(12, n), (18, n), (10, n), (20, n)] : List (ℤ × ℕ)).map Prod.snd).sum = 4 * n := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have hprod :
      (([(12, n), (18, n), (10, n), (20, n)] : List (ℤ × ℕ)).map
          (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod * ((C 15 + X) ^ (2 * n))
        = Gpoly n := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Gpoly]; ring
  rw [hsum, hprod] at key
  exact key

/-- **Sharp `3`-adic bound.**  `3^(4n−i) ∣ (Gpoly n).coeff i` (all `i`).
The `3`-bearing factors are `15,12,18` with exponents `2n,n,n`, total `4n`. -/
theorem Gpoly_coeff_dvd_3 (n i : ℕ) :
    (3 : ℤ) ^ (4 * n - i) ∣ (Gpoly n).coeff i := by
  have hp : ∀ q ∈ ([(15, 2 * n), (12, n), (18, n)] : List (ℤ × ℕ)), (3 : ℤ) ∣ q.1 := by
    intro q hq; fin_cases hq <;> norm_num
  have key := coeff_listprod_perprime_mul_dvd 3 [(15, 2 * n), (12, n), (18, n)] i
    ((C 10 + X) ^ n * (C 20 + X) ^ n) hp
  have hsum :
      (([(15, 2 * n), (12, n), (18, n)] : List (ℤ × ℕ)).map Prod.snd).sum = 4 * n := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have hprod :
      (([(15, 2 * n), (12, n), (18, n)] : List (ℤ × ℕ)).map
          (fun q => (C q.1 + X : ℤ[X]) ^ q.2)).prod * ((C 10 + X) ^ n * (C 20 + X) ^ n)
        = Gpoly n := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Gpoly]; ring
  rw [hsum, hprod] at key
  exact key

/-! ### 5. Weighted per-prime divisibility (using `v_p` of each base)

The bounds in §4 only count *how many* factors a prime divides, not *how deeply*
(`18 = 2·3²` carries `v_3 = 2`).  For the oSALIKHOV pole-term clearing the sharper *weighted*
bounds are needed:

  `2^(6n−2i) ∣ (Gpoly n).coeff i`   (`v_2`: `12,20 ↦ 2`, `18,10 ↦ 1`; weighted budget `6n`),
  `3^(5n−2i) ∣ (Gpoly n).coeff i`   (`v_3`: `18 ↦ 2`, `15,12 ↦ 1`;     weighted budget `5n`).

The engine carries the per-factor weight `w_k` as list data `(c_k, a_k, w_k)` with `p^{w_k} ∣ c_k`
and a uniform cap `w_k ≤ W`; the conclusion is `p^{(Σ w_k a_k) − W·m}`. -/

/-- The combinatorial `ℕ`-inequality powering the weighted induction step:
`(w·a + T) − W·m ≤ w·(a−u) + (T − W·v)` whenever `w ≤ W` and `u + v = m`.  (All subtraction is
truncated `ℕ`-subtraction.) -/
theorem wt_ineq {w W a u v m T : ℕ} (hw : w ≤ W) (huv : u + v = m) :
    (w * a + T) - W * m ≤ w * (a - u) + (T - W * v) := by
  have hWm : W * m = W * u + W * v := by rw [← huv]; ring
  have hwu : w * u ≤ W * u := Nat.mul_le_mul hw (le_refl u)
  by_cases hua : u ≤ a
  · have key1 : w * (a - u) + w * u = w * a := by rw [← mul_add, Nat.sub_add_cancel hua]
    omega
  · have hau : a ≤ u := by omega
    have hwa0 : w * (a - u) = 0 := by rw [Nat.sub_eq_zero_of_le hau, mul_zero]
    have hwa : w * a ≤ W * u :=
      (Nat.mul_le_mul (le_refl w) hau).trans (Nat.mul_le_mul hw (le_refl u))
    omega

/-- **Weighted per-prime convolution engine.**  Factors are `(c_k, a_k, w_k)` with `p^{w_k} ∣ c_k`
and `w_k ≤ W`.  Then `p^{(Σ w_k a_k) − W·m}` divides the `m`-th coefficient of
`(∏ (C c_k + X)^{a_k}) · H`. -/
theorem coeff_listprod_perprime_wt_mul_dvd (p : ℤ) (W : ℕ) :
    ∀ (L : List (ℤ × ℕ × ℕ)) (m : ℕ) (H : ℤ[X]),
      (∀ q ∈ L, p ^ q.2.2 ∣ q.1 ∧ q.2.2 ≤ W) →
      p ^ ((L.map (fun q => q.2.2 * q.2.1)).sum - W * m) ∣
        ((L.map (fun q => (C q.1 + X : ℤ[X]) ^ q.2.1)).prod * H).coeff m := by
  intro L
  induction L with
  | nil => intro m H _; simp
  | cons hd tl ih =>
    intro m H hq
    obtain ⟨c, a, w⟩ := hd
    obtain ⟨hpw, hwW⟩ := hq (c, a, w) (by simp)
    have hsumeq : (((c, a, w) :: tl).map (fun q => q.2.2 * q.2.1)).sum
        = w * a + (tl.map (fun q => q.2.2 * q.2.1)).sum := by simp
    rw [hsumeq]
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, Polynomial.coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨u, v⟩ huv
    have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
    have h1 : p ^ (w * (a - u)) ∣ ((C c + X : ℤ[X]) ^ a).coeff u := by
      rw [pow_mul]
      exact (pow_dvd_pow_of_dvd hpw (a - u)).trans (coeff_linfac_dvd c a u)
    have h2 : p ^ ((tl.map (fun q => q.2.2 * q.2.1)).sum - W * v) ∣
        ((tl.map (fun q => (C q.1 + X : ℤ[X]) ^ q.2.1)).prod * H).coeff v := by
      apply ih v H
      intro q hq'; exact hq q (by simp [hq'])
    have hle : w * a + (tl.map (fun q => q.2.2 * q.2.1)).sum - W * m
        ≤ w * (a - u) + ((tl.map (fun q => q.2.2 * q.2.1)).sum - W * v) :=
      wt_ineq hwW huvm
    refine (pow_dvd_pow p hle).trans ?_
    rw [pow_add]
    exact mul_dvd_mul h1 h2

/-- **Sharp weighted `2`-adic bound.**  `2^(6n−2i) ∣ (Gpoly n).coeff i`.
Weights `v_2`: `15↦0, 12↦2, 18↦1, 10↦1, 20↦2`; weighted budget `0·2n+2n+n+n+2n = 6n`, cap `W = 2`. -/
theorem Gpoly_coeff_dvd_2w (n i : ℕ) :
    (2 : ℤ) ^ (6 * n - 2 * i) ∣ (Gpoly n).coeff i := by
  have hq : ∀ q ∈ ([(15, 2 * n, 0), (12, n, 2), (18, n, 1), (10, n, 1), (20, n, 2)]
      : List (ℤ × ℕ × ℕ)), (2 : ℤ) ^ q.2.2 ∣ q.1 ∧ q.2.2 ≤ 2 := by
    intro q hq; fin_cases hq <;> exact ⟨by norm_num, by norm_num⟩
  have key := coeff_listprod_perprime_wt_mul_dvd 2 2
    [(15, 2 * n, 0), (12, n, 2), (18, n, 1), (10, n, 1), (20, n, 2)] i 1 hq
  have hsum : (([(15, 2 * n, 0), (12, n, 2), (18, n, 1), (10, n, 1), (20, n, 2)]
      : List (ℤ × ℕ × ℕ)).map (fun q => q.2.2 * q.2.1)).sum = 6 * n := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have hprod : (([(15, 2 * n, 0), (12, n, 2), (18, n, 1), (10, n, 1), (20, n, 2)]
      : List (ℤ × ℕ × ℕ)).map (fun q => (C q.1 + X : ℤ[X]) ^ q.2.1)).prod * 1 = Gpoly n := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Gpoly]; ring
  rw [hsum, hprod] at key
  exact key

/-- **Sharp weighted `3`-adic bound.**  `3^(5n−2i) ∣ (Gpoly n).coeff i`.
Weights `v_3`: `15↦1, 12↦1, 18↦2, 10↦0, 20↦0`; weighted budget `2n+n+2n = 5n`, cap `W = 2`. -/
theorem Gpoly_coeff_dvd_3w (n i : ℕ) :
    (3 : ℤ) ^ (5 * n - 2 * i) ∣ (Gpoly n).coeff i := by
  have hq : ∀ q ∈ ([(15, 2 * n, 1), (12, n, 1), (18, n, 2), (10, n, 0), (20, n, 0)]
      : List (ℤ × ℕ × ℕ)), (3 : ℤ) ^ q.2.2 ∣ q.1 ∧ q.2.2 ≤ 2 := by
    intro q hq; fin_cases hq <;> exact ⟨by norm_num, by norm_num⟩
  have key := coeff_listprod_perprime_wt_mul_dvd 3 2
    [(15, 2 * n, 1), (12, n, 1), (18, n, 2), (10, n, 0), (20, n, 0)] i 1 hq
  have hsum : (([(15, 2 * n, 1), (12, n, 1), (18, n, 2), (10, n, 0), (20, n, 0)]
      : List (ℤ × ℕ × ℕ)).map (fun q => q.2.2 * q.2.1)).sum = 5 * n := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have hprod : (([(15, 2 * n, 1), (12, n, 1), (18, n, 2), (10, n, 0), (20, n, 0)]
      : List (ℤ × ℕ × ℕ)).map (fun q => (C q.1 + X : ℤ[X]) ^ q.2.1)).prod * 1 = Gpoly n := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Gpoly]; ring
  rw [hsum, hprod] at key
  exact key

end OSalikhovGCoeff
