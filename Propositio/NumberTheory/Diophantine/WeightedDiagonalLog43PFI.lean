import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Residue
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# The cleared partial-fraction identity (PFI) for the weighted two-pole diagonal `Jₙ`

`WeightedDiagonalLog43Residue` defines the integer residues `aRes n j`, `bRes n j` as polynomial
coefficients of the truncated generating products.  Here we prove the **cleared partial-fraction
identity**

  `Xⁿ(1−X)ⁿ = Apoly n · (2+X)ⁿ⁺¹ + (1+X)ⁿ⁺¹ · Bpoly n`   (`PFI`)

where `Apoly n = ∑_{j=1}^{n+1} aRes n j · (1+X)ⁿ⁺¹⁻ʲ` and `Bpoly n = ∑_{j=1}^{n+1} bRes n j ·
(2+X)ⁿ⁺¹⁻ʲ` are the principal-part polynomials.  This is the algebraic heart of the single-log
integral identity `Jₙ = Pₙ + α₁(n)·log(4/3)`.

## Proof architecture

* **Truncated binomial inverse** (`serPos_inv`, `serNeg_inv`): `serPos n · (1−X)ⁿ⁺¹ ≡ 1` and
  `serNeg n · (1+X)ⁿ⁺¹ ≡ 1` modulo `Xⁿ⁺¹`.  These are *exact* in `ℤ⟦X⟧` via mathlib's
  `PowerSeries.invOneSubPow` (whose coefficients are `C(n+s,n)` = `serPos`); the `serNeg` version is
  the `rescale (−1)` image.
* **Local identities** (`LocalA`, `LocalB`): `Xⁿ⁺¹ ∣ (X−1)ⁿ(2−X)ⁿ − Apar n · (1+X)ⁿ⁺¹` etc., from
  the truncated inverse times `(X−1)ⁿ(2−X)ⁿ`.
* **Substitution** `X ↦ 1+X` (resp. `2+X`) (a ring hom, preserving divisibility) turns the local
  identities into the per-pole divisibilities `C1`, `C2`.
* **CRT + degree** (`PFI`): `(1+X)ⁿ⁺¹`, `(2+X)ⁿ⁺¹` are coprime, both divide the difference `D`,
  hence so does their product (degree `2n+2`); but `deg D ≤ 2n+1`, forcing `D = 0`.
* **Residue-sum-zero** (`aRes_one_add_bRes_one`): the `X^{2n+1}` coefficient of `PFI`.
-/

namespace WeightedDiagonalLog43

open Polynomial

/-! ### Coefficients of the truncated generating polynomials -/

/-- For `i ≤ n`, the `i`-th coefficient of `serPos n` is `C(n+i, n)`. -/
theorem serPos_coeff {n i : ℕ} (hi : i ≤ n) :
    (serPos n).coeff i = (Nat.choose (n + i) n : ℤ) := by
  unfold serPos
  rw [Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg (by omega), mul_zero]
  · intro hni
    exact absurd (Finset.mem_range.mpr (by omega)) hni

/-- For `i ≤ n`, the `i`-th coefficient of `serNeg n` is `(−1)ⁱ·C(n+i, n)`. -/
theorem serNeg_coeff {n i : ℕ} (hi : i ≤ n) :
    (serNeg n).coeff i = ((-1) ^ i * Nat.choose (n + i) n : ℤ) := by
  unfold serNeg
  rw [Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg (by omega), mul_zero]
  · intro hni
    exact absurd (Finset.mem_range.mpr (by omega)) hni

/-! ### The exact power-series inverses (mathlib `invOneSubPow`) -/

/-- `(∑ C(n+s,n) Xˢ)·(1−X)ⁿ⁺¹ = 1` in `ℤ⟦X⟧`. -/
theorem gPos_mul (n : ℕ) :
    (PowerSeries.mk fun s => (Nat.choose (n + s) n : ℤ)) * (1 - PowerSeries.X) ^ (n + 1) = 1 :=
  PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℤ n

/-- `(∑ (−1)ˢ C(n+s,n) Xˢ)·(1+X)ⁿ⁺¹ = 1` in `ℤ⟦X⟧` — the `rescale (−1)` image of `gPos_mul`. -/
theorem gNeg_mul (n : ℕ) :
    (PowerSeries.mk fun s => ((-1) ^ s * Nat.choose (n + s) n : ℤ)) * (1 + PowerSeries.X) ^ (n + 1)
      = 1 := by
  have hg : (PowerSeries.mk fun s => ((-1) ^ s * Nat.choose (n + s) n : ℤ))
      = PowerSeries.rescale (-1) (PowerSeries.mk fun s => (Nat.choose (n + s) n : ℤ)) := by
    rw [PowerSeries.rescale_mk]
  have h1 : PowerSeries.rescale (-1) (1 - PowerSeries.X) = (1 + PowerSeries.X : PowerSeries ℤ) := by
    rw [map_sub, map_one, PowerSeries.rescale_X, map_neg, map_one]; ring
  rw [hg, ← h1, ← map_pow, ← map_mul, gPos_mul, map_one]

/-! ### The truncated-inverse congruences -/

/-- **Truncated inverse, pole `x = −1`.**  `Xⁿ⁺¹ ∣ serNeg n · (1+X)ⁿ⁺¹ − 1`. -/
theorem serNeg_inv (n : ℕ) :
    (X : ℤ[X]) ^ (n + 1) ∣ (serNeg n * (1 + X) ^ (n + 1) - 1) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_one]
  -- transfer the product coefficient to power series
  have hcoe : (serNeg n * (1 + X) ^ (n + 1)).coeff m
      = PowerSeries.coeff m
          ((serNeg n : PowerSeries ℤ) * (1 + PowerSeries.X) ^ (n + 1)) := by
    rw [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_X]
  rw [hcoe]
  -- replace ↑(serNeg n) by gNeg up to coeff m (≤ n)
  have hrepl : PowerSeries.coeff m
        ((serNeg n : PowerSeries ℤ) * (1 + PowerSeries.X) ^ (n + 1))
      = PowerSeries.coeff m
          ((PowerSeries.mk fun s => ((-1) ^ s * Nat.choose (n + s) n : ℤ))
            * (1 + PowerSeries.X) ^ (n + 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hi : i ≤ m := by
      have := Finset.mem_antidiagonal.mp hij; omega
    have hin : i ≤ n := le_trans hi hmn
    congr 1
    rw [Polynomial.coeff_coe, serNeg_coeff hin, PowerSeries.coeff_mk]
  rw [hrepl, gNeg_mul, PowerSeries.coeff_one]
  by_cases h : m = 0 <;> simp [h]

/-- **Truncated inverse, pole `x = −2` frame.**  `Xⁿ⁺¹ ∣ serPos n · (1−X)ⁿ⁺¹ − 1`. -/
theorem serPos_inv (n : ℕ) :
    (X : ℤ[X]) ^ (n + 1) ∣ (serPos n * (1 - X) ^ (n + 1) - 1) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_one]
  have hcoe : (serPos n * (1 - X) ^ (n + 1)).coeff m
      = PowerSeries.coeff m
          ((serPos n : PowerSeries ℤ) * (1 - PowerSeries.X) ^ (n + 1)) := by
    rw [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X]
  rw [hcoe]
  have hrepl : PowerSeries.coeff m
        ((serPos n : PowerSeries ℤ) * (1 - PowerSeries.X) ^ (n + 1))
      = PowerSeries.coeff m
          ((PowerSeries.mk fun s => (Nat.choose (n + s) n : ℤ))
            * (1 - PowerSeries.X) ^ (n + 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hi : i ≤ m := by
      have := Finset.mem_antidiagonal.mp hij; omega
    have hin : i ≤ n := le_trans hi hmn
    congr 1
    rw [Polynomial.coeff_coe, serPos_coeff hin, PowerSeries.coeff_mk]
  rw [hrepl, gPos_mul, PowerSeries.coeff_one]
  by_cases h : m = 0 <;> simp [h]

/-! ### Principal-part polynomials and the local identities -/

/-- `PaA n = (X−1)ⁿ(2−X)ⁿ·serNeg n` — the pole-`x=−1` generating product (`aRes` reads its coeffs). -/
noncomputable def PaA (n : ℕ) : ℤ[X] := (X - 1) ^ n * (2 - X) ^ n * serNeg n

/-- `QB n = (−1)ⁿ⁺¹·(X−2)ⁿ(3−X)ⁿ·serPos n` — the pole-`x=−2` product (`bRes` reads its coeffs). -/
noncomputable def QB (n : ℕ) : ℤ[X] := C ((-1) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n * serPos n)

theorem aRes_eq_PaA (n j : ℕ) : aRes n j = (PaA n).coeff (n + 1 - j) := rfl

theorem bRes_eq_QB (n j : ℕ) : bRes n j = (QB n).coeff (n + 1 - j) := by
  unfold bRes QB
  rw [Polynomial.coeff_C_mul]

/-- `Apar n` = degree-`≤n` truncation of `PaA n` (in the `t = 1+x` frame). -/
noncomputable def Apar (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range (n + 1), C ((PaA n).coeff i) * X ^ i

/-- `Bpar n` = degree-`≤n` truncation of `QB n` (in the `s = 2+x` frame). -/
noncomputable def Bpar (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range (n + 1), C ((QB n).coeff i) * X ^ i

/-- The principal-part polynomial at `x=−1`: `Apoly n = ∑_{j=1}^{n+1} aRes n j·(1+X)ⁿ⁺¹⁻ʲ`,
written over `i = n+1−j`. -/
noncomputable def Apoly (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (n + 1), C (aRes n (n + 1 - i)) * (1 + X) ^ i

/-- The principal-part polynomial at `x=−2`: `Bpoly n = ∑_{j=1}^{n+1} bRes n j·(2+X)ⁿ⁺¹⁻ʲ`. -/
noncomputable def Bpoly (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (n + 1), C (bRes n (n + 1 - i)) * (2 + X) ^ i

/-- **Generic truncation divisibility.**  `Xⁿ⁺¹ ∣ p − trunc_{n+1}(p)`. -/
theorem trunc_sub_dvd (p : ℤ[X]) (n : ℕ) :
    (X : ℤ[X]) ^ (n + 1) ∣ (p - ∑ i ∈ Finset.range (n + 1), C (p.coeff i) * X ^ i) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  rw [Polynomial.coeff_sub]
  have hsum : (∑ i ∈ Finset.range (n + 1), C (p.coeff i) * X ^ i).coeff m = p.coeff m := by
    rw [Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; rw [if_neg (by omega), mul_zero]
    · intro hni; exact absurd (Finset.mem_range.mpr hm) hni
  rw [hsum, sub_self]

/-- `Apoly n = aeval (1+X) (Apar n)` — the substitution `X ↦ 1+x` carries the truncation to the
principal part. -/
theorem Apoly_eq (n : ℕ) : Apoly n = Polynomial.aeval (1 + X : ℤ[X]) (Apar n) := by
  unfold Apoly Apar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.algebraMap_eq]
  congr 2
  rw [aRes_eq_PaA]
  congr 1
  omega

/-- `Bpoly n = aeval (2+X) (Bpar n)`. -/
theorem Bpoly_eq (n : ℕ) : Bpoly n = Polynomial.aeval (2 + X : ℤ[X]) (Bpar n) := by
  unfold Bpoly Bpar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.algebraMap_eq]
  congr 2
  rw [bRes_eq_QB]
  congr 1
  omega

/-! ### The local divisibilities and the per-pole identities `C1`, `C2` -/

/-- **`C1`**: `(1+X)ⁿ⁺¹ ∣ Xⁿ(1−X)ⁿ − Apoly n·(2+X)ⁿ⁺¹`. -/
theorem C1 (n : ℕ) :
    (1 + X : ℤ[X]) ^ (n + 1) ∣ ((X) ^ n * (1 - X) ^ n - Apoly n * (2 + X) ^ (n + 1)) := by
  -- local identity in the t-frame
  have hLocalA : (X : ℤ[X]) ^ (n + 1) ∣ ((X - 1) ^ n * (2 - X) ^ n - Apar n * (1 + X) ^ (n + 1)) := by
    have d1 : (X : ℤ[X]) ^ (n + 1) ∣ ((X - 1) ^ n * (2 - X) ^ n - PaA n * (1 + X) ^ (n + 1)) := by
      have hbase := (serNeg_inv n).mul_left ((X - 1) ^ n * (2 - X) ^ n)
      have heq : ((X : ℤ[X]) - 1) ^ n * (2 - X) ^ n * (serNeg n * (1 + X) ^ (n + 1) - 1)
          = PaA n * (1 + X) ^ (n + 1) - (X - 1) ^ n * (2 - X) ^ n := by unfold PaA; ring
      rw [heq] at hbase
      have := dvd_neg.mpr hbase
      rwa [neg_sub] at this
    have d2 : (X : ℤ[X]) ^ (n + 1) ∣ ((PaA n - Apar n) * (1 + X) ^ (n + 1)) :=
      Dvd.dvd.mul_right (trunc_sub_dvd (PaA n) n) _
    have hsplit : ((X - 1) ^ n * (2 - X) ^ n - Apar n * (1 + X) ^ (n + 1))
        = ((X - 1) ^ n * (2 - X) ^ n - PaA n * (1 + X) ^ (n + 1))
          + (PaA n - Apar n) * (1 + X) ^ (n + 1) := by ring
    rw [hsplit]; exact dvd_add d1 d2
  -- substitution X ↦ 1+X
  have himg := map_dvd (Polynomial.aeval (1 + X : ℤ[X])) hLocalA
  have haX : Polynomial.aeval (1 + X : ℤ[X]) ((X : ℤ[X]) - 1) = X := by
    rw [map_sub, Polynomial.aeval_X, map_one]; ring
  have ha2X : Polynomial.aeval (1 + X : ℤ[X]) ((2 : ℤ[X]) - X) = 1 - X := by
    rw [map_sub, map_ofNat, Polynomial.aeval_X]; ring
  have ha1X : Polynomial.aeval (1 + X : ℤ[X]) ((1 : ℤ[X]) + X) = 2 + X := by
    rw [map_add, map_one, Polynomial.aeval_X]; ring
  simp only [map_sub, map_mul, map_pow, haX, ha2X, ha1X] at himg
  rw [← Apoly_eq, Polynomial.aeval_X] at himg
  exact himg

/-- **`C2`**: `(2+X)ⁿ⁺¹ ∣ Xⁿ(1−X)ⁿ − (1+X)ⁿ⁺¹·Bpoly n`. -/
theorem C2 (n : ℕ) :
    (2 + X : ℤ[X]) ^ (n + 1) ∣ ((X) ^ n * (1 - X) ^ n - (1 + X) ^ (n + 1) * Bpoly n) := by
  have hLocalB : (X : ℤ[X]) ^ (n + 1)
      ∣ (C ((-1) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n) - Bpar n * (1 - X) ^ (n + 1)) := by
    have d1 : (X : ℤ[X]) ^ (n + 1)
        ∣ (C ((-1) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n) - QB n * (1 - X) ^ (n + 1)) := by
      have hbase := (serPos_inv n).mul_left (C ((-1 : ℤ) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n))
      have heq : C ((-1 : ℤ) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n)
            * (serPos n * (1 - X) ^ (n + 1) - 1)
          = QB n * (1 - X) ^ (n + 1) - C ((-1) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n) := by
        unfold QB; ring
      rw [heq] at hbase
      have := dvd_neg.mpr hbase
      rwa [neg_sub] at this
    have d2 : (X : ℤ[X]) ^ (n + 1) ∣ ((QB n - Bpar n) * (1 - X) ^ (n + 1)) :=
      Dvd.dvd.mul_right (trunc_sub_dvd (QB n) n) _
    have hsplit : (C ((-1 : ℤ) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n) - Bpar n * (1 - X) ^ (n + 1))
        = (C ((-1) ^ (n + 1)) * ((X - 2) ^ n * (3 - X) ^ n) - QB n * (1 - X) ^ (n + 1))
          + (QB n - Bpar n) * (1 - X) ^ (n + 1) := by ring
    rw [hsplit]; exact dvd_add d1 d2
  have himg := map_dvd (Polynomial.aeval (2 + X : ℤ[X])) hLocalB
  have hbX : Polynomial.aeval (2 + X : ℤ[X]) ((X : ℤ[X]) - 2) = X := by
    rw [map_sub, Polynomial.aeval_X, map_ofNat]; ring
  have hb3X : Polynomial.aeval (2 + X : ℤ[X]) ((3 : ℤ[X]) - X) = 1 - X := by
    rw [map_sub, map_ofNat, Polynomial.aeval_X]; ring
  have hb1X : Polynomial.aeval (2 + X : ℤ[X]) ((1 : ℤ[X]) - X) = -1 - X := by
    rw [map_sub, map_one, Polynomial.aeval_X]; ring
  have hbC : Polynomial.aeval (2 + X : ℤ[X]) (C ((-1 : ℤ) ^ (n + 1))) = C ((-1) ^ (n + 1)) := by
    rw [Polynomial.aeval_C, Polynomial.algebraMap_eq]
  simp only [map_sub, map_mul, map_pow, hbX, hb3X, hb1X, Polynomial.aeval_C,
    Polynomial.algebraMap_eq] at himg
  rw [← Bpoly_eq, Polynomial.aeval_X,
    show (C (-1 : ℤ) : ℤ[X]) = -1 from by rw [map_neg, map_one]] at himg
  -- himg : (2+X)^(n+1) ∣ (-1)^(n+1)*(X^n*(1-X)^n) - Bpoly n * (-1-X)^(n+1)
  have hneg : ((-1 : ℤ[X]) - X) ^ (n + 1) = (-1) ^ (n + 1) * (1 + X) ^ (n + 1) := by
    rw [show (-1 : ℤ[X]) - X = (-1) * (1 + X) by ring, mul_pow]
  have hrw : (-1 : ℤ[X]) ^ (n + 1) * ((X) ^ n * (1 - X) ^ n)
        - Bpoly n * ((-1 : ℤ[X]) - X) ^ (n + 1)
      = (-1) ^ (n + 1) * ((X) ^ n * (1 - X) ^ n - (1 + X) ^ (n + 1) * Bpoly n) := by
    rw [hneg]; ring
  rw [hrw] at himg
  -- strip the unit (-1)^(n+1)
  have hunit : (-1 : ℤ[X]) ^ (n + 1)
        * ((-1 : ℤ[X]) ^ (n + 1) * ((X) ^ n * (1 - X) ^ n - (1 + X) ^ (n + 1) * Bpoly n))
      = (X) ^ n * (1 - X) ^ n - (1 + X) ^ (n + 1) * Bpoly n := by
    rw [← mul_assoc, ← mul_pow]; norm_num
  have h2 := himg.mul_left ((-1 : ℤ[X]) ^ (n + 1))
  rwa [hunit] at h2

/-! ### Monic degree facts for the CRT/degree finish -/

theorem natDegree_one_add_X : (1 + X : ℤ[X]).natDegree = 1 := by
  rw [show (1 + X : ℤ[X]) = X + C 1 by rw [Polynomial.C_1]; ring]; exact natDegree_X_add_C 1

theorem natDegree_two_add_X : (2 + X : ℤ[X]).natDegree = 1 := by
  rw [show (2 + X : ℤ[X]) = X + C 2 from by rw [show (C (2 : ℤ) : ℤ[X]) = 2 from map_ofNat C 2]; ring]
  exact natDegree_X_add_C 2

theorem monic_one_add_X : (1 + X : ℤ[X]).Monic := by
  rw [show (1 + X : ℤ[X]) = X + C 1 by rw [Polynomial.C_1]; ring]; exact monic_X_add_C 1

theorem monic_two_add_X : (2 + X : ℤ[X]).Monic := by
  rw [show (2 + X : ℤ[X]) = X + C 2 from by rw [show (C (2 : ℤ) : ℤ[X]) = 2 from map_ofNat C 2]; ring]
  exact monic_X_add_C 2

theorem natDegree_Apoly_le (n : ℕ) : (Apoly n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc (C (aRes n (n + 1 - i)) * (1 + X) ^ i).natDegree
      ≤ ((1 + X : ℤ[X]) ^ i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ i * (1 + X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ ≤ n := by rw [natDegree_one_add_X]; omega

theorem natDegree_Bpoly_le (n : ℕ) : (Bpoly n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc (C (bRes n (n + 1 - i)) * (2 + X) ^ i).natDegree
      ≤ ((2 + X : ℤ[X]) ^ i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ i * (2 + X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ ≤ n := by rw [natDegree_two_add_X]; omega

/-- **PFI — the cleared partial-fraction identity.**
`Xⁿ(1−X)ⁿ = Apoly n · (2+X)ⁿ⁺¹ + (1+X)ⁿ⁺¹ · Bpoly n`. -/
theorem PFI (n : ℕ) :
    (X : ℤ[X]) ^ n * (1 - X) ^ n = Apoly n * (2 + X) ^ (n + 1) + (1 + X) ^ (n + 1) * Bpoly n := by
  set D : ℤ[X] := (X) ^ n * (1 - X) ^ n - Apoly n * (2 + X) ^ (n + 1) - (1 + X) ^ (n + 1) * Bpoly n
    with hDdef
  have hd1 : (1 + X : ℤ[X]) ^ (n + 1) ∣ D := by
    have hsp : D = ((X) ^ n * (1 - X) ^ n - Apoly n * (2 + X) ^ (n + 1))
        - (1 + X) ^ (n + 1) * Bpoly n := by rw [hDdef]; try ring
    rw [hsp]; exact dvd_sub (C1 n) (Dvd.dvd.mul_right (dvd_refl _) _)
  have hd2 : (2 + X : ℤ[X]) ^ (n + 1) ∣ D := by
    have hsp : D = ((X) ^ n * (1 - X) ^ n - (1 + X) ^ (n + 1) * Bpoly n)
        - Apoly n * (2 + X) ^ (n + 1) := by rw [hDdef]; ring
    rw [hsp]; exact dvd_sub (C2 n) (Dvd.dvd.mul_left (dvd_refl _) _)
  have hcop : IsCoprime ((1 + X : ℤ[X]) ^ (n + 1)) ((2 + X) ^ (n + 1)) :=
    (IsCoprime.pow (⟨-1, 1, by ring⟩ : IsCoprime (1 + X : ℤ[X]) (2 + X)))
  have hdvd : ((1 + X : ℤ[X]) ^ (n + 1) * (2 + X) ^ (n + 1)) ∣ D := hcop.mul_dvd hd1 hd2
  have hD0 : D = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    have hprod : ((1 + X : ℤ[X]) ^ (n + 1) * (2 + X) ^ (n + 1)).natDegree = 2 * n + 2 := by
      rw [Polynomial.natDegree_mul (monic_one_add_X.pow _).ne_zero (monic_two_add_X.pow _).ne_zero,
        Polynomial.natDegree_pow, Polynomial.natDegree_pow, natDegree_one_add_X, natDegree_two_add_X]
      ring
    have hDle : D.natDegree ≤ 2 * n + 1 := by
      rw [hDdef]
      apply le_trans (Polynomial.natDegree_sub_le _ _)
      apply max_le
      · apply le_trans (Polynomial.natDegree_sub_le _ _)
        apply max_le
        · have hXn : ((X : ℤ[X]) ^ n).natDegree = n := by
            rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
          have h1X : (1 - X : ℤ[X]).natDegree ≤ 1 := by
            apply le_trans (Polynomial.natDegree_sub_le _ _); simp
          have h1Xn : ((1 - X : ℤ[X]) ^ n).natDegree ≤ n := by
            refine le_trans Polynomial.natDegree_pow_le ?_
            calc n * (1 - X : ℤ[X]).natDegree ≤ n * 1 := Nat.mul_le_mul le_rfl h1X
              _ = n := mul_one n
          calc ((X : ℤ[X]) ^ n * (1 - X) ^ n).natDegree
              ≤ ((X : ℤ[X]) ^ n).natDegree + ((1 - X : ℤ[X]) ^ n).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 2 * n + 1 := by rw [hXn]; omega
        · calc (Apoly n * (2 + X) ^ (n + 1)).natDegree
              ≤ (Apoly n).natDegree + ((2 + X : ℤ[X]) ^ (n + 1)).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 2 * n + 1 := by
                rw [Polynomial.natDegree_pow, natDegree_two_add_X]
                have := natDegree_Apoly_le n; omega
      · calc ((1 + X : ℤ[X]) ^ (n + 1) * Bpoly n).natDegree
            ≤ ((1 + X : ℤ[X]) ^ (n + 1)).natDegree + (Bpoly n).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 2 * n + 1 := by
              rw [Polynomial.natDegree_pow, natDegree_one_add_X]
              have := natDegree_Bpoly_le n; omega
    rw [hprod] at hle
    omega
  have hD0' : (X : ℤ[X]) ^ n * (1 - X) ^ n - Apoly n * (2 + X) ^ (n + 1)
      - (1 + X) ^ (n + 1) * Bpoly n = 0 := by rw [← hDdef]; exact hD0
  linear_combination hD0'

/-! ### Leading coefficients and residue-sum-zero -/

/-- For polynomials with `natDegree ≤ a`, `≤ b`, the top product coefficient factors. -/
theorem coeff_mul_top (p q : ℤ[X]) (a b : ℕ) (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨i, j⟩ hc hne
    rw [Finset.mem_antidiagonal] at hc
    rcases lt_or_ge i a with h | h
    · have hjb : b < j := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hjb), mul_zero]
    · have hia : a < i := by
        rcases h.lt_or_eq with h' | h'
        · exact h'
        · exact absurd (Prod.ext_iff.mpr ⟨h'.symm, by omega⟩) hne
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hia), zero_mul]
  · intro h; exact (h (by simp [Finset.mem_antidiagonal])).elim

/-- `(Apoly n).coeff n = aRes n 1` (top residue at the pole `x=−1`). -/
theorem coeff_Apoly_n (n : ℕ) : (Apoly n).coeff n = aRes n 1 := by
  unfold Apoly
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single n]
  · rw [Polynomial.coeff_C_mul, show n + 1 - n = 1 from by omega]
    have hnd : ((1 + X : ℤ[X]) ^ n).natDegree = n := by
      rw [Polynomial.natDegree_pow, natDegree_one_add_X, mul_one]
    have hcn : ((1 + X : ℤ[X]) ^ n).coeff n = 1 := by
      have h := (monic_one_add_X.pow n).coeff_natDegree; rwa [hnd] at h
    rw [hcn, mul_one]
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Polynomial.natDegree_pow, natDegree_one_add_X, mul_one]; omega), mul_zero]
  · intro hni; exact absurd (Finset.mem_range.mpr (by omega)) hni

/-- `(Bpoly n).coeff n = bRes n 1` (top residue at the pole `x=−2`). -/
theorem coeff_Bpoly_n (n : ℕ) : (Bpoly n).coeff n = bRes n 1 := by
  unfold Bpoly
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single n]
  · rw [Polynomial.coeff_C_mul, show n + 1 - n = 1 from by omega]
    have hnd : ((2 + X : ℤ[X]) ^ n).natDegree = n := by
      rw [Polynomial.natDegree_pow, natDegree_two_add_X, mul_one]
    have hcn : ((2 + X : ℤ[X]) ^ n).coeff n = 1 := by
      have h := (monic_two_add_X.pow n).coeff_natDegree; rwa [hnd] at h
    rw [hcn, mul_one]
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Polynomial.natDegree_pow, natDegree_two_add_X, mul_one]; omega), mul_zero]
  · intro hni; exact absurd (Finset.mem_range.mpr (by omega)) hni

/-- **Residue-sum-zero** `aRes n 1 + bRes n 1 = 0` — the `X^{2n+1}` coefficient of `PFI`
(the integrand decays like `1/x²` at `∞`, so the simple-residue sum vanishes). -/
theorem aRes_one_add_bRes_one (n : ℕ) : aRes n 1 + bRes n 1 = 0 := by
  have hA : (Apoly n * (2 + X) ^ (n + 1)).coeff (n + (n + 1)) = aRes n 1 := by
    rw [coeff_mul_top (Apoly n) ((2 + X) ^ (n + 1)) n (n + 1) (natDegree_Apoly_le n)
        (le_of_eq (by rw [Polynomial.natDegree_pow, natDegree_two_add_X, mul_one])), coeff_Apoly_n]
    have hnd : ((2 + X : ℤ[X]) ^ (n + 1)).natDegree = n + 1 := by
      rw [Polynomial.natDegree_pow, natDegree_two_add_X, mul_one]
    have hcn : ((2 + X : ℤ[X]) ^ (n + 1)).coeff (n + 1) = 1 := by
      have h := (monic_two_add_X.pow (n + 1)).coeff_natDegree; rwa [hnd] at h
    rw [hcn, mul_one]
  have hB : ((1 + X) ^ (n + 1) * Bpoly n).coeff (n + (n + 1)) = bRes n 1 := by
    rw [show n + (n + 1) = (n + 1) + n from by ring,
      coeff_mul_top ((1 + X) ^ (n + 1)) (Bpoly n) (n + 1) n
        (le_of_eq (by rw [Polynomial.natDegree_pow, natDegree_one_add_X, mul_one]))
        (natDegree_Bpoly_le n), coeff_Bpoly_n]
    have hnd : ((1 + X : ℤ[X]) ^ (n + 1)).natDegree = n + 1 := by
      rw [Polynomial.natDegree_pow, natDegree_one_add_X, mul_one]
    have hcn : ((1 + X : ℤ[X]) ^ (n + 1)).coeff (n + 1) = 1 := by
      have h := (monic_one_add_X.pow (n + 1)).coeff_natDegree; rwa [hnd] at h
    rw [hcn, one_mul]
  have hL : ((X : ℤ[X]) ^ n * (1 - X) ^ n).coeff (n + (n + 1)) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h1X : (1 - X : ℤ[X]).natDegree ≤ 1 := by
      apply le_trans (Polynomial.natDegree_sub_le _ _); simp
    have h1Xn : ((1 - X : ℤ[X]) ^ n).natDegree ≤ n := by
      refine le_trans Polynomial.natDegree_pow_le ?_
      calc n * (1 - X : ℤ[X]).natDegree ≤ n * 1 := Nat.mul_le_mul le_rfl h1X
        _ = n := mul_one n
    have hXn : ((X : ℤ[X]) ^ n).natDegree = n := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
    calc ((X : ℤ[X]) ^ n * (1 - X) ^ n).natDegree
        ≤ ((X : ℤ[X]) ^ n).natDegree + ((1 - X : ℤ[X]) ^ n).natDegree :=
          Polynomial.natDegree_mul_le
      _ < n + (n + 1) := by rw [hXn]; omega
  have key := congrArg (fun p : ℤ[X] => p.coeff (n + (n + 1))) (PFI n)
  simp only [Polynomial.coeff_add] at key
  rw [hA, hB, hL] at key
  linarith [key]

end WeightedDiagonalLog43

