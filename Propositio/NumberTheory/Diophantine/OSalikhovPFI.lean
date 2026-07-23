import Propositio.NumberTheory.Diophantine.OSalikhovCertificate
import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Partial-fraction integral identity (PFI) for the oSALIKHOV two-log integrand

Goal: the "connection identity" that closes `hdvd` for the μ(log₂3) prize.  The integrand

  `fOsal n x = x^(2n)(x²−9)^n(x²−25)^n / (x²−225)^(2n+1)`,

even, with double-order poles at `±15` (order `2n+1`).  Its partial fraction (over the proper part)
is

  `fOsal n = Pₙ(x) + Σ_{j=1}^{2n+1} c_j/(x−15)^j + Σ_{j=1}^{2n+1} d_j/(x+15)^j`,

with `Pₙ = numZ /ₘ denZ`, `d_j = (−1)^j c_j`, and `c_j = [t^{2n+1−j}] g(t)`,
`g(t) = (15+t)^{2n}(12+t)^n(18+t)^n(10+t)^n(20+t)^n/(30+t)^{2n+1}`.

Integrating over `[0,3]`:  the `j=1` log part collapses to `c_1·log(2/3)` (since `d_1 = −c_1` and
`log(12/15) − log(18/15) = log(2/3)`), and `c_1 = Bseq n` is verified.  Combined with
`E1_decomp : E1 = A1seq + Bseq·log(2/3)` and `Irrational (log (2/3))`, this gives the explicit
rational form of `A1seq` that closes `hdvd`.

## Status of this file (mirrors the COMPLETED log43 route in `WeightedDiagonalLog43{PFI,Star,Integrals}`)

PROVED, axiom-clean bricks:
* `numZ`, `denZ`, `denZ_monic`, `polyPartZ`, `remZ`, `numZ_div_identity` — the polynomial Euclidean
  division identity `numZ = denZ·polyPartZ + remZ` (the polynomial part = `numZ /ₘ denZ`).
* `aeval_numZ`, `aeval_denZ`, `fOsal_eq_div`, `aeval_denZ_ne_zero_of_lt`,
  `fOsal_eq_polyPart_add_rem` — `fOsal n x = Pₙ(x) + remₙ(x)/denₙ(x)` (the proper-fraction split,
  fully proved).
* **Brick 2** (the termwise integration lemmas, self-contained calculus):
  `integral_sub15_inv`, `integral_add15_inv`, `integral_sub15_zpow`, `integral_add15_zpow`.

PRECISE remaining `sorry`s (the genuinely deep content):
* `rem_div_den_partialFraction` — the residue partial fraction of the *proper* fraction
  `remₙ/denₙ` into principal parts at `±15` with coefficients `cResR/dResR`.
* `cResQ_one_eq_Bseq` — the verified simple-residue relation `c_1 = Bseq n`.  Its base window
  `n = 0,1,2` is now PROVED (`cResQ_zero_one`, `cResQ_one_one`, `cResQ_two_one`, via `gNum_C` +
  `lin_pow_coeff` finite coefficient computation), and the residual gap is isolated to the order-3
  recurrence for `n ↦ cResR n 1` by `cResR_one_eq_Bseq_of_rec` (the analog of
  `WeightedDiagonalLog43.JP_eq_Pexpl_of_rec`).

`E1_eq` (the assembly: integrate the PF expansion termwise) is fully PROVED modulo the two `sorry`s
above (`rem_div_den_partialFraction`, `cResQ_one_eq_Bseq`).

`A1seq_eq` (the `hdvd`-closing identity `A1seq = A1explicit`) is then PROVED from `E1_eq` +
`E1_decomp` by `add_right_cancel` — both decompositions carry the same `Bseq·log(2/3)` term, so no
irrationality input is needed.
-/

namespace OSalikhovPFI

open Polynomial
open OSalikhovTwoLog OSalikhovSequences OSalikhovHeight
open scoped BigOperators

/-! ## Brick 1a — the integer polynomials and the Euclidean division identity -/

/-- Numerator polynomial `numZ n = X^{2n}(X²−9)^n(X²−25)^n ∈ ℤ[X]`. -/
noncomputable def numZ (n : ℕ) : ℤ[X] := X ^ (2 * n) * (X ^ 2 - 9) ^ n * (X ^ 2 - 25) ^ n

/-- Denominator polynomial `denZ n = (X²−225)^{2n+1} ∈ ℤ[X]` (monic). -/
noncomputable def denZ (n : ℕ) : ℤ[X] := (X ^ 2 - 225) ^ (2 * n + 1)

/-- `denZ n` is monic (the base `X²−225 = X² − C 225` is monic, raised to a power). -/
theorem denZ_monic (n : ℕ) : (denZ n).Monic := by
  have hb : (X ^ 2 - 225 : ℤ[X]) = X ^ 2 - C (225 : ℤ) := by
    rw [show (225 : ℤ[X]) = C (225 : ℤ) from (map_ofNat C 225).symm]
  unfold denZ; rw [hb]
  exact (monic_X_pow_sub_C (225 : ℤ) (by norm_num)).pow _

/-- The polynomial part `Pₙ = numZ /ₘ denZ`. -/
noncomputable def polyPartZ (n : ℕ) : ℤ[X] := numZ n /ₘ denZ n

/-- The residue-remainder `remₙ = numZ %ₘ denZ` (degree `< deg denZ = 2(2n+1)`). -/
noncomputable def remZ (n : ℕ) : ℤ[X] := numZ n %ₘ denZ n

/-- **Euclidean division identity** `numZ = denZ·polyPartZ + remZ`. -/
theorem numZ_div_identity (n : ℕ) :
    numZ n = denZ n * polyPartZ n + remZ n := by
  have h := modByMonic_add_div (numZ n) (denZ n)
  unfold polyPartZ remZ
  linear_combination -h

/-! ## Brick 1b — `fOsal` as a rational function, and the proper-fraction split -/

theorem aeval_numZ (n : ℕ) (x : ℝ) :
    Polynomial.aeval x (numZ n) = x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n := by
  simp only [numZ, map_mul, map_pow, map_sub, map_ofNat, Polynomial.aeval_X]

theorem aeval_denZ (n : ℕ) (x : ℝ) :
    Polynomial.aeval x (denZ n) = (x ^ 2 - 225) ^ (2 * n + 1) := by
  simp only [denZ, map_pow, map_sub, map_ofNat, Polynomial.aeval_X]

/-- `fOsal n x = numₙ(x)/denₙ(x)` (relating the analytic integrand to the polynomial layer). -/
theorem fOsal_eq_div (n : ℕ) (x : ℝ) :
    fOsal n x = Polynomial.aeval x (numZ n) / Polynomial.aeval x (denZ n) := by
  rw [fOsal, aeval_numZ, aeval_denZ]

/-- On `[0,3]` (indeed for `x² < 225`), the denominator does not vanish. -/
theorem aeval_denZ_ne_zero_of_lt (n : ℕ) {x : ℝ} (hx : x ^ 2 < 225) :
    Polynomial.aeval x (denZ n) ≠ 0 := by
  rw [aeval_denZ]
  exact pow_ne_zero _ (by nlinarith)

/-- `aeval` of the division identity at a real point. -/
theorem aeval_numZ_div_identity (n : ℕ) (x : ℝ) :
    Polynomial.aeval x (numZ n)
      = Polynomial.aeval x (denZ n) * Polynomial.aeval x (polyPartZ n)
        + Polynomial.aeval x (remZ n) := by
  have h := congrArg (Polynomial.aeval x) (numZ_div_identity n)
  simpa only [map_add, map_mul] using h

/-- **Proper-fraction split** (fully proved): `fOsal n x = Pₙ(x) + remₙ(x)/denₙ(x)`
where `Pₙ(x) = aeval x (polyPartZ n)`.  Valid wherever `denₙ(x) ≠ 0`. -/
theorem fOsal_eq_polyPart_add_rem (n : ℕ) {x : ℝ}
    (hx : Polynomial.aeval x (denZ n) ≠ 0) :
    fOsal n x = Polynomial.aeval x (polyPartZ n)
      + Polynomial.aeval x (remZ n) / Polynomial.aeval x (denZ n) := by
  rw [fOsal_eq_div, aeval_numZ_div_identity]
  field_simp

/-! ## Brick 1c — the residue generating product and the residue coefficients

`g(t) = gNum(t)/(30+t)^{2n+1}` with `gNum(t) = (15+t)^{2n}(12+t)^n(18+t)^n(10+t)^n(20+t)^n`.
Expanding `1/(30+t)^{2n+1} = 30^{-(2n+1)} Σ_k (-1)^k C(2n+k,k) (t/30)^k` gives

  `c_j = [t^{2n+1−j}] g(t)
       = Σ_{k} (-1)^k C(2n+k,k) · gNum.coeff(2n+1−j−k) / 30^{2n+1+k}`,

and `d_j = (-1)^j c_j` (evenness of `fOsal`). -/

/-- `gNum n = (15+X)^{2n}(12+X)^n(18+X)^n(10+X)^n(20+X)^n ∈ ℤ[X]` — the residue generating
numerator (Taylor expansion around `t = x−15`). -/
noncomputable def gNum (n : ℕ) : ℤ[X] :=
  (15 + X) ^ (2 * n) * (12 + X) ^ n * (18 + X) ^ n * (10 + X) ^ n * (20 + X) ^ n

/-- Coefficient of `(C c + X)^m` via the binomial theorem: `[X^k] = c^(m−k)·C(m,k)`. -/
theorem lin_pow_coeff (c : ℤ) (m k : ℕ) :
    ((C c + X : ℤ[X]) ^ m).coeff k = c ^ (m - k) * (m.choose k : ℤ) := by
  rw [add_comm, coeff_X_add_C_pow]

/-- `gNum` rewritten with explicit `C`-constants (so `lin_pow_coeff` applies factorwise). -/
theorem gNum_C (n : ℕ) :
    gNum n = (C 15 + X) ^ (2 * n) * (C 12 + X) ^ n * (C 18 + X) ^ n
      * (C 10 + X) ^ n * (C 20 + X) ^ n := by
  unfold gNum; norm_num [map_ofNat]

/-- `c_j` (rational): the residue at the pole `x = 15`, order `j`. -/
noncomputable def cResQ (n j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * n + 2 - j),
    (-1 : ℚ) ^ k * (Nat.choose (2 * n + k) k : ℚ)
      * ((gNum n).coeff (2 * n + 1 - j - k) : ℚ) / (30 : ℚ) ^ (2 * n + 1 + k)

/-- `d_j = (−1)^j c_j` (the pole at `x = −15`, from evenness). -/
noncomputable def dResQ (n j : ℕ) : ℚ := (-1 : ℚ) ^ j * cResQ n j

/-- Real cast of `c_j`. -/
noncomputable def cResR (n j : ℕ) : ℝ := (cResQ n j : ℝ)

/-- Real cast of `d_j`. -/
noncomputable def dResR (n j : ℕ) : ℝ := (dResQ n j : ℝ)

theorem dResR_eq (n j : ℕ) : dResR n j = (-1 : ℝ) ^ j * cResR n j := by
  simp only [dResR, dResQ, cResR]; push_cast; ring

/-! ## Brick 1d — the deep partial fraction of the proper fraction (remaining `sorry`)

The proper rational function `remₙ/denₙ` decomposes into principal parts at `±15` with coefficients
exactly `cResR/dResR`.  This is the residue theorem / coefficient-comparison content (the analog of
log43's `PFI`, but for order-`2n+1` poles and rational residues). -/

/-- Power-series inverse: `mkInv · (30+X)^(2n+1) = 1` in `ℝ⟦X⟧`. -/
theorem mkInv_mul (n : ℕ) :
    (PowerSeries.mk fun s => ((-1:ℝ)^s * (Nat.choose (2*n+s) (2*n) : ℝ) / 30^(2*n+1+s)))
      * (30 + PowerSeries.X)^(2*n+1) = 1 := by
  have hbase := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℝ) (d := 2*n)
  have hr := congrArg (PowerSeries.rescale (-1/30 : ℝ)) hbase
  rw [map_mul, map_one, map_pow, PowerSeries.rescale_mk, map_sub, map_one,
    PowerSeries.rescale_X] at hr
  have hfac : (1 - PowerSeries.C (-1/30 : ℝ) * PowerSeries.X)
      = PowerSeries.C (1/30 : ℝ) * (30 + PowerSeries.X) := by
    have h30 : (30 : PowerSeries ℝ) = PowerSeries.C (30 : ℝ) :=
      (map_ofNat (PowerSeries.C (R := ℝ)) 30).symm
    rw [h30, mul_add, ← map_mul, show (1/30*30:ℝ) = 1 by norm_num, map_one,
      show (-1/30:ℝ) = -(1/30) by ring, map_neg]
    ring
  rw [hfac, mul_pow, ← map_pow] at hr
  have hcollect : (PowerSeries.mk fun s => ((-1:ℝ)^s * (Nat.choose (2*n+s) (2*n) : ℝ) / 30^(2*n+1+s)))
      = PowerSeries.C ((1/30 : ℝ)^(2*n+1))
        * (PowerSeries.mk fun s => ((-1/30 : ℝ)^s * (Nat.choose (2*n+s) (2*n) : ℝ))) := by
    ext s
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [div_pow, one_pow]
    field_simp
    ring
  rw [hcollect]
  linear_combination hr

/-- The truncated inverse series of `(30+X)^(2n+1)` over ℝ, degree `≤ 2n`. -/
noncomputable def serInvR (n : ℕ) : ℝ[X] :=
  ∑ s ∈ Finset.range (2*n+1),
    C ((-1:ℝ)^s * (Nat.choose (2*n+s) (2*n) : ℝ) / 30^(2*n+1+s)) * X^s

theorem serInvR_coeff {n k : ℕ} (hk : k ≤ 2*n) :
    (serInvR n).coeff k = (-1:ℝ)^k * (Nat.choose (2*n+k) (2*n):ℝ) / 30^(2*n+1+k) := by
  unfold serInvR
  rw [Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; rw [if_neg (by omega), mul_zero]
  · intro hni; exact absurd (Finset.mem_range.mpr (by omega)) hni

/-- **Truncated inverse over ℝ[X]**: `X^(2n+1) ∣ serInvR n · (30+X)^(2n+1) − 1`. -/
theorem serInvR_inv (n : ℕ) :
    (X : ℝ[X]) ^ (2*n+1) ∣ (serInvR n * (30 + X) ^ (2*n+1) - 1) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  have hmn : m ≤ 2*n := Nat.lt_succ_iff.mp hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_one]
  have h30coe : ((30 + X : ℝ[X]) : PowerSeries ℝ) = 30 + PowerSeries.X := by
    rw [Polynomial.coe_add, Polynomial.coe_X]
    congr 1
    rw [show (30:ℝ[X]) = C 30 from (map_ofNat C 30).symm, Polynomial.coe_C,
      show (30:PowerSeries ℝ) = PowerSeries.C 30 from (map_ofNat (PowerSeries.C (R:=ℝ)) 30).symm]
  have hcoe : (serInvR n * (30 + X) ^ (2*n+1)).coeff m
      = PowerSeries.coeff m
          ((serInvR n : PowerSeries ℝ) * (30 + PowerSeries.X) ^ (2*n+1)) := by
    rw [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow, h30coe]
  rw [hcoe]
  have hrepl : PowerSeries.coeff m
        ((serInvR n : PowerSeries ℝ) * (30 + PowerSeries.X) ^ (2*n+1))
      = PowerSeries.coeff m
          ((PowerSeries.mk fun s =>
              ((-1:ℝ)^s * (Nat.choose (2*n+s) (2*n):ℝ) / 30^(2*n+1+s)))
            * (30 + PowerSeries.X) ^ (2*n+1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hi : i ≤ m := by have := Finset.mem_antidiagonal.mp hij; omega
    have hin : i ≤ 2*n := le_trans hi hmn
    congr 1
    rw [Polynomial.coeff_coe, serInvR_coeff hin, PowerSeries.coeff_mk]
  rw [hrepl, mkInv_mul, PowerSeries.coeff_one]
  by_cases h : m = 0 <;> simp [h]

/-! ### Mapped polynomials and the generating product over ℝ -/

/-- `gNumR n = (gNum n) over ℝ`. -/
noncomputable def gNumR (n : ℕ) : ℝ[X] := (gNum n).map (Int.castRingHom ℝ)

/-- The generating product `g̃ = serInvR · gNumR` over ℝ. -/
noncomputable def gtildeR (n : ℕ) : ℝ[X] := serInvR n * gNumR n

theorem gNumR_eq (n : ℕ) :
    gNumR n = (15 + X) ^ (2 * n) * (12 + X) ^ n * (18 + X) ^ n * (10 + X) ^ n * (20 + X) ^ n := by
  unfold gNumR gNum
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_ofNat,
    Polynomial.map_X]

theorem numZR_eq (n : ℕ) :
    (numZ n).map (Int.castRingHom ℝ) = X ^ (2 * n) * (X ^ 2 - 9) ^ n * (X ^ 2 - 25) ^ n := by
  unfold numZ
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_ofNat,
    Polynomial.map_X]

theorem gNumR_coeff (n k : ℕ) : (gNumR n).coeff k = ((gNum n).coeff k : ℝ) := by
  unfold gNumR; rw [Polynomial.coeff_map]; simp

/-- **Coefficient bridge**: `g̃.coeff (2n+1−j) = cResR n j` for `j ≥ 1`. -/
theorem gtildeR_coeff_eq_cResR (n j : ℕ) (hj : 1 ≤ j) (hj2 : j ≤ 2 * n + 1) :
    (gtildeR n).coeff (2 * n + 1 - j) = cResR n j := by
  have hm : 2 * n + 1 - j ≤ 2 * n := by omega
  unfold gtildeR cResR cResQ
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rw [show 2 * n + 2 - j = (2 * n + 1 - j) + 1 by omega]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkm : k ≤ 2 * n + 1 - j := by omega
  have hk2n : k ≤ 2 * n := le_trans hkm hm
  rw [serInvR_coeff hk2n, gNumR_coeff]
  have hch : Nat.choose (2 * n + k) (2 * n) = Nat.choose (2 * n + k) k := by
    rw [← Nat.choose_symm (show 2 * n ≤ 2 * n + k by omega)]
    congr 1; omega
  rw [hch]
  ring

/-! ### `denZ` factorization and the comp/substitution identity -/

theorem denZ_factor (n : ℕ) :
    denZ n = (X - 15) ^ (2 * n + 1) * (X + 15) ^ (2 * n + 1) := by
  unfold denZ
  rw [← mul_pow]
  congr 1
  ring

/-- Substitution `X ↦ X−15` carries `gNumR` to `numZR`. -/
theorem aeval_sub15_gNumR (n : ℕ) :
    Polynomial.aeval (X - 15 : ℝ[X]) (gNumR n) = (numZ n).map (Int.castRingHom ℝ) := by
  rw [gNumR_eq, numZR_eq]
  simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, map_ofNat]
  rw [show ((X ^ 2 - 9 : ℝ[X])) = (X - 3) * (X + 3) by ring,
    show ((X ^ 2 - 25 : ℝ[X])) = (X - 5) * (X + 5) by ring, mul_pow, mul_pow]
  ring

/-! ### Truncation, principal-part polynomials, and the local identities -/

/-- Generic truncation divisibility over ℝ[X]: `X^N ∣ p − trunc_N p`. -/
theorem trunc_sub_dvd_R (p : ℝ[X]) (N : ℕ) :
    (X : ℝ[X]) ^ N ∣ (p - ∑ i ∈ Finset.range N, C (p.coeff i) * X ^ i) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  rw [Polynomial.coeff_sub]
  have hsum : (∑ i ∈ Finset.range N, C (p.coeff i) * X ^ i).coeff m = p.coeff m := by
    rw [Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; rw [if_neg (by omega), mul_zero]
    · intro hni; exact absurd (Finset.mem_range.mpr hm) hni
  rw [hsum, sub_self]

/-- Truncation of `g̃` to degree `< 2n+1`. -/
noncomputable def CparR (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (2 * n + 1), C ((gtildeR n).coeff i) * X ^ i

/-- Principal-part polynomial at the pole `x = 15`. -/
noncomputable def CpolyR (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (2 * n + 1), C ((gtildeR n).coeff i) * (X - 15) ^ i

/-- Principal-part polynomial at the pole `x = −15` (the reflected residues). -/
noncomputable def DpolyR (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (2 * n + 1),
    C ((-1 : ℝ) ^ (2 * n + 1 + i) * (gtildeR n).coeff i) * (X + 15) ^ i

theorem CpolyR_eq (n : ℕ) :
    CpolyR n = Polynomial.aeval (X - 15 : ℝ[X]) (CparR n) := by
  unfold CpolyR CparR
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.algebraMap_eq]

/-- **LocalC**: `X^(2n+1) ∣ gNumR − CparR·(30+X)^(2n+1)`. -/
theorem LocalC (n : ℕ) :
    (X : ℝ[X]) ^ (2 * n + 1) ∣ (gNumR n - CparR n * (30 + X) ^ (2 * n + 1)) := by
  have d1 : (X : ℝ[X]) ^ (2 * n + 1) ∣ (gNumR n - gtildeR n * (30 + X) ^ (2 * n + 1)) := by
    have hbase := (serInvR_inv n).mul_left (gNumR n)
    have heq : gNumR n * (serInvR n * (30 + X) ^ (2 * n + 1) - 1)
        = gtildeR n * (30 + X) ^ (2 * n + 1) - gNumR n := by unfold gtildeR; ring
    rw [heq] at hbase
    have := dvd_neg.mpr hbase
    rwa [neg_sub] at this
  have d2 : (X : ℝ[X]) ^ (2 * n + 1) ∣ ((gtildeR n - CparR n) * (30 + X) ^ (2 * n + 1)) :=
    Dvd.dvd.mul_right (trunc_sub_dvd_R (gtildeR n) (2 * n + 1)) _
  have hsplit : (gNumR n - CparR n * (30 + X) ^ (2 * n + 1))
      = (gNumR n - gtildeR n * (30 + X) ^ (2 * n + 1))
        + (gtildeR n - CparR n) * (30 + X) ^ (2 * n + 1) := by unfold CparR; ring
  rw [hsplit]; exact dvd_add d1 d2

/-- **C1num** (substitute `X ↦ X−15`): `(X−15)^(2n+1) ∣ numZR − CpolyR·(X+15)^(2n+1)`. -/
theorem C1num (n : ℕ) :
    (X - 15 : ℝ[X]) ^ (2 * n + 1)
      ∣ ((numZ n).map (Int.castRingHom ℝ) - CpolyR n * (X + 15) ^ (2 * n + 1)) := by
  have himg := map_dvd (Polynomial.aeval (X - 15 : ℝ[X])) (LocalC n)
  simp only [map_sub, map_mul, map_pow] at himg
  have h3015 : Polynomial.aeval (X - 15 : ℝ[X]) (30 + X : ℝ[X]) = X + 15 := by
    rw [map_add, Polynomial.aeval_X, map_ofNat]; ring
  rw [Polynomial.aeval_X, aeval_sub15_gNumR, h3015, ← CpolyR_eq] at himg
  exact himg

/-! ### Mapped denominator factorization and evenness -/

theorem denZR_factor (n : ℕ) :
    (denZ n).map (Int.castRingHom ℝ) = (X - 15) ^ (2 * n + 1) * (X + 15) ^ (2 * n + 1) := by
  rw [denZ_factor]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_ofNat, Polynomial.map_X]

theorem numZR_even (n : ℕ) :
    Polynomial.aeval (-X : ℝ[X]) ((numZ n).map (Int.castRingHom ℝ))
      = (numZ n).map (Int.castRingHom ℝ) := by
  simp only [numZR_eq]
  simp only [map_mul, map_pow, map_sub, map_ofNat, Polynomial.aeval_X, neg_sq]
  rw [show ((-X : ℝ[X])) ^ (2 * n) = X ^ (2 * n) by rw [pow_mul, neg_sq, ← pow_mul]]

theorem denZR_even (n : ℕ) :
    Polynomial.aeval (-X : ℝ[X]) ((denZ n).map (Int.castRingHom ℝ))
      = (denZ n).map (Int.castRingHom ℝ) := by
  rw [denZR_factor]
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, Polynomial.aeval_X]
  rw [show ((-X - 15 : ℝ[X])) = -(X + 15) by ring, show ((-X + 15 : ℝ[X])) = -(X - 15) by ring]
  rw [show (-(X + 15 : ℝ[X])) ^ (2 * n + 1) * (-(X - 15)) ^ (2 * n + 1)
      = ((X + 15) * (X - 15)) ^ (2 * n + 1) by rw [← mul_pow]; ring]
  rw [show ((X + 15) * (X - 15) : ℝ[X]) = (X - 15) * (X + 15) by ring, mul_pow]

/-- **`remZ` is even** (reflection-invariant): `aeval(−X)(remZR) = remZR`. -/
theorem remZ_even (n : ℕ) :
    Polynomial.aeval (-X : ℝ[X]) ((remZ n).map (Int.castRingHom ℝ))
      = (remZ n).map (Int.castRingHom ℝ) := by
  set φ := Int.castRingHom ℝ with hφ
  set r := (remZ n).map φ with hr
  set d := (denZ n).map φ with hd
  set qp := (polyPartZ n).map φ with hqp
  have hdmon : d.Monic := (denZ_monic n).map φ
  have hd0 : d ≠ 0 := hdmon.ne_zero
  have hid : (numZ n).map φ = d * qp + r := by
    have := congrArg (Polynomial.map φ) (numZ_div_identity n)
    simpa only [Polynomial.map_add, Polynomial.map_mul] using this
  have hrmod : r = (numZ n).map φ %ₘ d := by
    rw [hr, hd]; unfold remZ; exact (map_mod_divByMonic φ (denZ_monic n)).2
  have hdeg : r.degree < d.degree := by rw [hrmod]; exact Polynomial.degree_modByMonic_lt _ hdmon
  rcases eq_or_ne r 0 with h0 | h0
  · rw [h0]; simp
  · -- reflected division
    have hidr : (numZ n).map φ
        = d * (Polynomial.aeval (-X : ℝ[X]) qp) + (Polynomial.aeval (-X : ℝ[X]) r) := by
      have h := congrArg (Polynomial.aeval (-X : ℝ[X])) hid
      rw [numZR_even, map_add, map_mul, denZR_even] at h
      exact h
    -- d divides (aeval(-X) r - r)
    have hdvd : d ∣ (Polynomial.aeval (-X : ℝ[X]) r - r) := by
      refine ⟨qp - Polynomial.aeval (-X : ℝ[X]) qp, ?_⟩
      linear_combination hid - hidr
    have hwle : (Polynomial.aeval (-X : ℝ[X]) r - r).natDegree ≤ r.natDegree := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ le_rfl)
      have hc : Polynomial.aeval (-X : ℝ[X]) r = r.comp (-X) := (comp_eq_aeval).symm
      rw [hc]
      refine le_trans (Polynomial.natDegree_comp_le) ?_
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one]
    have hrd : r.natDegree < d.natDegree := Polynomial.natDegree_lt_natDegree h0 hdeg
    have hw0 : Polynomial.aeval (-X : ℝ[X]) r - r = 0 := by
      by_contra hne
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      omega
    exact sub_eq_zero.mp hw0

/-- **C2rem** (reflect C1rem): `(X+15)^(2n+1) ∣ remZR − (X−15)^(2n+1)·DpolyR`. -/
theorem DpolyR_eq_refl (n : ℕ) :
    DpolyR n = (-1 : ℝ[X]) ^ (2 * n + 1) * Polynomial.aeval (-X : ℝ[X]) (CpolyR n) := by
  unfold DpolyR CpolyR
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, map_pow, map_sub, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.algebraMap_eq, map_ofNat, Polynomial.C_mul, Polynomial.C_pow,
    map_neg, map_one]
  rw [show ((-X - 15 : ℝ[X])) = (-1) * (X + 15) by ring, mul_pow]
  ring

/-- **C1rem**: `(X−15)^(2n+1) ∣ remZR − CpolyR·(X+15)^(2n+1)`. -/
theorem C1rem (n : ℕ) :
    (X - 15 : ℝ[X]) ^ (2 * n + 1)
      ∣ ((remZ n).map (Int.castRingHom ℝ) - CpolyR n * (X + 15) ^ (2 * n + 1)) := by
  have hnr : (X - 15 : ℝ[X]) ^ (2 * n + 1)
      ∣ ((numZ n).map (Int.castRingHom ℝ) - (remZ n).map (Int.castRingHom ℝ)) := by
    have hid := congrArg (Polynomial.map (Int.castRingHom ℝ)) (numZ_div_identity n)
    simp only [Polynomial.map_add, Polynomial.map_mul] at hid
    rw [denZR_factor] at hid
    refine ⟨(X + 15) ^ (2 * n + 1) * (polyPartZ n).map (Int.castRingHom ℝ), ?_⟩
    linear_combination hid
  have hd := dvd_sub (C1num n) hnr
  have he : ((numZ n).map (Int.castRingHom ℝ) - CpolyR n * (X + 15) ^ (2 * n + 1))
      - ((numZ n).map (Int.castRingHom ℝ) - (remZ n).map (Int.castRingHom ℝ))
      = (remZ n).map (Int.castRingHom ℝ) - CpolyR n * (X + 15) ^ (2 * n + 1) := by ring
  rwa [he] at hd

/-- **C2rem** (reflect C1rem via `remZ` evenness): `(X+15)^(2n+1) ∣ remZR − (X−15)^(2n+1)·DpolyR`. -/
theorem C2rem (n : ℕ) :
    (X + 15 : ℝ[X]) ^ (2 * n + 1)
      ∣ ((remZ n).map (Int.castRingHom ℝ) - (X - 15) ^ (2 * n + 1) * DpolyR n) := by
  have himg := map_dvd (Polynomial.aeval (-X : ℝ[X])) (C1rem n)
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, map_ofNat] at himg
  rw [remZ_even] at himg
  rw [show ((-X - 15 : ℝ[X])) = (-1) * (X + 15) by ring,
    show ((-X + 15 : ℝ[X])) = (-1) * (X - 15) by ring, mul_pow, mul_pow] at himg
  have hrhs : Polynomial.aeval (-X : ℝ[X]) (CpolyR n)
        * ((-1 : ℝ[X]) ^ (2 * n + 1) * (X - 15) ^ (2 * n + 1))
      = (X - 15) ^ (2 * n + 1) * DpolyR n := by
    rw [DpolyR_eq_refl]; ring
  rw [hrhs] at himg
  exact dvd_trans (dvd_mul_left ((X + 15) ^ (2 * n + 1)) ((-1 : ℝ[X]) ^ (2 * n + 1))) himg

/-! ### Degree facts and the cleared partial-fraction identity -/

theorem natDegree_X_sub_15 : (X - 15 : ℝ[X]).natDegree = 1 := by
  rw [show (X - 15 : ℝ[X]) = X - C 15 by rw [map_ofNat]]; exact natDegree_X_sub_C 15

theorem natDegree_X_add_15 : (X + 15 : ℝ[X]).natDegree = 1 := by
  rw [show (X + 15 : ℝ[X]) = X + C 15 by rw [map_ofNat]]; exact natDegree_X_add_C 15

theorem monic_X_sub_15 : (X - 15 : ℝ[X]).Monic := by
  rw [show (X - 15 : ℝ[X]) = X - C 15 by rw [map_ofNat]]; exact monic_X_sub_C 15

theorem monic_X_add_15 : (X + 15 : ℝ[X]).Monic := by
  rw [show (X + 15 : ℝ[X]) = X + C 15 by rw [map_ofNat]]; exact monic_X_add_C 15

theorem natDegree_CpolyR_le (n : ℕ) : (CpolyR n).natDegree ≤ 2 * n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc (C ((gtildeR n).coeff i) * (X - 15) ^ i).natDegree
      ≤ ((X - 15 : ℝ[X]) ^ i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ i * (X - 15 : ℝ[X]).natDegree := Polynomial.natDegree_pow_le
    _ ≤ 2 * n := by rw [natDegree_X_sub_15]; omega

theorem natDegree_DpolyR_le (n : ℕ) : (DpolyR n).natDegree ≤ 2 * n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc (C ((-1 : ℝ) ^ (2 * n + 1 + i) * (gtildeR n).coeff i) * (X + 15) ^ i).natDegree
      ≤ ((X + 15 : ℝ[X]) ^ i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ i * (X + 15 : ℝ[X]).natDegree := Polynomial.natDegree_pow_le
    _ ≤ 2 * n := by rw [natDegree_X_add_15]; omega

theorem natDegree_denZR (n : ℕ) :
    ((denZ n).map (Int.castRingHom ℝ)).natDegree = 4 * n + 2 := by
  rw [denZR_factor,
    Polynomial.natDegree_mul (monic_X_sub_15.pow _).ne_zero (monic_X_add_15.pow _).ne_zero,
    Polynomial.natDegree_pow, Polynomial.natDegree_pow, natDegree_X_sub_15, natDegree_X_add_15]
  ring

theorem natDegree_remZR_le (n : ℕ) :
    ((remZ n).map (Int.castRingHom ℝ)).natDegree ≤ 4 * n + 1 := by
  have hdmon : ((denZ n).map (Int.castRingHom ℝ)).Monic := (denZ_monic n).map _
  have hrmod : (remZ n).map (Int.castRingHom ℝ)
      = (numZ n).map (Int.castRingHom ℝ) %ₘ (denZ n).map (Int.castRingHom ℝ) := by
    unfold remZ; exact (map_mod_divByMonic (Int.castRingHom ℝ) (denZ_monic n)).2
  rcases eq_or_ne ((remZ n).map (Int.castRingHom ℝ)) 0 with h | h
  · simp [h]
  · have hlt : ((remZ n).map (Int.castRingHom ℝ)).degree
        < ((denZ n).map (Int.castRingHom ℝ)).degree := by
      rw [hrmod]; exact Polynomial.degree_modByMonic_lt _ hdmon
    have hdN := natDegree_denZR n
    have := Polynomial.natDegree_lt_natDegree h hlt
    omega

/-- **The cleared partial-fraction identity** over ℝ[X]:
`remZR = CpolyR·(X+15)^(2n+1) + (X−15)^(2n+1)·DpolyR`. -/
theorem clearedPFI (n : ℕ) :
    (remZ n).map (Int.castRingHom ℝ)
      = CpolyR n * (X + 15) ^ (2 * n + 1) + (X - 15) ^ (2 * n + 1) * DpolyR n := by
  set rR := (remZ n).map (Int.castRingHom ℝ) with hrR
  set D := rR - CpolyR n * (X + 15) ^ (2 * n + 1) - (X - 15) ^ (2 * n + 1) * DpolyR n with hDdef
  have hd1 : (X - 15 : ℝ[X]) ^ (2 * n + 1) ∣ D := by
    have hs : D = (rR - CpolyR n * (X + 15) ^ (2 * n + 1)) - (X - 15) ^ (2 * n + 1) * DpolyR n := by
      rw [hDdef]
    rw [hs]; exact dvd_sub (C1rem n) (Dvd.dvd.mul_right (dvd_refl _) _)
  have hd2 : (X + 15 : ℝ[X]) ^ (2 * n + 1) ∣ D := by
    have hs : D = (rR - (X - 15) ^ (2 * n + 1) * DpolyR n) - CpolyR n * (X + 15) ^ (2 * n + 1) := by
      rw [hDdef]; ring
    rw [hs]; exact dvd_sub (C2rem n) (Dvd.dvd.mul_left (dvd_refl _) _)
  have hcoprime : IsCoprime (X - 15 : ℝ[X]) (X + 15) := by
    refine ⟨-C (1 / 30 : ℝ), C (1 / 30 : ℝ), ?_⟩
    have hcombine : -C (1 / 30 : ℝ) * (X - 15) + C (1 / 30 : ℝ) * (X + 15)
        = C (1 / 30 : ℝ) * 30 := by ring
    rw [hcombine, show (30 : ℝ[X]) = C (30 : ℝ) from (map_ofNat C 30).symm, ← map_mul,
      show (1 / 30 * 30 : ℝ) = 1 by norm_num, map_one]
  have hcop : IsCoprime ((X - 15 : ℝ[X]) ^ (2 * n + 1)) ((X + 15) ^ (2 * n + 1)) := hcoprime.pow
  have hdvd : ((X - 15 : ℝ[X]) ^ (2 * n + 1) * (X + 15) ^ (2 * n + 1)) ∣ D := hcop.mul_dvd hd1 hd2
  have hD0 : D = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    have hprod : ((X - 15 : ℝ[X]) ^ (2 * n + 1) * (X + 15) ^ (2 * n + 1)).natDegree = 4 * n + 2 := by
      rw [← denZR_factor]; exact natDegree_denZR n
    have hDle : D.natDegree ≤ 4 * n + 1 := by
      rw [hDdef]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (natDegree_remZR_le n) ?_)
        calc (CpolyR n * (X + 15) ^ (2 * n + 1)).natDegree
            ≤ (CpolyR n).natDegree + ((X + 15 : ℝ[X]) ^ (2 * n + 1)).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 4 * n + 1 := by
              rw [Polynomial.natDegree_pow, natDegree_X_add_15]
              have := natDegree_CpolyR_le n; omega
      · calc ((X - 15 : ℝ[X]) ^ (2 * n + 1) * DpolyR n).natDegree
            ≤ ((X - 15 : ℝ[X]) ^ (2 * n + 1)).natDegree + (DpolyR n).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 4 * n + 1 := by
              rw [Polynomial.natDegree_pow, natDegree_X_sub_15]
              have := natDegree_DpolyR_le n; omega
    rw [hprod] at hle; omega
  have hexpr : rR - CpolyR n * (X + 15) ^ (2 * n + 1) - (X - 15) ^ (2 * n + 1) * DpolyR n = 0 := by
    rw [← hDdef]; exact hD0
  linear_combination hexpr

/-! ### Division: from the cleared identity to the partial fraction -/

theorem gtildeR_coeff_i (n i : ℕ) (hi : i ≤ 2 * n) :
    (gtildeR n).coeff i = cResR n (2 * n + 1 - i) := by
  have := gtildeR_coeff_eq_cResR n (2 * n + 1 - i) (by omega) (by omega)
  rwa [show 2 * n + 1 - (2 * n + 1 - i) = i by omega] at this

theorem Csum_reindex (n : ℕ) {x : ℝ} (hx : (x - 15 : ℝ) ≠ 0) :
    (∑ i ∈ Finset.range (2 * n + 1), (gtildeR n).coeff i * (x - 15) ^ i) / (x - 15) ^ (2 * n + 1)
      = ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j / (x - 15) ^ j := by
  rw [Finset.sum_div]
  have hterm : ∀ i ∈ Finset.range (2 * n + 1),
      (gtildeR n).coeff i * (x - 15) ^ i / (x - 15) ^ (2 * n + 1)
        = cResR n (2 * n + 1 - i) / (x - 15) ^ (2 * n + 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gtildeR_coeff_i n i (by omega),
      div_eq_div_iff (pow_ne_zero _ hx) (pow_ne_zero _ hx), mul_assoc, ← pow_add,
      show i + (2 * n + 1 - i) = 2 * n + 1 by omega]
  rw [Finset.sum_congr rfl hterm]
  apply Finset.sum_bij' (fun a _ => 2 * n + 1 - a) (fun b _ => 2 * n + 1 - b)
  · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
  · intro b hb; rw [Finset.mem_Icc] at hb; rw [Finset.mem_range]; omega
  · intro a ha; rw [Finset.mem_range] at ha; omega
  · intro b hb; rw [Finset.mem_Icc] at hb; omega
  · intro a _; rfl

theorem Dsum_reindex (n : ℕ) {x : ℝ} (hx : (x + 15 : ℝ) ≠ 0) :
    (∑ i ∈ Finset.range (2 * n + 1),
        (-1 : ℝ) ^ (2 * n + 1 + i) * (gtildeR n).coeff i * (x + 15) ^ i) / (x + 15) ^ (2 * n + 1)
      = ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j / (x + 15) ^ j := by
  rw [Finset.sum_div]
  have hterm : ∀ i ∈ Finset.range (2 * n + 1),
      (-1 : ℝ) ^ (2 * n + 1 + i) * (gtildeR n).coeff i * (x + 15) ^ i / (x + 15) ^ (2 * n + 1)
        = dResR n (2 * n + 1 - i) / (x + 15) ^ (2 * n + 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gtildeR_coeff_i n i (by omega), dResR_eq]
    have hsign : (-1 : ℝ) ^ (2 * n + 1 + i) = (-1 : ℝ) ^ (2 * n + 1 - i) := by
      rw [show 2 * n + 1 + i = (2 * n + 1 - i) + 2 * i by omega, pow_add, pow_mul]
      norm_num
    rw [hsign, div_eq_div_iff (pow_ne_zero _ hx) (pow_ne_zero _ hx), mul_assoc, ← pow_add,
      show i + (2 * n + 1 - i) = 2 * n + 1 by omega]
  rw [Finset.sum_congr rfl hterm]
  apply Finset.sum_bij' (fun a _ => 2 * n + 1 - a) (fun b _ => 2 * n + 1 - b)
  · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
  · intro b hb; rw [Finset.mem_Icc] at hb; rw [Finset.mem_range]; omega
  · intro a ha; rw [Finset.mem_range] at ha; omega
  · intro b hb; rw [Finset.mem_Icc] at hb; omega
  · intro a _; rfl


/-- **Partial fraction of the proper part** (the residue theorem / coefficient-comparison
content; the order-`2n+1`-pole, rational-residue analog of `WeightedDiagonalLog43.PFI`).
`remₙ(x)/denₙ(x) = Σ_{j=1}^{2n+1} c_j/(x−15)^j + Σ_{j=1}^{2n+1} d_j/(x+15)^j`.
Proved via the cleared polynomial identity `clearedPFI` over `ℝ[X]` (truncated power-series
inverse `serInvR_inv` + per-pole local identities + coprime-factor CRT + degree bound), then
evaluated and divided. -/
theorem rem_div_den_partialFraction (n : ℕ) {x : ℝ} (hx15 : x ≠ 15) (hx15' : x ≠ -15) :
    Polynomial.aeval x (remZ n) / Polynomial.aeval x (denZ n)
      = (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j / (x - 15) ^ j)
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j / (x + 15) ^ j := by
  have hxm : (x - 15 : ℝ) ≠ 0 := sub_ne_zero.mpr hx15
  have hxp : (x + 15 : ℝ) ≠ 0 := fun h => hx15' (by linarith)
  have haeval_rem : Polynomial.aeval x (remZ n)
      = Polynomial.eval x ((remZ n).map (Int.castRingHom ℝ)) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq]
  have hden : Polynomial.aeval x (denZ n) = (x - 15) ^ (2 * n + 1) * (x + 15) ^ (2 * n + 1) := by
    rw [aeval_denZ, show (x ^ 2 - 225 : ℝ) = (x - 15) * (x + 15) by ring, mul_pow]
  have hC : Polynomial.eval x (CpolyR n)
      = ∑ i ∈ Finset.range (2 * n + 1), (gtildeR n).coeff i * (x - 15) ^ i := by
    unfold CpolyR; rw [Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl; intro i _
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X]
  have hD : Polynomial.eval x (DpolyR n)
      = ∑ i ∈ Finset.range (2 * n + 1),
          (-1 : ℝ) ^ (2 * n + 1 + i) * (gtildeR n).coeff i * (x + 15) ^ i := by
    unfold DpolyR; rw [Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl; intro i _
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X]
  have hev := congrArg (Polynomial.eval x) (clearedPFI n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_ofNat] at hev
  rw [hC, hD] at hev
  rw [haeval_rem, hev, hden, add_div,
    mul_div_mul_right _ _ (pow_ne_zero _ hxp), mul_div_mul_left _ _ (pow_ne_zero _ hxm),
    Csum_reindex n hxm, Dsum_reindex n hxp]


/-- **Full pointwise partial-fraction expansion** (proved modulo `rem_div_den_partialFraction`):
`fOsal n x = Pₙ(x) + Σ c_j/(x−15)^j + Σ d_j/(x+15)^j` on `0 ≤ x ≤ 3`. -/
theorem fOsal_partialFraction (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3) :
    fOsal n x = Polynomial.aeval x (polyPartZ n)
      + (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j / (x - 15) ^ j)
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j / (x + 15) ^ j := by
  have hx2 : x ^ 2 < 225 := by nlinarith
  have hd : Polynomial.aeval x (denZ n) ≠ 0 := aeval_denZ_ne_zero_of_lt n hx2
  have hx15 : x ≠ 15 := by intro h; rw [h] at hx2; norm_num at hx2
  have hx15' : x ≠ -15 := by intro h; rw [h] at hx2; norm_num at hx2
  rw [fOsal_eq_polyPart_add_rem n hd, rem_div_den_partialFraction n hx15 hx15']
  ring

/-! ## Brick 2 — the termwise integration lemmas over `[0,3]` (self-contained, PROVED)

On `[0,3]`: `x − 15 ∈ [−15,−12]` (negative), `x + 15 ∈ [15,18]` (positive).  These are the exact
analogs of `WeightedDiagonalLog43Integrals.{integral_one_add_inv, integral_one_add_pow_inv}`. -/

open intervalIntegral

/-- `∫₀³ (x−15)⁻¹ dx = log(12/15)`.  (Shift to `∫_{−15}^{−12} t⁻¹`, both endpoints `< 0`.) -/
theorem integral_sub15_inv : (∫ x in (0:ℝ)..3, (x - 15)⁻¹) = Real.log (12 / 15) := by
  have e : (∫ x in (0:ℝ)..3, (x - 15)⁻¹) = ∫ x in (0:ℝ)..3, ((fun t => t⁻¹) (x + (-15))) := by
    apply intervalIntegral.integral_congr; intro x _; simp [sub_eq_add_neg]
  rw [e, intervalIntegral.integral_comp_add_right (fun t => t⁻¹) (-15),
    show (0:ℝ) + -15 = -15 by norm_num, show (3:ℝ) + -15 = -12 by norm_num,
    integral_inv_of_neg (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- `∫₀³ (x+15)⁻¹ dx = log(18/15)`.  (Shift to `∫_{15}^{18} t⁻¹`, both endpoints `> 0`.) -/
theorem integral_add15_inv : (∫ x in (0:ℝ)..3, (x + 15)⁻¹) = Real.log (18 / 15) := by
  rw [intervalIntegral.integral_comp_add_right (fun t => t⁻¹) 15,
    show (0:ℝ) + 15 = 15 by norm_num, show (3:ℝ) + 15 = 18 by norm_num,
    integral_inv_of_pos (by norm_num) (by norm_num)]

/-- For `j ≥ 2`: `∫₀³ ((x−15)^j)⁻¹ dx = ((−12)^{1−j} − (−15)^{1−j})/(1−j)` (no log; rational). -/
theorem integral_sub15_zpow (j : ℕ) (hj : 2 ≤ j) :
    (∫ x in (0:ℝ)..3, ((x - 15) ^ j)⁻¹)
      = ((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)) := by
  have hj0 : (-(j : ℤ)) ≠ -1 := by omega
  have hint : (∫ x in (0:ℝ)..3, ((x - 15) ^ j)⁻¹)
      = ∫ x in (0:ℝ)..3, ((fun t => t ^ (-(j : ℤ))) (x + (-15))) := by
    apply intervalIntegral.integral_congr; intro x _
    simp only []
    rw [show (x + (-15) : ℝ) = x - 15 by ring, zpow_neg, zpow_natCast]
  rw [hint, intervalIntegral.integral_comp_add_right (fun t => t ^ (-(j : ℤ))) (-15),
    show (0:ℝ) + -15 = -15 by norm_num, show (3:ℝ) + -15 = -12 by norm_num,
    integral_zpow (Or.inr ⟨hj0, by norm_num [Set.mem_uIcc]⟩),
    show -(j : ℤ) + 1 = 1 - (j : ℤ) by ring]
  congr 1
  push_cast; ring

/-- For `j ≥ 2`: `∫₀³ ((x+15)^j)⁻¹ dx = (18^{1−j} − 15^{1−j})/(1−j)` (no log; rational). -/
theorem integral_add15_zpow (j : ℕ) (hj : 2 ≤ j) :
    (∫ x in (0:ℝ)..3, ((x + 15) ^ j)⁻¹)
      = ((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)) := by
  have hj0 : (-(j : ℤ)) ≠ -1 := by omega
  have hint : (∫ x in (0:ℝ)..3, ((x + 15) ^ j)⁻¹)
      = ∫ x in (0:ℝ)..3, ((fun t => t ^ (-(j : ℤ))) (x + 15)) := by
    apply intervalIntegral.integral_congr; intro x _
    simp only []
    rw [zpow_neg, zpow_natCast]
  rw [hint, intervalIntegral.integral_comp_add_right (fun t => t ^ (-(j : ℤ))) 15,
    show (0:ℝ) + 15 = 15 by norm_num, show (3:ℝ) + 15 = 18 by norm_num,
    integral_zpow (Or.inr ⟨hj0, by norm_num [Set.mem_uIcc]⟩),
    show -(j : ℤ) + 1 = 1 - (j : ℤ) by ring]
  congr 1
  push_cast; ring

/-- The simple-pole log combination collapses to `log(2/3)`:
`log(12/15) − log(18/15) = log(2/3)`. -/
theorem log_simple_pole_collapse :
    Real.log (12 / 15) - Real.log (18 / 15) = Real.log (2 / 3) := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ## Brick 1e / 3 — the verified residue relation and the assembly (remaining `sorry`s) -/

/-- **REMAINING GAP (verified numerically).**  The simple residue at `x = 15` equals `Bseq n`:
`c_1 = Bseq n`. -/
theorem cResQ_one_eq_Bseq (n : ℕ) : cResQ n 1 = OSalikhovIntCoord.BseqQ n := by
  sorry

/-- Base case `n = 0` of `cResQ_one_eq_Bseq`: `cResQ 0 1 = 1/30 = BseqQ 0` (the simple-pole
residue at the bottom of the recurrence window). -/
theorem cResQ_zero_one : cResQ 0 1 = OSalikhovIntCoord.BseqQ 0 := by
  simp only [cResQ, gNum, OSalikhovIntCoord.BseqQ, OSalikhovIntCoord.seqQ_zero]
  norm_num [Polynomial.coeff_one]

/-- Base case `n = 1`: `cResQ 1 1 = 409/30 = BseqQ 1` (finite coefficient computation via
`gNum_C` + `lin_pow_coeff`). -/
theorem cResQ_one_one : cResQ 1 1 = OSalikhovIntCoord.BseqQ 1 := by
  simp only [cResQ, OSalikhovIntCoord.BseqQ, OSalikhovIntCoord.seqQ_one, gNum_C]
  simp only [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, lin_pow_coeff]
  norm_num [Nat.choose]

/-- Base case `n = 2`: `cResQ 2 1 = 139867/10 = BseqQ 2` (finite coefficient computation). -/
theorem cResQ_two_one : cResQ 2 1 = OSalikhovIntCoord.BseqQ 2 := by
  simp only [cResQ, OSalikhovIntCoord.BseqQ, OSalikhovIntCoord.seqQ_two, gNum_C]
  simp only [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, lin_pow_coeff]
  norm_num [Nat.choose]

/-- **Reduction of `cResQ_one_eq_Bseq` to the order-3 recurrence** (mirrors
`WeightedDiagonalLog43.JP_eq_Pexpl_of_rec`).  The three base cases `n = 0,1,2` are now *proved*
(`cResQ_zero_one`, `cResQ_one_one`, `cResQ_two_one`); together with `Bseq_rec` and the order-3
uniqueness engine, the *sole* remaining input is that the simple-residue sequence `n ↦ cResR n 1`
satisfies the same oSALIKHOV order-3 recurrence as `Bseq` (the Almkvist–Zeilberger / Gosper
second-solution telescoping). -/
theorem cResR_one_eq_Bseq_of_rec
    (hrec : OrderThreeRecurrence.Recurrence p0R p1R p2R p3R (fun n => cResR n 1)) :
    ∀ n, cResR n 1 = Bseq n := by
  have hp3 : ∀ n, p3R n ≠ 0 := fun n => (p3R_pos n).ne'
  refine OrderThreeRecurrence.recurrence_unique p0R p1R p2R p3R
    (fun n => cResR n 1) Bseq hrec Bseq_rec hp3 ?_ ?_ ?_
  · simp only [cResR]; rw [cResQ_zero_one, OSalikhovIntCoord.BseqQ_cast]
  · simp only [cResR]; rw [cResQ_one_one, OSalikhovIntCoord.BseqQ_cast]
  · simp only [cResR]; rw [cResQ_two_one, OSalikhovIntCoord.BseqQ_cast]

/-- The explicit rational part: `A1explicit n = ∫₀³ Pₙ + Σ_{j≥2} (pole rational terms)`.
The polynomial-part integral is rational; each `j ≥ 2` term integrates (Brick 2) to a rational. -/
noncomputable def A1explicit (n : ℕ) : ℝ :=
  (∫ x in (0:ℝ)..3, Polynomial.aeval x (polyPartZ n))
    + (∑ j ∈ Finset.Icc 2 (2 * n + 1),
        cResR n j * (((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))))
    + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
        dResR n j * (((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)))

/-- **REMAINING GAP (assembly).**  Integrating `fOsal_partialFraction` over `[0,3]` term by term
(Brick 2 + `integral_finset_sum`), using `d_1 = −c_1`, `c_1 = Bseq n`, and
`log(12/15) − log(18/15) = log(2/3)`:
`E1 n = A1explicit n + Bseq n · log(2/3)`. -/
theorem E1_eq (n : ℕ) : E1 n = A1explicit n + Bseq n * Real.log (2 / 3) := by
  -- Integrability of the individual `(x∓15)`-power terms on `[0,3]`.
  have hcterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hdterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  -- Integrability of the polynomial part and the two finite sums.
  have hPoly : IntervalIntegrable (fun x => Polynomial.aeval x (polyPartZ n)) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hB : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hC : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  -- Rewrite `E1` as the integral of the pointwise partial-fraction expansion.
  have hcong : E1 n = ∫ x in (0:ℝ)..3,
      ((Polynomial.aeval x (polyPartZ n)
          + (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹))
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) := by
    rw [show E1 n = ∫ x in (0:ℝ)..3, fOsal n x from rfl]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
    simp only [Set.mem_Icc] at hx
    rw [fOsal_partialFraction n hx.1 hx.2]
    simp only [div_eq_mul_inv]
  -- The c-side sum integral, split off the `j=1` log term.
  have hIcc : Finset.Icc 1 (2 * n + 1) = insert 1 (Finset.Icc 2 (2 * n + 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 (2 * n + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hCsum : (∫ x in (0:ℝ)..3,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹)
      = cResR n 1 * Real.log (12 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            cResR n j * (((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hcterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_sub15_inv
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_sub15_zpow j hj.1]
  have hDsum : (∫ x in (0:ℝ)..3,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹)
      = dResR n 1 * Real.log (18 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            dResR n j * (((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hdterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_add15_inv
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_add15_zpow j hj.1]
  -- The simple-pole log contribution collapses to `Bseq n · log(2/3)`.
  have hlog : cResR n 1 * Real.log (12 / 15) + dResR n 1 * Real.log (18 / 15)
      = Bseq n * Real.log (2 / 3) := by
    have hb : cResR n 1 = Bseq n := by
      simp only [cResR]; rw [cResQ_one_eq_Bseq, OSalikhovIntCoord.BseqQ_cast]
    rw [dResR_eq, hb]
    linear_combination (Bseq n) * log_simple_pole_collapse
  -- Assemble.
  rw [hcong, intervalIntegral.integral_add (hPoly.add hB) hC,
    intervalIntegral.integral_add hPoly hB, hCsum, hDsum, A1explicit]
  linear_combination hlog

/-- **REMAINING GAP (assembly finish).**  From `E1_decomp` (`E1 = A1seq + Bseq·log(2/3)`), `E1_eq`,
and `Irrational (log (2/3))`: the rational parts agree, `A1seq n = A1explicit n`.  This is the
identity that closes `hdvd`. -/
theorem A1seq_eq (n : ℕ) : A1seq n = A1explicit n := by
  have hdec := OSalikhovTwoLog.E1_decomp n
  have heq := E1_eq n
  -- A1seq n + Bseq n·log(2/3) = A1explicit n + Bseq n·log(2/3) ⇒ A1seq n = A1explicit n
  rw [hdec] at heq
  exact add_right_cancel heq

/-! ## Brick 1e (raw) — the residue-coefficient integral identity, sorry-free

`E1_eq_raw` is the *decoupled* version of `E1_eq`: it integrates the partial-fraction expansion of
`fOsal` over `[0,3]` keeping the **raw** simple residue `cResR n 1` as the coefficient of
`log(2/3)`, WITHOUT substituting `cResR n 1 = Bseq n`.  Hence it is **sorry-free** (it does not use
`cResQ_one_eq_Bseq`).  It is the oSALIKHOV analogue of `WeightedDiagonalLog43.Jstar`
(`Jₙ = Pexpl n + aRes(n,1)·log(4/3)`), and is the entry point for the irrationality bootstrap. -/
theorem E1_eq_raw (n : ℕ) : E1 n = A1explicit n + cResR n 1 * Real.log (2 / 3) := by
  have hcterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hdterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hPoly : IntervalIntegrable (fun x => Polynomial.aeval x (polyPartZ n)) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hB : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hC : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 3 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hcong : E1 n = ∫ x in (0:ℝ)..3,
      ((Polynomial.aeval x (polyPartZ n)
          + (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹))
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) := by
    rw [show E1 n = ∫ x in (0:ℝ)..3, fOsal n x from rfl]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hx
    simp only [Set.mem_Icc] at hx
    rw [fOsal_partialFraction n hx.1 hx.2]
    simp only [div_eq_mul_inv]
  have hIcc : Finset.Icc 1 (2 * n + 1) = insert 1 (Finset.Icc 2 (2 * n + 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 (2 * n + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hCsum : (∫ x in (0:ℝ)..3,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹)
      = cResR n 1 * Real.log (12 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            cResR n j * (((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hcterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_sub15_inv
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_sub15_zpow j hj.1]
  have hDsum : (∫ x in (0:ℝ)..3,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹)
      = dResR n 1 * Real.log (18 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            dResR n j * (((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hdterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_add15_inv
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_add15_zpow j hj.1]
  -- The simple-pole log contribution collapses to `cResR n 1 · log(2/3)` (no `Bseq` substitution).
  have hlog : cResR n 1 * Real.log (12 / 15) + dResR n 1 * Real.log (18 / 15)
      = cResR n 1 * Real.log (2 / 3) := by
    rw [dResR_eq]
    linear_combination (cResR n 1) * log_simple_pole_collapse
  rw [hcong, intervalIntegral.integral_add (hPoly.add hB) hC,
    intervalIntegral.integral_add hPoly hB, hCsum, hDsum, A1explicit]
  linear_combination hlog

/-- **Linear-independence reduction.**  Given (i) `Irrational (log (2/3))` and (ii) that the
explicit rational part `A1explicit` is in fact a rational number (this is proved unconditionally
*downstream* as `OSalikhovHdvdExplicit.A1expl_cast_eq` combined with `A1expl_clear`, which exhibit
`A1explicit n = ↑(A1expl n)` with `A1expl n : ℚ`), the residue identity `cResQ n 1 = BseqQ n`
follows: the two integral decompositions `E1_decomp` (`E1 = A1seq + Bseq·log(2/3)`) and `E1_eq_raw`
(`E1 = A1explicit + cResR(·,1)·log(2/3)`) give a `ℚ`-rational combination
`(A1seq − A1explicit) + (Bseq − cResR(·,1))·log(2/3) = 0`; by `ℚ`-linear independence of
`{1, log(2/3)}` (i.e. irrationality of `log(2/3)`), both coefficients vanish.

This is the exact oSALIKHOV analogue of how `WeightedDiagonalLog43.aRes_recurrence_holds` extracts a
residue identity from `Jstar` + irrationality.  It isolates the *entire* remaining content of
`cResQ_one_eq_Bseq` into the single classical fact `Irrational (Real.log (2/3))`. -/
theorem cResQ_one_eq_Bseq_of_irrational
    (hirr : Irrational (Real.log (2 / 3)))
    (hQrat : ∀ m, ∃ q : ℚ, A1explicit m = (q : ℝ)) :
    ∀ n, cResQ n 1 = OSalikhovIntCoord.BseqQ n := by
  intro n
  obtain ⟨q, hq⟩ := hQrat n
  by_contra hne
  set r : ℚ := cResQ n 1 - OSalikhovIntCoord.BseqQ n with hrdef
  have hrne : r ≠ 0 := sub_ne_zero.mpr hne
  -- The two decompositions of `E1 n`, combined into a single real identity.
  have hdec := OSalikhovTwoLog.E1_decomp n
  have hraw := E1_eq_raw n
  have hcombine : A1seq n + Bseq n * Real.log (2 / 3)
      = (q : ℝ) + (cResQ n 1 : ℝ) * Real.log (2 / 3) := by
    rw [← hdec, hraw, hq]; simp only [cResR]
  -- Cast bridges (`A1seq` here is `OSalikhovSequences.A1seq`, defeq to the `OSalikhovHdet` one).
  have hA1 : A1seq n = (OSalikhovIntCoord.A1seqQ n : ℝ) := (OSalikhovIntCoord.A1seqQ_cast n).symm
  have hBeq : Bseq n = (OSalikhovIntCoord.BseqQ n : ℝ) := (OSalikhovIntCoord.BseqQ_cast n).symm
  rw [hA1, hBeq] at hcombine
  -- Solve for `log(2/3)` as a rational, contradicting irrationality.
  have hL : Real.log (2 / 3) = (((OSalikhovIntCoord.A1seqQ n - q) / r : ℚ) : ℝ) := by
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hrne
    have hstep : ((OSalikhovIntCoord.A1seqQ n - q : ℚ) : ℝ)
        = Real.log (2 / 3) * (r : ℝ) := by
      rw [hrdef]; push_cast; push_cast at hcombine; linear_combination hcombine
    rw [Rat.cast_div, hstep, mul_div_assoc, div_self hrR, mul_one]
  exact hirr ⟨(OSalikhovIntCoord.A1seqQ n - q) / r, hL.symm⟩

/-! ## A2 analogs — the same construction integrated over `[0,5]`

On `[0,5]`: `x − 15 ∈ [−15,−10]` (negative), `x + 15 ∈ [15,20]` (positive).  The `j=1` log part
collapses to `c_1·(−log 2)` (since `d_1 = −c_1` and `log(10/15) − log(20/15) = log(1/2) = −log 2`),
matching `E2_decomp : E2 = A2seq − Bseq·log 2`. -/

/-- `∫₀⁵ (x−15)⁻¹ dx = log(10/15)`.  (Shift to `∫_{−15}^{−10} t⁻¹`, both endpoints `< 0`.) -/
theorem integral_sub15_inv_five : (∫ x in (0:ℝ)..5, (x - 15)⁻¹) = Real.log (10 / 15) := by
  have e : (∫ x in (0:ℝ)..5, (x - 15)⁻¹) = ∫ x in (0:ℝ)..5, ((fun t => t⁻¹) (x + (-15))) := by
    apply intervalIntegral.integral_congr; intro x _; simp [sub_eq_add_neg]
  rw [e, intervalIntegral.integral_comp_add_right (fun t => t⁻¹) (-15),
    show (0:ℝ) + -15 = -15 by norm_num, show (5:ℝ) + -15 = -10 by norm_num,
    integral_inv_of_neg (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- `∫₀⁵ (x+15)⁻¹ dx = log(20/15)`.  (Shift to `∫_{15}^{20} t⁻¹`, both endpoints `> 0`.) -/
theorem integral_add15_inv_five : (∫ x in (0:ℝ)..5, (x + 15)⁻¹) = Real.log (20 / 15) := by
  rw [intervalIntegral.integral_comp_add_right (fun t => t⁻¹) 15,
    show (0:ℝ) + 15 = 15 by norm_num, show (5:ℝ) + 15 = 20 by norm_num,
    integral_inv_of_pos (by norm_num) (by norm_num)]

/-- For `j ≥ 2`: `∫₀⁵ ((x−15)^j)⁻¹ dx = ((−10)^{1−j} − (−15)^{1−j})/(1−j)` (no log; rational). -/
theorem integral_sub15_zpow_five (j : ℕ) (hj : 2 ≤ j) :
    (∫ x in (0:ℝ)..5, ((x - 15) ^ j)⁻¹)
      = ((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)) := by
  have hj0 : (-(j : ℤ)) ≠ -1 := by omega
  have hint : (∫ x in (0:ℝ)..5, ((x - 15) ^ j)⁻¹)
      = ∫ x in (0:ℝ)..5, ((fun t => t ^ (-(j : ℤ))) (x + (-15))) := by
    apply intervalIntegral.integral_congr; intro x _
    simp only []
    rw [show (x + (-15) : ℝ) = x - 15 by ring, zpow_neg, zpow_natCast]
  rw [hint, intervalIntegral.integral_comp_add_right (fun t => t ^ (-(j : ℤ))) (-15),
    show (0:ℝ) + -15 = -15 by norm_num, show (5:ℝ) + -15 = -10 by norm_num,
    integral_zpow (Or.inr ⟨hj0, by norm_num [Set.mem_uIcc]⟩),
    show -(j : ℤ) + 1 = 1 - (j : ℤ) by ring]
  congr 1
  push_cast; ring

/-- For `j ≥ 2`: `∫₀⁵ ((x+15)^j)⁻¹ dx = (20^{1−j} − 15^{1−j})/(1−j)` (no log; rational). -/
theorem integral_add15_zpow_five (j : ℕ) (hj : 2 ≤ j) :
    (∫ x in (0:ℝ)..5, ((x + 15) ^ j)⁻¹)
      = ((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)) := by
  have hj0 : (-(j : ℤ)) ≠ -1 := by omega
  have hint : (∫ x in (0:ℝ)..5, ((x + 15) ^ j)⁻¹)
      = ∫ x in (0:ℝ)..5, ((fun t => t ^ (-(j : ℤ))) (x + 15)) := by
    apply intervalIntegral.integral_congr; intro x _
    simp only []
    rw [zpow_neg, zpow_natCast]
  rw [hint, intervalIntegral.integral_comp_add_right (fun t => t ^ (-(j : ℤ))) 15,
    show (0:ℝ) + 15 = 15 by norm_num, show (5:ℝ) + 15 = 20 by norm_num,
    integral_zpow (Or.inr ⟨hj0, by norm_num [Set.mem_uIcc]⟩),
    show -(j : ℤ) + 1 = 1 - (j : ℤ) by ring]
  congr 1
  push_cast; ring

/-- The simple-pole log combination over `[0,5]` collapses to `−log 2`:
`log(10/15) − log(20/15) = log(1/2) = −log 2`. -/
theorem log_simple_pole_collapse_five :
    Real.log (10 / 15) - Real.log (20 / 15) = -Real.log 2 := by
  rw [← Real.log_div (by norm_num) (by norm_num),
    show (10 / 15) / (20 / 15) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

/-- **Full pointwise partial-fraction expansion** on `0 ≤ x ≤ 5` (proved modulo
`rem_div_den_partialFraction`). -/
theorem fOsal_partialFraction_five (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx5 : x ≤ 5) :
    fOsal n x = Polynomial.aeval x (polyPartZ n)
      + (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j / (x - 15) ^ j)
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j / (x + 15) ^ j := by
  have hx2 : x ^ 2 < 225 := by nlinarith
  have hd : Polynomial.aeval x (denZ n) ≠ 0 := aeval_denZ_ne_zero_of_lt n hx2
  have hx15 : x ≠ 15 := by intro h; rw [h] at hx2; norm_num at hx2
  have hx15' : x ≠ -15 := by intro h; rw [h] at hx2; norm_num at hx2
  rw [fOsal_eq_polyPart_add_rem n hd, rem_div_den_partialFraction n hx15 hx15']
  ring

/-- The explicit rational part of `E2`: `A2explicit n = ∫₀⁵ Pₙ + Σ_{j≥2} (pole rational terms)`. -/
noncomputable def A2explicit (n : ℕ) : ℝ :=
  (∫ x in (0:ℝ)..5, Polynomial.aeval x (polyPartZ n))
    + (∑ j ∈ Finset.Icc 2 (2 * n + 1),
        cResR n j * (((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))))
    + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
        dResR n j * (((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)))

/-- **The `E2` partial-fraction integral identity** (proved modulo `rem_div_den_partialFraction`
and `cResQ_one_eq_Bseq`): `E2 n = A2explicit n − Bseq n · log 2`. -/
theorem E2_eq (n : ℕ) : E2 n = A2explicit n - Bseq n * Real.log 2 := by
  -- Integrability of the individual `(x∓15)`-power terms on `[0,5]`.
  have hcterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 5 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hdterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 5 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hPoly : IntervalIntegrable (fun x => Polynomial.aeval x (polyPartZ n)) MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hB : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹) MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hC : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hcong : E2 n = ∫ x in (0:ℝ)..5,
      ((Polynomial.aeval x (polyPartZ n)
          + (∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹))
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹) := by
    rw [show E2 n = ∫ x in (0:ℝ)..5, fOsal n x from rfl]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hx
    simp only [Set.mem_Icc] at hx
    rw [fOsal_partialFraction_five n hx.1 hx.2]
    simp only [div_eq_mul_inv]
  have hIcc : Finset.Icc 1 (2 * n + 1) = insert 1 (Finset.Icc 2 (2 * n + 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 (2 * n + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hCsum : (∫ x in (0:ℝ)..5,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), cResR n j * ((x - 15) ^ j)⁻¹)
      = cResR n 1 * Real.log (10 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            cResR n j * (((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hcterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_sub15_inv_five
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_sub15_zpow_five j hj.1]
  have hDsum : (∫ x in (0:ℝ)..5,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), dResR n j * ((x + 15) ^ j)⁻¹)
      = dResR n 1 * Real.log (20 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            dResR n j * (((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hdterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact integral_add15_inv_five
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, integral_add15_zpow_five j hj.1]
  have hlog : cResR n 1 * Real.log (10 / 15) + dResR n 1 * Real.log (20 / 15)
      = -(Bseq n * Real.log 2) := by
    have hb : cResR n 1 = Bseq n := by
      simp only [cResR]; rw [cResQ_one_eq_Bseq, OSalikhovIntCoord.BseqQ_cast]
    rw [dResR_eq, hb]
    linear_combination (Bseq n) * log_simple_pole_collapse_five
  rw [hcong, intervalIntegral.integral_add (hPoly.add hB) hC,
    intervalIntegral.integral_add hPoly hB, hCsum, hDsum, A2explicit]
  linear_combination hlog

/-- **`hdvd`-closing identity for `A2`** (from `E2_decomp` and `E2_eq`): `A2seq n = A2explicit n`. -/
theorem A2seq_eq (n : ℕ) : A2seq n = A2explicit n := by
  have hdec := OSalikhovTwoLog.E2_decomp n
  have heq := E2_eq n
  rw [hdec] at heq
  exact sub_left_inj.mp heq

end OSalikhovPFI

