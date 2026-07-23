import Propositio.NumberTheory.Diophantine.OSalikhovPFI
import Propositio.NumberTheory.Diophantine.OSalikhovHdvdExplicit
import Propositio.NumberTheory.Diophantine.OSalikhovDecomp
import Propositio.NumberTheory.Diophantine.OSalikhovGCoeff
import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Propositio.NumberTheory.Collatz.Chebyshev30LcmAll
import Propositio.NumberTheory.Collatz.PowGapOfHdvd
import Propositio.NumberTheory.Diophantine.OSalikhovMeasureOfHdvd
import Mathlib

/-!
# `Irrational (Real.log (2/3))` from the construction, and an UNCONDITIONAL Collatz `PowGap`

This file closes the last gap of the oSALIKHOV/Apéry-second-solution route to a Baker-free Collatz
`PowGap`.  Its three steps:

* **STEP 1** (`cResQ_one_times_30`): `30 · cResQ n 1 ∈ ℤ` — i.e. `(cResQ n 1).den ∣ 30`.  The simple
  residue `c₁` of `fOsal n` has denominator dividing `30`.  Proof: the `j = 1` analogue of the
  `poleTerm` clearing, using the sharp per-prime coefficient bounds
  `OSalikhovGCoeff.Gpoly_coeff_dvd_{2,3,5}` (`p^(4n−i) ∣ coeff i`) combined coprimely to
  `30^(4n−i) ∣ (gNum n).coeff i`.

* **STEP 2** (`irrational_log_two_thirds`): `Irrational (Real.log (2/3))`, proved *from the
  construction* (non-circular).  From `E1_eq_raw` (`E1 = A1explicit + cResR(·,1)·log(2/3)`) and the
  integrality bricks, `tgt n · E1 n = aₙ + bₙ·log(2/3)` is a nonzero integer combination of
  `1, log(2/3)` that tends to `0` (decay `|E1 n| ≤ 3·(1/100)ⁿ`, `tgt n ≤ 6·30ⁿ`).  A rational
  `log(2/3)` would make it a nonzero integer of modulus `< 1` — contradiction.  Clones
  `DiagonalIntegralLog2.log_two_irrational`.

* **STEP 3** (`collatz_powGap_unconditional`): feed the irrationality into
  `cResQ_one_eq_Bseq_of_irrational` to get `cResQ n 1 = BseqQ n` unconditionally, re-derive the
  `hdvd`-closing identities `A1seqQ n = A1expl n`, `A2seqQ n = A2expl n` **without** PFI's
  `cResQ_one_eq_Bseq` `sorry`, and conclude `PowGap` via `collatz_powGap_of_hdvd`.
-/

namespace OSalikhovUnconditional

open Filter
open scoped BigOperators

/-! ## STEP 1 — `(cResQ n 1).den ∣ 30` -/

/-- **STEP 1.**  `30 · cResQ n 1` is an integer (equivalently `(cResQ n 1).den ∣ 30`).
The simple-residue `c₁ = cResQ n 1 = ∑_k (−1)^k C(2n+k,k)·coeff(2n−k)/30^(2n+1+k)`, so
`30·c₁ = ∑_k (−1)^k C(2n+k,k)·coeff(2n−k)/30^(2n+k)`; with `i = 2n−k` the per-prime sharp bounds
`p^(4n−i) ∣ coeff i` combine to `30^(2n+k)=30^(4n−i) ∣ coeff(2n−k)`, clearing each term. -/
theorem cResQ_one_times_30 (n : ℕ) :
    ∃ z : ℤ, (30 : ℚ) * OSalikhovPFI.cResQ n 1 = (z : ℚ) := by
  classical
  -- per-term integrality
  have hterm : ∀ k ∈ Finset.range (2 * n + 2 - 1), ∃ w : ℤ,
      (30 : ℚ) * ((-1 : ℚ) ^ k * (Nat.choose (2 * n + k) k : ℚ)
        * ((OSalikhovPFI.gNum n).coeff (2 * n + 1 - 1 - k) : ℚ) / (30 : ℚ) ^ (2 * n + 1 + k))
        = (w : ℚ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk2n : k ≤ 2 * n := by omega
    set i := 2 * n - k with hi
    have hidx : 2 * n + 1 - 1 - k = i := by omega
    have he : 4 * n - i = 2 * n + k := by omega
    have hcoeff : (OSalikhovPFI.gNum n).coeff i = (OSalikhovGCoeff.Gpoly n).coeff i := by
      rw [← OSalikhovHdvdExplicit.gZ_eq_gNum, OSalikhovHdvdExplicit.gZ_eq_Gpoly]
    have d2 : (2 : ℤ) ^ (2 * n + k) ∣ (OSalikhovPFI.gNum n).coeff i := by
      rw [hcoeff, ← he]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_2 n i
    have d3 : (3 : ℤ) ^ (2 * n + k) ∣ (OSalikhovPFI.gNum n).coeff i := by
      rw [hcoeff, ← he]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_3 n i
    have d5 : (5 : ℤ) ^ (2 * n + k) ∣ (OSalikhovPFI.gNum n).coeff i := by
      rw [hcoeff, ← he]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_5 n i
    have c23 : IsCoprime (2 : ℤ) 3 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
    have c25 : IsCoprime (2 : ℤ) 5 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
    have c35 : IsCoprime (3 : ℤ) 5 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
    have d235 : ((2 : ℤ) ^ (2 * n + k) * 3 ^ (2 * n + k) * 5 ^ (2 * n + k))
        ∣ (OSalikhovPFI.gNum n).coeff i :=
      ((c25.pow).mul_left (c35.pow)).mul_dvd (c23.pow.mul_dvd d2 d3) d5
    have h30e : (30 : ℤ) ^ (2 * n + k)
        = 2 ^ (2 * n + k) * 3 ^ (2 * n + k) * 5 ^ (2 * n + k) := by
      rw [show (30 : ℤ) = 2 * 3 * 5 by norm_num]; simp only [mul_pow]
    have d30 : (30 : ℤ) ^ (2 * n + k) ∣ (OSalikhovPFI.gNum n).coeff i := by rw [h30e]; exact d235
    obtain ⟨c, hc⟩ := d30
    refine ⟨(-1 : ℤ) ^ k * (Nat.choose (2 * n + k) k : ℤ) * c, ?_⟩
    rw [hidx]
    have hcQ : ((OSalikhovPFI.gNum n).coeff i : ℚ) = (30 : ℚ) ^ (2 * n + k) * (c : ℚ) := by
      rw [hc]; push_cast; ring
    rw [hcQ]
    have hsplit : (30 : ℚ) ^ (2 * n + 1 + k) = 30 * 30 ^ (2 * n + k) := by
      rw [show 2 * n + 1 + k = (2 * n + k) + 1 by omega, pow_succ]; ring
    rw [hsplit]
    have h30Q : (30 : ℚ) ^ (2 * n + k) ≠ 0 := by positivity
    push_cast
    field_simp
  -- assemble the sum
  let zf : ℕ → ℤ := fun k => if h : k ∈ Finset.range (2 * n + 2 - 1) then (hterm k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (2 * n + 2 - 1), zf k, ?_⟩
  unfold OSalikhovPFI.cResQ
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [zf, dif_pos hk]
  exact (hterm k hk).choose_spec

/-! ## `tgt` facts -/

theorem tgt_pos (n : ℕ) : 0 < OSalikhovHdvdExplicit.tgt n := by
  unfold OSalikhovHdvdExplicit.tgt
  have hl : 0 < LcmGrowthBound.lcmUpto (2 * n) :=
    Nat.pos_of_ne_zero (LcmGrowthBound.lcmUpto_ne_zero _)
  positivity

theorem tgt_le (n : ℕ) (hn : 1 ≤ n) : OSalikhovHdvdExplicit.tgt n ≤ 6 * 30 ^ n := by
  unfold OSalikhovHdvdExplicit.tgt
  have h := CollatzChebyshev30.lcm_two_n_le_target_all n hn
  calc 3 ^ n * 30 * LcmGrowthBound.lcmUpto (2 * n)
      = 3 ^ n * (30 * LcmGrowthBound.lcmUpto (2 * n)) := by ring
    _ ≤ 3 ^ n * (6 * 10 ^ n) := by gcongr
    _ = 6 * 30 ^ n := by rw [show (30 : ℕ) ^ n = 3 ^ n * 10 ^ n by rw [← mul_pow]; norm_num]; ring

/-! ## STEP 2a — `E1 n ≠ 0` (constant sign on `(0,3)`) -/

/-- On `(0,3)` the integrand `fOsal n` is strictly negative:  numerator
`x^(2n)((x²−9)(x²−25))ⁿ > 0` (both factors negative ⇒ product positive), denominator
`(x²−225)^(2n+1) < 0` (odd power of a negative). -/
theorem fOsal_neg_of_mem (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 3) :
    OSalikhovTwoLog.fOsal n x < 0 := by
  obtain ⟨hx0, hx3⟩ := hx
  unfold OSalikhovTwoLog.fOsal
  have hx2 : x ^ 2 < 9 := by nlinarith
  have hnumpos : 0 < x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n := by
    have hh : x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n
        = (x ^ 2) ^ n * ((x ^ 2 - 9) * (x ^ 2 - 25)) ^ n := by
      rw [pow_mul, mul_pow]; ring
    rw [hh]
    apply mul_pos (pow_pos (pow_pos hx0 2) n)
    apply pow_pos
    apply mul_pos_of_neg_of_neg <;> nlinarith
  have hdenneg : (x ^ 2 - 225) ^ (2 * n + 1) < 0 := by
    apply Odd.pow_neg ⟨n, by ring⟩
    nlinarith
  exact div_neg_of_pos_of_neg hnumpos hdenneg

/-- **STEP 2a.**  `E1 n ≠ 0`:  `∫₀³ fOsal n < 0`, since `−fOsal n > 0` on `(0,3)`. -/
theorem E1_ne_zero (n : ℕ) : OSalikhovTwoLog.E1 n ≠ 0 := by
  have hpos : 0 < ∫ x in (0 : ℝ)..3, (- OSalikhovTwoLog.fOsal n x) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (OSalikhovTwoLog.fOsal_intervalIntegrable_three n).neg
    · intro x hx; exact neg_pos.mpr (fOsal_neg_of_mem n hx)
    · norm_num
  have hE : OSalikhovTwoLog.E1 n = ∫ x in (0 : ℝ)..3, OSalikhovTwoLog.fOsal n x := rfl
  rw [intervalIntegral.integral_neg, ← hE] at hpos
  exact ne_of_lt (by linarith)

/-! ## STEP 2b — the integer linear form `tgt n · E1 n = aₙ + bₙ·log(2/3)` -/

/-- **STEP 2b.**  `tgt n · E1 n` is an integer combination of `1` and `log(2/3)`. -/
theorem E1_int_combo (n : ℕ) :
    ∃ a b : ℤ, (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovTwoLog.E1 n
      = (a : ℝ) + (b : ℝ) * Real.log (2 / 3) := by
  obtain ⟨az, haz⟩ := OSalikhovHdvdExplicit.A1expl_clear n
  obtain ⟨bz0, hbz0⟩ := cResQ_one_times_30 n
  set b : ℤ := (3 : ℤ) ^ n * (LcmGrowthBound.lcmUpto (2 * n) : ℤ) * bz0 with hbdef
  refine ⟨az, b, ?_⟩
  -- the `a`-part
  have ha : (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.A1explicit n = (az : ℝ) := by
    have h1 : (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.A1explicit n
        = (((OSalikhovHdvdExplicit.tgt n : ℚ) * OSalikhovHdvdExplicit.A1expl n : ℚ) : ℝ) := by
      rw [← OSalikhovHdvdExplicit.A1expl_cast_eq n]; push_cast; ring
    rw [h1, haz]; norm_cast
  -- the `b`-part
  have htgt : (OSalikhovHdvdExplicit.tgt n : ℚ)
      = 30 * ((3 : ℚ) ^ n * (LcmGrowthBound.lcmUpto (2 * n) : ℚ)) := by
    unfold OSalikhovHdvdExplicit.tgt; push_cast; ring
  have hbq : (OSalikhovHdvdExplicit.tgt n : ℚ) * OSalikhovPFI.cResQ n 1 = (b : ℚ) := by
    rw [htgt]
    have hreassoc : 30 * ((3 : ℚ) ^ n * (LcmGrowthBound.lcmUpto (2 * n) : ℚ))
          * OSalikhovPFI.cResQ n 1
        = ((3 : ℚ) ^ n * (LcmGrowthBound.lcmUpto (2 * n) : ℚ)) * (30 * OSalikhovPFI.cResQ n 1) := by
      ring
    rw [hreassoc, hbz0, hbdef]; push_cast; ring
  have hbr : (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.cResR n 1 = (b : ℝ) := by
    have hcast : (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.cResR n 1
        = (((OSalikhovHdvdExplicit.tgt n : ℚ) * OSalikhovPFI.cResQ n 1 : ℚ) : ℝ) := by
      show (OSalikhovHdvdExplicit.tgt n : ℝ) * ((OSalikhovPFI.cResQ n 1 : ℚ) : ℝ) = _
      push_cast; ring
    rw [hcast, hbq]; norm_cast
  -- assemble
  rw [OSalikhovPFI.E1_eq_raw n]
  have key : (OSalikhovHdvdExplicit.tgt n : ℝ)
        * (OSalikhovPFI.A1explicit n + OSalikhovPFI.cResR n 1 * Real.log (2 / 3))
      = (OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.A1explicit n
        + ((OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovPFI.cResR n 1) * Real.log (2 / 3) := by
    ring
  rw [key, ha, hbr]

/-! ## STEP 2 — `Irrational (Real.log (2/3))` -/

/-- **STEP 2.**  `Real.log (2/3)` is irrational, proved directly from the oSALIKHOV construction.
Clone of `DiagonalIntegralLog2.log_two_irrational`. -/
theorem irrational_log_two_thirds : Irrational (Real.log (2 / 3)) := by
  rintro ⟨r, hr⟩
  set bI : ℤ := (r.den : ℤ) with hbI
  have hbpos : (0 : ℝ) < (bI : ℝ) := by rw [hbI]; exact_mod_cast r.pos
  have hbne : (bI : ℝ) ≠ 0 := ne_of_gt hbpos
  have hlog : Real.log (2 / 3) = (r.num : ℝ) / (bI : ℝ) := by
    rw [← hr, Rat.cast_def, hbI]; push_cast; ring
  -- nonzero integer ≥ 1
  have hge : ∀ n : ℕ, (1 : ℝ) ≤ |(bI : ℝ) * ((OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovTwoLog.E1 n)| := by
    intro n
    obtain ⟨a, b, hab⟩ := E1_int_combo n
    set M : ℤ := bI * a + b * r.num with hM
    have hval : (bI : ℝ) * ((OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovTwoLog.E1 n) = (M : ℝ) := by
      rw [hab, hlog, hM]; push_cast; field_simp
    have hMne : M ≠ 0 := by
      have hne : (M : ℝ) ≠ 0 := by
        rw [← hval]
        exact mul_ne_zero hbne
          (mul_ne_zero (by exact_mod_cast (tgt_pos n).ne') (E1_ne_zero n))
      exact_mod_cast hne
    have h1 : (1 : ℝ) ≤ |(M : ℝ)| := by
      have hZ : (1 : ℤ) ≤ |M| := Int.one_le_abs hMne
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|M| : ℤ) : ℝ) := by exact_mod_cast hZ
        _ = |(M : ℝ)| := by rw [Int.cast_abs]
    rwa [hval]
  -- decay bound (n ≥ 1)
  have hdecay : ∀ n : ℕ, 1 ≤ n →
      |(bI : ℝ) * ((OSalikhovHdvdExplicit.tgt n : ℝ) * OSalikhovTwoLog.E1 n)|
        ≤ 18 * |(bI : ℝ)| * (3 / 10 : ℝ) ^ n := by
    intro n hn
    rw [abs_mul, abs_mul]
    have htabs : |(OSalikhovHdvdExplicit.tgt n : ℝ)| = (OSalikhovHdvdExplicit.tgt n : ℝ) :=
      abs_of_nonneg (by positivity)
    rw [htabs]
    have he1 : |OSalikhovTwoLog.E1 n| ≤ 3 * (1 / 100) ^ n := OSalikhovTwoLog.E1_abs_le n
    have htle : (OSalikhovHdvdExplicit.tgt n : ℝ) ≤ 6 * 30 ^ n := by exact_mod_cast tgt_le n hn
    have hstep : (OSalikhovHdvdExplicit.tgt n : ℝ) * |OSalikhovTwoLog.E1 n| ≤ 18 * (3 / 10) ^ n := by
      calc (OSalikhovHdvdExplicit.tgt n : ℝ) * |OSalikhovTwoLog.E1 n|
          ≤ (6 * 30 ^ n) * (3 * (1 / 100) ^ n) :=
            mul_le_mul htle he1 (abs_nonneg _) (by positivity)
        _ = 18 * (3 / 10) ^ n := by
            rw [show (3 / 10 : ℝ) ^ n = 30 ^ n * (1 / 100) ^ n by
              rw [← mul_pow]; norm_num]
            ring
    calc |(bI : ℝ)| * ((OSalikhovHdvdExplicit.tgt n : ℝ) * |OSalikhovTwoLog.E1 n|)
        ≤ |(bI : ℝ)| * (18 * (3 / 10) ^ n) := by
          apply mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
      _ = 18 * |(bI : ℝ)| * (3 / 10) ^ n := by ring
  -- the geometric majorant → 0
  have htend : Tendsto (fun n : ℕ => 18 * |(bI : ℝ)| * (3 / 10 : ℝ) ^ n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 10) (by norm_num : (3 / 10 : ℝ) < 1)
    have h2 := h.const_mul (18 * |(bI : ℝ)|)
    simpa using h2
  obtain ⟨n, hUlt, hn1⟩ :=
    ((htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).and (eventually_ge_atTop 1)).exists
  have hlow := hge n
  have hupp := hdecay n hn1
  linarith

/-! ## STEP 3 — the unconditional Collatz `PowGap` -/

/-- `cResQ n 1 = BseqQ n`, now UNCONDITIONAL via `irrational_log_two_thirds`. -/
theorem cResQ_one_eq_BseqQ (n : ℕ) : OSalikhovPFI.cResQ n 1 = OSalikhovIntCoord.BseqQ n :=
  OSalikhovPFI.cResQ_one_eq_Bseq_of_irrational irrational_log_two_thirds
    (fun m => ⟨OSalikhovHdvdExplicit.A1expl m, (OSalikhovHdvdExplicit.A1expl_cast_eq m).symm⟩) n

/-- `cResR n 1 = Bseq n` (real cast of the previous). -/
theorem cResR_one_eq_Bseq (n : ℕ) :
    OSalikhovPFI.cResR n 1 = OSalikhovSequences.Bseq n := by
  show ((OSalikhovPFI.cResQ n 1 : ℚ) : ℝ) = OSalikhovSequences.Bseq n
  rw [cResQ_one_eq_BseqQ n, OSalikhovIntCoord.BseqQ_cast n]

/-- The raw `E2` integral identity (clone of `OSalikhovPFI.E2_eq` keeping the raw residue
`cResR n 1`, hence **sorry-free** — it does not invoke `cResQ_one_eq_Bseq`). -/
theorem E2_eq_raw (n : ℕ) :
    OSalikhovTwoLog.E2 n = OSalikhovPFI.A2explicit n - OSalikhovPFI.cResR n 1 * Real.log 2 := by
  have hcterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => OSalikhovPFI.cResR n j * ((x - 15) ^ j)⁻¹)
        MeasureTheory.volume 0 5 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hdterm : ∀ j : ℕ,
      IntervalIntegrable (fun x => OSalikhovPFI.dResR n j * ((x + 15) ^ j)⁻¹)
        MeasureTheory.volume 0 5 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hPoly : IntervalIntegrable
      (fun x => Polynomial.aeval x (OSalikhovPFI.polyPartZ n)) MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hB : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.cResR n j * ((x - 15) ^ j)⁻¹)
      MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.2]
  have hC : IntervalIntegrable
      (fun x => ∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.dResR n j * ((x + 15) ^ j)⁻¹)
      MeasureTheory.volume 0 5 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
      simp only [Set.mem_Icc] at hx
      refine pow_ne_zero _ ?_
      intro h; linarith [hx.1]
  have hcong : OSalikhovTwoLog.E2 n = ∫ x in (0 : ℝ)..5,
      ((Polynomial.aeval x (OSalikhovPFI.polyPartZ n)
          + (∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.cResR n j * ((x - 15) ^ j)⁻¹))
        + ∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.dResR n j * ((x + 15) ^ j)⁻¹) := by
    rw [show OSalikhovTwoLog.E2 n = ∫ x in (0 : ℝ)..5, OSalikhovTwoLog.fOsal n x from rfl]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
    simp only [Set.mem_Icc] at hx
    rw [OSalikhovPFI.fOsal_partialFraction_five n hx.1 hx.2]
    simp only [div_eq_mul_inv]
  have hIcc : Finset.Icc 1 (2 * n + 1) = insert 1 (Finset.Icc 2 (2 * n + 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 (2 * n + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hCsum : (∫ x in (0 : ℝ)..5,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.cResR n j * ((x - 15) ^ j)⁻¹)
      = OSalikhovPFI.cResR n 1 * Real.log (10 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            OSalikhovPFI.cResR n j
              * (((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hcterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact OSalikhovPFI.integral_sub15_inv_five
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, OSalikhovPFI.integral_sub15_zpow_five j hj.1]
  have hDsum : (∫ x in (0 : ℝ)..5,
        ∑ j ∈ Finset.Icc 1 (2 * n + 1), OSalikhovPFI.dResR n j * ((x + 15) ^ j)⁻¹)
      = OSalikhovPFI.dResR n 1 * Real.log (20 / 15)
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1),
            OSalikhovPFI.dResR n j
              * (((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    rw [intervalIntegral.integral_finset_sum (fun j _ => hdterm j), hIcc,
      Finset.sum_insert h1notin]
    congr 1
    · rw [intervalIntegral.integral_const_mul]; congr 1
      simp only [pow_one]; exact OSalikhovPFI.integral_add15_inv_five
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [intervalIntegral.integral_const_mul, OSalikhovPFI.integral_add15_zpow_five j hj.1]
  have hlog : OSalikhovPFI.cResR n 1 * Real.log (10 / 15)
        + OSalikhovPFI.dResR n 1 * Real.log (20 / 15)
      = -(OSalikhovPFI.cResR n 1 * Real.log 2) := by
    rw [OSalikhovPFI.dResR_eq]
    linear_combination (OSalikhovPFI.cResR n 1) * OSalikhovPFI.log_simple_pole_collapse_five
  rw [hcong, intervalIntegral.integral_add (hPoly.add hB) hC,
    intervalIntegral.integral_add hPoly hB, hCsum, hDsum, OSalikhovPFI.A2explicit]
  linear_combination hlog

/-- `A1seq n = A1explicit n`, UNCONDITIONAL (does not use PFI's `A1seq_eq`/`cResQ_one_eq_Bseq`). -/
theorem A1seq_eq_uncond (n : ℕ) :
    OSalikhovHdet.A1seq n = OSalikhovPFI.A1explicit n := by
  have hdec := OSalikhovTwoLog.E1_decomp n
  have hraw := OSalikhovPFI.E1_eq_raw n
  rw [cResR_one_eq_Bseq n] at hraw
  rw [hdec] at hraw
  exact add_right_cancel hraw

/-- `A2seq n = A2explicit n`, UNCONDITIONAL. -/
theorem A2seq_eq_uncond (n : ℕ) :
    OSalikhovSequences.A2seq n = OSalikhovPFI.A2explicit n := by
  have hdec := OSalikhovTwoLog.E2_decomp n
  have hraw := E2_eq_raw n
  rw [cResR_one_eq_Bseq n] at hraw
  rw [hdec] at hraw
  exact sub_left_inj.mp hraw

/-- `A1seqQ n = A1expl n`, UNCONDITIONAL (the `hdvd`-closing identity, no `sorry`). -/
theorem A1expl_eq_uncond (n : ℕ) : OSalikhovIntCoord.A1seqQ n = OSalikhovHdvdExplicit.A1expl n := by
  have h : (OSalikhovIntCoord.A1seqQ n : ℝ) = ((OSalikhovHdvdExplicit.A1expl n : ℚ) : ℝ) := by
    rw [OSalikhovIntCoord.A1seqQ_cast n, A1seq_eq_uncond n, OSalikhovHdvdExplicit.A1expl_cast_eq n]
  exact_mod_cast h

/-- `A2seqQ n = A2expl n`, UNCONDITIONAL. -/
theorem A2expl_eq_uncond (n : ℕ) : OSalikhovIntCoord.A2seqQ n = OSalikhovHdvdExplicit.A2expl n := by
  have h : (OSalikhovIntCoord.A2seqQ n : ℝ) = ((OSalikhovHdvdExplicit.A2expl n : ℚ) : ℝ) := by
    rw [OSalikhovIntCoord.A2seqQ_cast n, A2seq_eq_uncond n, OSalikhovHdvdExplicit.A2expl_cast_eq n]
  exact_mod_cast h

/-- **The elementary divisibility `hdvd`, UNCONDITIONAL.**
`DenIntN n ∣ 3ⁿ·30·lcm(1..2n)`, with no `sorry` anywhere upstream. -/
theorem hdvd_uncond (n : ℕ) :
    OSalikhovIntCoord.DenIntN n ∣ 3 ^ n * 30 * LcmGrowthBound.lcmUpto (2 * n) := by
  have hA2 : (OSalikhovIntCoord.A2seqQ n).den ∣ OSalikhovHdvdExplicit.tgt n := by
    rw [A2expl_eq_uncond n]; exact OSalikhovHdvdExplicit.A2expl_den_dvd n
  have hS : (OSalikhovIntCoord.A1seqQ n + OSalikhovIntCoord.A2seqQ n).den
      ∣ OSalikhovHdvdExplicit.tgt n := by
    rw [A1expl_eq_uncond n, A2expl_eq_uncond n]; exact OSalikhovHdvdExplicit.sum_expl_den_dvd n
  exact Nat.lcm_dvd hS hA2

/-- **FULLY UNCONDITIONAL Collatz `PowGap` (no Baker).**  The capstone: feed `hdvd_uncond` into the
sorry-free `CollatzPowGapOfHdvd.collatz_powGap_of_hdvd`. -/
theorem collatz_powGap_unconditional : CollatzDescentDichotomy.PowGap :=
  CollatzPowGapOfHdvd.collatz_powGap_of_hdvd hdvd_uncond

/-- **Unconditional effective irrationality measure of `log₂3`.**  Feeding the now-proved
`hdvd_uncond` into the oSALIKHOV measure engine gives the effective irrationality measure of
`Real.logb 2 3` with exponent `≤ 61` — sorry-free.  This is the transcendence-theory output the
whole construction targets (a Rhin/Salikhov-type effective measure), now unconditional. -/
theorem osalikhov_logb23_measure_unconditional :
    ∃ (Q ρ C : ℝ), 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      Real.log Q / Real.log ρ⁻¹ ≤ 60 ∧
      ∃ A : ℝ, 0 < A ∧
        ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * (A / Real.log 2) * q →
          C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.logb 2 3 - (p : ℝ) / q| :=
  OSalikhovConsolidated.osalikhov_logb23_measure_of_hdvd hdvd_uncond

-- (`log₂3` is irrational as an immediate corollary of `osalikhov_logb23_measure_unconditional`:
-- the lower bound `C/q^μ > 0` gives `log₂3 ≠ p/q` for all rationals with large denominator.)

-- Axiom audit.  Target: no `sorryAx`.
#print axioms collatz_powGap_unconditional
#print axioms osalikhov_logb23_measure_unconditional

end OSalikhovUnconditional
