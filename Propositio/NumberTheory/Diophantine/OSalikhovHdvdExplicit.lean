import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Propositio.NumberTheory.Collatz.PowGapOfHdvd
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Propositio.NumberTheory.Diophantine.OSalikhovGCoeff
import Propositio.NumberTheory.Diophantine.OSalikhovPFI
import Mathlib.Tactic

/-!
# Reducing `hdvd` to the explicit partial-fraction closed form

The whole Collatz-PowGap prize (`CollatzPowGapOfHdvd.collatz_powGap_of_hdvd`) is sorry-free except
its single elementary input

  `hdvd : ∀ m, OSalikhovIntCoord.DenIntN m ∣ 3 ^ m * 30 * LcmGrowthBound.lcmUpto (2 * m)`.

Here `DenIntN m = Nat.lcm (A1seqQ m + A2seqQ m).den (A2seqQ m).den`, where `A1seqQ, A2seqQ : ℕ → ℚ`
are the rational parts of the oSALIKHOV integrals `E1 = ∫₀³ fOsal`, `E2 = ∫₀⁵ fOsal`,
`fOsal n x = x^{2n}(x²−9)^n(x²−25)^n / (x²−225)^{2n+1}` (poles `±15`, order `2n+1`).

This file gives the **explicit partial-fraction closed form** of `A1seqQ`/`A2seqQ` over `ℚ` and
proves the **denominator bound** on that explicit form *outright* (modulo a clearly isolated
`p`-adic coefficient toolkit), thereby reducing `hdvd` to the single deep identity
"explicit form = `A1seqQ`/`A2seqQ`" (`A1expl_eq` / `A2expl_eq`).

## The closed form

Partial fractions of `fOsal n` in `t = x − 15` give, with the (even) numerator
`g(t) = (15+t)^{2n}(12+t)^n(18+t)^n(10+t)^n(20+t)^n` and the `(30+t)^{-(2n+1)}` binomial series,

  `c_j = [t^{2n+1−j}] g`,   `d_j = (−1)^j c_j`     (residues at `x = ±15`),

and, integrating the polynomial part `Pₙ = fOsal n /ₘ (x²−225)^{2n+1}` plus the pole terms,

  `A1 = ∫₀³ Pₙ + Σ_{j=2}^{2n+1} (1/−(j−1))·[ c_j((−12)^{−(j−1)}−(−15)^{−(j−1)})
                                              + d_j(18^{−(j−1)}−15^{−(j−1)}) ]`,
  `A2 = ∫₀⁵ Pₙ + Σ_{j=2}^{2n+1} (1/−(j−1))·[ c_j((−10)^{−(j−1)}−(−15)^{−(j−1)})
                                              + d_j(20^{−(j−1)}−15^{−(j−1)}) ]`.

(`∫₀ᵇ Pₙ = Σ_k (Pₙ.coeff k)·bᵏ⁺¹/(k+1)`.)  All of this is verified numerically in
`experiments/osalikhov_pf_cancellation.clj` and `osalikhov_residue_derive.clj`.

## What is proved here

* **Step 2 (the heart):** `A1expl_den_dvd` / `A2expl_den_dvd` — the denominator of the explicit form
  divides `3ⁿ·30·lcm(1..2n)`.  The polynomial-part contribution is cleared **fully** (`Pₙ` has
  integer coefficients, and `(k+1) ∣ lcm(1..2n)`).  The pole-term contribution is reduced to the
  single per-term `p`-adic clearing lemma `poleTermA1_clear` / `poleTermA2_clear` (the gZ-coefficient
  divisibility toolkit), left as a documented `sorry`.
* **Step 3 (the reduction):** `hdvd_explicit` proves `hdvd` modulo the explicit-form identities
  `A1expl_eq` / `A2expl_eq` (left as documented `sorry`s — the deep PFI/recurrence step), and
  `collatz_powGap_unconditional_modulo_eq` feeds it into the capstone.

## Remaining `sorry`s (exactly four)

1. `poleTermA1_clear` — `(3ⁿ·30·lcm(1..2n))·(pole term j of A1)` is an integer.
2. `poleTermA2_clear` — same for A2.
3. `A1expl_eq` — `A1seqQ n = A1expl n` (closed-form identity).
4. `A2expl_eq` — `A2seqQ n = A2expl n`.
-/

namespace OSalikhovHdvdExplicit

open Polynomial
open scoped BigOperators
open LcmGrowthBound OSalikhovIntCoord

/-! ## The clearing target -/

/-- The denominator-clearing factor `tgt n = 3ⁿ · 30 · lcm(1..2n)` (the RHS of `hdvd`). -/
noncomputable def tgt (n : ℕ) : ℕ := 3 ^ n * 30 * lcmUpto (2 * n)

/-! ## Elementary: an integer-clearing witness forces a denominator divisibility -/

/-- **Converse of `dvd_clears`.**  If `N·q` is an integer (`N : ℕ`), then `q.den ∣ N`. -/
theorem den_dvd_of_clear {q : ℚ} {N : ℕ} (h : ∃ z : ℤ, (N : ℚ) * q = (z : ℚ)) : q.den ∣ N := by
  obtain ⟨z, hz⟩ := h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact dvd_zero _
  · have hNne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq : q = (z : ℚ) / (N : ℚ) := by rw [eq_div_iff hNne, mul_comm]; exact hz
    have hcast : (q.den : ℤ) ∣ (N : ℤ) := by
      have hqdiv : q = Rat.divInt z (N : ℤ) := by rw [hq, Rat.divInt_eq_div]; push_cast; ring
      rw [hqdiv]; exact Rat.den_dvd z (N : ℤ)
    exact_mod_cast hcast

/-! ## Step 1 — the explicit form over ℚ -/

/-- The numerator `(x²−225)`-free factor of the residue generator, in `t = x − 15`:
`gZ n = (15+t)^{2n}(12+t)^n(18+t)^n(10+t)^n(20+t)^n` (an integer polynomial). -/
noncomputable def gZ (n : ℕ) : ℤ[X] :=
  (C 15 + X) ^ (2 * n) * (C 12 + X) ^ n * (C 18 + X) ^ n * (C 10 + X) ^ n * (C 20 + X) ^ n

/-- The residue `c_j = [t^{2n+1−j}] g` of `fOsal n` at the pole `x = 15`, via the binomial series of
`(30+t)^{−(2n+1)} = 30^{−(2n+1)}·Σ_k (−1)^k C(2n+k,k)(t/30)^k`:
`cRes n j = Σ_{k=0}^{2n+1−j} (−1)^k C(2n+k,k)·(gZ n).coeff(2n+1−j−k) / 30^{2n+1+k}`. -/
noncomputable def cRes (n j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * n + 2 - j),
    (((-1) ^ k * (Nat.choose (2 * n + k) k) * (gZ n).coeff (2 * n + 1 - j - k) : ℤ) : ℚ)
      / (30 : ℚ) ^ (2 * n + 1 + k)

/-- The residue `d_j = (−1)^j c_j` of `fOsal n` at the pole `x = −15` (the integrand is even). -/
noncomputable def dRes (n j : ℕ) : ℚ := (-1 : ℚ) ^ j * cRes n j

/-- The integer numerator polynomial `x^{2n}(x²−9)^n(x²−25)^n` of `fOsal n`. -/
noncomputable def numZ (n : ℕ) : ℤ[X] := X ^ (2 * n) * (X ^ 2 - C 9) ^ n * (X ^ 2 - C 25) ^ n

/-- The monic denominator polynomial `(x²−225)^{2n+1}` of `fOsal n`. -/
noncomputable def denZ (n : ℕ) : ℤ[X] := (X ^ 2 - C 225) ^ (2 * n + 1)

/-- The polynomial part `Pₙ = numZ /ₘ denZ` of `fOsal n` (integer coefficients, since `denZ` is
monic and `numZ` has integer coefficients). -/
noncomputable def polyPartZ (n : ℕ) : ℤ[X] := numZ n /ₘ denZ n

/-- `∫₀ᵉ Pₙ = Σ_{k=0}^{2n−1} (Pₙ.coeff k)·e^{k+1}/(k+1)` — the polynomial-part integral with upper
endpoint the integer `e` (`e = 3` for `A1`, `e = 5` for `A2`). -/
noncomputable def polyIntE (n : ℕ) (e : ℤ) : ℚ :=
  ∑ k ∈ Finset.range (2 * n), ((polyPartZ n).coeff k : ℚ) * (e : ℚ) ^ (k + 1) / ((k : ℚ) + 1)

/-- The pole term `j` of `A1` (endpoints `0,3`; factors `−12,−15,18,15`). -/
noncomputable def poleTermA1 (n j : ℕ) : ℚ :=
  (1 / (-((j : ℚ) - 1))) *
    (cRes n j * (((-12 : ℚ) ^ (j - 1))⁻¹ - ((-15 : ℚ) ^ (j - 1))⁻¹)
      + dRes n j * (((18 : ℚ) ^ (j - 1))⁻¹ - ((15 : ℚ) ^ (j - 1))⁻¹))

/-- The pole term `j` of `A2` (endpoints `0,5`; factors `−10,−15,20,15`). -/
noncomputable def poleTermA2 (n j : ℕ) : ℚ :=
  (1 / (-((j : ℚ) - 1))) *
    (cRes n j * (((-10 : ℚ) ^ (j - 1))⁻¹ - ((-15 : ℚ) ^ (j - 1))⁻¹)
      + dRes n j * (((20 : ℚ) ^ (j - 1))⁻¹ - ((15 : ℚ) ^ (j - 1))⁻¹))

/-- The pole sum `Σ_{j=2}^{2n+1}` of `A1`. -/
noncomputable def A1poleSum (n : ℕ) : ℚ := ∑ j ∈ Finset.Icc 2 (2 * n + 1), poleTermA1 n j

/-- The pole sum `Σ_{j=2}^{2n+1}` of `A2`. -/
noncomputable def A2poleSum (n : ℕ) : ℚ := ∑ j ∈ Finset.Icc 2 (2 * n + 1), poleTermA2 n j

/-- **The explicit closed form of `A1seqQ`** (`= ∫₀³ Pₙ + pole sum`). -/
noncomputable def A1expl (n : ℕ) : ℚ := polyIntE n 3 + A1poleSum n

/-- **The explicit closed form of `A2seqQ`** (`= ∫₀⁵ Pₙ + pole sum`). -/
noncomputable def A2expl (n : ℕ) : ℚ := polyIntE n 5 + A2poleSum n

/-! ## Step 2 — the denominator bound on the explicit form

The polynomial-part contribution is cleared completely; the pole-term contribution is reduced to the
isolated `p`-adic coefficient toolkit `poleTermA1_clear` / `poleTermA2_clear`. -/

/-- A single polynomial-part summand clears: `tgt n · (a/(k+1)) ∈ ℤ` whenever `k+1 ≤ 2n`, because
`(k+1) ∣ lcm(1..2n)`. -/
theorem clear_int_div_kp1 (n k : ℕ) (hk : k + 1 ≤ 2 * n) (a : ℤ) :
    ∃ w : ℤ, (tgt n : ℚ) * ((a : ℚ) / ((k : ℚ) + 1)) = (w : ℚ) := by
  obtain ⟨c, hc⟩ := dvd_lcmUpto (show 1 ≤ k + 1 by omega) hk
  refine ⟨(3 : ℤ) ^ n * 30 * c * a, ?_⟩
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  simp only [tgt]
  rw [hc]
  push_cast
  field_simp

/-- **Polynomial-part integrality (fully proved).**  `tgt n · ∫₀ᵉ Pₙ ∈ ℤ`. -/
theorem polyIntE_clear (n : ℕ) (e : ℤ) : ∃ z : ℤ, (tgt n : ℚ) * polyIntE n e = (z : ℚ) := by
  classical
  have hterm : ∀ k ∈ Finset.range (2 * n), ∃ z : ℤ,
      (tgt n : ℚ) * (((polyPartZ n).coeff k : ℚ) * (e : ℚ) ^ (k + 1) / ((k : ℚ) + 1)) = (z : ℚ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : k + 1 ≤ 2 * n := by omega
    obtain ⟨w, hw⟩ := clear_int_div_kp1 n k hk1 ((polyPartZ n).coeff k * e ^ (k + 1))
    exact ⟨w, by rw [← hw]; push_cast; ring⟩
  let zf : ℕ → ℤ := fun k => if h : k ∈ Finset.range (2 * n) then (hterm k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (2 * n), zf k, ?_⟩
  simp only [polyIntE]
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [zf, dif_pos hk]
  exact (hterm k hk).choose_spec

/-! ### Endpoint-cancellation helpers -/

/-- `gZ` is definitionally the toolkit polynomial `Gpoly`. -/
theorem gZ_eq_Gpoly (n : ℕ) : gZ n = OSalikhovGCoeff.Gpoly n := rfl

/-- The `A1` endpoint fraction: `12^{-m} − 18^{-m} = (3^m − 2^m)/6^{2m}`. -/
theorem frac_12_18 (m : ℕ) :
    ((12:ℚ)^m)⁻¹ - ((18:ℚ)^m)⁻¹ = ((3:ℚ)^m - 2^m) / (6:ℚ)^(2*m) := by
  have h12 : (12:ℚ)^m ≠ 0 := by positivity
  have h18 : (18:ℚ)^m ≠ 0 := by positivity
  have h6 : (6:ℚ)^(2*m) ≠ 0 := by positivity
  have e1 : (6:ℚ)^(2*m) = 3^m * 12^m := by
    rw [← mul_pow, show (3:ℚ)*12 = 36 by norm_num, pow_mul]; norm_num
  have e2 : (6:ℚ)^(2*m) = 2^m * 18^m := by
    rw [← mul_pow, show (2:ℚ)*18 = 36 by norm_num, pow_mul]; norm_num
  rw [eq_div_iff h6, sub_mul]
  nth_rewrite 1 [e1]
  nth_rewrite 1 [e2]
  field_simp

/-- The `A2` endpoint fraction: `10^{-m} − 20^{-m} = (2^m − 1)/(2^{2m}·5^m)`. -/
theorem frac_10_20 (m : ℕ) :
    ((10:ℚ)^m)⁻¹ - ((20:ℚ)^m)⁻¹ = ((2:ℚ)^m - 1) / ((2:ℚ)^(2*m) * 5^m) := by
  have h10 : (10:ℚ)^m ≠ 0 := by positivity
  have h20 : (20:ℚ)^m ≠ 0 := by positivity
  have hd : (2:ℚ)^(2*m) * 5^m ≠ 0 := by positivity
  have e1 : (2:ℚ)^(2*m)*5^m = 2^m * 10^m := by
    rw [show (10:ℚ) = 2*5 by norm_num, mul_pow, ← mul_assoc, ← pow_add, two_mul]
  have e2 : (2:ℚ)^(2*m)*5^m = 20^m := by
    rw [show (20:ℚ) = 2^2*5 by norm_num, mul_pow, ← pow_mul]
  rw [eq_div_iff hd, sub_mul]
  nth_rewrite 1 [e1]
  nth_rewrite 1 [e2]
  field_simp

/-- **Endpoint collapse for `A1`.**  The two `15^{−e}` terms cancel:
`poleTermA1 n j = ((-1)^{j-1}/(-(j-1)))·cRes n j·(3^{j-1}−2^{j-1})/6^{2(j-1)}`. -/
theorem poleTermA1_collapse (n j : ℕ) (hj : 2 ≤ j) :
    poleTermA1 n j
      = ((-1:ℚ)^(j-1) / (-((j:ℚ)-1))) * cRes n j
          * (((3:ℚ)^(j-1) - 2^(j-1)) / (6:ℚ)^(2*(j-1))) := by
  have hsinv : ((-1:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) := by rw [← inv_pow]; norm_num
  have hjpow : (-1:ℚ)^j = -((-1:ℚ)^(j-1)) := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    rw [pow_succ]; ring
  have hn12 : ((-12:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) * ((12:ℚ)^(j-1))⁻¹ := by
    rw [show (-12:ℚ) = (-1)*12 by norm_num, mul_pow, mul_inv_rev, hsinv]; ring
  have hn15 : ((-15:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) * ((15:ℚ)^(j-1))⁻¹ := by
    rw [show (-15:ℚ) = (-1)*15 by norm_num, mul_pow, mul_inv_rev, hsinv]; ring
  unfold poleTermA1 dRes
  rw [hn12, hn15, hjpow, ← frac_12_18 (j-1)]
  ring

/-- **Endpoint collapse for `A2`.**  The two `15^{−e}` terms cancel:
`poleTermA2 n j = ((-1)^{j-1}/(-(j-1)))·cRes n j·(2^{j-1}−1)/(2^{2(j-1)}·5^{j-1})`. -/
theorem poleTermA2_collapse (n j : ℕ) (hj : 2 ≤ j) :
    poleTermA2 n j
      = ((-1:ℚ)^(j-1) / (-((j:ℚ)-1))) * cRes n j
          * (((2:ℚ)^(j-1) - 1) / ((2:ℚ)^(2*(j-1)) * 5^(j-1))) := by
  have hsinv : ((-1:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) := by rw [← inv_pow]; norm_num
  have hjpow : (-1:ℚ)^j = -((-1:ℚ)^(j-1)) := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    rw [pow_succ]; ring
  have hn10 : ((-10:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) * ((10:ℚ)^(j-1))⁻¹ := by
    rw [show (-10:ℚ) = (-1)*10 by norm_num, mul_pow, mul_inv_rev, hsinv]; ring
  have hn15 : ((-15:ℚ)^(j-1))⁻¹ = (-1:ℚ)^(j-1) * ((15:ℚ)^(j-1))⁻¹ := by
    rw [show (-15:ℚ) = (-1)*15 by norm_num, mul_pow, mul_inv_rev, hsinv]; ring
  unfold poleTermA2 dRes
  rw [hn10, hn15, hjpow, ← frac_10_20 (j-1)]
  ring

/-! ### Per-term summands (collapsed form) -/

/-- The `k`-th summand of `tgt n · poleTermA1 n j` (after endpoint collapse + expanding `cRes`). -/
noncomputable def sA1term (n j k : ℕ) : ℚ :=
  (tgt n : ℚ) * ((-1:ℚ)^(j-1) / (-((j:ℚ)-1)))
    * ((((-1)^k * (Nat.choose (2*n+k) k) * (gZ n).coeff (2*n+1-j-k) : ℤ) : ℚ)
        / (30:ℚ)^(2*n+1+k))
    * (((3:ℚ)^(j-1) - 2^(j-1)) / (6:ℚ)^(2*(j-1)))

/-- The `k`-th summand of `tgt n · poleTermA2 n j`. -/
noncomputable def sA2term (n j k : ℕ) : ℚ :=
  (tgt n : ℚ) * ((-1:ℚ)^(j-1) / (-((j:ℚ)-1)))
    * ((((-1)^k * (Nat.choose (2*n+k) k) * (gZ n).coeff (2*n+1-j-k) : ℤ) : ℚ)
        / (30:ℚ)^(2*n+1+k))
    * (((2:ℚ)^(j-1) - 1) / ((2:ℚ)^(2*(j-1)) * 5^(j-1)))

/-- `tgt n · poleTermA1 n j` is the sum of its per-term summands. -/
theorem tgt_poleTermA1_sum (n j : ℕ) (hj : 2 ≤ j) :
    (tgt n : ℚ) * poleTermA1 n j = ∑ k ∈ Finset.range (2*n+2-j), sA1term n j k := by
  rw [poleTermA1_collapse n j hj]
  simp only [cRes, sA1term, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- `tgt n · poleTermA2 n j` is the sum of its per-term summands. -/
theorem tgt_poleTermA2_sum (n j : ℕ) (hj : 2 ≤ j) :
    (tgt n : ℚ) * poleTermA2 n j = ∑ k ∈ Finset.range (2*n+2-j), sA2term n j k := by
  rw [poleTermA2_collapse n j hj]
  simp only [cRes, sA2term, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Pairwise coprimality of the prime bases in `ℤ`. -/
private theorem cop23 : IsCoprime (2:ℤ) 3 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
private theorem cop25 : IsCoprime (2:ℤ) 5 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
private theorem cop35 : IsCoprime (3:ℤ) 5 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide

/-- **Per-term clearing for `A1`.**  Each summand `sA1term n j k` is an integer. -/
theorem sA1term_clear (n j k : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 2*n+1) (hk : k < 2*n+2-j) :
    ∃ w : ℤ, sA1term n j k = (w : ℚ) := by
  -- coefficient divisibilities (weighted 2,3 and sharp 5)
  have hb2 : (2:ℤ)^(6*n - 2*(2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_2w n (2*n+1-j-k)
  have hb3 : (3:ℤ)^(5*n - 2*(2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_3w n (2*n+1-j-k)
  have hb5 : (5:ℤ)^(4*n - (2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_5 n (2*n+1-j-k)
  set M' : ℤ := (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
      * ((3:ℤ)^(j-1) - 2^(j-1)) with hM'
  -- 2-adic: 2^P ∣ M'
  have h2_30g : (2:ℤ)^(6*n - 2*(2*n+1-j-k) + 1) ∣ 30 * (gZ n).coeff (2*n+1-j-k) := by
    rw [pow_succ, mul_comm 30 ((gZ n).coeff (2*n+1-j-k))]
    exact mul_dvd_mul hb2 (by norm_num)
  have h2P : (2:ℤ)^(2*n+1+k+2*(j-1)) ∣ 30 * (gZ n).coeff (2*n+1-j-k) :=
    (pow_dvd_pow 2 (by omega)).trans h2_30g
  have h2M : (2:ℤ)^(2*n+1+k+2*(j-1)) ∣ M' := by
    have h := h2P.mul_left ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((3:ℤ)^(j-1) - 2^(j-1))
        = ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
            * (30 * (gZ n).coeff (2*n+1-j-k)) by ring]
    exact h
  -- 3-adic: 3^P ∣ M'  (uses the explicit 3^n in tgt)
  have h3exp : (3:ℤ)^n * ((3:ℤ)^(5*n - 2*(2*n+1-j-k)) * 3)
      = 3^(n + (5*n - 2*(2*n+1-j-k)) + 1) := by
    rw [← mul_assoc, ← pow_add, ← pow_succ]
  have h3P : (3:ℤ)^(2*n+1+k+2*(j-1)) ∣ (3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30) := by
    have hstep : (3:ℤ)^n * ((3:ℤ)^(5*n - 2*(2*n+1-j-k)) * 3)
        ∣ (3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30) :=
      mul_dvd_mul (dvd_refl _) (mul_dvd_mul hb3 (by norm_num))
    rw [h3exp] at hstep
    exact (pow_dvd_pow 3 (by omega)).trans hstep
  have h3M : (3:ℤ)^(2*n+1+k+2*(j-1)) ∣ M' := by
    have h := h3P.mul_left ((↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((3:ℤ)^(j-1) - 2^(j-1))
        = ((↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
            * ((3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30)) by ring]
    exact h
  -- 5-adic: 5^R ∣ M'
  have h5_30g : (5:ℤ)^(4*n - (2*n+1-j-k) + 1) ∣ 30 * (gZ n).coeff (2*n+1-j-k) := by
    rw [pow_succ, mul_comm 30 ((gZ n).coeff (2*n+1-j-k))]
    exact mul_dvd_mul hb5 (by norm_num)
  have h5R : (5:ℤ)^(2*n+1+k) ∣ 30 * (gZ n).coeff (2*n+1-j-k) :=
    (pow_dvd_pow 5 (by omega)).trans h5_30g
  have h5M : (5:ℤ)^(2*n+1+k) ∣ M' := by
    have h := h5R.mul_left ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((3:ℤ)^(j-1) - 2^(j-1))
        = ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((3:ℤ)^(j-1) - 2^(j-1)))
            * (30 * (gZ n).coeff (2*n+1-j-k)) by ring]
    exact h
  -- combine the three prime powers (pairwise coprime)
  have d235 : ((2:ℤ)^(2*n+1+k+2*(j-1)) * 3^(2*n+1+k+2*(j-1)) * 5^(2*n+1+k)) ∣ M' :=
    ((cop25.pow).mul_left (cop35.pow)).mul_dvd (cop23.pow.mul_dvd h2M h3M) h5M
  -- prime-power factorisation of the natural denominator
  have hPF : (30:ℤ)^(2*n+1+k) * 6^(2*(j-1))
      = 2^(2*n+1+k+2*(j-1)) * 3^(2*n+1+k+2*(j-1)) * 5^(2*n+1+k) := by
    rw [show (30:ℤ) = 2*3*5 by norm_num, show (6:ℤ) = 2*3 by norm_num]
    simp only [mul_pow]; ring
  have hdvd_M' : ((30:ℤ)^(2*n+1+k) * 6^(2*(j-1))) ∣ M' := by rw [hPF]; exact d235
  have he_L : (↑(j-1):ℤ) ∣ (↑(lcmUpto (2*n)) : ℤ) := by
    exact_mod_cast dvd_lcmUpto (show 1 ≤ j-1 by omega) (show j-1 ≤ 2*n by omega)
  have hdvd : ((↑(j-1):ℤ) * ((30:ℤ)^(2*n+1+k) * 6^(2*(j-1)))) ∣ ((↑(lcmUpto (2*n)):ℤ) * M') :=
    mul_dvd_mul he_L hdvd_M'
  obtain ⟨q, hq⟩ := hdvd
  -- assemble the ℚ witness
  refine ⟨(-(-1:ℤ)^(j-1) * (-1)^k) * q, ?_⟩
  have hjcast : (j:ℚ) - 1 = ((j-1:ℕ):ℚ) := by rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hj1 : (0:ℚ) < (j:ℚ) - 1 := by
    have : (2:ℚ) ≤ (j:ℚ) := by exact_mod_cast hj
    linarith
  have h30 : (30:ℚ)^(2*n+1+k) ≠ 0 := by positivity
  have h6 : (6:ℚ)^(2*(j-1)) ≠ 0 := by positivity
  have hqQ : ((↑(lcmUpto (2*n)) * M' : ℤ):ℚ)
      = (((j:ℚ)-1) * ((30:ℚ)^(2*n+1+k) * 6^(2*(j-1)))) * (q:ℚ) := by
    rw [hjcast]; exact_mod_cast hq
  have expand : sA1term n j k
      = ((-1:ℚ)^(j-1) * (-1)^k) * ((↑(lcmUpto (2*n)) * M' : ℤ):ℚ)
          / (-(((j:ℚ)-1) * ((30:ℚ)^(2*n+1+k) * 6^(2*(j-1))))) := by
    simp only [sA1term, tgt, hM']
    push_cast
    field_simp
  rw [expand, hqQ]
  push_cast
  field_simp

/-- **TOOLKIT `sorry` (1/4).**  Per-term `p`-adic clearing of an `A1` pole term.

**Cancellation identity (algebraically verified).**  With `e := j − 1`, the four endpoint powers of
`poleTermA1` collapse (the two `15^{−e}` terms cancel because `dRes = (−1)^j cRes`):
`poleTermA1 n j = ((-1)^e / (-(e:ℚ))) · cRes n j · (3^e − 2^e) / 6^(2e)`,
since `(-12)^{-e} − 18^{-e}` … `= (3^e − 2^e)/6^{2e}` with `3^e − 2^e` coprime to `6`.
So the only endpoint denominator content is `6^{2e} = 2^{2e}·3^{2e}` (plus the `1/(j−1)` and the
`30^{2n+1+k}` inside `cRes`).

**Per-prime accounting (worst term `k`, set `i := 2n+1−j−k`).**  Using the *weighted* coefficient
bounds (now proved in `OSalikhovGCoeff`):
* `v_2`: need `(2n+1+k) + 2e + v_2(j−1)`; have `v_2(gZ.coeff i) ≥ 6n−2i` (`Gpoly_coeff_dvd_2w`) plus
  `v_2(tgt) = 1 + ⌊log₂ 2n⌋`.  Surplus `= k + (⌊log₂ 2n⌋ − v_2(j−1)) ≥ 0`.
* `v_3`: need `(2n+1+k) + 2e + v_3(j−1)`; have `v_3(gZ.coeff i) ≥ 5n−2i` (`Gpoly_coeff_dvd_3w`,
  for `i ≤ n`, i.e. `j+k ≥ n+1`; the `3ⁿ` in `tgt` is essential here) plus `v_3(tgt) = n+1+⌊log₃ 2n⌋`.
  Surplus `= k + (⌊log₃ 2n⌋ − v_3(j−1)) ≥ 0`.  (For `i > n`, i.e. `j ≤ n`, the simpler `4n−i` bound
  `Gpoly_coeff_dvd_3` already suffices.)
* `v_5`: need only `2n+1+k + v_5(j−1)` (no `5` in `6^{2e}`); have `v_5 ≥ 4n−i` (`Gpoly_coeff_dvd_5`)
  plus `1 + ⌊log₅ 2n⌋`.  Ample surplus.

**Crucially:** the *simple* per-prime bounds `4n−i` are INSUFFICIENT for `p = 2, 3` (the `6^{2e}`
endpoint denominator costs `2e` of each, giving a gap of order `j−1`); the WEIGHTED bounds
(`6n−2i`, `5n−2i`) are exactly what closes the accounting.  Remaining to a full Lean proof: the ℚ
cancellation rewrite, `v_p(lcmUpto) = ⌊log_p⌋` / `(j−1) ∣ lcmUpto`, and assembling pairwise-coprime
`2^·3^·5^` divisibilities into one ℤ witness.  Per-term truth verified `n ≤ 8` in
`experiments/osalikhov_a2_perterm_check.clj`. -/
theorem poleTermA1_clear (n j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 2 * n + 1) :
    ∃ z : ℤ, (tgt n : ℚ) * poleTermA1 n j = (z : ℚ) := by
  classical
  rw [tgt_poleTermA1_sum n j hj]
  have hterm : ∀ k ∈ Finset.range (2*n+2-j), ∃ w : ℤ, sA1term n j k = (w : ℚ) := by
    intro k hk; rw [Finset.mem_range] at hk; exact sA1term_clear n j k hj hj' hk
  let zf : ℕ → ℤ := fun k => if h : k ∈ Finset.range (2*n+2-j) then (hterm k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (2*n+2-j), zf k, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [zf, dif_pos hk]
  exact (hterm k hk).choose_spec

/-- **TOOLKIT `sorry` (2/4).**  Per-term `p`-adic clearing of an `A2` pole term (endpoints `0,5`).

Same structure as `poleTermA1_clear`.  Here the endpoints are `−10,−15,20,15`; the two `15^{−e}`
terms again cancel, giving `poleTermA1`-style collapse
`poleTermA2 n j = ((-1)^e/(-(e:ℚ)))·cRes n j·(10^{-e} − 20^{-e})`,
and `10^{-e} − 20^{-e} = (2^e − 1)/(2^{2e}·5^e)` (with `2^e−1` odd).  So the endpoint denominator
content is `2^{2e}·5^e` (no `3` this time).  Per-prime:
* `v_2`: identical to A1 — covered by `Gpoly_coeff_dvd_2w` (`6n−2i`), surplus `k + (⌊log₂ 2n⌋ −
  v_2(j−1))`.
* `v_5`: need `(2n+1+k) + e + v_5(j−1)`; have `v_5 ≥ 4n−i = 2n+j+k−1` (`Gpoly_coeff_dvd_5`) plus
  `1 + ⌊log₅ 2n⌋`.  Since `e = j−1`, the `j`-content of the coefficient exactly pays the `5^e`, and
  surplus `= ⌊log₅ 2n⌋ − v_5(j−1) ≥ 0`.
* `v_3`: free (the `3ⁿ·30·lcm` content dwarfs the bare `30^{2n+1+k}`).
Same residual Lean infrastructure as `poleTermA1_clear`. -/
theorem sA2term_clear (n j k : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 2*n+1) (hk : k < 2*n+2-j) :
    ∃ w : ℤ, sA2term n j k = (w : ℚ) := by
  have hb2 : (2:ℤ)^(6*n - 2*(2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_2w n (2*n+1-j-k)
  have hb3 : (3:ℤ)^(5*n - 2*(2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_3w n (2*n+1-j-k)
  have hb5 : (5:ℤ)^(4*n - (2*n+1-j-k)) ∣ (gZ n).coeff (2*n+1-j-k) := by
    rw [gZ_eq_Gpoly]; exact OSalikhovGCoeff.Gpoly_coeff_dvd_5 n (2*n+1-j-k)
  set M' : ℤ := (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
      * ((2:ℤ)^(j-1) - 1) with hM'
  -- 2-adic: 2^P ∣ M'
  have h2_30g : (2:ℤ)^(6*n - 2*(2*n+1-j-k) + 1) ∣ 30 * (gZ n).coeff (2*n+1-j-k) := by
    rw [pow_succ, mul_comm 30 ((gZ n).coeff (2*n+1-j-k))]
    exact mul_dvd_mul hb2 (by norm_num)
  have h2P : (2:ℤ)^(2*n+1+k+2*(j-1)) ∣ 30 * (gZ n).coeff (2*n+1-j-k) :=
    (pow_dvd_pow 2 (by omega)).trans h2_30g
  have h2M : (2:ℤ)^(2*n+1+k+2*(j-1)) ∣ M' := by
    have h := h2P.mul_left ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((2:ℤ)^(j-1) - 1)
        = ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
            * (30 * (gZ n).coeff (2*n+1-j-k)) by ring]
    exact h
  -- 3-adic: 3^Q ∣ M' (Q = 2n+1+k)
  have h3exp : (3:ℤ)^n * ((3:ℤ)^(5*n - 2*(2*n+1-j-k)) * 3)
      = 3^(n + (5*n - 2*(2*n+1-j-k)) + 1) := by
    rw [← mul_assoc, ← pow_add, ← pow_succ]
  have h3Q : (3:ℤ)^(2*n+1+k) ∣ (3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30) := by
    have hstep : (3:ℤ)^n * ((3:ℤ)^(5*n - 2*(2*n+1-j-k)) * 3)
        ∣ (3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30) :=
      mul_dvd_mul (dvd_refl _) (mul_dvd_mul hb3 (by norm_num))
    rw [h3exp] at hstep
    exact (pow_dvd_pow 3 (by omega)).trans hstep
  have h3M : (3:ℤ)^(2*n+1+k) ∣ M' := by
    have h := h3Q.mul_left ((↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((2:ℤ)^(j-1) - 1)
        = ((↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
            * ((3:ℤ)^n * ((gZ n).coeff (2*n+1-j-k) * 30)) by ring]
    exact h
  -- 5-adic: 5^R ∣ M' (R = 2n+1+k+(j-1))
  have h5_30g : (5:ℤ)^(4*n - (2*n+1-j-k) + 1) ∣ 30 * (gZ n).coeff (2*n+1-j-k) := by
    rw [pow_succ, mul_comm 30 ((gZ n).coeff (2*n+1-j-k))]
    exact mul_dvd_mul hb5 (by norm_num)
  have h5R : (5:ℤ)^(2*n+1+k+(j-1)) ∣ 30 * (gZ n).coeff (2*n+1-j-k) :=
    (pow_dvd_pow 5 (by omega)).trans h5_30g
  have h5M : (5:ℤ)^(2*n+1+k+(j-1)) ∣ M' := by
    have h := h5R.mul_left ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
    rw [hM', show (3:ℤ)^n * 30 * (↑(Nat.choose (2*n+k) k)) * (gZ n).coeff (2*n+1-j-k)
          * ((2:ℤ)^(j-1) - 1)
        = ((3:ℤ)^n * (↑(Nat.choose (2*n+k) k)) * ((2:ℤ)^(j-1) - 1))
            * (30 * (gZ n).coeff (2*n+1-j-k)) by ring]
    exact h
  have d235 : ((2:ℤ)^(2*n+1+k+2*(j-1)) * 3^(2*n+1+k) * 5^(2*n+1+k+(j-1))) ∣ M' :=
    ((cop25.pow).mul_left (cop35.pow)).mul_dvd (cop23.pow.mul_dvd h2M h3M) h5M
  have hPF : (30:ℤ)^(2*n+1+k) * ((2:ℤ)^(2*(j-1)) * 5^(j-1))
      = 2^(2*n+1+k+2*(j-1)) * 3^(2*n+1+k) * 5^(2*n+1+k+(j-1)) := by
    rw [show (30:ℤ) = 2*3*5 by norm_num]
    simp only [mul_pow]; ring
  have hdvd_M' : ((30:ℤ)^(2*n+1+k) * ((2:ℤ)^(2*(j-1)) * 5^(j-1))) ∣ M' := by rw [hPF]; exact d235
  have he_L : (↑(j-1):ℤ) ∣ (↑(lcmUpto (2*n)) : ℤ) := by
    exact_mod_cast dvd_lcmUpto (show 1 ≤ j-1 by omega) (show j-1 ≤ 2*n by omega)
  have hdvd : ((↑(j-1):ℤ) * ((30:ℤ)^(2*n+1+k) * ((2:ℤ)^(2*(j-1)) * 5^(j-1))))
      ∣ ((↑(lcmUpto (2*n)):ℤ) * M') := mul_dvd_mul he_L hdvd_M'
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨(-(-1:ℤ)^(j-1) * (-1)^k) * q, ?_⟩
  have hjcast : (j:ℚ) - 1 = ((j-1:ℕ):ℚ) := by rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hj1 : (0:ℚ) < (j:ℚ) - 1 := by
    have : (2:ℚ) ≤ (j:ℚ) := by exact_mod_cast hj
    linarith
  have h30 : (30:ℚ)^(2*n+1+k) ≠ 0 := by positivity
  have hden2 : (2:ℚ)^(2*(j-1)) * 5^(j-1) ≠ 0 := by positivity
  have hqQ : ((↑(lcmUpto (2*n)) * M' : ℤ):ℚ)
      = (((j:ℚ)-1) * ((30:ℚ)^(2*n+1+k) * ((2:ℚ)^(2*(j-1)) * 5^(j-1)))) * (q:ℚ) := by
    rw [hjcast]; exact_mod_cast hq
  have expand : sA2term n j k
      = ((-1:ℚ)^(j-1) * (-1)^k) * ((↑(lcmUpto (2*n)) * M' : ℤ):ℚ)
          / (-(((j:ℚ)-1) * ((30:ℚ)^(2*n+1+k) * ((2:ℚ)^(2*(j-1)) * 5^(j-1))))) := by
    simp only [sA2term, tgt, hM']
    push_cast
    field_simp
  rw [expand, hqQ]
  push_cast
  field_simp

theorem poleTermA2_clear (n j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 2 * n + 1) :
    ∃ z : ℤ, (tgt n : ℚ) * poleTermA2 n j = (z : ℚ) := by
  classical
  rw [tgt_poleTermA2_sum n j hj]
  have hterm : ∀ k ∈ Finset.range (2*n+2-j), ∃ w : ℤ, sA2term n j k = (w : ℚ) := by
    intro k hk; rw [Finset.mem_range] at hk; exact sA2term_clear n j k hj hj' hk
  let zf : ℕ → ℤ := fun k => if h : k ∈ Finset.range (2*n+2-j) then (hterm k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (2*n+2-j), zf k, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [zf, dif_pos hk]
  exact (hterm k hk).choose_spec

/-- The `A1` pole sum clears (assembled from the per-term toolkit lemma). -/
theorem A1poleSum_clear (n : ℕ) : ∃ z : ℤ, (tgt n : ℚ) * A1poleSum n = (z : ℚ) := by
  classical
  have hterm : ∀ j ∈ Finset.Icc 2 (2 * n + 1), ∃ z : ℤ,
      (tgt n : ℚ) * poleTermA1 n j = (z : ℚ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact poleTermA1_clear n j hj.1 hj.2
  let zf : ℕ → ℤ := fun j => if h : j ∈ Finset.Icc 2 (2 * n + 1) then (hterm j h).choose else 0
  refine ⟨∑ j ∈ Finset.Icc 2 (2 * n + 1), zf j, ?_⟩
  simp only [A1poleSum]
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [zf, dif_pos hj]
  exact (hterm j hj).choose_spec

/-- The `A2` pole sum clears. -/
theorem A2poleSum_clear (n : ℕ) : ∃ z : ℤ, (tgt n : ℚ) * A2poleSum n = (z : ℚ) := by
  classical
  have hterm : ∀ j ∈ Finset.Icc 2 (2 * n + 1), ∃ z : ℤ,
      (tgt n : ℚ) * poleTermA2 n j = (z : ℚ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact poleTermA2_clear n j hj.1 hj.2
  let zf : ℕ → ℤ := fun j => if h : j ∈ Finset.Icc 2 (2 * n + 1) then (hterm j h).choose else 0
  refine ⟨∑ j ∈ Finset.Icc 2 (2 * n + 1), zf j, ?_⟩
  simp only [A2poleSum]
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [zf, dif_pos hj]
  exact (hterm j hj).choose_spec

/-- `tgt n · A1expl n ∈ ℤ`. -/
theorem A1expl_clear (n : ℕ) : ∃ z : ℤ, (tgt n : ℚ) * A1expl n = (z : ℚ) := by
  obtain ⟨z1, h1⟩ := polyIntE_clear n 3
  obtain ⟨z2, h2⟩ := A1poleSum_clear n
  exact ⟨z1 + z2, by simp only [A1expl]; rw [mul_add, h1, h2]; push_cast; ring⟩

/-- `tgt n · A2expl n ∈ ℤ`. -/
theorem A2expl_clear (n : ℕ) : ∃ z : ℤ, (tgt n : ℚ) * A2expl n = (z : ℚ) := by
  obtain ⟨z1, h1⟩ := polyIntE_clear n 5
  obtain ⟨z2, h2⟩ := A2poleSum_clear n
  exact ⟨z1 + z2, by simp only [A2expl]; rw [mul_add, h1, h2]; push_cast; ring⟩

/-- `tgt n · (A1expl n + A2expl n) ∈ ℤ`. -/
theorem sum_expl_clear (n : ℕ) : ∃ z : ℤ, (tgt n : ℚ) * (A1expl n + A2expl n) = (z : ℚ) := by
  obtain ⟨z1, h1⟩ := A1expl_clear n
  obtain ⟨z2, h2⟩ := A2expl_clear n
  exact ⟨z1 + z2, by rw [mul_add, h1, h2]; push_cast; ring⟩

/-- **Denominator bound for `A1expl`.**  `(A1expl n).den ∣ 3ⁿ·30·lcm(1..2n)`. -/
theorem A1expl_den_dvd (n : ℕ) : (A1expl n).den ∣ tgt n := den_dvd_of_clear (A1expl_clear n)

/-- **Denominator bound for `A2expl`.**  `(A2expl n).den ∣ 3ⁿ·30·lcm(1..2n)`. -/
theorem A2expl_den_dvd (n : ℕ) : (A2expl n).den ∣ tgt n := den_dvd_of_clear (A2expl_clear n)

/-- **Denominator bound for `A1expl + A2expl`.** -/
theorem sum_expl_den_dvd (n : ℕ) : (A1expl n + A2expl n).den ∣ tgt n :=
  den_dvd_of_clear (sum_expl_clear n)

/-! ## Step 2½ — the bridge to the PFI closed form (`A1explicit`/`A2explicit`)

The explicit ℚ forms `A1expl`/`A2expl` of this file cast to the ℝ closed forms
`OSalikhovPFI.A1explicit`/`A2explicit`.  Wiring these casts to `OSalikhovPFI.A1seq_eq`/`A2seq_eq`
(proved modulo PFI's two deep `sorry`s) discharges `A1expl_eq`/`A2expl_eq`. -/

/-- The two residue generators agree (`C 15` numerals vs bare `15`). -/
theorem gZ_eq_gNum (n : ℕ) : gZ n = OSalikhovPFI.gNum n := by
  unfold gZ OSalikhovPFI.gNum
  rw [map_ofNat C 15, map_ofNat C 12, map_ofNat C 18, map_ofNat C 10, map_ofNat C 20]

/-- The residue `c_j` of this file equals `OSalikhovPFI.cResQ`. -/
theorem cRes_eq_cResQ (n j : ℕ) : cRes n j = OSalikhovPFI.cResQ n j := by
  unfold cRes OSalikhovPFI.cResQ
  apply Finset.sum_congr rfl
  intro k _
  rw [gZ_eq_gNum]
  push_cast
  ring

/-- The residue `d_j` of this file equals `OSalikhovPFI.dResQ`. -/
theorem dRes_eq_dResQ (n j : ℕ) : dRes n j = OSalikhovPFI.dResQ n j := by
  unfold dRes OSalikhovPFI.dResQ
  rw [cRes_eq_cResQ]

/-- `numZ` agrees with `OSalikhovPFI.numZ` (numeral vs `C`). -/
theorem numZ_eq (n : ℕ) : numZ n = OSalikhovPFI.numZ n := by
  have h9 : (C (9 : ℤ) : ℤ[X]) = 9 := map_ofNat C 9
  have h25 : (C (25 : ℤ) : ℤ[X]) = 25 := map_ofNat C 25
  unfold numZ OSalikhovPFI.numZ
  rw [h9, h25]

/-- `denZ` agrees with `OSalikhovPFI.denZ`. -/
theorem denZ_eq (n : ℕ) : denZ n = OSalikhovPFI.denZ n := by
  have h225 : (C (225 : ℤ) : ℤ[X]) = 225 := map_ofNat C 225
  unfold denZ OSalikhovPFI.denZ
  rw [h225]

/-- `polyPartZ` agrees with `OSalikhovPFI.polyPartZ`. -/
theorem polyPartZ_eq (n : ℕ) : polyPartZ n = OSalikhovPFI.polyPartZ n := by
  unfold polyPartZ OSalikhovPFI.polyPartZ
  rw [numZ_eq, denZ_eq]

/-- `denZ n` is monic. -/
theorem denZ_monic (n : ℕ) : (denZ n).Monic := by
  unfold denZ
  exact (monic_X_pow_sub_C (225 : ℤ) (by norm_num)).pow _

/-- `numZ n` is monic. -/
theorem numZ_monic (n : ℕ) : (numZ n).Monic := by
  unfold numZ
  exact (((monic_X_pow (2 * n)).mul ((monic_X_pow_sub_C (9 : ℤ) (by norm_num)).pow n)).mul
    ((monic_X_pow_sub_C (25 : ℤ) (by norm_num)).pow n))

/-- `natDegree (numZ n) = 6n`. -/
theorem numZ_natDegree (n : ℕ) : (numZ n).natDegree = 6 * n := by
  have m1 : (X ^ (2 * n) : ℤ[X]).Monic := monic_X_pow _
  have m2 : ((X ^ 2 - C 9) ^ n : ℤ[X]).Monic := (monic_X_pow_sub_C (9 : ℤ) (by norm_num)).pow _
  have m3 : ((X ^ 2 - C 25) ^ n : ℤ[X]).Monic := (monic_X_pow_sub_C (25 : ℤ) (by norm_num)).pow _
  unfold numZ
  rw [(m1.mul m2).natDegree_mul m3, m1.natDegree_mul m2,
      (monic_X_pow_sub_C (9 : ℤ) (by norm_num)).natDegree_pow n,
      (monic_X_pow_sub_C (25 : ℤ) (by norm_num)).natDegree_pow n]
  simp only [Polynomial.natDegree_X_pow, natDegree_X_pow_sub_C]
  ring

/-- `natDegree (denZ n) = 4n+2`. -/
theorem denZ_natDegree (n : ℕ) : (denZ n).natDegree = 4 * n + 2 := by
  unfold denZ
  rw [(monic_X_pow_sub_C (225 : ℤ) (by norm_num)).natDegree_pow (2 * n + 1), natDegree_X_pow_sub_C]
  ring

/-- `natDegree (polyPartZ n) = 6n − (4n+2)`. -/
theorem polyPartZ_natDegree (n : ℕ) : (polyPartZ n).natDegree = 6 * n - (4 * n + 2) := by
  unfold polyPartZ
  rw [natDegree_divByMonic _ (denZ_monic n), numZ_natDegree, denZ_natDegree]

/-- At `n = 0` the polynomial part vanishes (degree `numZ 0 = 0 < 2 = degree denZ 0`). -/
theorem polyPartZ_zero : polyPartZ 0 = 0 := by
  unfold polyPartZ
  refine (Polynomial.divByMonic_eq_zero_iff (denZ_monic 0)).2 ?_
  rw [degree_eq_natDegree (numZ_monic 0).ne_zero, degree_eq_natDegree (denZ_monic 0).ne_zero,
      numZ_natDegree, denZ_natDegree]
  exact_mod_cast (show 6 * 0 < 4 * 0 + 2 by norm_num)

/-- The support of the polynomial part lies in `range (2n)` (its degree is `2n−2`). -/
theorem polyPartZ_supp (n : ℕ) : (polyPartZ n).support ⊆ Finset.range (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [polyPartZ_zero]; simp
  · apply Polynomial.supp_subset_range
    rw [polyPartZ_natDegree]
    omega

/-- **Polynomial-part integral as an explicit coefficient sum.**  For any `p` whose support lies in
`range N`, `∫₀ᵉ aeval x p = Σ_{k<N} (p.coeff k)·eᵏ⁺¹/(k+1)`. -/
theorem integral_aeval_range (p : ℤ[X]) (N : ℕ) (e : ℝ)
    (hsupp : p.support ⊆ Finset.range N) :
    (∫ x in (0:ℝ)..e, Polynomial.aeval x p)
      = ∑ k ∈ Finset.range N, (p.coeff k : ℝ) * e ^ (k + 1) / ((k : ℝ) + 1) := by
  have haeval : ∀ x : ℝ, Polynomial.aeval x p = ∑ k ∈ p.support, (p.coeff k : ℝ) * x ^ k := by
    intro x
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro k _
    simp [algebraMap_int_eq]
  calc (∫ x in (0:ℝ)..e, Polynomial.aeval x p)
      = ∫ x in (0:ℝ)..e, ∑ k ∈ p.support, (p.coeff k : ℝ) * x ^ k :=
        intervalIntegral.integral_congr (fun x _ => haeval x)
    _ = ∑ k ∈ p.support, ∫ x in (0:ℝ)..e, (p.coeff k : ℝ) * x ^ k :=
        intervalIntegral.integral_finset_sum (fun k _ =>
          (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 e)
    _ = ∑ k ∈ p.support, (p.coeff k : ℝ) * e ^ (k + 1) / ((k : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k),
            sub_zero]
        ring
    _ = ∑ k ∈ Finset.range N, (p.coeff k : ℝ) * e ^ (k + 1) / ((k : ℝ) + 1) :=
        Finset.sum_subset hsupp (fun k _ hk => by
          rw [Polynomial.notMem_support_iff.mp hk]; simp)

/-- **Per-term cast for `A1`.**  `↑(poleTermA1 n j) = cResR·(…)/(1−j) + dResR·(…)/(1−j)`. -/
theorem A1poleTerm_cast (n j : ℕ) (hj : 2 ≤ j) :
    ((poleTermA1 n j : ℚ) : ℝ)
      = OSalikhovPFI.cResR n j *
          (((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)))
        + OSalikhovPFI.dResR n j *
          (((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
  have hcast : (1 - (j : ℤ)) = -((j - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
  have e12 : (-12 : ℝ) ^ (1 - (j : ℤ)) = ((-12 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e15 : (-15 : ℝ) ^ (1 - (j : ℤ)) = ((-15 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e18 : (18 : ℝ) ^ (1 - (j : ℤ)) = ((18 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e15' : (15 : ℝ) ^ (1 - (j : ℤ)) = ((15 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have hden : (1 : ℝ) - ((j : ℤ) : ℝ) = -((j : ℝ) - 1) := by push_cast; ring
  have hc : ((cRes n j : ℚ) : ℝ) = OSalikhovPFI.cResR n j := by
    unfold OSalikhovPFI.cResR; rw [cRes_eq_cResQ]
  have hd : ((dRes n j : ℚ) : ℝ) = OSalikhovPFI.dResR n j := by
    unfold OSalikhovPFI.dResR; rw [dRes_eq_dResQ]
  rw [e12, e15, e18, e15', hden]
  unfold poleTermA1
  push_cast
  rw [hc, hd]
  ring

/-- **Per-term cast for `A2`** (endpoints `−10, 20`). -/
theorem A2poleTerm_cast (n j : ℕ) (hj : 2 ≤ j) :
    ((poleTermA2 n j : ℚ) : ℝ)
      = OSalikhovPFI.cResR n j *
          (((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ)))
        + OSalikhovPFI.dResR n j *
          (((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
  have hcast : (1 - (j : ℤ)) = -((j - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
  have e10 : (-10 : ℝ) ^ (1 - (j : ℤ)) = ((-10 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e15 : (-15 : ℝ) ^ (1 - (j : ℤ)) = ((-15 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e20 : (20 : ℝ) ^ (1 - (j : ℤ)) = ((20 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have e15' : (15 : ℝ) ^ (1 - (j : ℤ)) = ((15 : ℝ) ^ (j - 1))⁻¹ := by
    rw [hcast, zpow_neg, zpow_natCast]
  have hden : (1 : ℝ) - ((j : ℤ) : ℝ) = -((j : ℝ) - 1) := by push_cast; ring
  have hc : ((cRes n j : ℚ) : ℝ) = OSalikhovPFI.cResR n j := by
    unfold OSalikhovPFI.cResR; rw [cRes_eq_cResQ]
  have hd : ((dRes n j : ℚ) : ℝ) = OSalikhovPFI.dResR n j := by
    unfold OSalikhovPFI.dResR; rw [dRes_eq_dResQ]
  rw [e10, e15, e20, e15', hden]
  unfold poleTermA2
  push_cast
  rw [hc, hd]
  ring

/-- **Bridge for `A1`.**  `↑(A1expl n) = OSalikhovPFI.A1explicit n`. -/
theorem A1expl_cast_eq (n : ℕ) : ((A1expl n : ℚ) : ℝ) = OSalikhovPFI.A1explicit n := by
  have hpoly : ((polyIntE n 3 : ℚ) : ℝ)
      = ∫ x in (0:ℝ)..3, Polynomial.aeval x (OSalikhovPFI.polyPartZ n) := by
    simp only [polyIntE]
    rw [show OSalikhovPFI.polyPartZ n = polyPartZ n from (polyPartZ_eq n).symm,
        integral_aeval_range (polyPartZ n) (2 * n) (3 : ℝ) (polyPartZ_supp n)]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpole : ((A1poleSum n : ℚ) : ℝ)
      = (∑ j ∈ Finset.Icc 2 (2 * n + 1), OSalikhovPFI.cResR n j *
            (((-12 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))))
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1), OSalikhovPFI.dResR n j *
            (((18 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    simp only [A1poleSum]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact A1poleTerm_cast n j hj.1
  simp only [A1expl, OSalikhovPFI.A1explicit]
  rw [Rat.cast_add, hpoly, hpole]
  ring

/-- **Bridge for `A2`.**  `↑(A2expl n) = OSalikhovPFI.A2explicit n`. -/
theorem A2expl_cast_eq (n : ℕ) : ((A2expl n : ℚ) : ℝ) = OSalikhovPFI.A2explicit n := by
  have hpoly : ((polyIntE n 5 : ℚ) : ℝ)
      = ∫ x in (0:ℝ)..5, Polynomial.aeval x (OSalikhovPFI.polyPartZ n) := by
    simp only [polyIntE]
    rw [show OSalikhovPFI.polyPartZ n = polyPartZ n from (polyPartZ_eq n).symm,
        integral_aeval_range (polyPartZ n) (2 * n) (5 : ℝ) (polyPartZ_supp n)]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpole : ((A2poleSum n : ℚ) : ℝ)
      = (∑ j ∈ Finset.Icc 2 (2 * n + 1), OSalikhovPFI.cResR n j *
            (((-10 : ℝ) ^ (1 - (j : ℤ)) - (-15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))))
        + ∑ j ∈ Finset.Icc 2 (2 * n + 1), OSalikhovPFI.dResR n j *
            (((20 : ℝ) ^ (1 - (j : ℤ)) - (15 : ℝ) ^ (1 - (j : ℤ))) / (1 - (j : ℤ))) := by
    simp only [A2poleSum]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact A2poleTerm_cast n j hj.1
  simp only [A2expl, OSalikhovPFI.A2explicit]
  rw [Rat.cast_add, hpoly, hpole]
  ring

/-! ## Step 3 — the reduction of `hdvd`

The two explicit-form identities are the deep partial-fraction/recurrence step (the second solution
of the order-3 recurrence equals the closed form); verified numerically in
`experiments/osalikhov_pf_cancellation.clj`.  They are the only mathematical content left. -/

/-- **DEEP `sorry` (3/4).**  `A1seqQ n = A1expl n`: the recurrence-defined rational part equals the
partial-fraction closed form.  (Numerically verified `n ≤ 4` in `osalikhov_pf_cancellation.clj`.) -/
theorem A1expl_eq (n : ℕ) : A1seqQ n = A1expl n := by
  have h : (A1seqQ n : ℝ) = ((A1expl n : ℚ) : ℝ) := by
    rw [A1seqQ_cast, A1expl_cast_eq n]
    exact OSalikhovPFI.A1seq_eq n
  exact_mod_cast h

/-- **DEEP `sorry` (4/4).**  `A2seqQ n = A2expl n`. -/
theorem A2expl_eq (n : ℕ) : A2seqQ n = A2expl n := by
  have h : (A2seqQ n : ℝ) = ((A2expl n : ℚ) : ℝ) := by
    rw [A2seqQ_cast, A2expl_cast_eq n]
    exact OSalikhovPFI.A2seq_eq n
  exact_mod_cast h

/-- **`hdvd` for the explicit form.**  `DenIntN n ∣ 3ⁿ·30·lcm(1..2n)`, modulo `A1expl_eq`/`A2expl_eq`
and the per-term toolkit. -/
theorem hdvd_explicit (n : ℕ) :
    DenIntN n ∣ 3 ^ n * 30 * lcmUpto (2 * n) := by
  have hA2 : (A2seqQ n).den ∣ tgt n := by rw [A2expl_eq]; exact A2expl_den_dvd n
  have hS : (A1seqQ n + A2seqQ n).den ∣ tgt n := by
    rw [A1expl_eq n, A2expl_eq n]; exact sum_expl_den_dvd n
  exact Nat.lcm_dvd hS hA2

/-- **Collatz `PowGap` (no Baker), modulo the explicit-form identities.**  Feeding `hdvd_explicit`
into the sorry-free capstone `CollatzPowGapOfHdvd.collatz_powGap_of_hdvd`.  The only remaining
`sorry`s are `poleTermA1_clear`, `poleTermA2_clear` (toolkit) and `A1expl_eq`, `A2expl_eq` (deep). -/
theorem collatz_powGap_unconditional_modulo_eq : CollatzDescentDichotomy.PowGap :=
  CollatzPowGapOfHdvd.collatz_powGap_of_hdvd hdvd_explicit

-- Axiom audit.  The polynomial-part clearing and the den-helper are axiom-clean
-- (`propext, Classical.choice, Quot.sound`); the denominator bounds and capstone additionally
-- carry `sorryAx` only via the four documented `sorry`s (pole-term toolkit + explicit-form identity).
#print axioms polyIntE_clear
#print axioms den_dvd_of_clear
#print axioms poleTermA1_clear
#print axioms poleTermA2_clear
#print axioms A1expl_eq
#print axioms A2expl_eq
#print axioms hdvd_explicit
#print axioms collatz_powGap_unconditional_modulo_eq

end OSalikhovHdvdExplicit
