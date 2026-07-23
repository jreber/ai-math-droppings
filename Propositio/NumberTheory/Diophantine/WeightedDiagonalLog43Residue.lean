import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2TwoAdic
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Decomp
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Measure
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Integrality
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic

/-!
# The explicit residue closed form for `Pₙ = JP n` and the denominator miracle

The single-log decomposition `Jₙ = Pₙ + α₁(n)·log(4/3)` (`J_decomp`) has rational part `Pₙ = JP n`.
The effective irrationality measure of `log(4/3)` (`WeightedDiagonalLog43MeasureFinal`) needs the
**denominator bound** `den(Pₙ) ∣ lcm(1..n)`.  The prior route isolated this as the opaque per-step
`hstep`.  Here we give the **explicit closed form** the frontier called for, and *prove the
denominator miracle outright*.

## The closed form (partial fractions of the two-pole integrand)

`Jₙ = ∫₀¹ xⁿ(1−x)ⁿ/[(1+x)(2+x)]ⁿ⁺¹ dx`.  Partial fractions in `x` give residues `a_j` (pole `x=−1`)
and `b_j` (pole `x=−2`), and term-by-term integration yields

  `Jₙ = a₁·log 2 + b₁·log(3/2) + Σ_{i=1}^n [a_{i+1}(1−2^{−i}) + b_{i+1}(2^{−i}−3^{−i})]/i`,

with `a₁ = α₁(n) = −b₁` (residue-sum-zero ⟹ a single `log(4/3)`).  Coefficient extraction gives the
explicit integer residues (`serPos`/`serNeg` are the degree-`n` truncations of `(1∓X)^{-(n+1)}`):

  `aRes n j = [X^{n+1−j}]((X−1)ⁿ(2−X)ⁿ·serNeg n)`,
  `bRes n j = (−1)ⁿ⁺¹·[X^{n+1−j}]((X−2)ⁿ(3−X)ⁿ·serPos n)`.

## The denominator miracle (PROVED here)

`2^i ∣ aRes n (i+1)`, `2^i ∣ bRes n (i+1)`, `3^i ∣ bRes n (i+1)` — so each bracket
`a_{i+1}(1−2^{−i}) + b_{i+1}(2^{−i}−3^{−i})` is an **integer**, and the `1/i` is cleared by
`lcm(1..n)`.  The 2-adic facts reuse the `log 2` construction's `two_pow_dvd_coeff`; the 3-adic fact
uses the general-constant clone `const_pow_dvd_const_sub_X_pow_coeff` proved below.

This file proves everything **unconditionally** down to the single explicit sequence identity
`JP n = Pexpl n` (`hPexpl`, verified numerically `n ≤ 21`): the recurrence-defined `JP` equals the
closed form.  That identity (the second solution satisfies the same three-term recurrence) is the
one remaining input, replacing the opaque `hstep` with a concrete Zeilberger-style equality.
-/

namespace WeightedDiagonalLog43

open Polynomial

/-! ### The general-constant `p`-adic coefficient divisibility (clone of the `log 2` 2-adic lemma) -/

/-- **Every coefficient of `(c − X)ⁿ` of index `j` is divisible by `c^(n−j)`.**
The constant-`c` generalisation of `DiagonalIntegralLog2.two_pow_dvd_two_sub_X_pow_coeff`; the proof
is identical (induction via `(C c − X)ⁿ⁺¹ = C c·p − X·p`), the only `c`-specific step being
`c·cⁿ = cⁿ⁺¹`. -/
theorem const_pow_dvd_const_sub_X_pow_coeff (c : ℤ) (n j : ℕ) :
    c ^ (n - j) ∣ ((C c - X : ℤ[X]) ^ n).coeff j := by
  induction n generalizing j with
  | zero => rcases j with _ | j <;> simp
  | succ n ih =>
    set p : ℤ[X] := (C c - X : ℤ[X]) ^ n with hp
    have hrec : ((C c - X : ℤ[X]) ^ (n + 1)).coeff j = c * p.coeff j - (X * p).coeff j := by
      rw [pow_succ, mul_comm ((C c - X : ℤ[X]) ^ n) (C c - X), ← hp, sub_mul,
        Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [hrec]
    rcases j with _ | j
    · rw [Polynomial.coeff_X_mul_zero, sub_zero, Nat.sub_zero]
      have h1 : c ^ (n - 0) ∣ p.coeff 0 := by simpa using ih 0
      calc c ^ (n + 1) = c * c ^ n := by ring
        _ ∣ c * p.coeff 0 := by rw [Nat.sub_zero] at h1; exact mul_dvd_mul_left c h1
    · rw [Polynomial.coeff_X_mul]
      have hA : c ^ (n + 1 - (j + 1)) ∣ c * p.coeff (j + 1) := by
        by_cases hjn : j + 1 ≤ n
        · have he : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
          rw [he, pow_succ, mul_comm]
          exact mul_dvd_mul (dvd_refl c) (ih (j + 1))
        · have : n + 1 - (j + 1) = 0 := by omega
          rw [this, pow_zero]; exact one_dvd _
      have hB : c ^ (n + 1 - (j + 1)) ∣ p.coeff j := by
        have he : n + 1 - (j + 1) = n - j := by omega
        rw [he]; exact ih j
      exact dvd_sub hA hB

/-- `3^(n−w) ∣ ((3 − X)ⁿ).coeff w`. -/
theorem three_pow_dvd_three_sub_X_pow_coeff (n w : ℕ) :
    (3 : ℤ) ^ (n - w) ∣ ((3 - X : ℤ[X]) ^ n).coeff w := by
  have h := const_pow_dvd_const_sub_X_pow_coeff 3 n w
  have hC : (C (3 : ℤ) - X : ℤ[X]) = (3 - X : ℤ[X]) := by
    rw [map_ofNat]
  rwa [hC] at h

/-- `2^(n−v) ∣ ((X − 2)ⁿ).coeff v` (from the `2 − X` version up to the unit `(−1)ⁿ`). -/
theorem two_pow_dvd_X_sub_two_pow_coeff (n v : ℕ) :
    (2 : ℤ) ^ (n - v) ∣ ((X - 2 : ℤ[X]) ^ n).coeff v := by
  have h := DiagonalIntegralLog2.two_pow_dvd_two_sub_X_pow_coeff n v
  have h1 : (X - 2 : ℤ[X]) = C ((-1 : ℤ)) * (2 - X) := by
    rw [Polynomial.C_neg, Polynomial.C_1]; ring
  have heq : (X - 2 : ℤ[X]) ^ n = C ((-1 : ℤ) ^ n) * (2 - X) ^ n := by
    rw [h1, mul_pow, ← map_pow]
  rw [heq, Polynomial.coeff_C_mul]
  exact Dvd.dvd.mul_left h _

/-! ### The truncated generating polynomials and the multiplicative `p`-adic helpers -/

/-- `serPos n = ∑_{s=0}^n C(n+s,n)·Xˢ` — the degree-`n` truncation of `(1−X)^{-(n+1)}`. -/
noncomputable def serPos (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (n + 1), (C ((n + s).choose n : ℤ)) * X ^ s

/-- `serNeg n = ∑_{s=0}^n (−1)ˢ·C(n+s,n)·Xˢ` — the degree-`n` truncation of `(1+X)^{-(n+1)}`. -/
noncomputable def serNeg (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (n + 1), (C (((-1) ^ s * (n + s).choose n : ℤ))) * X ^ s

/-- **2-adic multiplicative helper.**  `2^(n−m) ∣ coeff m((X−1)ⁿ(2−X)ⁿ·H)` for any `H`.
Each antidiagonal split `(u,v)`, `u+v=m`, has `u ≤ m`, so `2^(n−m) ∣ 2^(n−u) ∣ coeff u`. -/
theorem two_pow_dvd_mul_coeff (n m : ℕ) (H : ℤ[X]) :
    (2 : ℤ) ^ (n - m) ∣ ((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n * H).coeff m := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
  have hpow : (2 : ℤ) ^ (n - m) ∣ (2 : ℤ) ^ (n - u) :=
    pow_dvd_pow 2 (Nat.sub_le_sub_left (by omega) n)
  exact Dvd.dvd.mul_right (hpow.trans (DiagonalIntegralLog2.two_pow_dvd_coeff n u)) _

/-- **2-adic multiplicative helper, pole `x=−2`.**  `2^(n−m) ∣ coeff m((X−2)ⁿ(3−X)ⁿ·H)`. -/
theorem two_pow_dvd_mul_coeff_b (n m : ℕ) (H : ℤ[X]) :
    (2 : ℤ) ^ (n - m) ∣ ((X - 2 : ℤ[X]) ^ n * (3 - X) ^ n * H).coeff m := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
  -- coeff u ((X−2)ⁿ(3−X)ⁿ) is divisible by 2^(n−u)
  have hcoeff : (2 : ℤ) ^ (n - u) ∣ ((X - 2 : ℤ[X]) ^ n * (3 - X) ^ n).coeff u := by
    rw [Polynomial.coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨a, b⟩ hab
    have habu : a + b = u := Finset.mem_antidiagonal.mp hab
    have : (2 : ℤ) ^ (n - u) ∣ (2 : ℤ) ^ (n - a) := pow_dvd_pow 2 (Nat.sub_le_sub_left (by omega) n)
    exact Dvd.dvd.mul_right (this.trans (two_pow_dvd_X_sub_two_pow_coeff n a)) _
  have hpow : (2 : ℤ) ^ (n - m) ∣ (2 : ℤ) ^ (n - u) :=
    pow_dvd_pow 2 (Nat.sub_le_sub_left (by omega) n)
  exact Dvd.dvd.mul_right (hpow.trans hcoeff) _

/-- **3-adic multiplicative helper, pole `x=−2`.**  `3^(n−m) ∣ coeff m((X−2)ⁿ(3−X)ⁿ·H)`. -/
theorem three_pow_dvd_mul_coeff_b (n m : ℕ) (H : ℤ[X]) :
    (3 : ℤ) ^ (n - m) ∣ ((X - 2 : ℤ[X]) ^ n * (3 - X) ^ n * H).coeff m := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvm : u + v = m := Finset.mem_antidiagonal.mp huv
  have hcoeff : (3 : ℤ) ^ (n - u) ∣ ((X - 2 : ℤ[X]) ^ n * (3 - X) ^ n).coeff u := by
    rw [Polynomial.coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨a, b⟩ hab
    have habu : a + b = u := Finset.mem_antidiagonal.mp hab
    -- the (3−X)ⁿ factor sits at index b ≤ u, contributing 3^(n−b)
    have : (3 : ℤ) ^ (n - u) ∣ (3 : ℤ) ^ (n - b) := pow_dvd_pow 3 (Nat.sub_le_sub_left (by omega) n)
    exact Dvd.dvd.mul_left (this.trans (three_pow_dvd_three_sub_X_pow_coeff n b)) _
  have hpow : (3 : ℤ) ^ (n - m) ∣ (3 : ℤ) ^ (n - u) :=
    pow_dvd_pow 3 (Nat.sub_le_sub_left (by omega) n)
  exact Dvd.dvd.mul_right (hpow.trans hcoeff) _

/-! ### The explicit integer residues -/

/-- `aRes n j` — the integer residue at the pole `x = −1` (coefficient `[X^{n+1−j}]`). -/
noncomputable def aRes (n j : ℕ) : ℤ :=
  ((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n * serNeg n).coeff (n + 1 - j)

/-- `bRes n j` — the integer residue at the pole `x = −2`. -/
noncomputable def bRes (n j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n + 1) * ((X - 2 : ℤ[X]) ^ n * (3 - X) ^ n * serPos n).coeff (n + 1 - j)

/-- `2^i ∣ aRes n (i+1)` for `i ≤ n`. -/
theorem two_pow_dvd_aRes {n i : ℕ} (hi : i ≤ n) : (2 : ℤ) ^ i ∣ aRes n (i + 1) := by
  have h := two_pow_dvd_mul_coeff n (n - i) (serNeg n)
  have he : n - (n - i) = i := by omega
  have hj : n + 1 - (i + 1) = n - i := by omega
  rw [he] at h
  unfold aRes
  rw [hj]
  exact h

/-- `2^i ∣ bRes n (i+1)` for `i ≤ n`. -/
theorem two_pow_dvd_bRes {n i : ℕ} (hi : i ≤ n) : (2 : ℤ) ^ i ∣ bRes n (i + 1) := by
  have h := two_pow_dvd_mul_coeff_b n (n - i) (serPos n)
  have he : n - (n - i) = i := by omega
  have hj : n + 1 - (i + 1) = n - i := by omega
  rw [he] at h
  unfold bRes
  rw [hj]
  exact Dvd.dvd.mul_left h _

/-- `3^i ∣ bRes n (i+1)` for `i ≤ n`. -/
theorem three_pow_dvd_bRes {n i : ℕ} (hi : i ≤ n) : (3 : ℤ) ^ i ∣ bRes n (i + 1) := by
  have h := three_pow_dvd_mul_coeff_b n (n - i) (serPos n)
  have he : n - (n - i) = i := by omega
  have hj : n + 1 - (i + 1) = n - i := by omega
  rw [he] at h
  unfold bRes
  rw [hj]
  exact Dvd.dvd.mul_left h _

/-! ### The explicit rational `Pₙ` and the denominator bound (the miracle, assembled) -/

open scoped BigOperators
open LcmGrowthBound

/-- The bracket `a_{i+1}(1−2^{−i}) + b_{i+1}(2^{−i}−3^{−i})` of the closed form, as a rational. -/
noncomputable def Pbracket (n i : ℕ) : ℚ :=
  (aRes n (i + 1) : ℚ) * (1 - ((2 : ℚ) ^ i)⁻¹)
    + (bRes n (i + 1) : ℚ) * (((2 : ℚ) ^ i)⁻¹ - ((3 : ℚ) ^ i)⁻¹)

/-- **The explicit closed form**
`Pexpl n = ∑_{i=1}^n [a_{i+1}(1−2^{−i}) + b_{i+1}(2^{−i}−3^{−i})]/i`. -/
noncomputable def Pexpl (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, Pbracket n i / (i : ℚ)

/-- **Per-bracket integrality** (the 2,3-adic miracle in action): for `1 ≤ i ≤ n`, the bracket
`a_{i+1}(1−2^{−i}) + b_{i+1}(2^{−i}−3^{−i})` is an integer.  Indeed it equals
`a_{i+1} − a_{i+1}/2^i + b_{i+1}/2^i − b_{i+1}/3^i`, and `2^i ∣ a_{i+1}`, `2^i ∣ b_{i+1}`,
`3^i ∣ b_{i+1}`. -/
theorem Pbracket_int {n i : ℕ} (hi : i ≤ n) : ∃ z : ℤ, Pbracket n i = (z : ℚ) := by
  obtain ⟨A2, hA2⟩ := two_pow_dvd_aRes hi
  obtain ⟨B2, hB2⟩ := two_pow_dvd_bRes hi
  obtain ⟨B3, hB3⟩ := three_pow_dvd_bRes hi
  refine ⟨aRes n (i + 1) - A2 + B2 - B3, ?_⟩
  have h2 : ((2 : ℚ) ^ i) ≠ 0 := by positivity
  have h3 : ((3 : ℚ) ^ i) ≠ 0 := by positivity
  have key : ∀ xq cq Cq : ℚ, cq ≠ 0 → xq = cq * Cq → xq * cq⁻¹ = Cq := by
    intro xq cq Cq hc hx
    rw [hx, mul_comm cq Cq, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have e2a : (aRes n (i + 1) : ℚ) * ((2 : ℚ) ^ i)⁻¹ = (A2 : ℚ) :=
    key _ _ _ h2 (by rw [hA2]; push_cast; ring)
  have e2b : (bRes n (i + 1) : ℚ) * ((2 : ℚ) ^ i)⁻¹ = (B2 : ℚ) :=
    key _ _ _ h2 (by rw [hB2]; push_cast; ring)
  have e3b : (bRes n (i + 1) : ℚ) * ((3 : ℚ) ^ i)⁻¹ = (B3 : ℚ) :=
    key _ _ _ h3 (by rw [hB3]; push_cast; ring)
  unfold Pbracket
  rw [mul_sub, mul_one, mul_sub, e2a, e2b, e3b]
  push_cast; ring

/-- **The denominator miracle (PROVED).**  `lcm(1..n)` clears the denominator of the explicit
closed form `Pexpl n`: there is an integer `z` with `lcm(1..n)·Pexpl n = z`.  Each summand `i`
contributes `(lcm(1..n)/i)·(integer bracket)` since `i ∣ lcm(1..n)` (`dvd_lcmUpto`) and the bracket
is an integer (`Pbracket_int`). -/
theorem lcmUpto_mul_Pexpl_int (n : ℕ) : ∃ z : ℤ, (lcmUpto n : ℚ) * Pexpl n = (z : ℚ) := by
  classical
  have hterm : ∀ i ∈ Finset.Icc 1 n,
      ∃ z : ℤ, (lcmUpto n : ℚ) * (Pbracket n i / (i : ℚ)) = (z : ℚ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨z0, hz0⟩ := Pbracket_int hi.2
    obtain ⟨D', hD'⟩ := dvd_lcmUpto hi.1 hi.2
    refine ⟨D' * z0, ?_⟩
    have hiQ : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hz0, hD']
    push_cast
    field_simp
  let zfun : ℕ → ℤ := fun i => if h : i ∈ Finset.Icc 1 n then (hterm i h).choose else 0
  refine ⟨∑ i ∈ Finset.Icc 1 n, zfun i, ?_⟩
  unfold Pexpl
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [zfun, dif_pos hi]
  exact (hterm i hi).choose_spec

/-! ### The unconditional measure modulo the closed-form identity `JP = Pexpl`

The denominator miracle is proven outright above.  The only remaining input is the explicit
sequence identity `JP n = Pexpl n` (the recurrence-defined rational part equals the partial-fraction
closed form — equivalently, `Pexpl` satisfies the same three-term recurrence; verified numerically
for `n ≤ 21`).  This replaces the opaque per-step `hstep` with a concrete, Zeilberger-style equality
of explicit objects, and the 2,3-adic "miracle" that `hstep` left unexplained is now a *theorem*. -/

/-- **Effective irrationality measure of `log(4/3)`, modulo the closed-form identity `JP = Pexpl`.**
With the denominator miracle proven (`lcmUpto_mul_Pexpl_int`) and integrality of `α₁` already
discharged (`Jα_int`), the full effective measure follows from the single explicit identity
`∀ n, JP n = Pexpl n`. -/
theorem log43_measure_of_Pexpl_eq (hPexpl : ∀ n, JP n = Pexpl n) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_int_den Jα_int
    (fun n => by rw [hPexpl n]; exact lcmUpto_mul_Pexpl_int n)

end WeightedDiagonalLog43
