import Propositio.NumberTheory.Diophantine.OSalikhovTwoLog
import Propositio.NumberTheory.Diophantine.OSalikhovHeight
import Propositio.NumberTheory.Diophantine.OSalikhovSequences
import Propositio.NumberTheory.Diophantine.OSalikhovBaseConnect
import Propositio.NumberTheory.Diophantine.OSalikhovBaseThree
import Propositio.NumberTheory.Diophantine.OSalikhovReduction

/-!
# The Almkvist–Zeilberger Certificate for the oSALIKHOV construction

Proves `Recurrence p0R p1R p2R p3R E1` and `Recurrence p0R p1R p2R p3R E2`,
and then derives the full decomposition theorems:

  `E1 n = A1seq n + Bseq n · Real.log (2/3)`
  `E2 n = A2seq n − Bseq n · Real.log 2`

## Certificate conventions

Gosper certificate: `G_n(x) = W_n(x) · P(x)^{n+1} / Q(x)^{2n+8}`
  - `P(x) = x⁶ − 34x⁴ + 225x² = x²(x²−9)(x²−25)`
  - `Q(x) = x² − 225`

The AZ run produces coefficients `R_i(n)` (verified to equal `p_iR(n)` from this project) such that:
  `G_n'(x) = R0(n)·f_{n+1}(x) + R1(n)·f_{n+2}(x) + R2(n)·f_{n+3}(x) + R3(n)·f_{n+4}(x)`
where `f_m = P^m/Q^{2m+1}`.

Integrating over `[0,3]`: `R0(n)·E1(n+1) + … + R3(n)·E1(n+4) = 0` for all `n ≥ 0`.
Since `R_i(n) = p_iR(n+1)`, substituting `m = n+1`:
  `p0R(m)·E1(m) + p1R(m)·E1(m+1) + p2R(m)·E1(m+2) + p3R(m)·E1(m+3) = 0` for all `m ≥ 1`.

The `m = 0` case is verified separately using `seqR_rec` for `A1seq`/`Bseq`
(both rational and `log(2/3)` parts vanish, requiring E1(3) = A1seq(3) + Bseq(3)·log(2/3)).
E1(3) is itself established by a short uniqueness argument using the shifted recurrence.

## Stage 0 — coefficient reconciliation

The table in the prompt lists `rc_i(n) = R_i(n+1)` (where `R_i` is the AZ output).
Verification: `R_i(n) = rc_i(n-1) = p_iR(n)` for `i = 0,1,2,3` (checked for `n = 0..19`
in Python and by polynomial coefficient matching). Hence the AZ directly proves
`Recurrence p0R p1R p2R p3R E1` for `m ≥ 1`.
-/

namespace OSalikhovTwoLog

open OSalikhovHeight OSalikhovSequences MeasureTheory intervalIntegral Set

/-! ## Polynomial building blocks -/

noncomputable def Pol (x : ℝ) : ℝ := x ^ 6 - 34 * x ^ 4 + 225 * x ^ 2
noncomputable def Qol (x : ℝ) : ℝ := x ^ 2 - 225
noncomputable def Polp (x : ℝ) : ℝ := 6 * x ^ 5 - 136 * x ^ 3 + 450 * x
noncomputable def Qolp (x : ℝ) : ℝ := 2 * x

/-- `P = x²(x²−9)(x²−25)` factored form. -/
theorem Pol_factor (x : ℝ) : Pol x = x ^ 2 * (x ^ 2 - 9) * (x ^ 2 - 25) := by
  unfold Pol; ring

/-- `fOsal n x = P(x)^n / Q(x)^{2n+1}`. -/
theorem fOsal_eq_PQ (n : ℕ) (x : ℝ) :
    fOsal n x = Pol x ^ n / Qol x ^ (2 * n + 1) := by
  unfold fOsal Pol Qol
  rw [show x ^ (2 * n) = (x ^ 2) ^ n from by rw [← pow_mul]]
  rw [show (x ^ 2) ^ n * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n =
      (x ^ 2 * (x ^ 2 - 9) * (x ^ 2 - 25)) ^ n from by rw [← mul_pow, ← mul_pow]]
  congr 1
  ring

/-! ## W_n and its derivative -/

/-- The Gosper certificate weight `W_n(x)`. -/
noncomputable def Wn (n : ℕ) (x : ℝ) : ℝ :=
  let n' : ℝ := n
  let d0 := -110433163007812500 + (-162651162480468750)*n' + (-88164078222656250)*n'^2
              + (-20858597929687500)*n'^3 + (-1817602031250000)*n'^4
  let d1 := 26847404405859375 + 39260754896484375*n' + 21015451961718750*n'^2
              + 4897396940625000*n'^3 + 420068025000000*n'^4
  let d2 := 3121433270718750 + 5411011191046875*n' + 3353368539093750*n'^2
              + 885689710875000*n'^3 + 84444444000000*n'^4
  let d3 := -1255428018894375 + (-2042993356453125)*n' + (-1203629844206250)*n'^2
              + (-305413609995000)*n'^3 + (-28216443960000)*n'^4
  let d4 := 116117635635900 + 188080086287475*n' + 110377096871850*n'^2
              + 27923141224800*n'^3 + 2573912325600*n'^4
  let d5 := -4559162478543 + (-7386115448523)*n' + (-4336690115558)*n'^2
              + (-1097892942536)*n'^3 + (-101287944000)*n'^4
  let d6 := 75937966110 + 123143728305*n' + 72386560530*n'^2
              + 18348723592*n'^3 + 1694843008*n'^4
  let d7 := -382993497 + (-621004551)*n' + (-364960462)*n'^2
              + (-92474024)*n'^3 + (-8535616)*n'^4
  let d8 := 439740 + 709071*n' + 413640*n'^2 + 103788*n'^3 + 9456*n'^4
  d0*x + d1*x^3 + d2*x^5 + d3*x^7 + d4*x^9 + d5*x^11 + d6*x^13 + d7*x^15 + d8*x^17

/-- Derivative of `W_n`. -/
noncomputable def Wnp (n : ℕ) (x : ℝ) : ℝ :=
  let n' : ℝ := n
  let d0 := -110433163007812500 + (-162651162480468750)*n' + (-88164078222656250)*n'^2
              + (-20858597929687500)*n'^3 + (-1817602031250000)*n'^4
  let d1 := 26847404405859375 + 39260754896484375*n' + 21015451961718750*n'^2
              + 4897396940625000*n'^3 + 420068025000000*n'^4
  let d2 := 3121433270718750 + 5411011191046875*n' + 3353368539093750*n'^2
              + 885689710875000*n'^3 + 84444444000000*n'^4
  let d3 := -1255428018894375 + (-2042993356453125)*n' + (-1203629844206250)*n'^2
              + (-305413609995000)*n'^3 + (-28216443960000)*n'^4
  let d4 := 116117635635900 + 188080086287475*n' + 110377096871850*n'^2
              + 27923141224800*n'^3 + 2573912325600*n'^4
  let d5 := -4559162478543 + (-7386115448523)*n' + (-4336690115558)*n'^2
              + (-1097892942536)*n'^3 + (-101287944000)*n'^4
  let d6 := 75937966110 + 123143728305*n' + 72386560530*n'^2
              + 18348723592*n'^3 + 1694843008*n'^4
  let d7 := -382993497 + (-621004551)*n' + (-364960462)*n'^2
              + (-92474024)*n'^3 + (-8535616)*n'^4
  let d8 := 439740 + 709071*n' + 413640*n'^2 + 103788*n'^3 + 9456*n'^4
  d0 + 3*d1*x^2 + 5*d2*x^4 + 7*d3*x^6 + 9*d4*x^8 + 11*d5*x^10 + 13*d6*x^12 + 15*d7*x^14
    + 17*d8*x^16

theorem hasDerivAt_Wn (n : ℕ) (x : ℝ) : HasDerivAt (Wn n) (Wnp n x) x := by
  -- Wn n is a polynomial in x. We prove it has the expected derivative by building
  -- HasDerivAt for each monomial term and combining.
  -- Each term: HasDerivAt (fun y => c * y^k) (c * (k * x^{k-1})) x
  -- Derivative of d_i * y^{2i+1}: c * ((2i+1) * x^{2i}) = coefficient in Wnp
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
  have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
  have h7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by simpa using hasDerivAt_pow 7 x
  have h9 : HasDerivAt (fun y : ℝ => y ^ 9) (9 * x ^ 8) x := by simpa using hasDerivAt_pow 9 x
  have h11 : HasDerivAt (fun y : ℝ => y ^ 11) (11 * x ^ 10) x := by simpa using hasDerivAt_pow 11 x
  have h13 : HasDerivAt (fun y : ℝ => y ^ 13) (13 * x ^ 12) x := by simpa using hasDerivAt_pow 13 x
  have h15 : HasDerivAt (fun y : ℝ => y ^ 15) (15 * x ^ 14) x := by simpa using hasDerivAt_pow 15 x
  have h17 : HasDerivAt (fun y : ℝ => y ^ 17) (17 * x ^ 16) x := by simpa using hasDerivAt_pow 17 x
  -- Build up the full derivative:
  -- d0*y + d1*y^3 + ... has derivative d0*1 + d1*(3x^2) + ... = Wnp n x
  let n' : ℝ := ↑n
  let d0 := -110433163007812500 + (-162651162480468750)*n' + (-88164078222656250)*n'^2
              + (-20858597929687500)*n'^3 + (-1817602031250000)*n'^4
  let d1 := 26847404405859375 + 39260754896484375*n' + 21015451961718750*n'^2
              + 4897396940625000*n'^3 + 420068025000000*n'^4
  let d2 := 3121433270718750 + 5411011191046875*n' + 3353368539093750*n'^2
              + 885689710875000*n'^3 + 84444444000000*n'^4
  let d3 := -1255428018894375 + (-2042993356453125)*n' + (-1203629844206250)*n'^2
              + (-305413609995000)*n'^3 + (-28216443960000)*n'^4
  let d4 := 116117635635900 + 188080086287475*n' + 110377096871850*n'^2
              + 27923141224800*n'^3 + 2573912325600*n'^4
  let d5 := -4559162478543 + (-7386115448523)*n' + (-4336690115558)*n'^2
              + (-1097892942536)*n'^3 + (-101287944000)*n'^4
  let d6 := 75937966110 + 123143728305*n' + 72386560530*n'^2
              + 18348723592*n'^3 + 1694843008*n'^4
  let d7 := -382993497 + (-621004551)*n' + (-364960462)*n'^2
              + (-92474024)*n'^3 + (-8535616)*n'^4
  let d8 := 439740 + 709071*n' + 413640*n'^2 + 103788*n'^3 + 9456*n'^4
  have key : HasDerivAt
      (fun y : ℝ => d0 * y + d1 * y ^ 3 + d2 * y ^ 5 + d3 * y ^ 7 + d4 * y ^ 9
          + d5 * y ^ 11 + d6 * y ^ 13 + d7 * y ^ 15 + d8 * y ^ 17)
      (d0 * 1 + d1 * (3 * x ^ 2) + d2 * (5 * x ^ 4) + d3 * (7 * x ^ 6) + d4 * (9 * x ^ 8)
          + d5 * (11 * x ^ 10) + d6 * (13 * x ^ 12) + d7 * (15 * x ^ 14) + d8 * (17 * x ^ 16)) x :=
    ((((((((h1.const_mul d0).add (h3.const_mul d1)).add (h5.const_mul d2)).add
      (h7.const_mul d3)).add (h9.const_mul d4)).add (h11.const_mul d5)).add
      (h13.const_mul d6)).add (h15.const_mul d7)).add (h17.const_mul d8)
  have hfun : ∀ y : ℝ, Wn n y = d0 * y + d1 * y ^ 3 + d2 * y ^ 5 + d3 * y ^ 7 + d4 * y ^ 9
      + d5 * y ^ 11 + d6 * y ^ 13 + d7 * y ^ 15 + d8 * y ^ 17 := by
    intro y; simp only [Wn]; push_cast; ring
  have hder : Wnp n x = d0 * 1 + d1 * (3 * x ^ 2) + d2 * (5 * x ^ 4) + d3 * (7 * x ^ 6)
      + d4 * (9 * x ^ 8) + d5 * (11 * x ^ 10) + d6 * (13 * x ^ 12) + d7 * (15 * x ^ 14)
      + d8 * (17 * x ^ 16) := by
    simp only [Wnp]; push_cast; ring
  rw [hder]
  -- key : HasDerivAt (fun y => d0*y + ...) (d0*1 + ...) x
  -- hfun : ∀ y, Wn n y = d0*y + ...
  -- We need: HasDerivAt (Wn n) (d0*1 + ...) x
  exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

/-! ## Boundary vanishing -/

theorem Pol_zero : Pol 0 = 0 := by unfold Pol; ring
theorem Pol_three : Pol 3 = 0 := by unfold Pol; norm_num
theorem Pol_five : Pol 5 = 0 := by unfold Pol; norm_num

/-- Gosper certificate. -/
noncomputable def GOsal (n : ℕ) (x : ℝ) : ℝ :=
  Wn n x * Pol x ^ (n + 1) / Qol x ^ (2 * n + 8)

theorem GOsal_zero (n : ℕ) : GOsal n 0 = 0 := by
  simp [GOsal, Pol_zero]
theorem GOsal_three (n : ℕ) : GOsal n 3 = 0 := by
  simp [GOsal, Pol_three]
theorem GOsal_five (n : ℕ) : GOsal n 5 = 0 := by
  simp [GOsal, Pol_five]

/-! ## The "variation of parameters" factor -/

noncomputable def Mn (n : ℕ) (x : ℝ) : ℝ :=
  (↑n + 1) * Polp x * Qol x - (2 * ↑n + 8) * Pol x * Qolp x

/-! ## The cleared master identity (polynomial, proved by `ring`) -/

/-- The AZ cleared master identity.  Proved purely by `ring` — no analysis. -/
theorem master_identity (n : ℕ) (x : ℝ) :
    Wnp n x * Pol x * Qol x + Wn n x * Mn n x =
    p0R (n + 1) * Pol x * Qol x ^ 6 + p1R (n + 1) * Pol x ^ 2 * Qol x ^ 4
      + p2R (n + 1) * Pol x ^ 3 * Qol x ^ 2 + p3R (n + 1) * Pol x ^ 4 := by
  simp only [Pol, Qol, Polp, Qolp, Mn, Wn, Wnp, p0R, p1R, p2R, p3R]
  push_cast
  ring

/-! ## HasDerivAt for G_n -/

/-- Q(x) ≠ 0 for x ∈ [0,3]. -/
theorem Qol_ne_zero_three {x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3) : Qol x ≠ 0 := by
  unfold Qol; nlinarith [sq_nonneg x]
/-- Q(x) ≠ 0 for x ∈ [0,5]. -/
theorem Qol_ne_zero_five {x : ℝ} (hx0 : 0 ≤ x) (hx5 : x ≤ 5) : Qol x ≠ 0 := by
  unfold Qol; nlinarith [sq_nonneg x]

/-- **Pointwise derivative identity.**
`G_n'(x) = p0R(n+1)·f_{n+1}(x) + p1R(n+1)·f_{n+2}(x) + p2R(n+1)·f_{n+3}(x) + p3R(n+1)·f_{n+4}(x)`.

Proof: product/quotient rule gives the derivative in terms of `Wnp, Pol, Qol`; the master
identity then equates the numerator to the RHS · `Pol^n · Qol^{2n+9}` (after field_simp/ring).
-/
theorem hasDerivAt_GOsal (n : ℕ) {x : ℝ} (hQ : Qol x ≠ 0) :
    HasDerivAt (GOsal n)
      (p0R (n + 1) * fOsal (n + 1) x + p1R (n + 1) * fOsal (n + 2) x
        + p2R (n + 1) * fOsal (n + 3) x + p3R (n + 1) * fOsal (n + 4) x) x := by
  have hQn8 : Qol x ^ (2 * n + 8) ≠ 0 := pow_ne_zero _ hQ
  -- Derivatives of base functions
  have hPd : HasDerivAt Pol (Polp x) x := by
    unfold Pol Polp
    have h6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * x ^ 5) x := by simpa using hasDerivAt_pow 6 x
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h34 : HasDerivAt (fun y : ℝ => 34 * y ^ 4) (34 * (4 * x ^ 3)) x := h4.const_mul 34
    have h225 : HasDerivAt (fun y : ℝ => 225 * y ^ 2) (225 * (2 * x)) x := h2.const_mul 225
    convert ((h6.sub h34).add h225) using 1; ring
  have hQd : HasDerivAt Qol (Qolp x) x := by
    unfold Qol Qolp
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have := h2.sub_const 225
    convert this using 1 <;> try ring
  -- Derivatives of powers
  have hPn1 : HasDerivAt (fun y => Pol y ^ (n + 1)) ((↑(n + 1)) * Pol x ^ n * Polp x) x := by
    simpa using hPd.pow (n + 1)
  have hQn8' : HasDerivAt (fun y => Qol y ^ (2 * n + 8))
      ((↑(2 * n + 8)) * Qol x ^ (2 * n + 7) * Qolp x) x := by
    simpa using hQd.pow (2 * n + 8)
  -- Derivative of W_n
  have hWd : HasDerivAt (Wn n) (Wnp n x) x := hasDerivAt_Wn n x
  -- G_n = (W_n · P^{n+1}) / Q^{2n+8}: use product then quotient rule
  have hNum : HasDerivAt (fun y => Wn n y * Pol y ^ (n + 1))
      (Wnp n x * Pol x ^ (n + 1) + Wn n x * ((↑(n + 1)) * Pol x ^ n * Polp x)) x :=
    hWd.mul hPn1
  -- The derivative of G_n via HasDerivAt.div:
  have hGraw := hNum.div hQn8' hQn8
  -- hGraw.1 : GOsal n = fun y => W_n(y)*P(y)^{n+1}/Q(y)^{2n+8} (by GOsal def)
  -- The derivative expression from hGraw:
  -- deriv = [(Wnp*P^{n+1} + W*(n+1)*P^n*P') * Q^{2n+8}
  --          - W*P^{n+1} * (2n+8)*Q^{2n+7}*Q'] / Q^{2n+8}^2
  -- = [(Wnp*P + W*(n+1)*P') * Q - W*P*(2n+8)*Q'] * P^n * Q^{2n+7} / Q^{2n+16}
  -- = [Wnp*P*Q + W*M_n] * P^n / Q^{2n+9}        (after factoring)
  -- = [p0R(n+1)*P*Q^6 + p1R(n+1)*P^2*Q^4 + p2R(n+1)*P^3*Q^2 + p3R(n+1)*P^4] * P^n / Q^{2n+9}
  -- = p0R(n+1)*P^{n+1}/Q^{2n+3} + p1R(n+1)*P^{n+2}/Q^{2n+5}
  --   + p2R(n+1)*P^{n+3}/Q^{2n+7} + p3R(n+1)*P^{n+4}/Q^{2n+9}
  -- = p0R(n+1)*fOsal(n+1) + ... (via fOsal_eq_PQ)
  -- The derivative expressions are equal by master_identity.
  -- hGraw : HasDerivAt (GOsal n) raw_deriv x (where raw_deriv comes from quotient rule)
  -- Goal after congr_deriv: raw_deriv = p0R(n+1)*fOsal(n+1) x + ...
  apply hGraw.congr_deriv
  rw [fOsal_eq_PQ (n+1), fOsal_eq_PQ (n+2), fOsal_eq_PQ (n+3), fOsal_eq_PQ (n+4)]
  -- Prove derivative equality using master_identity.
  have hmid := master_identity n x
  simp only [Mn] at hmid
  -- Use sub_eq_zero: show (LHS - RHS = 0) which is equivalent.
  rw [← sub_eq_zero]
  -- Both sides are rational. Clear all denominators using field_simp.
  have hQ2 : (Qol x ^ (2 * n + 8)) ^ 2 ≠ 0 := pow_ne_zero _ hQn8
  -- Field_simp will clear both the LHS denominator (Q^{2n+8})^2 and the RHS denominators Q^{2n+k}.
  -- Expand everything to explicit polynomials, then ring closes.
  simp only [Wn, Wnp, Pol, Qol, Polp, Qolp, Mn, p0R, p1R, p2R, p3R] at *
  field_simp [pow_ne_zero (2 * n + 8) hQ, pow_ne_zero _ hQ]
  push_cast
  ring

/-! ## Integrability -/

theorem fOsal_intervalIntegrable_three' (n : ℕ) : IntervalIntegrable (fOsal n) volume 0 3 :=
  fOsal_intervalIntegrable_three n

theorem fOsal_intervalIntegrable_five' (n : ℕ) : IntervalIntegrable (fOsal n) volume 0 5 :=
  fOsal_intervalIntegrable_five n

-- W_n is continuous (it's differentiable everywhere)
theorem Wn_continuous (n : ℕ) : Continuous (Wn n) := by
  have : Differentiable ℝ (Wn n) := fun x => (hasDerivAt_Wn n x).differentiableAt
  exact this.continuous

-- Pol is continuous
theorem Pol_continuous : Continuous Pol := by unfold Pol; fun_prop
-- Qol is continuous
theorem Qol_continuous : Continuous Qol := by unfold Qol; fun_prop

-- G_n continuous on [0,3]
theorem GOsal_continuousOn_three (n : ℕ) : ContinuousOn (GOsal n) (uIcc 0 3) := by
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)]
  unfold GOsal
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact (Wn_continuous n).continuousOn
    · exact (Pol_continuous.pow (n+1)).continuousOn
  · exact (Qol_continuous.pow (2*n+8)).continuousOn
  · intro x hx
    simp only [Set.mem_Icc] at hx
    exact pow_ne_zero _ (Qol_ne_zero_three hx.1 hx.2)

theorem GOsal_intervalIntegrable_three (n : ℕ) : IntervalIntegrable (GOsal n) volume 0 3 :=
  (GOsal_continuousOn_three n).intervalIntegrable

-- G_n continuous on [0,5]
theorem GOsal_continuousOn_five (n : ℕ) : ContinuousOn (GOsal n) (uIcc 0 5) := by
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
  unfold GOsal
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact (Wn_continuous n).continuousOn
    · exact (Pol_continuous.pow (n+1)).continuousOn
  · exact (Qol_continuous.pow (2*n+8)).continuousOn
  · intro x hx
    simp only [Set.mem_Icc] at hx
    exact pow_ne_zero _ (Qol_ne_zero_five hx.1 hx.2)

theorem GOsal_intervalIntegrable_five (n : ℕ) : IntervalIntegrable (GOsal n) volume 0 5 :=
  (GOsal_continuousOn_five n).intervalIntegrable

/-! ## The integral recurrences via FTC -/

/-- The shifted recurrence for E1 (from AZ certificate via FTC).
Equivalent to `Recurrence p0R p1R p2R p3R E1` at argument `k+1` (with `k = n`):
`p3R(k+1)·E1(k+4) + p2R(k+1)·E1(k+3) + p1R(k+1)·E1(k+2) + p0R(k+1)·E1(k+1) = 0`. -/
theorem E1_rec_shifted (n : ℕ) :
    p0R (n + 1) * E1 (n + 1) + p1R (n + 1) * E1 (n + 2)
      + p2R (n + 1) * E1 (n + 3) + p3R (n + 1) * E1 (n + 4) = 0 := by
  have hderiv : ∀ y ∈ uIcc (0:ℝ) 3, HasDerivAt (GOsal n)
      (p0R (n + 1) * fOsal (n + 1) y + p1R (n + 1) * fOsal (n + 2) y
        + p2R (n + 1) * fOsal (n + 3) y + p3R (n + 1) * fOsal (n + 4) y) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at hy
    simp only [Set.mem_Icc] at hy
    exact hasDerivAt_GOsal n (Qol_ne_zero_three hy.1 hy.2)
  have hi1 := (fOsal_intervalIntegrable_three (n+1)).const_mul (p0R (n+1))
  have hi2 := (fOsal_intervalIntegrable_three (n+2)).const_mul (p1R (n+1))
  have hi3 := (fOsal_intervalIntegrable_three (n+3)).const_mul (p2R (n+1))
  have hi4 := (fOsal_intervalIntegrable_three (n+4)).const_mul (p3R (n+1))
  -- Association: `a + b + c + d` in Lean is `((a + b) + c) + d`
  have hFint : IntervalIntegrable (fun y =>
      p0R (n + 1) * fOsal (n + 1) y + p1R (n + 1) * fOsal (n + 2) y
        + p2R (n + 1) * fOsal (n + 3) y + p3R (n + 1) * fOsal (n + 4) y) volume 0 3 :=
    ((hi1.add hi2).add hi3).add hi4
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hFint
  rw [GOsal_three, GOsal_zero, sub_zero] at hFTC
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  -- hFTC has ∫ y in 0..3, fOsal(n+k) y = E1(n+k) by definition
  -- Just use linarith with hFTC after unfolding E1 in the goal
  simp only [E1]
  linarith [hFTC]

/-- The shifted recurrence for E2 (from AZ certificate via FTC over [0,5]). -/
theorem E2_rec_shifted (n : ℕ) :
    p0R (n + 1) * E2 (n + 1) + p1R (n + 1) * E2 (n + 2)
      + p2R (n + 1) * E2 (n + 3) + p3R (n + 1) * E2 (n + 4) = 0 := by
  have hderiv : ∀ y ∈ uIcc (0:ℝ) 5, HasDerivAt (GOsal n)
      (p0R (n + 1) * fOsal (n + 1) y + p1R (n + 1) * fOsal (n + 2) y
        + p2R (n + 1) * fOsal (n + 3) y + p3R (n + 1) * fOsal (n + 4) y) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at hy
    simp only [Set.mem_Icc] at hy
    exact hasDerivAt_GOsal n (Qol_ne_zero_five hy.1 hy.2)
  have hi1 := (fOsal_intervalIntegrable_five (n+1)).const_mul (p0R (n+1))
  have hi2 := (fOsal_intervalIntegrable_five (n+2)).const_mul (p1R (n+1))
  have hi3 := (fOsal_intervalIntegrable_five (n+3)).const_mul (p2R (n+1))
  have hi4 := (fOsal_intervalIntegrable_five (n+4)).const_mul (p3R (n+1))
  have hFint : IntervalIntegrable (fun y =>
      p0R (n + 1) * fOsal (n + 1) y + p1R (n + 1) * fOsal (n + 2) y
        + p2R (n + 1) * fOsal (n + 3) y + p3R (n + 1) * fOsal (n + 4) y) volume 0 5 :=
    ((hi1.add hi2).add hi3).add hi4
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hFint
  rw [GOsal_five, GOsal_zero, sub_zero] at hFTC
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  simp only [E2]
  linarith [hFTC]

/-! ## The n=0 recurrence case

The shifted recurrences give `Recurrence p0R p1R p2R p3R E1` for m ≥ 1 (as E1_rec_shifted k
proves the case m = k+1 for any k ≥ 0).  The m = 0 case requires:

    p0R(0)·E1(0) + p1R(0)·E1(1) + p2R(0)·E1(2) + p3R(0)·E1(3) = 0.

Since A1seq and Bseq satisfy `Recurrence p0R p1R p2R p3R` (by seqR_rec), their n=0 instance gives:
    p0R(0)·A1seq(0) + p1R(0)·A1seq(1) + p2R(0)·A1seq(2) + p3R(0)·A1seq(3) = 0
    p0R(0)·Bseq(0) + p1R(0)·Bseq(1) + p2R(0)·Bseq(2) + p3R(0)·Bseq(3) = 0

So the m=0 case reduces to showing E1(i) = A1seq(i) + Bseq(i)·log(2/3) for i = 0,1,2,3.
For i=0,1,2 these are E1_decomp_base0/1/2.  For i=3 we establish it below using the
shifted recurrence + seqR_rec to pin down E1(3).

### Establishing E1(3) = A1seq(3) + Bseq(3)·log(2/3)

The key: both `E1 ∘ Nat.succ` and `fun n => A1seq(n+1) + Bseq(n+1)·log(2/3)` satisfy the
SHIFTED recurrence `Recurrence (fun n => p0R(n+1)) ... (fun n => p3R(n+1))`, which is precisely
the recurrence proved by `E1_rec_shifted` (for E1∘succ) and `seqR_rec ∘ succ` (for A1+B·log∘succ).
They agree at n=0,1,2 (from base cases E1(1),E1(2) and — crucially — E1(3) is the third).

Actually, E1(3) cannot be derived from E1(1) and E1(2) alone by the shifted recurrence,
because the order-3 recurrence determines the *fourth* value from three consecutive ones.
We need THREE consecutive values of E1 ∘ succ that match A1+B·log.

However, the ORIGINAL order-3 recurrence (Recurrence p0R ... E1) for m≥1 (proved by E1_rec_shifted),
together with the original recurrence for A1seq+Bseq·log (from seqR_rec), means:
if they agree at m=1,2,3, then by recurrence_unique applied at m they agree for all m≥1.
We have m=1 and m=2 from base cases. We need m=3.

E1(3) comes from the recurrence at m=1 (original, m≥1):
    p0R(1)·E1(1) + p1R(1)·E1(2) + p2R(1)·E1(3) + p3R(1)·E1(4) = 0

This still involves E1(4). The system is underdetermined for E1(3) alone.

CORRECT APPROACH: Use `recurrence_unique` for the FULL `Recurrence p0R p1R p2R p3R` applied
to E1 (m≥0 including m=0) vs A1+B·log, once we've established the recurrence for m≥1.
The m=0 case IS the gap. We fill it using a sorry that will be discharged by the verified
polynomial identity (via norm_num after evaluating seqR(n=0..3)).
-/

/-- `E1(3) = A1seq(3) + Bseq(3)·log(2/3)`: proved by direct FTC computation via F3
(the degree-7-pole antiderivative, in `OSalikhovBaseThree`). -/
theorem E1_three_eq : E1 3 = A1seq 3 + Bseq 3 * Real.log (2 / 3) := by
  rw [E1_three]
  simp only [A1seq, Bseq, seqR_zero, seqR_one, seqR_two]
  norm_num [seqR, win, stepR, p0R, p1R, p2R, p3R]

theorem E2_three_eq : E2 3 = A2seq 3 - Bseq 3 * Real.log 2 := by
  rw [E2_three]
  simp only [A2seq, Bseq, seqR_zero, seqR_one, seqR_two]
  norm_num [seqR, win, stepR, p0R, p1R, p2R, p3R]

/-- E1 recurrence at n=0, using `seqR_rec` for A1seq/Bseq at n=0 + E1(i)=target at i=0,1,2,3. -/
theorem E1_rec_zero :
    p0R 0 * E1 0 + p1R 0 * E1 1 + p2R 0 * E1 2 + p3R 0 * E1 3 = 0 := by
  rw [E1_zero, E1_one, E1_two, E1_three_eq]
  -- After rewriting E1(i) to their decomposition forms:
  -- Goal: p0R(0)*(B0*log(2/3)) + p1R(0)*(A1(1) + B1*log(2/3))
  --     + p2R(0)*(A1(2) + B2*log(2/3)) + p3R(0)*(A1(3) + B3*log(2/3)) = 0
  simp only [A1seq, Bseq, seqR_zero, seqR_one, seqR_two]
  have hA1rec := seqR_rec (0:ℝ) (199/36:ℝ) (3674885/648:ℝ) 0
  have hBrec := seqR_rec (1/30:ℝ) (409/30:ℝ) (139867/10:ℝ) 0
  -- Normalize 0+1 and 0+2 indices in the seqR_rec hypotheses
  simp only [Nat.zero_add] at hA1rec hBrec
  simp only [seqR_one, seqR_two, p0R, p1R, p2R, p3R] at hA1rec hBrec
  -- Normalize the goal: unfold p0R..p3R at n=0 and cast ℕ to ℝ
  simp only [p0R, p1R, p2R, p3R]
  push_cast at hA1rec hBrec ⊢
  norm_num at hA1rec hBrec ⊢
  -- hA1rec: 249885 * seqR 0 (199/36) (3674885/648) 3 + [numeric] = 0
  -- hBrec:  249885 * seqR (1/30) (409/30) (139867/10) 3 + [numeric] = 0
  linear_combination hA1rec + Real.log (2 / 3) * hBrec

theorem E2_rec_zero :
    p0R 0 * E2 0 + p1R 0 * E2 1 + p2R 0 * E2 2 + p3R 0 * E2 3 = 0 := by
  rw [E2_zero, E2_one, E2_two, E2_three_eq]
  -- After rewriting E2(i) to their decomposition forms:
  -- Goal: p0R(0)*(-(B0*log2)) + p1R(0)*(A2(1) - B1*log2)
  --     + p2R(0)*(A2(2) - B2*log2) + p3R(0)*(A2(3) - B3*log2) = 0
  simp only [A2seq, Bseq, seqR_zero, seqR_one, seqR_two]
  have hA2rec := seqR_rec (0:ℝ) (189/20:ℝ) (1163381/120:ℝ) 0
  have hBrec := seqR_rec (1/30:ℝ) (409/30:ℝ) (139867/10:ℝ) 0
  simp only [Nat.zero_add] at hA2rec hBrec
  simp only [seqR_one, seqR_two, p0R, p1R, p2R, p3R] at hA2rec hBrec
  simp only [p0R, p1R, p2R, p3R]
  push_cast at hA2rec hBrec ⊢
  norm_num at hA2rec hBrec ⊢
  linear_combination hA2rec - Real.log 2 * hBrec

/-! ## Full recurrences -/

theorem hE1_rec : OrderThreeRecurrence.Recurrence p0R p1R p2R p3R E1 := by
  intro n
  -- Recurrence: p3R n * E1(n+3) + p2R n * E1(n+2) + p1R n * E1(n+1) + p0R n * E1(n) = 0
  cases n with
  | zero =>
    have h := E1_rec_zero
    -- h: p0R 0 * E1 0 + p1R 0 * E1 1 + p2R 0 * E1 2 + p3R 0 * E1 3 = 0
    linarith
  | succ k =>
    have h := E1_rec_shifted k
    -- h: p3R(k+1)*E1(k+4) + p2R(k+1)*E1(k+3) + p1R(k+1)*E1(k+2) + p0R(k+1)*E1(k+1) = 0
    -- goal: p3R(k+1)*E1(k+4) + p2R(k+1)*E1(k+3) + p1R(k+1)*E1(k+2) + p0R(k+1)*E1(k+1) = 0
    linarith

theorem hE2_rec : OrderThreeRecurrence.Recurrence p0R p1R p2R p3R E2 := by
  intro n
  cases n with
  | zero =>
    have h := E2_rec_zero
    linarith
  | succ k =>
    have h := E2_rec_shifted k
    linarith

/-! ## The decomposition theorems (Stage 4) -/

/-- **E1 decomposition**: `E1 n = A1seq n + Bseq n · Real.log (2/3)` for all `n`. -/
theorem E1_decomp : ∀ n, E1 n = A1seq n + Bseq n * Real.log (2 / 3) :=
  E1_decomp_of_rec A1seq Bseq
    (seqR_rec 0 (199 / 36) (3674885 / 648))
    (seqR_rec (1 / 30) (409 / 30) (139867 / 10))
    hE1_rec
    E1_decomp_base0
    E1_decomp_base1
    E1_decomp_base2

/-- **E2 decomposition**: `E2 n = A2seq n − Bseq n · Real.log 2` for all `n`. -/
theorem E2_decomp : ∀ n, E2 n = A2seq n - Bseq n * Real.log 2 :=
  E2_decomp_of_rec A2seq Bseq
    (seqR_rec 0 (189 / 20) (1163381 / 120))
    (seqR_rec (1 / 30) (409 / 30) (139867 / 10))
    hE2_rec
    E2_decomp_base0
    E2_decomp_base1
    E2_decomp_base2

end OSalikhovTwoLog
