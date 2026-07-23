import Mathlib.NumberTheory.Chebyshev

namespace CollatzChebyshev30

open Chebyshev Real Finset

/-- A psi-theta gap strictly tighter than mathlib's
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` (`|ψ x - θ x| ≤ 2√x·log x`): the `log x`
factor is removed from the leading `√x` (and the next two square-root-scale terms),
surviving only on the genuinely lower-order `x^(1/5)` tail. -/
theorem psi_sub_theta_le_tight (x : ℝ) (hx : 2 ≤ x) :
    psi x - theta x ≤ Real.log 4 *
      (Real.sqrt x + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4)
       + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5)) := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  set m := ⌊Real.log x / Real.log 2⌋₊ with hm
  have h0 : (0:ℝ) ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg hx1) (Real.log_nonneg (by norm_num))
  calc ∑ n ∈ Icc 2 m, theta (x ^ ((1:ℝ)/n))
      ≤ ∑ n ∈ Icc 2 m, Real.log 4 * x ^ ((1:ℝ)/n) :=
        Finset.sum_le_sum fun i _ => theta_le_log4_mul_x (Real.rpow_nonneg (by linarith) _)
    _ = Real.log 4 * ∑ n ∈ Icc 2 m, x ^ ((1:ℝ)/n) := by rw [Finset.mul_sum]
    _ ≤ Real.log 4 * (Real.sqrt x + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4)
          + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
        calc ∑ n ∈ Icc 2 m, x ^ ((1:ℝ)/n)
            = ∑ n ∈ Finset.filter (fun n => n ≤ 4) (Icc 2 m), x ^ ((1:ℝ)/n)
                + ∑ n ∈ Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m), x ^ ((1:ℝ)/n) :=
              (Finset.sum_filter_add_sum_filter_not _ _ _).symm
          _ ≤ (Real.sqrt x + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4))
                + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5) := by
              apply add_le_add
              · -- head: n ∈ {2,3,4}
                rw [Real.sqrt_eq_rpow]
                have hsub : Finset.filter (fun n => n ≤ 4) (Icc 2 m) ⊆ Icc 2 4 := by
                  intro n hn
                  rw [Finset.mem_filter, Finset.mem_Icc] at hn
                  rw [Finset.mem_Icc]; omega
                calc ∑ n ∈ Finset.filter (fun n => n ≤ 4) (Icc 2 m), x ^ ((1:ℝ)/n)
                    ≤ ∑ n ∈ Icc (2:ℕ) 4, x ^ ((1:ℝ)/n) :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub
                        (fun i _ _ => Real.rpow_nonneg (by linarith) _)
                  _ = x ^ ((1:ℝ)/2) + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4) := by
                      rw [show (Icc 2 4 : Finset ℕ) = {2,3,4} from by decide,
                          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                          Finset.sum_singleton]
                      push_cast; ring
              · -- tail: n ≥ 5, each term ≤ x^(1/5), at most (log x/log 2) terms
                calc ∑ n ∈ Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m), x ^ ((1:ℝ)/n)
                    ≤ ∑ n ∈ Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m), x ^ ((1:ℝ)/5) := by
                      apply Finset.sum_le_sum
                      intro n hn
                      rw [Finset.mem_filter, Finset.mem_Icc] at hn
                      apply Real.rpow_le_rpow_of_exponent_le hx1
                      apply one_div_le_one_div_of_le (by norm_num)
                      have : 5 ≤ n := by omega
                      exact_mod_cast this
                  _ = ((Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m)).card : ℝ) * x ^ ((1:ℝ)/5) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                  _ ≤ (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5) := by
                      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
                      have hle : (Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m)).card ≤ m := by
                        calc (Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m)).card
                            ≤ (Icc 2 m).card := Finset.card_filter_le _ _
                          _ = m + 1 - 2 := by rw [Nat.card_Icc]
                          _ ≤ m := by omega
                      calc ((Finset.filter (fun n => ¬ n ≤ 4) (Icc 2 m)).card : ℝ)
                          ≤ (m : ℝ) := by exact_mod_cast hle
                        _ ≤ Real.log x / Real.log 2 := Nat.floor_le h0

#print axioms psi_sub_theta_le_tight

end CollatzChebyshev30
