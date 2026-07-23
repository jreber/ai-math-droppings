import Propositio.Collatz.Chebyshev30M
import Propositio.Collatz.Chebyshev30Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chebyshev-30: an explicit linear upper bound on `log M(N)`

This file proves `log M(N) ≤ A·N + 4·log N + 4` where `A` is the period-30 entropy constant
`A = ½log2 + ⅓log3 + ⅕log5 − (1/30)log30 ≈ 0.921` and `M(N) = N!·(N/30)! / ((N/2)!·(N/3)!·(N/5)!)`
is the Chebyshev-30 integer from `CollatzChebyshev30M`.

The bound is the two-sided Stirling estimate: the upper Stirling bound (`log_factorial_le`) is used
on the numerator factorials `N!`, `(N/30)!` and the lower Stirling bound (`le_log_factorial`) on the
denominator factorials `(N/2)!`, `(N/3)!`, `(N/5)!`.  The `n log n − n` main terms recombine, by the
period-30 weight balance `1 + 1/30 = 1/2 + 1/3 + 1/5`, into the entropy constant `A`, leaving only the
floor-vs-real corrections (each `≤ log N + 1`) and the constant `2 − 3·½log(2π) ≤ 0`.
-/

namespace CollatzChebyshev30

open Real

/-- The period-30 entropy constant `A = ½log2 + ⅓log3 + ⅕log5 − (1/30)log30 ≈ 0.921`. -/
noncomputable def Aentropy : ℝ :=
  1/2 * Real.log 2 + 1/3 * Real.log 3 + 1/5 * Real.log 5 - 1/30 * Real.log 30

/-- **Convexity helper.** For `1 ≤ s ≤ t`,
`t·log t − s·log s ≤ (t − s)·(log t + 1)`.  (From `log(t/s) ≤ t/s − 1`.) -/
theorem mul_log_sub_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    t * Real.log t - s * Real.log s ≤ (t - s) * (Real.log t + 1) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hcancel : s * (t / s) = t := by rw [mul_comm]; exact div_mul_cancel₀ t hsne
  have h1 : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hkey : s * Real.log (t / s) ≤ t - s := by
    have h2 : s * Real.log (t / s) ≤ s * (t / s - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hs0)
    have h3 : s * (t / s - 1) = t - s := by rw [mul_sub, mul_one, hcancel]
    linarith [h2, h3.le, h3.ge]
  have hsplit : s * Real.log (t / s) = s * Real.log t - s * Real.log s := by
    rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hs0)]; ring
  have hh : s * Real.log t - s * Real.log s ≤ t - s := by rw [← hsplit]; exact hkey
  nlinarith [hh]

set_option maxHeartbeats 1200000 in
/-- **Explicit linear upper bound on `log M(N)`.**  For `N ≥ 30`,
`log M(N) ≤ A·N + 4·log N + 4`, with `A = Aentropy ≈ 0.921`. -/
theorem logM_le_linear (N : ℕ) (hN : 30 ≤ N) :
    Real.log (M N) ≤ Aentropy * N + 4 * Real.log N + 4 := by
  -- Nat floor lower bounds.
  have hN1 : 1 ≤ N := by omega
  have ha1 : 1 ≤ N / 2 := by omega
  have hb1 : 1 ≤ N / 3 := by omega
  have hc1 : 1 ≤ N / 5 := by omega
  have he1 : 1 ≤ N / 30 := by omega
  -- Real casts.
  have hNR : (30 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have haR : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast ha1
  have hbR : (1 : ℝ) ≤ ((N / 3 : ℕ) : ℝ) := by exact_mod_cast hb1
  have hcR : (1 : ℝ) ≤ ((N / 5 : ℕ) : ℝ) := by exact_mod_cast hc1
  have heR : (1 : ℝ) ≤ ((N / 30 : ℕ) : ℝ) := by exact_mod_cast he1
  -- Positivity of all the factorial casts.
  have hMpos : (0 : ℝ) < (M N : ℝ) := by exact_mod_cast M_pos N
  have hNfpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hefpos : (0 : ℝ) < (Nat.factorial (N / 30) : ℝ) := by exact_mod_cast Nat.factorial_pos (N / 30)
  have hafpos : (0 : ℝ) < (Nat.factorial (N / 2) : ℝ) := by exact_mod_cast Nat.factorial_pos (N / 2)
  have hbfpos : (0 : ℝ) < (Nat.factorial (N / 3) : ℝ) := by exact_mod_cast Nat.factorial_pos (N / 3)
  have hcfpos : (0 : ℝ) < (Nat.factorial (N / 5) : ℝ) := by exact_mod_cast Nat.factorial_pos (N / 5)
  -- STEP 1: cast the exact factorial-ratio identity to ℝ, then take logs.
  have hmul : (M N : ℝ) * ((Nat.factorial (N / 2) : ℝ) * (Nat.factorial (N / 3) : ℝ)
        * (Nat.factorial (N / 5) : ℝ))
      = (Nat.factorial N : ℝ) * (Nat.factorial (N / 30) : ℝ) := by
    have h := M_mul_den N
    have h2 : ((M N * M_den N : ℕ) : ℝ) = ((M_num N : ℕ) : ℝ) := by exact_mod_cast h
    simp only [M_den, M_num, Nat.cast_mul] at h2
    linear_combination h2
  have habpos : (0 : ℝ) < (Nat.factorial (N / 2) : ℝ) * (Nat.factorial (N / 3) : ℝ) :=
    mul_pos hafpos hbfpos
  have hprodpos : (0 : ℝ) < (Nat.factorial (N / 2) : ℝ) * (Nat.factorial (N / 3) : ℝ)
      * (Nat.factorial (N / 5) : ℝ) := mul_pos habpos hcfpos
  have hlogM : Real.log (M N : ℝ)
      = Real.log (Nat.factorial N : ℝ) + Real.log (Nat.factorial (N / 30) : ℝ)
        - Real.log (Nat.factorial (N / 2) : ℝ) - Real.log (Nat.factorial (N / 3) : ℝ)
        - Real.log (Nat.factorial (N / 5) : ℝ) := by
    have e1 : Real.log ((M N : ℝ) * ((Nat.factorial (N / 2) : ℝ) * (Nat.factorial (N / 3) : ℝ)
            * (Nat.factorial (N / 5) : ℝ)))
        = Real.log ((Nat.factorial N : ℝ) * (Nat.factorial (N / 30) : ℝ)) := by rw [hmul]
    rw [Real.log_mul (ne_of_gt hMpos) (ne_of_gt hprodpos),
        Real.log_mul (ne_of_gt habpos) (ne_of_gt hcfpos),
        Real.log_mul (ne_of_gt hafpos) (ne_of_gt hbfpos),
        Real.log_mul (ne_of_gt hNfpos) (ne_of_gt hefpos)] at e1
    linarith [e1]
  -- STEP 3: Stirling upper bounds (numerator) and lower bounds (denominator).
  have hSN := log_factorial_le hN1
  have hSe := log_factorial_le he1
  have hSa := le_log_factorial ha1
  have hSb := le_log_factorial hb1
  have hSc := le_log_factorial hc1
  -- STEP 2 packaged: floor-to-real correction for a subtracted factorial.
  have step4 : ∀ (s t : ℝ), 1 ≤ s → s ≤ t → t - s ≤ 1 → 0 ≤ Real.log t →
      Real.log t ≤ Real.log (N : ℝ) →
      -(s * Real.log s) ≤ -(t * Real.log t) + Real.log (N : ℝ) + 1 := by
    intro s t hs hst hdiff hlogt hmono
    have hkey := mul_log_sub_le hs hst
    have hprod : (0 : ℝ) ≤ (1 - (t - s)) * (Real.log t + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hkey, hprod, hmono]
  -- STEP 4a/b/c: real-division comparisons for a = N/2, b = N/3, c = N/5.
  have hsta : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]; exact_mod_cast Nat.div_mul_le_self N 2
  have hstb : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; exact_mod_cast Nat.div_mul_le_self N 3
  have hstc : ((N / 5 : ℕ) : ℝ) ≤ (N : ℝ) / 5 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 5)]; exact_mod_cast Nat.div_mul_le_self N 5
  have hda : (N : ℝ) / 2 - ((N / 2 : ℕ) : ℝ) ≤ 1 := by
    have h : N ≤ 2 * (N / 2) + 1 := by omega
    have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hdb : (N : ℝ) / 3 - ((N / 3 : ℕ) : ℝ) ≤ 1 := by
    have h : N ≤ 3 * (N / 3) + 2 := by omega
    have h2 : (N : ℝ) ≤ 3 * ((N / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast h
    linarith
  have hdc : (N : ℝ) / 5 - ((N / 5 : ℕ) : ℝ) ≤ 1 := by
    have h : N ≤ 5 * (N / 5) + 4 := by omega
    have h2 : (N : ℝ) ≤ 5 * ((N / 5 : ℕ) : ℝ) + 4 := by exact_mod_cast h
    linarith
  have hla : (0 : ℝ) ≤ Real.log ((N : ℝ) / 2) := Real.log_nonneg (by linarith)
  have hlb : (0 : ℝ) ≤ Real.log ((N : ℝ) / 3) := Real.log_nonneg (by linarith)
  have hlc : (0 : ℝ) ≤ Real.log ((N : ℝ) / 5) := Real.log_nonneg (by linarith)
  have hma : Real.log ((N : ℝ) / 2) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmb : Real.log ((N : ℝ) / 3) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmc : Real.log ((N : ℝ) / 5) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have h4a := step4 ((N / 2 : ℕ) : ℝ) ((N : ℝ) / 2) haR hsta hda hla hma
  have h4b := step4 ((N / 3 : ℕ) : ℝ) ((N : ℝ) / 3) hbR hstb hdb hlb hmb
  have h4c := step4 ((N / 5 : ℕ) : ℝ) ((N : ℝ) / 5) hcR hstc hdc hlc hmc
  -- STEP 4b': the added e = N/30 term, x·log x increasing on [1,∞).
  have step4b : ∀ (s t : ℝ), 1 ≤ s → s ≤ t → s * Real.log s ≤ t * Real.log t := by
    intro s t hs hst
    have hslog : 0 ≤ Real.log s := Real.log_nonneg hs
    have hlogmono : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - s) hslog,
      mul_nonneg (by linarith : (0:ℝ) ≤ t) (by linarith : (0:ℝ) ≤ Real.log t - Real.log s)]
  have hste : ((N / 30 : ℕ) : ℝ) ≤ (N : ℝ) / 30 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 30)]; exact_mod_cast Nat.div_mul_le_self N 30
  have h4e := step4b ((N / 30 : ℕ) : ℝ) ((N : ℝ) / 30) heR hste
  -- STEP 5: the exact real entropy identity.
  have hAid : (N : ℝ) * Real.log (N : ℝ) + ((N : ℝ) / 30) * Real.log ((N : ℝ) / 30)
      - ((N : ℝ) / 2) * Real.log ((N : ℝ) / 2) - ((N : ℝ) / 3) * Real.log ((N : ℝ) / 3)
      - ((N : ℝ) / 5) * Real.log ((N : ℝ) / 5) = Aentropy * (N : ℝ) := by
    rw [Real.log_div (ne_of_gt hNpos) (by norm_num : (2:ℝ) ≠ 0),
        Real.log_div (ne_of_gt hNpos) (by norm_num : (3:ℝ) ≠ 0),
        Real.log_div (ne_of_gt hNpos) (by norm_num : (5:ℝ) ≠ 0),
        Real.log_div (ne_of_gt hNpos) (by norm_num : (30:ℝ) ≠ 0)]
    unfold Aentropy
    ring
  -- Integer (linear) term: N/2 + N/3 + N/5 ≤ N + N/30 + 1.
  have hII : ((N / 2 : ℕ) : ℝ) + ((N / 3 : ℕ) : ℝ) + ((N / 5 : ℕ) : ℝ)
      ≤ (N : ℝ) + ((N / 30 : ℕ) : ℝ) + 1 := by
    have h : N / 2 + N / 3 + N / 5 ≤ N + N / 30 + 1 := by omega
    exact_mod_cast h
  -- Half-log term helpers.
  have hlogeN : Real.log ((N / 30 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast he1
    · exact_mod_cast Nat.div_le_self N 30
  have hloga0 : (0 : ℝ) ≤ Real.log ((N / 2 : ℕ) : ℝ) := Real.log_nonneg haR
  have hlogb0 : (0 : ℝ) ≤ Real.log ((N / 3 : ℕ) : ℝ) := Real.log_nonneg hbR
  have hlogc0 : (0 : ℝ) ≤ Real.log ((N / 5 : ℕ) : ℝ) := Real.log_nonneg hcR
  -- Constant term: ½log(2π) ≥ 2/3, hence 2 − 3·½log(2π) ≤ 0.
  have hpi : (4 : ℝ) ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
  have hlog4le : Real.log 4 ≤ Real.log (2 * Real.pi) := Real.log_le_log (by norm_num) hpi
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hDge : (2 : ℝ) / 3 ≤ Real.log (2 * Real.pi) / 2 := by
    linarith [hlog4le, hlog4, hl2]
  -- STEP 6: assemble everything linearly.
  rw [hlogM]
  linarith [hSN, hSe, hSa, hSb, hSc, h4a, h4b, h4c, h4e, hAid, hII,
    hlogeN, hloga0, hlogb0, hlogc0, hDge]

end CollatzChebyshev30
