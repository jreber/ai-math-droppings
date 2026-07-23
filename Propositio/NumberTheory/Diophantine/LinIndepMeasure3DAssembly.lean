import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Propositio.NumberTheory.Diophantine.LinIndepMeasure3D
import Propositio.NumberTheory.Diophantine.LinIndepMeasure3DMain
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination

namespace LinIndepMeasure3D
open Real

private theorem cof_bound2 (H C : ℝ) (p q r s : ℤ)
    (hp : |(p:ℝ)| ≤ H) (hq : |(q:ℝ)| ≤ H) (hr : |(r:ℝ)| ≤ C) (hs : |(s:ℝ)| ≤ C) :
    |((p*r - q*s : ℤ):ℝ)| ≤ 2*H*C := by
  push_cast
  have h1 : |(p:ℝ)*r - q*s| ≤ |(p:ℝ)*r| + |(q:ℝ)*s| := by
    have h := abs_add_le ((p:ℝ)*r) (-(q*s));
    rwa [← sub_eq_add_neg, abs_neg] at h
  have h2 : |(p:ℝ)*r| ≤ H*C := by
    rw [abs_mul]
    exact mul_le_mul hp hr (abs_nonneg _) (le_trans (abs_nonneg _) hp)
  have h3 : |(q:ℝ)*s| ≤ H*C := by
    rw [abs_mul]
    exact mul_le_mul hq hs (abs_nonneg _) (le_trans (abs_nonneg _) hq)
  linarith

private theorem leadcof_bound2 (C : ℝ) (x1 x2 y1 y2 : ℤ)
    (hx1 : |(x1:ℝ)| ≤ C) (hx2 : |(x2:ℝ)| ≤ C) (hy1 : |(y1:ℝ)| ≤ C) (hy2 : |(y2:ℝ)| ≤ C) :
    |((x1*y2 - x2*y1 : ℤ):ℝ)| ≤ 2*C*C := by
  push_cast
  have h1 : |(x1:ℝ)*y2 - x2*y1| ≤ |(x1:ℝ)*y2| + |(x2:ℝ)*y1| := by
    have h := abs_add_le ((x1:ℝ)*y2) (-((x2:ℝ)*y1));
    rwa [← sub_eq_add_neg, abs_neg] at h
  have h2 : |(x1:ℝ)*y2| ≤ C*C := by
    rw [abs_mul]
    exact mul_le_mul hx1 hy2 (abs_nonneg _) (le_trans (abs_nonneg _) hx1)
  have h3 : |(x2:ℝ)*y1| ≤ C*C := by
    rw [abs_mul]
    exact mul_le_mul hx2 hy1 (abs_nonneg _) (le_trans (abs_nonneg _) hx2)
  linarith

private theorem budget_final (H A B Q A' ρ : ℝ) (n:ℕ) (cof1 cof2 : ℤ) (La Lb : ℝ)
    (hH0 : 0 < H) (hA0 : 0 < A) (hB0 : 0 < B) (hQ0 : 0 < Q) (hA'0 : 0 < A')
    (hcof1 : |(cof1:ℝ)| ≤ 2*H*(B*Q^(n+2))) (hcof2 : |(cof2:ℝ)| ≤ 2*H*(B*Q^(n+2)))
    (hLa : |La| ≤ A*ρ^n) (hLb : |Lb| ≤ A*ρ^n)
    (hstep : (Q*ρ)^n ≤ 1/(2*A'*H))
    (hAbound : 4*A*B*Q^2 ≤ A') :
    |(cof1:ℝ)| * |La| + |(cof2:ℝ)| * |Lb| ≤ 1/2 := by
  have e1 : |(cof1:ℝ)| * |La| ≤ (2*H*(B*Q^(n+2))) * (A*ρ^n) :=
    mul_le_mul hcof1 hLa (abs_nonneg _) (by positivity)
  have e2 : |(cof2:ℝ)| * |Lb| ≤ (2*H*(B*Q^(n+2))) * (A*ρ^n) :=
    mul_le_mul hcof2 hLb (abs_nonneg _) (by positivity)
  have ekey : (2*H*(B*Q^(n+2))) * (A*ρ^n) = 2*A*B*Q^2*H * (Q*ρ)^n := by
    rw [mul_pow, pow_add]; ring
  rw [ekey] at e1 e2
  have hstep2 : 2*A*B*Q^2*H * (Q*ρ)^n ≤ 2*A*B*Q^2*H * (1/(2*A'*H)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have hsimpl : 2*A*B*Q^2*H * (1/(2*A'*H)) = A*B*Q^2/A' := by
    field_simp
  rw [hsimpl] at hstep2
  have hfinal : A*B*Q^2/A' ≤ 1/4 := by
    rw [div_le_iff₀ hA'0]
    nlinarith [hAbound]
  linarith [e1, e2, hstep2, hfinal]

private theorem leadcof_final (H B Q A' s' : ℝ) (n : ℕ) (leadCof : ℤ)
    (hH0 : 0 < H) (hB0 : 0 < B) (hQ0 : 1 < Q) (hA'0 : 0 < A')
    (hleadcof : |(leadCof:ℝ)| ≤ 2*(B*Q^(n+2))*(B*Q^(n+2)))
    (hqn : (Q:ℝ)^n ≤ Q*(2*A')^s' * H^s') :
    |(leadCof:ℝ)| ≤ (2*B^2*Q^6*(2*A')^(2*s')) * H^(2*s') := by
  have hQn_nn : (0:ℝ) ≤ Q^n := by positivity
  have hRHS_nn : (0:ℝ) ≤ Q*(2*A')^s' * H^s' := by positivity
  have hsq : (Q:ℝ)^n * Q^n ≤ (Q*(2*A')^s' * H^s') * (Q*(2*A')^s' * H^s') :=
    mul_le_mul hqn hqn hQn_nn hRHS_nn
  have hexpand : (Q*(2*A')^s' * H^s') * (Q*(2*A')^s' * H^s')
      = Q^2 * (2*A')^(2*s') * H^(2*s') := by
    rw [show (2*s':ℝ) = s' + s' by ring, Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
    ring
  rw [hexpand] at hsq
  have hchain : |(leadCof:ℝ)| ≤ 2*(B*Q^(n+2))*(B*Q^(n+2)) := hleadcof
  have heq2 : 2*(B*Q^(n+2))*(B*Q^(n+2)) = 2*B^2*Q^4*(Q^n*Q^n) := by
    rw [pow_add]; ring
  rw [heq2] at hchain
  have hfin : 2*B^2*Q^4*(Q^n*Q^n) ≤ 2*B^2*Q^4*(Q^2 * (2*A')^(2*s') * H^(2*s')) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have heq3 : 2*B^2*Q^4*(Q^2 * (2*A')^(2*s') * H^(2*s')) = (2*B^2*Q^6*(2*A')^(2*s')) * H^(2*s') := by
    ring
  rw [heq3] at hfin
  linarith [hchain, hfin]

/-- **Generic index selection for the 3-D engine, in the convergent regime `Q·ρ<1`.**
This discharges the `budget` hypothesis of `linindep_measure_3d_of_budget` FROM the same kind
of basic rate hypotheses that drive the 1-D engine (`irrationality_measure_le`), by reusing
`IrrMeasureCombination.exists_good_index` with the *cleared* rate `ρ' := Q·ρ` (the genuine
budget-controlling rate: the cofactor in `linform3_det_atom` carries ONE test height and ONE
construction-row height, so the product against a small form scales as `H·(Qρ)ⁿ`, not `H·ρⁿ`).

This requires `Q·ρ < 1`: an EXTRA hypothesis beyond the 1-D theory's `ρ<1` alone. When it holds,
the assembly is completely unconditional and yields the explicit exponent
`μ = 2·log Q / log (Qρ)⁻¹` (sharper than the naive additive-budget exponent
`2 + 2·log Q/log ρ⁻¹` documented in `linindep_measure_3d_of_budget`'s header, because this
index selection balances the genuinely divergent rate `Qρ` directly rather than reusing the
1-D index formula unchanged).

CAVEAT (documented honestly, matches `docs/kb/failed/` 2026-06-23 findings): for the target
`(log2,log3)` weighted-diagonal / oSALIKHOV constructions, the cleared rates give `Q·ρ > 1`,
so `hQρ` is NOT satisfiable there — this theorem does not, by itself, produce a finite
`μ(log₂3)`. It completes the *abstract engine assembly* (the index-selection + determinant
lower-bound wiring identified as the residual gap in the frontier notes) and is directly usable
by any FUTURE 3-D construction whose cleared rates satisfy `Q·ρ<1`. -/
theorem linindep_measure_3d_of_rates
    (u v : ℝ) (a0 a1 a2 : ℕ → ℤ) (A B ρ Q : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hQ : 1 < Q)
    (hQρ : Q * ρ < 1)
    (hsmall : ∀ n, |(a0 n : ℝ) + a1 n * u + a2 n * v| ≤ A * ρ ^ n)
    (hcoef1 : ∀ n, |(a1 n : ℝ)| ≤ B * Q ^ n)
    (hcoef2 : ∀ n, |(a2 n : ℝ)| ≤ B * Q ^ n)
    (hdet3 : ∀ n : ℕ,
      a0 n * (a1 (n+1) * a2 (n+2) - a2 (n+1) * a1 (n+2))
        - a1 n * (a0 (n+1) * a2 (n+2) - a2 (n+1) * a0 (n+2))
        + a2 n * (a0 (n+1) * a1 (n+2) - a1 (n+1) * a0 (n+2)) ≠ 0) :
    ∃ C > 0, ∀ q s t : ℤ, ¬ (q = 0 ∧ s = 0 ∧ t = 0) →
      C / (((max (max |q| |s|) |t| : ℤ) : ℝ)) ^ (2 * (Real.log Q / Real.log (Q*ρ)⁻¹))
        ≤ |(q : ℝ) + s * u + t * v| := by
  have hQ0 : (0:ℝ) < Q := lt_trans one_pos hQ
  set ρ' : ℝ := Q * ρ with hρ'def
  have hρ'0 : 0 < ρ' := by rw [hρ'def]; positivity
  have hρ'1 : ρ' < 1 := hQρ
  set A' : ℝ := 8 * A * B * Q ^ 2 + 1 with hA'def
  have hA'pos : 0 < A' := by rw [hA'def]; positivity
  have hAbound : 4 * A * B * Q^2 ≤ A' := by
    rw [hA'def]; nlinarith [mul_pos (mul_pos hA hB) (pow_pos hQ0 2)]
  have hA'ge1 : 1 ≤ A' := by
    rw [hA'def]
    have h8ABQ2 : 0 ≤ 8 * A * B * Q^2 := by positivity
    linarith
  set s' : ℝ := Real.log Q / Real.log ρ'⁻¹ with hs'def
  have hs'pos : 0 < s' := by
    rw [hs'def]
    have hinv1 : 1 < ρ'⁻¹ := by rw [one_lt_inv_iff₀]; exact ⟨hρ'0, hρ'1⟩
    exact div_pos (Real.log_pos hQ) (Real.log_pos hinv1)
  set K : ℝ := 2 * B^2 * Q^6 * (2*A')^(2*s') with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hp : 0 < (2*A')^(2*s') := Real.rpow_pos_of_pos (by positivity) _
    positivity
  apply linindep_measure_3d_of_budget u v K (2*s') hKpos
  intro q s t hqst
  set H : ℝ := (((max (max |q| |s|) |t| : ℤ) : ℝ)) with hHdef
  have hH1 : (1 : ℝ) ≤ H := by
    rw [hHdef]
    have : (1 : ℤ) ≤ max (max |q| |s|) |t| := by
      rcases not_and_or.mp hqst with h | h
      · exact le_trans (Int.one_le_abs h) (le_trans (le_max_left _ _) (le_max_left _ _))
      · rcases not_and_or.mp h with h | h
        · exact le_trans (Int.one_le_abs h) (le_trans (le_max_right _ _) (le_max_left _ _))
        · exact le_trans (Int.one_le_abs h) (le_max_right _ _)
    exact_mod_cast this
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hqH : |(q:ℝ)| ≤ H := by
    rw [hHdef]; exact_mod_cast (le_trans (le_max_left _ _) (le_max_left _ _) : |q| ≤ max (max |q| |s|) |t|)
  have hsH : |(s:ℝ)| ≤ H := by
    rw [hHdef]; exact_mod_cast (le_trans (le_max_right _ _) (le_max_left _ _) : |s| ≤ max (max |q| |s|) |t|)
  have htH : |(t:ℝ)| ≤ H := by
    rw [hHdef]; exact_mod_cast (le_max_right _ _ : |t| ≤ max (max |q| |s|) |t|)
  have hAq : (1:ℝ) ≤ 2 * A' * H := by nlinarith [hA'ge1, hH1]
  obtain ⟨n, hin, hiin⟩ := IrrMeasureCombination.exists_good_index A' ρ' Q hA'pos hρ'0 hρ'1 hQ H hAq
  -- Turn `hin : A' * ρ'^n ≤ 1/(2*H)` into `hstep : (Q*ρ)^n ≤ 1/(2*A'*H)`.
  have hstep : (Q*ρ)^n ≤ 1/(2*A'*H) := by
    rw [← hρ'def]
    rw [le_div_iff₀ (by positivity)]
    have h1 : A' * ρ'^n * (2*H) ≤ (1/(2*H)) * (2*H) :=
      mul_le_mul_of_nonneg_right hin (by positivity)
    rw [div_mul_cancel₀] at h1
    · nlinarith [h1]
    · positivity
  -- Uniform monotone bounds across the three rows n, n+1, n+2.
  have hQpow_mono : ∀ i j : ℕ, i ≤ j → (Q:ℝ)^i ≤ Q^j := fun i j hij => pow_le_pow_right₀ (le_of_lt hQ) hij
  have hρpow_mono : ∀ i j : ℕ, i ≤ j → (ρ:ℝ)^j ≤ ρ^i :=
    fun i j hij => pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) hij
  have hcoefB1 : ∀ k, k ≤ n+2 → |(a1 k:ℝ)| ≤ B*Q^(n+2) := by
    intro k hk
    calc |(a1 k:ℝ)| ≤ B*Q^k := hcoef1 k
      _ ≤ B*Q^(n+2) := mul_le_mul_of_nonneg_left (hQpow_mono k (n+2) hk) (le_of_lt hB)
  have hcoefB2 : ∀ k, k ≤ n+2 → |(a2 k:ℝ)| ≤ B*Q^(n+2) := by
    intro k hk
    calc |(a2 k:ℝ)| ≤ B*Q^k := hcoef2 k
      _ ≤ B*Q^(n+2) := mul_le_mul_of_nonneg_left (hQpow_mono k (n+2) hk) (le_of_lt hB)
  have hPhiA : ∀ k, n ≤ k → |(a0 k : ℝ) + a1 k * u + a2 k * v| ≤ A*ρ^n := by
    intro k hk
    calc |(a0 k : ℝ) + a1 k * u + a2 k * v| ≤ A*ρ^k := hsmall k
      _ ≤ A*ρ^n := mul_le_mul_of_nonneg_left (hρpow_mono n k hk) (le_of_lt hA)
  have hD := hdet3 n
  rcases det_pair_lower_bound u v (a0 n) (a1 n) (a2 n) (a0 (n+1)) (a1 (n+1)) (a2 (n+1))
    (a0 (n+2)) (a1 (n+2)) (a2 (n+2)) q s t hqst hD with hBC | hAC | hAB
  · -- pair {B,C}: rows n+1, n+2
    refine ⟨a1 (n+1) * a2 (n+2) - a2 (n+1) * a1 (n+2),
      t * a1 (n+2) - s * a2 (n+2), s * a2 (n+1) - t * a1 (n+1),
      (a0 (n+1):ℝ) + a1 (n+1) * u + a2 (n+1) * v,
      (a0 (n+2):ℝ) + a1 (n+2) * u + a2 (n+2) * v, hBC, ?_, ?_⟩
    · exact budget_final H A B Q A' ρ n _ _ _ _ hH0 hA hB hQ0 hA'pos
        (cof_bound2 H (B*Q^(n+2)) t s (a1 (n+2)) (a2 (n+2)) htH hsH (hcoefB1 (n+2) (by omega)) (hcoefB2 (n+2) (by omega)))
        (cof_bound2 H (B*Q^(n+2)) s t (a2 (n+1)) (a1 (n+1)) hsH htH (hcoefB2 (n+1) (by omega)) (hcoefB1 (n+1) (by omega)))
        (hPhiA (n+1) (by omega)) (hPhiA (n+2) (by omega)) hstep hAbound
    · exact leadcof_final H B Q A' s' n _ hH0 hB hQ hA'pos
        (leadcof_bound2 (B*Q^(n+2)) (a1 (n+1)) (a2 (n+1)) (a1 (n+2)) (a2 (n+2))
          (hcoefB1 (n+1) (by omega)) (hcoefB2 (n+1) (by omega)) (hcoefB1 (n+2) (by omega)) (hcoefB2 (n+2) (by omega)))
        hiin
  · -- pair {A,C}: rows n, n+2
    refine ⟨a1 n * a2 (n+2) - a2 n * a1 (n+2),
      t * a1 (n+2) - s * a2 (n+2), s * a2 n - t * a1 n,
      (a0 n:ℝ) + a1 n * u + a2 n * v,
      (a0 (n+2):ℝ) + a1 (n+2) * u + a2 (n+2) * v, hAC, ?_, ?_⟩
    · exact budget_final H A B Q A' ρ n _ _ _ _ hH0 hA hB hQ0 hA'pos
        (cof_bound2 H (B*Q^(n+2)) t s (a1 (n+2)) (a2 (n+2)) htH hsH (hcoefB1 (n+2) (by omega)) (hcoefB2 (n+2) (by omega)))
        (cof_bound2 H (B*Q^(n+2)) s t (a2 n) (a1 n) hsH htH (hcoefB2 n (by omega)) (hcoefB1 n (by omega)))
        (hPhiA n (by omega)) (hPhiA (n+2) (by omega)) hstep hAbound
    · exact leadcof_final H B Q A' s' n _ hH0 hB hQ hA'pos
        (leadcof_bound2 (B*Q^(n+2)) (a1 n) (a2 n) (a1 (n+2)) (a2 (n+2))
          (hcoefB1 n (by omega)) (hcoefB2 n (by omega)) (hcoefB1 (n+2) (by omega)) (hcoefB2 (n+2) (by omega)))
        hiin
  · -- pair {A,B}: rows n, n+1
    refine ⟨a1 n * a2 (n+1) - a2 n * a1 (n+1),
      t * a1 (n+1) - s * a2 (n+1), s * a2 n - t * a1 n,
      (a0 n:ℝ) + a1 n * u + a2 n * v,
      (a0 (n+1):ℝ) + a1 (n+1) * u + a2 (n+1) * v, hAB, ?_, ?_⟩
    · exact budget_final H A B Q A' ρ n _ _ _ _ hH0 hA hB hQ0 hA'pos
        (cof_bound2 H (B*Q^(n+2)) t s (a1 (n+1)) (a2 (n+1)) htH hsH (hcoefB1 (n+1) (by omega)) (hcoefB2 (n+1) (by omega)))
        (cof_bound2 H (B*Q^(n+2)) s t (a2 n) (a1 n) hsH htH (hcoefB2 n (by omega)) (hcoefB1 n (by omega)))
        (hPhiA n (by omega)) (hPhiA (n+1) (by omega)) hstep hAbound
    · exact leadcof_final H B Q A' s' n _ hH0 hB hQ hA'pos
        (leadcof_bound2 (B*Q^(n+2)) (a1 n) (a2 n) (a1 (n+1)) (a2 (n+1))
          (hcoefB1 n (by omega)) (hcoefB2 n (by omega)) (hcoefB1 (n+1) (by omega)) (hcoefB2 (n+1) (by omega)))
        hiin

end LinIndepMeasure3D
