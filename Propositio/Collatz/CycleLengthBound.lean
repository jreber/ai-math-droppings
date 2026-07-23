import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Propositio.Collatz.CycleTelescope
import Propositio.NumberTheory.Diophantine.OSalikhovUnconditional

/-!
# Explicit length bound for Collatz `cc`-cycles from the unconditional measure of `log₂3`

## What is proved

Compose two independently proved pillars of the repository:

1. **The cycle side** (`CollatzCascadeCycles` + `CollatzCycleTelescope`): a cycle
   `cc^[L] n = n` of the fully compressed odd Collatz map, *started at its minimal
   element* `n` (hypothesis `hmin : ∀ i < L, n ≤ cc^[i] n`), satisfies the exact
   multiplicative identity `2^A · ∏ cc^[i] n = ∏ (3·cc^[i] n + 1)` with
   `A = S n L = Σ_{i<L} v₂(3·cc^[i] n + 1)`.  Since every factor obeys
   `3m + 1 ≤ (3 + 1/n)·m` for `m ≥ n`, this pins

       3^L < 2^A ≤ (3 + 1/n)^L,

   hence the **approximation quality** (`cycle_approx_quality`):

       0 < A/L − log₂3 ≤ 1/(3·n·log 2) ≤ 1/(2n).

   A long cycle through a large minimal element forces `A/L` to be an
   *extremely good* rational approximation to `log₂3`.

2. **The transcendence side** (`OSalikhovUnconditional`): the fully unconditional
   (Baker-free) effective irrationality measure of `log₂3`:  there are explicit
   constants `C > 0` and exponent `μ ≤ 61` with `C/q^μ ≤ |log₂3 − p/q|` for all
   integers `p, q` with `q` beyond an explicit threshold.

Feeding 1 into 2 yields the **main theorem** (`cycle_min_le_const_mul_length_pow`):
there is an explicit constant `K > 0` such that every `cc`-cycle of length `L ≥ 1`,
viewed at its minimal element `n`, satisfies

    n ≤ K · L^61.

Contrapositive (`cycle_length_pow_ge`): `K′·n ≤ L^61`, i.e. a cycle passing through
a large element must be **long**: `L ≥ (K′·n)^(1/61)`.  This turns the astronomical
verified lower bounds on a hypothetical cycle's minimal element into explicit
lower bounds on its length — polynomial in place of the trivial exponential
relation `n < 4^L` (also proved here, as `cycle_min_lt_four_pow`).

## Normalization notes

* `S n L` (from `CollatzCycleTelescope`) is definitionally the total valuation
  `Σ_{i<L} v₂(3·cc^[i] n + 1)`; `S_eq_sum` records this.
* The measure's side condition `1 ≤ 2·(A/log 2)·q` holds once `L ≥ L₀` for the
  explicit threshold `L₀ = ⌈log 2/(2A)⌉₊`; lengths `L < L₀` are absorbed into the
  constant via the elementary bound `n < 4^L` — no case is left out.
* The trivial cycle `n = 1` satisfies all conclusions, so no nontriviality
  hypothesis is needed anywhere in this file.

## Axiom audit

Everything in this file is sorry-free, and this file itself introduces no axiom
and no `decide`-family tactic.  The cycle-side results (`cycle_approx_quality`,
`cycle_approx_quality_abs`, `cycle_log_gap`, `cycle_min_le`, `cycle_min_lt_four_pow`,
`two_pow_le_rat_pow`, …) audit to exactly `[propext, Classical.choice, Quot.sound]`.
The two composition theorems (`cycle_min_le_const_mul_length_pow`,
`cycle_length_pow_ge`) additionally inherit the two `native_decide` finite-fact
axioms already present in
`OSalikhovUnconditional.osalikhov_logb23_measure_unconditional`
(`CollatzChebyshev30.census_1_to_8499`, `OSalikhovDenBound.DenIntN_bound_30_fin41`)
— the known, documented caveat of the unconditional measure; nothing new is
added here.
-/

namespace CollatzCycleLengthBound

open TerrasDensity (cc)
open CollatzCycleTelescope (S Steiner)

local notation "Odd" => TerrasDensity.Odd

/-! ## Elementary bookkeeping -/

/-- An odd natural is positive. -/
theorem one_le_of_odd {n : ℕ} (hodd : Odd n) : 1 ≤ n := by
  obtain ⟨k, hk⟩ := hodd; omega

/-- `S n L` is by definition the total 2-adic valuation `A` of the first `L` steps. -/
theorem S_eq_sum (n L : ℕ) :
    S n L = ∑ i ∈ Finset.range L, padicValNat 2 (3 * cc^[i] n + 1) := rfl

/-- Partial-product bound along any odd orbit: `2^{S n i} · cc^[i] n ≤ 4^i · n`.
Each step multiplies by `2^{aᵢ}·cc^[i+1]/cc^[i] = (3·cc^[i]+1)/cc^[i] ≤ 4`. -/
theorem pow_S_mul_iterate_le (n : ℕ) (hodd : Odd n) (i : ℕ) :
    2 ^ S n i * cc^[i] n ≤ 4 ^ i * n := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hstep := CollatzCascadeCycles.pow_v2_mul_iterate n i
    have hone := CollatzCascadeCycles.one_le_iterate n hodd i
    rw [CollatzCycleTelescope.S_succ, pow_add]
    calc 2 ^ S n i * 2 ^ padicValNat 2 (3 * cc^[i] n + 1) * cc^[i + 1] n
        = 2 ^ S n i * (2 ^ padicValNat 2 (3 * cc^[i] n + 1) * cc^[i + 1] n) := by
          rw [mul_assoc]
      _ = 2 ^ S n i * (3 * cc^[i] n + 1) := by rw [hstep]
      _ ≤ 2 ^ S n i * (4 * cc^[i] n) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (2 ^ S n i * cc^[i] n) := by ring
      _ ≤ 4 * (4 ^ i * n) := Nat.mul_le_mul_left _ ih
      _ = 4 ^ (i + 1) * n := by ring

/-- If the orbit stays `≥ n` (minimality) then `2^{S n i} ≤ 4^i`. -/
theorem pow_S_le (n : ℕ) (hodd : Odd n) (i : ℕ) (hge : n ≤ cc^[i] n) :
    2 ^ S n i ≤ 4 ^ i := by
  have h := pow_S_mul_iterate_le n hodd i
  have hn := one_le_of_odd hodd
  have h2 : 2 ^ S n i * n ≤ 4 ^ i * n :=
    le_trans (Nat.mul_le_mul_left _ hge) h
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

/-- Steiner-numerator bound at the minimal element: `Steiner n L ≤ 4^L − 3^L`. -/
theorem steiner_le (n L : ℕ) (hodd : Odd n) (hmin : ∀ i < L, n ≤ cc^[i] n) :
    Steiner n L ≤ 4 ^ L - 3 ^ L := by
  have key : ∀ i, i ≤ L → Steiner n i ≤ 4 ^ i - 3 ^ i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hih := ih (by omega)
      have hSi : 2 ^ S n i ≤ 4 ^ i := pow_S_le n hodd i (hmin i (by omega))
      have h34 : (3 : ℕ) ^ i ≤ 4 ^ i := Nat.pow_le_pow_left (by norm_num) i
      have hrec := CollatzCycleTelescope.Steiner_succ n i
      have h4 : (4 : ℕ) ^ (i + 1) = 4 * 4 ^ i := by rw [pow_succ]; ring
      have h3 : (3 : ℕ) ^ (i + 1) = 3 * 3 ^ i := by rw [pow_succ]; ring
      omega
  exact key L le_rfl

/-! ## The minimal element of an `L`-cycle is `< 4^L` (elementary patch bound) -/

/-- The minimal element of an `L`-step `cc`-cycle satisfies `n ≤ 4^L − 3^L`:
from the telescoped cycle equation `(2^A − 3^L)·n = Steiner n L` with
`2^A − 3^L ≥ 1` and `Steiner n L ≤ 4^L − 3^L`. -/
theorem cycle_min_le (n L : ℕ) (hodd : Odd n) (hL : 1 ≤ L) (hcyc : cc^[L] n = n)
    (hmin : ∀ i < L, n ≤ cc^[i] n) :
    n ≤ 4 ^ L - 3 ^ L := by
  have hident := CollatzCycleTelescope.cycle_telescope_identity n hodd L hL hcyc
  have hlt : (3 : ℕ) ^ L < 2 ^ S n L := by
    rw [S_eq_sum]
    exact CollatzCascadeCycles.cc_cycle_three_pow_lt n L hodd hcyc hL
  have hst := steiner_le n L hodd hmin
  have h2 : 3 ^ L * n + n ≤ 3 ^ L * n + Steiner n L := by
    calc 3 ^ L * n + n = (3 ^ L + 1) * n := by ring
      _ ≤ 2 ^ S n L * n := Nat.mul_le_mul_right n (by omega)
      _ = 3 ^ L * n + Steiner n L := hident
  exact le_trans (Nat.le_of_add_le_add_left h2) hst

/-- Weakened form: `n < 4^L`. -/
theorem cycle_min_lt_four_pow (n L : ℕ) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hmin : ∀ i < L, n ≤ cc^[i] n) :
    n < 4 ^ L := by
  have h := cycle_min_le n L hodd hL hcyc hmin
  have h3 : 0 < (3 : ℕ) ^ L := pow_pos (by norm_num) L
  have h34 : (3 : ℕ) ^ L ≤ 4 ^ L := Nat.pow_le_pow_left (by norm_num) L
  omega

/-! ## The sharp real upper bound `2^A ≤ (3 + 1/n)^L` -/

/-- **Sharp cycle upper bound.**  For a cycle started at its minimal element,
each factor of the exact product identity obeys `3m + 1 ≤ (3 + 1/n)·m`, so

    2^{S n L} ≤ (3 + 1/n)^L. -/
theorem two_pow_le_rat_pow (n L : ℕ) (hodd : Odd n) (hcyc : cc^[L] n = n)
    (hmin : ∀ i < L, n ≤ cc^[i] n) :
    (2 : ℝ) ^ S n L ≤ (3 + 1 / (n : ℝ)) ^ L := by
  have hn := one_le_of_odd hodd
  have hnposN : 0 < n := hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposN
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hident := CollatzCascadeCycles.cc_cycle_prod_identity n L hodd hcyc
  rw [← S_eq_sum] at hident
  have hidentR : (2 : ℝ) ^ S n L * ∏ i ∈ Finset.range L, (cc^[i] n : ℝ)
      = ∏ i ∈ Finset.range L, (3 * (cc^[i] n : ℝ) + 1) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hident
  have hPpos : (0 : ℝ) < ∏ i ∈ Finset.range L, (cc^[i] n : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h1 : 0 < cc^[i] n := CollatzCascadeCycles.one_le_iterate n hodd i
    exact_mod_cast h1
  have hprod_le : ∏ i ∈ Finset.range L, (3 * (cc^[i] n : ℝ) + 1)
      ≤ ∏ i ∈ Finset.range L, ((3 + 1 / (n : ℝ)) * (cc^[i] n : ℝ)) := by
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i hi
      have hge : (n : ℝ) ≤ (cc^[i] n : ℝ) := by
        exact_mod_cast hmin i (Finset.mem_range.mp hi)
      have hexpand : (3 + 1 / (n : ℝ)) * (cc^[i] n : ℝ)
          = 3 * (cc^[i] n : ℝ) + (cc^[i] n : ℝ) / (n : ℝ) := by
        field_simp
      have hquot : (1 : ℝ) ≤ (cc^[i] n : ℝ) / (n : ℝ) :=
        (le_div_iff₀ hnpos).mpr (by linarith)
      rw [hexpand]
      linarith
  have hsplit : ∏ i ∈ Finset.range L, ((3 + 1 / (n : ℝ)) * (cc^[i] n : ℝ))
      = (3 + 1 / (n : ℝ)) ^ L * ∏ i ∈ Finset.range L, (cc^[i] n : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hchain : (2 : ℝ) ^ S n L * ∏ i ∈ Finset.range L, (cc^[i] n : ℝ)
      ≤ (3 + 1 / (n : ℝ)) ^ L * ∏ i ∈ Finset.range L, (cc^[i] n : ℝ) := by
    rw [hidentR]
    rw [hsplit] at hprod_le
    exact hprod_le
  exact le_of_mul_le_mul_right hchain hPpos

/-! ## The logarithmic gap `0 < A·log 2 − L·log 3 ≤ L/(3n)` -/

/-- **Logarithmic form of the cycle constraint.**  `3^L < 2^A ≤ (3+1/n)^L` gives

    0 < A·log 2 − L·log 3 ≤ L·log(1 + 1/(3n)) ≤ L/(3n). -/
theorem cycle_log_gap (n L : ℕ) (hodd : Odd n) (hL : 1 ≤ L) (hcyc : cc^[L] n = n)
    (hmin : ∀ i < L, n ≤ cc^[i] n) :
    0 < (S n L : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ∧
      (S n L : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ≤ (L : ℝ) / (3 * (n : ℝ)) := by
  have hn := one_le_of_odd hodd
  have hnposN : 0 < n := hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposN
  constructor
  · have hlt : (3 : ℕ) ^ L < 2 ^ S n L := by
      rw [S_eq_sum]
      exact CollatzCascadeCycles.cc_cycle_three_pow_lt n L hodd hcyc hL
    have hltR : (3 : ℝ) ^ L < (2 : ℝ) ^ S n L := by exact_mod_cast hlt
    have hlog := Real.log_lt_log (by positivity) hltR
    rw [Real.log_pow, Real.log_pow] at hlog
    linarith
  · have hle := two_pow_le_rat_pow n L hodd hcyc hmin
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow, Real.log_pow] at hlog
    have hsplit : Real.log (3 + 1 / (n : ℝ))
        = Real.log 3 + Real.log (1 + 1 / (3 * (n : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (by positivity))]
      congr 1
      field_simp
    rw [hsplit, mul_add] at hlog
    have hbound : Real.log (1 + 1 / (3 * (n : ℝ))) ≤ 1 / (3 * (n : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 1 + 1 / (3 * (n : ℝ)) by positivity)
      linarith
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have hmul : (L : ℝ) * Real.log (1 + 1 / (3 * (n : ℝ)))
        ≤ (L : ℝ) * (1 / (3 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound hLnn
    have heq : (L : ℝ) * (1 / (3 * (n : ℝ))) = (L : ℝ) / (3 * (n : ℝ)) := by ring
    linarith

/-! ## Approximation quality: a cycle forces `A/L` within `1/(2n)` of `log₂3` -/

/-- **Approximation quality of a `cc`-cycle.**  For a cycle of length `L` at its
minimal element `n`, with `A = S n L` the total valuation,

    0 < A/L − log₂3 ≤ 1/(2n).

(The sharp constant is `1/(3·log 2) ≈ 0.4809`, rounded up to `1/2`.) -/
theorem cycle_approx_quality (n L : ℕ) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hmin : ∀ i < L, n ≤ cc^[i] n) :
    0 < (S n L : ℝ) / (L : ℝ) - Real.logb 2 3 ∧
      (S n L : ℝ) / (L : ℝ) - Real.logb 2 3 ≤ 1 / (2 * (n : ℝ)) := by
  obtain ⟨hpos, hup⟩ := cycle_log_gap n L hodd hL hcyc hmin
  have hn := one_le_of_odd hodd
  have hnposN : 0 < n := hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposN
  have hLposN : 0 < L := hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLposN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : (S n L : ℝ) / (L : ℝ) - Real.logb 2 3
      = ((S n L : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3) / ((L : ℝ) * Real.log 2) := by
    simp only [Real.logb]
    field_simp
  have hden : (0 : ℝ) < (L : ℝ) * Real.log 2 := mul_pos hLpos hlog2
  constructor
  · rw [hδ]
    exact div_pos hpos hden
  · rw [hδ, div_le_iff₀ hden]
    have hlog23 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have h9 := Real.log_two_gt_d9
      norm_num at h9 ⊢
      linarith
    have h1 : 1 / (2 * (n : ℝ)) * ((L : ℝ) * (2 / 3)) = (L : ℝ) / (3 * (n : ℝ)) := by
      field_simp
    have h2 : 1 / (2 * (n : ℝ)) * ((L : ℝ) * (2 / 3))
        ≤ 1 / (2 * (n : ℝ)) * ((L : ℝ) * Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlog23 hLpos.le
    linarith

/-- Absolute-value form: `|log₂3 − A/L| ≤ 1/(2n)`. -/
theorem cycle_approx_quality_abs (n L : ℕ) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hmin : ∀ i < L, n ≤ cc^[i] n) :
    |Real.logb 2 3 - (S n L : ℝ) / (L : ℝ)| ≤ 1 / (2 * (n : ℝ)) := by
  obtain ⟨h1, h2⟩ := cycle_approx_quality n L hodd hL hcyc hmin
  rw [abs_sub_comm, abs_of_pos h1]
  exact h2

/-! ## Main theorem: composition with the unconditional measure of `log₂3` -/

/-- **MAIN THEOREM — explicit polynomial bound on the minimal cycle element.**

There is an explicit constant `K > 0` (built from the constants of the
unconditional oSALIKHOV measure of `log₂3` — exponent `≤ 61`) such that every
cycle `cc^[L] n = n` (`L ≥ 1`, `n` odd) viewed at its minimal element
(`hmin`) satisfies

    n ≤ K · L^61.

Equivalently: the minimal element of a length-`L` `cc`-cycle is polynomially
bounded in `L` — an enormous strengthening of the elementary `n < 4^L`.
Proof: the cycle forces `|log₂3 − A/L| ≤ 1/(2n)` (`cycle_approx_quality_abs`);
the measure forbids `|log₂3 − A/L| < C/L^μ` (`μ ≤ 61`) once `L ≥ L₀`, so
`n ≤ L^μ/(2C) ≤ L^61/(2C)`; the finitely many lengths `L < L₀` are absorbed
into `K` via `n < 4^L`.  No nontriviality hypothesis is needed. -/
theorem cycle_min_le_const_mul_length_pow :
    ∃ K : ℝ, 0 < K ∧ ∀ n L : ℕ, Odd n → 1 ≤ L → cc^[L] n = n →
      (∀ i < L, n ≤ cc^[i] n) → (n : ℝ) ≤ K * (L : ℝ) ^ 61 := by
  obtain ⟨Q, ρ, C, hC, hρ0, hρ1, hQ, hexp, Am, hAm, hmeas⟩ :=
    OSalikhovUnconditional.osalikhov_logb23_measure_unconditional
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set L₀ : ℕ := ⌈Real.log 2 / (2 * Am)⌉₊ with hL₀def
  set K : ℝ := max (1 / (2 * C)) ((4 : ℝ) ^ L₀) with hKdef
  have hKC : 1 / (2 * C) ≤ K := le_max_left _ _
  have hK4 : (4 : ℝ) ^ L₀ ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity : (0 : ℝ) < (4 : ℝ) ^ L₀) hK4
  refine ⟨K, hKpos, ?_⟩
  intro n L hodd hL hcyc hmin
  have hn1 : 1 ≤ n := one_le_of_odd hodd
  have hnposN : 0 < n := hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposN
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL61 : (1 : ℝ) ≤ (L : ℝ) ^ 61 := one_le_pow₀ hL1R
  rcases Nat.lt_or_ge L L₀ with hcase | hcase
  · -- Small lengths `L < L₀`: absorb via the elementary bound `n < 4^L ≤ 4^L₀ ≤ K`.
    have hsmall := cycle_min_lt_four_pow n L hodd hL hcyc hmin
    have h1 : (n : ℝ) < (4 : ℝ) ^ L := by exact_mod_cast hsmall
    have h2 : (4 : ℝ) ^ L ≤ (4 : ℝ) ^ L₀ :=
      pow_le_pow_right₀ (by norm_num) hcase.le
    calc (n : ℝ) ≤ K := le_trans h1.le (le_trans h2 hK4)
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * (L : ℝ) ^ 61 := mul_le_mul_of_nonneg_left hL61 hKpos.le
  · -- Large lengths `L ≥ L₀`: the measure applies.
    have hceil : Real.log 2 / (2 * Am) ≤ (L₀ : ℝ) := Nat.le_ceil _
    have hL0L : (L₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcase
    have hfactor : (0 : ℝ) < 2 * (Am / Real.log 2) :=
      mul_pos two_pos (div_pos hAm hlog2)
    have hside : (1 : ℝ) ≤ 2 * (Am / Real.log 2) * (L : ℝ) := by
      have heq : 2 * (Am / Real.log 2) * (Real.log 2 / (2 * Am)) = 1 := by
        field_simp
      calc (1 : ℝ) = 2 * (Am / Real.log 2) * (Real.log 2 / (2 * Am)) := heq.symm
        _ ≤ 2 * (Am / Real.log 2) * (L : ℝ) :=
            mul_le_mul_of_nonneg_left (le_trans hceil hL0L) hfactor.le
    have hq1 : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    have hmeas' := hmeas ((S n L : ℕ) : ℤ) ((L : ℕ) : ℤ) hq1 (by push_cast; exact hside)
    push_cast at hmeas'
    have habs := cycle_approx_quality_abs n L hodd hL hcyc hmin
    set μ : ℝ := 1 + Real.log Q / Real.log ρ⁻¹ with hμdef
    -- hmeas' : C / (L:ℝ) ^ μ ≤ |log₂3 − A/L| ≤ 1/(2n)
    have hkey : C / (L : ℝ) ^ μ ≤ 1 / (2 * (n : ℝ)) := le_trans hmeas' habs
    have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le one_pos hL1R
    have hpowpos : (0 : ℝ) < (L : ℝ) ^ μ := Real.rpow_pos_of_pos hLpos μ
    have h2nC : 2 * (n : ℝ) * C ≤ (L : ℝ) ^ μ := by
      rw [div_le_div_iff₀ hpowpos (by positivity)] at hkey
      nlinarith [hkey]
    have hμ61 : μ ≤ (61 : ℝ) := by rw [hμdef]; linarith
    have hpow61 : (L : ℝ) ^ μ ≤ (L : ℝ) ^ (61 : ℕ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1R hμ61
      rwa [show ((61 : ℝ)) = ((61 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have hfin : 2 * (n : ℝ) * C ≤ (L : ℝ) ^ 61 := le_trans h2nC hpow61
    have hCne : C ≠ 0 := ne_of_gt hC
    calc (n : ℝ) = 2 * (n : ℝ) * C / (2 * C) := by field_simp
      _ ≤ (L : ℝ) ^ 61 / (2 * C) := div_le_div_of_nonneg_right hfin (by positivity)
      _ = 1 / (2 * C) * (L : ℝ) ^ 61 := by ring
      _ ≤ K * (L : ℝ) ^ 61 := mul_le_mul_of_nonneg_right hKC (by positivity)

/-- **Corollary — long cycles are forced by large minimal elements.**

There is an explicit `K′ > 0` with `K′·n ≤ L^61` for every `cc`-cycle of length
`L ≥ 1` at its minimal element `n`; i.e. `L ≥ (K′·n)^(1/61)`.  In particular,
for every bound `B`, all cycles with `L^61 < K′·B` have minimal element `> B` —
lengths admitting a cycle with `n_min ≤ B` are explicitly excluded below the
threshold `(K′·B)^(1/61)`. -/
theorem cycle_length_pow_ge :
    ∃ K : ℝ, 0 < K ∧ ∀ n L : ℕ, Odd n → 1 ≤ L → cc^[L] n = n →
      (∀ i < L, n ≤ cc^[i] n) → K * (n : ℝ) ≤ (L : ℝ) ^ 61 := by
  obtain ⟨K, hK, h⟩ := cycle_min_le_const_mul_length_pow
  refine ⟨1 / K, by positivity, ?_⟩
  intro n L hodd hL hcyc hmin
  have hle := h n L hodd hL hcyc hmin
  have h2 : 1 / K * (n : ℝ) ≤ 1 / K * (K * (L : ℝ) ^ 61) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have h3 : 1 / K * (K * (L : ℝ) ^ 61) = (L : ℝ) ^ 61 := by
    field_simp
  linarith

end CollatzCycleLengthBound
