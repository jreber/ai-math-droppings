import Propositio.Collatz.DescentDichotomy
import Propositio.Collatz.AlmostAllDescend
import Propositio.Collatz.TailDecayUncond
import Propositio.Collatz.BinomialTail
import Mathlib.Tactic

/-!
# The Everett–Terras "almost all integers descend" theorem — UNCONDITIONAL

`CollatzAlmostAllDescend.collatz_almost_all_descend` was stated conditional on the
power-gap input `hpow` (`2^k ≤ 3^{aCoef}` for non-descending lifts), which
`CollatzDescentDichotomy` reduced to the Baker-class `PowGap`.

This file removes that dependency. The key observation: `PowGap`'s full
`(3/2)^a` strength is only needed in the thin threshold band
`3^a < 2^k < 2·3^a` (i.e. `aCoef` exactly at `≈ k·log₃2`); those residues are
negligible by the same binary-entropy counting that powers the result. The
**elementary** descent (`2^k ≥ 2·3^a ⟹ descent`, gap `≥ 3^a`, no Diophantine
input) gives "non-descending ⟹ `aCoef ≥ minOdd k − 1`", and the tail at the
shifted threshold `minOdd k − 1` still decays (one extra central-binomial term).

Result: `collatz_almost_all_descend_uncond : Tendsto (fun k => β(k)/2^k) atTop (𝓝 0)`
with **no `PowGap`, no Baker, no `sorry`** — axiom-clean. This is the genuine
Everett–Terras theorem (Everett 1977; Terras 1976), which is Baker-free.
-/

open Filter Topology
open scoped BigOperators

namespace CollatzAlmostAllDescendUncond

open TerrasDensity CollatzDensityCount
open CollatzDescentDichotomy
open CollatzAlmostAllDescend
open CollatzNonDescentWeight (minOdd minOdd_le_of_two_pow_le two_pow_le_three_pow_minOdd)
open CollatzParityBijection (Q pvMap pvMap_injective Q_eq_iff_PVEq)

/-! ## §1  The elementary (Baker-free) descent dichotomy -/

/-- **Elementary descent dichotomy.**  A non-descending lift has `2^k ≤ 2·3^{aCoef}`.
Reuses the already-proved `cCoef_mul_bound`; the trivial gap `d > 3^a` (available
once `2·3^a < 2^k`) replaces the Diophantine `PowGap`. -/
theorem three_pow_ge_of_non_descent_elem (n k : Nat) (hn : 2 ^ k ≤ n)
    (hnd : n ≤ T_iter n k) : 2 ^ k ≤ 2 * 3 ^ (aCoef n k) := by
  set a := aCoef n k with ha
  set c := cCoef n k with hc
  have haf : 2 ^ k * T_iter n k = 3 ^ a * n + c := affine_form n k
  have h1 : 2 ^ k * n ≤ 3 ^ a * n + c := by
    have : 2 ^ k * n ≤ 2 ^ k * T_iter n k := Nat.mul_le_mul_left _ hnd
    omega
  have h2 : (c + 2 ^ k) * 2 ^ a ≤ 3 ^ a * 2 ^ k := cCoef_mul_bound n k
  by_contra hlt'
  rw [Nat.not_le] at hlt'   -- hlt' : 2 * 3 ^ a < 2 ^ k
  obtain ⟨d, hd, hd1⟩ : ∃ d, 2 ^ k = 3 ^ a + d ∧ 3 ^ a < d :=
    ⟨2 ^ k - 3 ^ a, by omega, by omega⟩
  have h2add : c * 2 ^ a + (3 ^ a + d) * 2 ^ a ≤ 3 ^ a * (3 ^ a + d) := by
    have e : (c + 2 ^ k) * 2 ^ a = c * 2 ^ a + 2 ^ k * 2 ^ a := by ring
    rw [e, hd] at h2; linarith [h2]
  have hcn : d * n ≤ c := by
    have e : 2 ^ k * n = 3 ^ a * n + d * n := by rw [hd]; ring
    rw [e] at h1; omega
  have hcnQ : d * n * 2 ^ a ≤ c * 2 ^ a := Nat.mul_le_mul_right _ hcn
  have hnlow : d * (3 ^ a + d) * 2 ^ a ≤ d * n * 2 ^ a := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
  have hbig' : (3 ^ a + d) * 2 ^ a * (d + 1) ≤ 3 ^ a * (3 ^ a + d) := by
    have hstep : d * (3 ^ a + d) * 2 ^ a + (3 ^ a + d) * 2 ^ a
        ≤ c * 2 ^ a + (3 ^ a + d) * 2 ^ a := by
      have := le_trans hnlow hcnQ; omega
    have hle := le_trans hstep h2add
    have efac : d * (3 ^ a + d) * 2 ^ a + (3 ^ a + d) * 2 ^ a
        = (3 ^ a + d) * 2 ^ a * (d + 1) := by ring
    rw [efac] at hle; exact hle
  have hposfac : 0 < 3 ^ a + d := by positivity
  have hcancel : 2 ^ a * (d + 1) ≤ 3 ^ a := by
    have hcomm : (3 ^ a + d) * (2 ^ a * (d + 1)) ≤ (3 ^ a + d) * 3 ^ a := by
      calc (3 ^ a + d) * (2 ^ a * (d + 1))
          = (3 ^ a + d) * 2 ^ a * (d + 1) := by ring
        _ ≤ 3 ^ a * (3 ^ a + d) := hbig'
        _ = (3 ^ a + d) * 3 ^ a := by ring
    exact Nat.le_of_mul_le_mul_left hcomm hposfac
  have hle : d + 1 ≤ 2 ^ a * (d + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- From the elementary descent conclusion `2^k ≤ 2·3^a`, the odd-step count is at
least `minOdd k − 1` (the threshold shifted down by one). -/
theorem minOdd_pred_le (k a : ℕ) (h : 2 ^ k ≤ 2 * 3 ^ a) : minOdd k - 1 ≤ a := by
  by_contra hlt
  rw [Nat.not_le] at hlt                -- a < minOdd k - 1
  have ha1 : a + 1 < minOdd k := by omega
  have h3 : 3 ^ (a + 1) < 2 ^ k := by
    rw [← Nat.not_le]
    intro hle; have := minOdd_le_of_two_pow_le k (a + 1) hle; omega
  have hcontra : 2 * 3 ^ a < 2 ^ k := by
    calc 2 * 3 ^ a ≤ 3 * 3 ^ a := Nat.mul_le_mul_right _ (by norm_num)
      _ = 3 ^ (a + 1) := by rw [pow_succ]; ring
      _ < 2 ^ k := h3
  omega

/-! ## §2  Heavy-tail count at an arbitrary threshold -/

/-- Length-`k` parity vectors with Hamming weight `≥ t`. -/
def heavySet' (k t : Nat) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun v => t ≤ weight v)

/-- The heavy count at threshold `t` equals the binomial upper tail (general `t`;
the `t = minOdd k` case is `heavy_card_eq_upperTail`). -/
theorem heavy_card_eq_upperTail' (k t : Nat) :
    (heavySet' k t).card = CollatzBinomialTail.upperTail k t := by
  unfold heavySet' CollatzBinomialTail.upperTail
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun v : Fin k → Bool => weight v) (t := Finset.Icc t k)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [← card_weight_eq k i]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hw⟩; exact hw
    · intro hw; exact ⟨by rw [hw]; exact hi.1, hw⟩
  · intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨hv.2, weight_le v⟩

/-! ## §3  `β(k) ≤ upperTail k (minOdd k − 1)` — unconditional -/

theorem beta_le_tail_pred (k : Nat) (_hk : 1 ≤ k) :
    beta k ≤ CollatzBinomialTail.upperTail k (minOdd k - 1) := by
  rw [beta_eq_badSet_card, ← heavy_card_eq_upperTail']
  apply Finset.card_le_card_of_injOn (pvMap k)
  · intro r hr
    rw [Finset.mem_coe, badSet, Finset.mem_filter] at hr
    have hfalse : descByB (r.val + 2 ^ k) k = false := hr.2
    have hge2k : 2 ^ k ≤ r.val + 2 ^ k := by omega
    have hnd : r.val + 2 ^ k ≤ T_iter (r.val + 2 ^ k) k :=
      le_T_iter_of_not_descByB _ k hfalse
    have helem : 2 ^ k ≤ 2 * 3 ^ (aCoef (r.val + 2 ^ k) k) :=
      three_pow_ge_of_non_descent_elem (r.val + 2 ^ k) k hge2k hnd
    have hge : minOdd k - 1 ≤ aCoef (r.val + 2 ^ k) k :=
      minOdd_pred_le k (aCoef (r.val + 2 ^ k) k) helem
    have hPV : Q k r.val = Q k (r.val + 2 ^ k) := by
      apply (Q_eq_iff_PVEq r.val (r.val + 2 ^ k) k).2
      apply CollatzDensityCount.PVEq_of_mod_eq; simp
    have hw : weight (pvMap k r) = aCoef (r.val + 2 ^ k) k := by
      unfold pvMap; rw [hPV, ← aCoef_eq_weight]
    rw [Finset.mem_coe, heavySet', Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hw]; exact hge⟩
  · intro a _ b _ hab; exact pvMap_injective k hab

/-! ## §4  The shifted-threshold tail still decays -/

theorem upperTail_minOdd_pred_decay :
    Tendsto (fun k => (CollatzBinomialTail.upperTail k (minOdd k - 1) : ℝ) / 2 ^ k)
      atTop (𝓝 0) := by
  -- term 1: C(k, minOdd k − 1)/2^k → 0 (sub-central + central_decay)
  have hc : Tendsto (fun k => (k.choose (minOdd k - 1) : ℝ) / 2 ^ k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity) (fun k => ?_) CollatzTailDecayUncond.central_decay
    gcongr
    exact_mod_cast Nat.choose_le_middle _ _
  -- term 2: existing minOdd-threshold decay
  have ht := CollatzTailDecayUncond.upperTail_minOdd_decay
  have hsum := hc.add ht
  rw [add_zero] at hsum
  apply hsum.congr'
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{k | 1 ≤ k}, Filter.eventually_atTop.mpr ⟨1, fun k hk => hk⟩, ?_⟩
  intro k hk
  have hm1 : 1 ≤ minOdd k := by
    rcases Nat.eq_zero_or_pos (minOdd k) with h0 | h
    · exfalso
      have hsp := two_pow_le_three_pow_minOdd k
      rw [h0, pow_zero] at hsp
      have : 2 ≤ 2 ^ k := by
        calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    · exact h
  have hmk : minOdd k ≤ k := minOdd_le_of_two_pow_le k k (Nat.pow_le_pow_left (by norm_num) k)
  have hsplit : CollatzBinomialTail.upperTail k (minOdd k - 1)
      = k.choose (minOdd k - 1) + CollatzBinomialTail.upperTail k (minOdd k) := by
    unfold CollatzBinomialTail.upperTail
    have hins : Finset.Icc (minOdd k - 1) k
        = insert (minOdd k - 1) (Finset.Icc (minOdd k) k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : (minOdd k - 1) ∉ Finset.Icc (minOdd k) k := by
      simp only [Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert hnm]
  show (k.choose (minOdd k - 1) : ℝ) / 2 ^ k
      + (CollatzBinomialTail.upperTail k (minOdd k) : ℝ) / 2 ^ k
      = (CollatzBinomialTail.upperTail k (minOdd k - 1) : ℝ) / 2 ^ k
  rw [hsplit]; push_cast; ring

/-! ## §5  HEADLINE — the unconditional Everett–Terras capstone -/

/-- **`collatz_almost_all_descend_uncond` (UNCONDITIONAL HEADLINE).**
The Everett–Terras "almost all integers descend" theorem with NO power-gap / Baker
hypothesis: the density of residues mod `2^k` whose lift fails to descend within `k`
Terras steps tends to `0`. Axiom-clean. -/
theorem collatz_almost_all_descend_uncond :
    Tendsto (fun k => (beta k : ℝ) / 2 ^ k) atTop (𝓝 0) := by
  have htail := upperTail_minOdd_pred_decay
  have hbound : ∀ k, beta k ≤ CollatzBinomialTail.upperTail k (minOdd k - 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have h0 : CollatzBinomialTail.upperTail 0 (minOdd 0 - 1) = 1 := by decide
      rw [h0]
      calc beta 0 ≤ 2 ^ 0 := by unfold beta; omega
        _ = 1 := by norm_num
    · exact beta_le_tail_pred k hk1
  apply squeeze_zero (fun k => by positivity) (fun k => ?_) htail
  gcongr
  exact_mod_cast hbound k

end CollatzAlmostAllDescendUncond
