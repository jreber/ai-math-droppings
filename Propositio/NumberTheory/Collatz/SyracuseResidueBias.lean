import Propositio.NumberTheory.Collatz.SyracuseThreeAdicBias
import Propositio.NumberTheory.Collatz.SyracuseValuationDistribution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The genuine 2:1 residue bias of the Syracuse map — Lean 4 (NEW, capstone)

This file is the **capstone** of the Syracuse 3-adic-bias arc.  Combining the two
already-proven pillars

* `SyracuseThreeAdicBias.Syr_mod_three_eq` — for odd `N`, the Syracuse residue mod `3`
  is `1` when `v₂(3N+1)` is even and `2` when it is odd, and
* `SyracuseValuationDistribution.card_valuation_eq` — the exact geometric count
  `#{N < 2^K : v₂(3N+1) = j} = 2^{K-j-1}` for `1 ≤ j ≤ K-1`,

we prove that among odd `N`, the Syracuse residue `2` occurs asymptotically **twice as
often** as the residue `1`:

    A(K) / B(K)  →  2     (K → ∞),

where `A(K)` (resp. `B(K)`) counts odd `N < 2^K` whose Syracuse image is `≡ 2` (resp.
`≡ 1`) mod `3`.  This is the genuine `2:1` bias driving Tao's Syracuse-distribution
heuristic, here proved as an honest limit (the finite counts differ from the clean
`2/3 : 1/3` split by a bounded `±1` boundary term, which is negligible against the
`2^{K-1}` growth).

## Main results

* `Aodd_add_Bodd`        — exact total: `A(K) + B(K) = 2^{K-1}`  (every odd `N` has
                           residue `1` or `2`).
* `residue_bias_two_to_one` — **HEADLINE**: `A(K)/B(K) → 2`.

All `sorry`-free and axiom-clean.
-/

namespace SyracuseResidueBias

open Finset Filter Topology
open SyracuseThreeAdicBias SyracuseValuationDistribution
open scoped BigOperators

/-- `3N+1` is even iff `N` is odd. -/
theorem two_dvd_iff_odd (N : ℕ) : 2 ∣ 3 * N + 1 ↔ Odd N := by
  rw [Nat.odd_iff, Nat.dvd_iff_mod_eq_zero]
  omega

/-- For odd `N` the valuation `v₂(3N+1)` is at least `1`; conversely `1 ≤ v N` forces
`N` odd.  (This is what makes `card_valuation_eq`, stated for all `N`, count only odd
`N` once `j ≥ 1`.) -/
theorem odd_iff_one_le_v (N : ℕ) : Odd N ↔ 1 ≤ v N := by
  have ha : (3 * N + 1) ≠ 0 := by omega
  unfold v
  rw [← padicValNat_dvd_iff_le ha, pow_one]
  exact (two_dvd_iff_odd N).symm

/-- Membership in the residue-`2` set, recast purely via the parity of the valuation:
for any `N`, (`N` odd and `Syr N ≡ 2`) ⟺ `v₂(3N+1)` is odd. -/
theorem memA_iff (N : ℕ) :
    (Odd N ∧ (Syr N : ZMod 3) = 2) ↔ Odd (v N) := by
  constructor
  · rintro ⟨hN, h2⟩
    rw [Syr_mod_three_eq N hN] at h2
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    unfold v at hodd
    rw [if_pos hodd] at h2
    exact absurd h2 (by decide)
  · intro hodd
    have hN : Odd N := (odd_iff_one_le_v N).mpr (by obtain ⟨k, hk⟩ := hodd; omega)
    unfold v at hodd
    refine ⟨hN, ?_⟩
    rw [Syr_mod_three_eq N hN, if_neg (Nat.not_even_iff_odd.mpr hodd)]

/-- Membership in the residue-`1` set, recast via the valuation: for any `N`,
(`N` odd and `Syr N ≡ 1`) ⟺ (`v₂(3N+1)` even and `≥ 1`). -/
theorem memB_iff (N : ℕ) :
    (Odd N ∧ (Syr N : ZMod 3) = 1) ↔ (Even (v N) ∧ 1 ≤ v N) := by
  constructor
  · rintro ⟨hN, h1⟩
    have hv1 : 1 ≤ v N := (odd_iff_one_le_v N).mp hN
    refine ⟨?_, hv1⟩
    rw [Syr_mod_three_eq N hN] at h1
    by_contra hev
    rw [Nat.not_even_iff_odd] at hev
    unfold v at hev
    rw [if_neg (Nat.not_even_iff_odd.mpr hev)] at h1
    exact absurd h1 (by decide)
  · rintro ⟨hev, hv1⟩
    have hN : Odd N := (odd_iff_one_le_v N).mpr hv1
    unfold v at hev
    refine ⟨hN, ?_⟩
    rw [Syr_mod_three_eq N hN, if_pos hev]

/-- Number of odd `N < 2^K` with Syracuse residue `2` (`⟺ v₂(3N+1)` odd). -/
noncomputable def Aodd (K : ℕ) : ℕ :=
  ((Finset.range (2 ^ K)).filter (fun N => Odd N ∧ (Syr N : ZMod 3) = 2)).card

/-- Number of odd `N < 2^K` with Syracuse residue `1` (`⟺ v₂(3N+1)` positive even). -/
noncomputable def Bodd (K : ℕ) : ℕ :=
  ((Finset.range (2 ^ K)).filter (fun N => Odd N ∧ (Syr N : ZMod 3) = 1)).card

/-- **Exact total.** Every odd `N` has Syracuse residue `1` or `2` (never `0`), so the
two counts partition the odd numbers below `2^K`:  `A(K) + B(K) = 2^{K-1}`. -/
theorem Aodd_add_Bodd (K : ℕ) (hK : 1 ≤ K) : Aodd K + Bodd K = 2 ^ (K - 1) := by
  unfold Aodd Bodd
  rw [← card_union_of_disjoint, ← filter_or]
  · -- the union predicate collapses to "N ≡ 1 mod 2" (i.e. Odd N), count 2^{K-1}
    have hcollapse :
        ((Finset.range (2 ^ K)).filter
          (fun N => (Odd N ∧ (Syr N : ZMod 3) = 2) ∨ (Odd N ∧ (Syr N : ZMod 3) = 1)))
          = (Finset.range (2 ^ K)).filter (fun N => N ≡ 1 [MOD 2]) := by
      apply filter_congr
      intro N _
      constructor
      · rintro (⟨hN, _⟩ | ⟨hN, _⟩) <;>
          · rw [Nat.ModEq]; rw [Nat.odd_iff] at hN; omega
      · intro h
        have hN : Odd N := by rw [Nat.odd_iff]; rw [Nat.ModEq] at h; omega
        have hr := Syr_mod_three_eq N hN
        by_cases hev : Even (padicValNat 2 (3 * N + 1))
        · exact Or.inr ⟨hN, by rw [hr, if_pos hev]⟩
        · exact Or.inl ⟨hN, by rw [hr, if_neg hev]⟩
    rw [hcollapse, ← Nat.count_eq_card_filter_range,
      Nat.count_modEq_card (2 ^ K) (by norm_num) 1]
    have hsplit : (2 : ℕ) ^ K = 2 ^ (K - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    split_ifs with h <;> omega
  · -- disjointness: residues 2 and 1 are different
    apply Finset.disjoint_left.2
    intro N hN2 hN1
    rw [Finset.mem_filter] at hN2 hN1
    exact absurd (hN2.2.2.symm.trans hN1.2.2) (by decide)

/-! ## Closed-form interior sums and the geometric lower bounds -/

/-- `∑_{i<m} 2^i = 2^m - 1`. -/
theorem sum_two_pow (m : ℕ) : ∑ i ∈ range m, (2 : ℕ) ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega

/-- `∑_{i<m} 2^{m-1-i} = 2^m - 1` (descending exponent). -/
theorem sum_two_pow_rev (m : ℕ) : ∑ i ∈ range m, (2 : ℕ) ^ (m - 1 - i) = 2 ^ m - 1 :=
  (Finset.sum_range_reflect (fun i => (2 : ℕ) ^ i) m).trans (sum_two_pow m)

/-- Interior odd-valuation count: number of `N < 2^K` with `v₂(3N+1)` odd and `< K`. -/
noncomputable def SA (K : ℕ) : ℕ :=
  ∑ j ∈ (range K).filter (fun j => Odd j), 2 ^ (K - j - 1)

/-- Interior even-valuation count: number of `N < 2^K` with `v₂(3N+1)` positive even
and `< K`. -/
noncomputable def SB (K : ℕ) : ℕ :=
  ∑ j ∈ (range K).filter (fun j => Even j ∧ 1 ≤ j), 2 ^ (K - j - 1)

/-- The even-valuation interior count equals `SB K` (sum of `card_valuation_eq` over even
`j` in `[1, K-1]`). -/
theorem interior_even_card (K : ℕ) :
    ((range (2 ^ K)).filter (fun N => Even (v N) ∧ 1 ≤ v N ∧ v N < K)).card = SB K := by
  unfold SB
  rw [Finset.card_eq_sum_card_fiberwise
      (f := v) (t := (range K).filter (fun j => Even j ∧ 1 ≤ j))
      (by
        intro N hN
        rw [Finset.mem_coe, Finset.mem_filter] at hN
        obtain ⟨_, hev, h1, hlt⟩ := hN
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨hlt, hev, h1⟩)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjK, hjev, hj1⟩ := hj
  rw [Finset.filter_filter]
  have hfiber : (range (2 ^ K)).filter (fun N => (Even (v N) ∧ 1 ≤ v N ∧ v N < K) ∧ v N = j)
      = (range (2 ^ K)).filter (fun N => v N = j) := by
    apply Finset.filter_congr
    intro N _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      refine ⟨⟨?_, ?_, ?_⟩, h⟩
      · rw [h]; exact hjev
      · rw [h]; exact hj1
      · rw [h]; exact hjK
  rw [hfiber, card_valuation_eq K j hj1 (by omega)]

/-- The odd-valuation interior count equals `SA K`. -/
theorem interior_odd_card (K : ℕ) :
    ((range (2 ^ K)).filter (fun N => Odd (v N) ∧ v N < K)).card = SA K := by
  unfold SA
  rw [Finset.card_eq_sum_card_fiberwise
      (f := v) (t := (range K).filter (fun j => Odd j))
      (by
        intro N hN
        rw [Finset.mem_coe, Finset.mem_filter] at hN
        obtain ⟨_, hodd, hlt⟩ := hN
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨hlt, hodd⟩)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjK, hjodd⟩ := hj
  have hj1 : 1 ≤ j := by obtain ⟨k, hk⟩ := hjodd; omega
  rw [Finset.filter_filter]
  have hfiber : (range (2 ^ K)).filter (fun N => (Odd (v N) ∧ v N < K) ∧ v N = j)
      = (range (2 ^ K)).filter (fun N => v N = j) := by
    apply Finset.filter_congr
    intro N _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      refine ⟨⟨?_, ?_⟩, h⟩
      · rw [h]; exact hjodd
      · rw [h]; exact hjK
  rw [hfiber, card_valuation_eq K j hj1 (by omega)]

/-- **Lower bound on `B`.** The even-valuation interior is contained in the residue-`1`
odd set, so `SB K ≤ B(K)`. -/
theorem SB_le_Bodd (K : ℕ) : SB K ≤ Bodd K := by
  rw [← interior_even_card]
  unfold Bodd
  apply Finset.card_le_card
  intro N hN
  rw [Finset.mem_filter] at hN ⊢
  obtain ⟨hr, hev, h1, _⟩ := hN
  exact ⟨hr, (memB_iff N).mpr ⟨hev, h1⟩⟩

/-- **Lower bound on `A`.** `SA K ≤ A(K)`. -/
theorem SA_le_Aodd (K : ℕ) : SA K ≤ Aodd K := by
  rw [← interior_odd_card]
  unfold Aodd
  apply Finset.card_le_card
  intro N hN
  rw [Finset.mem_filter] at hN ⊢
  obtain ⟨hr, hodd, _⟩ := hN
  exact ⟨hr, (memA_iff N).mpr hodd⟩

/-- The two interior sums account for all of `[1, K-1]`:  `SA K + SB K + 1 = 2^{K-1}`.
(The `+1` is the single boundary odd `N < 2^K` whose valuation is `≥ K`.) -/
theorem SA_add_SB (K : ℕ) (_hK : 1 ≤ K) : SA K + SB K + 1 = 2 ^ (K - 1) := by
  unfold SA SB
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  have hterm : ∀ j ∈ range K,
      (if Odd j then (2 : ℕ) ^ (K - j - 1) else 0)
        + (if (Even j ∧ 1 ≤ j) then (2 : ℕ) ^ (K - j - 1) else 0)
        = (if 1 ≤ j then (2 : ℕ) ^ (K - j - 1) else 0) := by
    intro j _
    by_cases h1 : 1 ≤ j
    · rw [if_pos h1]
      rcases Nat.even_or_odd j with he | ho
      · rw [if_neg (Nat.not_odd_iff_even.mpr he), if_pos ⟨he, h1⟩, zero_add]
      · rw [if_pos ho, if_neg (fun hc => (Nat.not_even_iff_odd.mpr ho) hc.1), add_zero]
    · rw [if_neg h1, if_neg (fun ho => h1 (by obtain ⟨k, hk⟩ := ho; omega)),
        if_neg (fun hc => h1 hc.2), add_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hIco : (range K).filter (fun j => 1 ≤ j) = Finset.Ico 1 K := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hsimp : ∀ i ∈ range (K - 1),
      (2 : ℕ) ^ (K - (1 + i) - 1) = 2 ^ ((K - 1) - 1 - i) := by
    intro i _; congr 1; omega
  rw [Finset.sum_congr rfl hsimp, sum_two_pow_rev (K - 1)]
  have h2 : 0 < 2 ^ (K - 1) := pow_pos (by norm_num) (K - 1)
  omega

/-- **Upper bound on `B`.** `B(K) ≤ SB K + 1`.  (Combines the total `A+B = 2^{K-1}`,
the two lower bounds, and `SA + SB + 1 = 2^{K-1}`.) -/
theorem Bodd_le_SB_succ (K : ℕ) (hK : 1 ≤ K) : Bodd K ≤ SB K + 1 := by
  have h1 := SA_le_Aodd K
  have h2 := Aodd_add_Bodd K hK
  have h3 := SA_add_SB K hK
  omega

/-! ## The geometric limit `SB K / 2^{K-1} → 1/3` -/

theorem tendsto_SB_ratio :
    Tendsto (fun K => (SB K : ℝ) / 2 ^ (K - 1)) atTop (nhds (1 / 3)) := by
  -- (SB K : ℝ) / 2^{K-1} = ∑_{j even, 1≤j<K} (1/2)^j
  have heq : ∀ K, (SB K : ℝ) / 2 ^ (K - 1)
      = ∑ j ∈ (range K).filter (fun j => Even j ∧ 1 ≤ j), (1 / 2 : ℝ) ^ j := by
    intro K
    unfold SB
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjK, _, hj1⟩ := hj
    have hsplit : (2 : ℝ) ^ (K - 1) = 2 ^ (K - j - 1) * 2 ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.cast_pow, Nat.cast_ofNat, hsplit, div_pow, one_pow, div_mul_eq_div_div,
      div_self (by positivity : (2 : ℝ) ^ (K - j - 1) ≠ 0)]
  -- the masked series and its sum 1/3
  set c : ℕ → ℝ := fun j => if (Even j ∧ 1 ≤ j) then (1 / 2 : ℝ) ^ j else 0 with hc
  have hsumc : HasSum c (1 / 3) := by
    have hgeo : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ n) (4 / 3) := by
      have h := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      have he : (1 - 1 / 4 : ℝ)⁻¹ = 4 / 3 := by norm_num
      rwa [he] at h
    have hg2 : HasSum (fun n : ℕ => (1 / 4 : ℝ) * (1 / 4) ^ n) (1 / 3) := by
      have h := hgeo.mul_left (1 / 4)
      have he : (1 / 4 : ℝ) * (4 / 3) = 1 / 3 := by norm_num
      rwa [he] at h
    have hci : HasSum (fun n : ℕ => c (2 * n + 2)) (1 / 3) := by
      have hfun : (fun n : ℕ => c (2 * n + 2)) = (fun n : ℕ => (1 / 4 : ℝ) * (1 / 4) ^ n) := by
        funext n
        simp only [hc]
        rw [if_pos ⟨⟨n + 1, by ring⟩, by omega⟩,
          show 2 * n + 2 = 2 * (n + 1) from by ring, pow_mul,
          show ((1 : ℝ) / 2) ^ 2 = 1 / 4 from by norm_num, pow_succ]
        ring
      rw [hfun]; exact hg2
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
      intro a b h; simp only at h; omega
    have hzero : ∀ x ∉ Set.range (fun n : ℕ => 2 * n + 2), c x = 0 := by
      intro x hx
      simp only [hc]
      rw [if_neg]
      rintro ⟨hev, h1⟩
      apply hx
      obtain ⟨m, hm⟩ := hev
      exact ⟨m - 1, by show 2 * (m - 1) + 2 = x; omega⟩
    exact (hinj.hasSum_iff hzero).mp hci
  have hpart := hsumc.tendsto_sum_nat
  have hpsum : ∀ n, (∑ i ∈ range n, c i)
      = ∑ j ∈ (range n).filter (fun j => Even j ∧ 1 ≤ j), (1 / 2 : ℝ) ^ j := by
    intro n; rw [Finset.sum_filter]
  exact (tendsto_congr heq).mpr (hpart.congr hpsum)

/-! ## Headline: the 2:1 limit -/

/-- **HEADLINE — the genuine 2:1 Syracuse residue bias.**
Among odd `N < 2^K`, the count `A(K)` of Syracuse residue `2` divided by the count
`B(K)` of residue `1` tends to `2`:  residue `2` occurs asymptotically twice as often
as residue `1`. -/
theorem residue_bias_two_to_one :
    Tendsto (fun K => (Aodd K : ℝ) / (Bodd K)) atTop (nhds 2) := by
  have htpos : ∀ K, (0 : ℝ) < 2 ^ (K - 1) := fun K => by positivity
  have hKm1 : Tendsto (fun K : ℕ => K - 1) atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro b; exact ⟨b + 1, fun n hn => by omega⟩
  have h1t : Tendsto (fun K : ℕ => (1 : ℝ) / 2 ^ (K - 1)) atTop (nhds 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).comp hKm1
    refine hp.congr (fun K => ?_)
    simp only [Function.comp]
    rw [div_pow, one_pow]
  have hsb := tendsto_SB_ratio
  have hupper : Tendsto (fun K => (SB K : ℝ) / 2 ^ (K - 1) + 1 / 2 ^ (K - 1))
      atTop (nhds (1 / 3)) := by simpa using hsb.add h1t
  -- B/t → 1/3 by squeeze
  have hbt : Tendsto (fun K => (Bodd K : ℝ) / 2 ^ (K - 1)) atTop (nhds (1 / 3)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsb hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with K _
      gcongr
      exact_mod_cast SB_le_Bodd K
    · filter_upwards [eventually_ge_atTop 1] with K hK
      rw [← add_div]
      gcongr
      exact_mod_cast Bodd_le_SB_succ K hK
  -- A/t → 2/3
  have hat : Tendsto (fun K => (Aodd K : ℝ) / 2 ^ (K - 1)) atTop (nhds (2 / 3)) := by
    have hlim : Tendsto (fun K => 1 - (Bodd K : ℝ) / 2 ^ (K - 1)) atTop (nhds (1 - 1 / 3)) :=
      tendsto_const_nhds.sub hbt
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 from by norm_num] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hcast : (Aodd K : ℝ) + (Bodd K : ℝ) = 2 ^ (K - 1) := by
      exact_mod_cast Aodd_add_Bodd K hK
    rw [eq_comm, div_eq_iff (ne_of_gt (htpos K)), sub_mul, one_mul,
      div_mul_cancel₀ _ (ne_of_gt (htpos K))]
    linarith [hcast]
  -- A/B = (A/t)/(B/t) → (2/3)/(1/3) = 2
  have hfinal : Tendsto
      (fun K => ((Aodd K : ℝ) / 2 ^ (K - 1)) / ((Bodd K : ℝ) / 2 ^ (K - 1)))
      atTop (nhds ((2 / 3) / (1 / 3))) := hat.div hbt (by norm_num)
  rw [show (2 / 3 : ℝ) / (1 / 3) = 2 from by norm_num] at hfinal
  refine hfinal.congr (fun K => ?_)
  rw [div_div_div_cancel_right₀ (ne_of_gt (htpos K))]

end SyracuseResidueBias
