import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.DescentDensityF2
import Propositio.NumberTheory.Collatz.DescentDensity78
import Propositio.NumberTheory.Collatz.DensityCount

/-!
# General-`k` lower density of Collatz-descending integers: `≥ |GoodK k| / 2^k`

`CollatzDensityCount.F_eq_count_over_pow` pins the density of `{n : DescBy n k}` at
`D(k)/2^k`, but only for `k ≤ 6` (each level needed a hand-built residue analysis).
Here we prove the lower-density half for **every** `k`, with NO per-level work:

  `descBy_density_general : p * 2^k < (GoodK k).card * q → density_bounded_below (DescBy · k) p q`

where `GoodK k = (Finset.range (2^k)).filter (fun r => descByB (r+2^k) k)` is the set of
descending residues mod `2^k` (so `(GoodK k).card = D k`).

The engine is `descBy_of_repr`: if the canonical representative `r + 2^k` of a residue
class descends within `k` steps, then **every** `n ≥ 2^k` in that class descends — a
direct consequence of the Terras affine form `2^j·T_iter n j = 3^(aCoef n j)·n + cCoef n j`
(`affine_form`) together with `coef_congr` (the coefficients depend only on `n mod 2^k`)
and the fact that `r + 2^k` is the **smallest** element `≥ 2^k` of its class, so the
descent inequality, once true there, is monotone in `n`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace CollatzDescentDensityGeneral

open TerrasDensity
open CollatzStoppingF3
open CollatzDensityCount
open CollatzDescentDensityF2
open CollatzDescentDensity78

attribute [local instance] Classical.propDecidable

/-- **Representative descent transfers to the whole class.** If the canonical lift
`r + 2^k` of the residue `r < 2^k` descends within `k` Terras steps, then every
`n ≥ 2^k` congruent to `r` mod `2^k` also descends within `k` steps. -/
theorem descBy_of_repr (k r n : Nat) (hr : r < 2 ^ k) (hn : 2 ^ k ≤ n)
    (hmod : n % 2 ^ k = r) (hrep : descByB (r + 2 ^ k) k = true) : DescBy n k := by
  -- representative descends at some step j ∈ [1,k]
  obtain ⟨j, hj1, hjk, hlt⟩ := (descByB_iff _ _).1 hrep
  -- residues agree mod 2^k, hence parity vectors agree up to level k, hence at level j
  have hrep_mod : (r + 2 ^ k) % 2 ^ k = r := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  have hmodk : n % 2 ^ k = (r + 2 ^ k) % 2 ^ k := by rw [hrep_mod, hmod]
  have hpvk : PVEq n (r + 2 ^ k) k := PVEq_of_mod_eq n (r + 2 ^ k) k hmodk
  have hpvj : PVEq n (r + 2 ^ k) j := fun i hi => hpvk i (lt_of_lt_of_le hi hjk)
  obtain ⟨hac, hcc⟩ := coef_congr j n (r + 2 ^ k) hpvj
  set a := aCoef (r + 2 ^ k) j with ha_def
  set c := cCoef (r + 2 ^ k) j with hc_def
  -- n ≥ r + 2^k  (the representative is the least element ≥ 2^k of the class)
  have hn_ge : r + 2 ^ k ≤ n := by
    have hdm := Nat.div_add_mod n (2 ^ k)
    rw [hmod] at hdm
    have hpos : 0 < n / 2 ^ k := Nat.div_pos hn (by positivity)
    have hge : 2 ^ k * 1 ≤ 2 ^ k * (n / 2 ^ k) := Nat.mul_le_mul_left _ hpos
    omega
  -- affine form at the representative, combined with hlt
  have h2jpos : 0 < 2 ^ j := by positivity
  have hkey : 3 ^ a * (r + 2 ^ k) + c < 2 ^ j * (r + 2 ^ k) := by
    have haff := affine_form (r + 2 ^ k) j
    have hmul : 2 ^ j * T_iter (r + 2 ^ k) j < 2 ^ j * (r + 2 ^ k) :=
      mul_lt_mul_of_pos_left hlt h2jpos
    rw [← ha_def, ← hc_def] at haff
    omega
  -- transfer the affine descent inequality from r+2^k to n (monotone in n)
  have hfinal : 3 ^ a * n + c < 2 ^ j * n := by
    have h1 : (3 : ℤ) ^ a * ((r : ℤ) + 2 ^ k) + c < 2 ^ j * ((r : ℤ) + 2 ^ k) := by
      have := hkey; push_cast at this ⊢; linarith
    have h2 : ((r : ℤ) + 2 ^ k) ≤ n := by exact_mod_cast hn_ge
    have hMpos : (0 : ℤ) < (r : ℤ) + 2 ^ k := by positivity
    have h3 : (3 : ℤ) ^ a ≤ 2 ^ j := by
      by_contra hcon
      simp only [not_le] at hcon
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hcon) (le_of_lt hMpos)]
    have hz : (3 : ℤ) ^ a * n + c < 2 ^ j * n := by
      nlinarith [h1, mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℤ) ≤ 2 ^ j - 3 ^ a)]
    have hcast : (3 : ℤ) ^ a * (n : ℤ) + c < 2 ^ j * (n : ℤ) := hz
    exact_mod_cast hcast
  -- conclude descent at step j for n
  refine ⟨j, hj1, hjk, ?_⟩
  have haffn := affine_form n j
  rw [hac, hcc] at haffn
  have : 2 ^ j * T_iter n j < 2 ^ j * n := by rw [haffn]; exact hfinal
  exact lt_of_mul_lt_mul_left this (Nat.zero_le _)

/-- The descending residues mod `2^k` (canonical-lift form). `(GoodK k).card = D k`. -/
def GoodK (k : Nat) : Finset Nat :=
  (Finset.range (2 ^ k)).filter (fun r => descByB (r + 2 ^ k) k)

/-- Lower density of a finite disjoint union of residue classes mod `m`, truncated
at threshold `t` (so each class `{n : n % m = r ∧ t ≤ n}` keeps lower density `≥ 1/m`). -/
theorem dbb_residue_set_t (m t : Nat) (p q : Nat) (hm : 0 < m) (hfrac : p * m < q) :
    ∀ S : Finset Nat, (∀ r ∈ S, r < m) →
      density_bounded_below (fun n => n % m ∈ S ∧ t ≤ n) (S.card * p) q := by
  intro S
  induction S using Finset.induction with
  | empty => intro _; exact ⟨0, fun N _ => by simp⟩
  | @insert r S hr ih =>
    intro hmem
    have hmem' : ∀ x ∈ S, x < m := fun x hx => hmem x (Finset.mem_insert_of_mem hx)
    have hrm : r < m := hmem r (Finset.mem_insert_self r S)
    have hr1 : density_bounded_below (fun n => n % m = r ∧ t ≤ n) p q :=
      dbb_residue_trunc m r p q t hm hrm hfrac
    have hdisj : ∀ n, ¬ ((n % m = r ∧ t ≤ n) ∧ (n % m ∈ S ∧ t ≤ n)) := by
      intro n hh
      exact hr (by rw [← hh.1.1]; exact hh.2.1)
    have hu := dbb_union hdisj hr1 (ih hmem')
    have hpred : (fun n => (n % m = r ∧ t ≤ n) ∨ (n % m ∈ S ∧ t ≤ n))
        = (fun n => n % m ∈ insert r S ∧ t ≤ n) := by
      funext n
      simp only [Finset.mem_insert, eq_iff_iff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    rw [hpred] at hu
    have hcard : (insert r S).card * p = p + S.card * p := by
      rw [Finset.card_insert_of_notMem hr]; ring
    rw [hcard]; exact hu

/-- **General-`k` lower density bound for the actual Terras descent set.**
For every `k ≥ 1` and every `p/q < |GoodK k| / 2^k`, the lower natural density of
`{n : DescBy n k}` (integers descending within `k` Terras steps) is at least `p/q`.
Since `(GoodK k).card = D k`, this is `density(DescBy · k) ≥ D(k)/2^k` for ALL `k`,
extending `F_eq_count_over_pow` (previously `k ≤ 6`). -/
theorem descBy_density_general (k : Nat) (p q : Nat)
    (hfrac : p * 2 ^ k < (GoodK k).card * q) :
    density_bounded_below (fun n => DescBy n k) p q := by
  have h2k : 0 < 2 ^ k := by positivity
  -- lower density of the good residue classes (truncated at 2^k)
  have hset : density_bounded_below (fun n => n % 2 ^ k ∈ GoodK k ∧ 2 ^ k ≤ n)
      ((GoodK k).card * p) (2 ^ k * p + 1) :=
    dbb_residue_set_t (2 ^ k) (2 ^ k) p (2 ^ k * p + 1) h2k (by rw [Nat.mul_comm p (2 ^ k)]; omega) (GoodK k)
      (fun r hr => by rw [GoodK, Finset.mem_filter, Finset.mem_range] at hr; exact hr.1)
  -- each such n descends within k steps
  have hsub : density_bounded_below (fun n => DescBy n k) ((GoodK k).card * p) (2 ^ k * p + 1) := by
    refine dbb_subset (fun n hh => ?_) hset
    obtain ⟨hmemn, hge⟩ := hh
    rw [GoodK, Finset.mem_filter, Finset.mem_range] at hmemn
    exact descBy_of_repr k (n % 2 ^ k) n (Nat.mod_lt _ h2k) hge rfl hmemn.2
  -- ratio monotonicity: p/q ≤ (GoodK k).card·p / (2^k·p+1)  ⟸  p·(2^k·p+1) ≤ (GoodK k).card·p·q
  refine dbb_mono (by omega) ?_ hsub
  have hcomm : p * 2 ^ k = 2 ^ k * p := Nat.mul_comm p (2 ^ k)
  have hbound : 2 ^ k * p + 1 ≤ (GoodK k).card * q := by omega
  calc p * (2 ^ k * p + 1) ≤ p * ((GoodK k).card * q) := Nat.mul_le_mul_left p hbound
    _ = (GoodK k).card * p * q := by ring

/-- `(GoodK k).card = D k`: the Finset count equals the corpus's List-based `D`. -/
theorem goodK_card_eq_D (k : Nat) : (GoodK k).card = D k := by
  unfold GoodK D
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
  congr 1
  apply List.filter_congr
  intro x _
  simp

set_option maxRecDepth 20000 in
/-- `(GoodK 10).card = 960` (kernel-`decide`, via the List-based `D 10`). -/
theorem goodK10_card : (GoodK 10).card = 960 := by
  rw [goodK_card_eq_D]; decide

/-- **Lower natural density of integers descending within 10 Terras steps ≥ 15/16.**
A new explicit bound beyond the previously-formalized 7/8 (`F_eq_count_over_pow`, k≤6),
obtained by instantiating `descBy_density_general` at `k = 10` (`D(10) = 960`,
`960/1024 = 15/16`). Axiom-clean. -/
theorem descBy10_density (p q : Nat) (hpq : 16 * p < 15 * q) :
    density_bounded_below (fun n => DescBy n 10) p q := by
  apply descBy_density_general 10 p q
  rw [goodK10_card]
  have h1024 : (2 : Nat) ^ 10 = 1024 := by norm_num
  rw [h1024]
  omega

set_option maxRecDepth 100000 in
/-- `(GoodK 13).card = 7825` (kernel-`decide`, via the List-based `D 13`). -/
theorem goodK13_card : (GoodK 13).card = 7825 := by
  rw [goodK_card_eq_D]; decide

/-- **Lower natural density of integers descending within 13 Terras steps ≥ 61/64.**
A strictly sharper bound than `descBy10_density` (15/16 = 0.9375): instantiating
`descBy_density_general` at `k = 13` gives `D(13) = 7825`, and
`7825 / 8192 = 0.9552… > 61/64 = 0.953125`. Axiom-clean (no `native_decide`).
From `64·p < 61·q` we get `8192·p = 128·(64·p) < 128·61·q = 7808·q < 7825·q`. -/
theorem descBy13_density (p q : Nat) (hpq : 64 * p < 61 * q) :
    density_bounded_below (fun n => DescBy n 13) p q := by
  apply descBy_density_general 13 p q
  rw [goodK13_card]
  have h8192 : (2 : Nat) ^ 13 = 8192 := by norm_num
  rw [h8192]
  omega

/-! ## Monotonicity of the descending-density ladder (all `k`, no computation) -/

/-- Each descending residue `r` mod `2^k` lifts to a descending residue mod `2^{k+1}`,
either `r` (b = false) or `r + 2^k` (b = true): the first `k` Terras steps depend only on
`r mod 2^k`, so both lifts still drop within `k ≤ k+1` steps (`descBy_of_repr`). -/
private theorem good_lift (k r : Nat) (hrmem : r ∈ GoodK k) (b : Bool) :
    r + (if b then 2 ^ k else 0) ∈ GoodK (k + 1) := by
  rw [GoodK, Finset.mem_filter, Finset.mem_range] at hrmem ⊢
  obtain ⟨hrlt, hrep⟩ := hrmem
  set r' := r + (if b then 2 ^ k else 0) with hr'
  have hr'lt : r' < 2 ^ (k + 1) := by
    rw [hr', pow_succ]; cases b <;> simp <;> omega
  refine ⟨hr'lt, ?_⟩
  set n := r' + 2 ^ (k + 1) with hn
  have hn_ge : 2 ^ k ≤ n := by rw [hn, pow_succ]; omega
  have hmod : n % 2 ^ k = r := by
    have key : n = r + 2 ^ k * (if b then 3 else 2) := by
      rw [hn, hr', pow_succ]; cases b <;> simp <;> ring
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have hdesc := descBy_of_repr k r n hrlt hn_ge hmod hrep
  exact (descByB_iff n (k + 1)).2
    (by obtain ⟨j, hj1, hjk, hlt⟩ := hdesc; exact ⟨j, hj1, by omega, hlt⟩)

/-- **Monotone density ladder.** `D(k+1) ≥ 2·D(k)` for *every* `k`: each descending
residue mod `2^k` lifts to two distinct descending residues mod `2^{k+1}` (`r` and
`r + 2^k`). Proved structurally with no `decide` — so unlike the per-level computed
counts there is no `k`-ceiling. Consequence (`D_density_mono`): the descending density
`D(k)/2^k` is non-decreasing, so the best computed lower bound (currently `61/64` at
`k = 13`) is valid for *all* larger step-budgets too. Axiom-clean. -/
theorem D_mono (k : Nat) : 2 * D k ≤ D (k + 1) := by
  rw [← goodK_card_eq_D k, ← goodK_card_eq_D (k + 1)]
  have hsub : GoodK k ∪ (GoodK k).image (· + 2 ^ k) ⊆ GoodK (k + 1) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · have := good_lift k x hx false; simpa using this
    · rw [Finset.mem_image] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have := good_lift k r hr true; simpa using this
  have hdisj : Disjoint (GoodK k) ((GoodK k).image (· + 2 ^ k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [GoodK, Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_image] at hb
    obtain ⟨r, _, hra⟩ := hb
    omega
  have hcardimg : ((GoodK k).image (· + 2 ^ k)).card = (GoodK k).card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hun : (GoodK k ∪ (GoodK k).image (· + 2 ^ k)).card = 2 * (GoodK k).card := by
    rw [Finset.card_union_of_disjoint hdisj, hcardimg]; ring
  calc 2 * (GoodK k).card = (GoodK k ∪ (GoodK k).image (· + 2 ^ k)).card := hun.symm
    _ ≤ (GoodK (k + 1)).card := Finset.card_le_card hsub

/-- **The descending density `D(k)/2^k` is non-decreasing in `k`** (cross-multiplied
form `D(k)·2^{k+1} ≤ D(k+1)·2^k`). Immediate from `D_mono`. -/
theorem D_density_mono (k : Nat) : D k * 2 ^ (k + 1) ≤ D (k + 1) * 2 ^ k := by
  calc D k * 2 ^ (k + 1) = 2 * D k * 2 ^ k := by rw [pow_succ]; ring
    _ ≤ D (k + 1) * 2 ^ k := Nat.mul_le_mul_right _ (D_mono k)

/-- Iterated monotonicity: `D(k₀)/2^{k₀} ≤ D(k)/2^k` for all `k ≥ k₀` (cross-multiplied
`D(k₀)·2^k ≤ D(k)·2^{k₀}`), by `Nat.le_induction` over `D_mono`. -/
theorem D_ratio_ge (k₀ : Nat) : ∀ k, k₀ ≤ k → D k₀ * 2 ^ k ≤ D k * 2 ^ k₀ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih =>
    calc D k₀ * 2 ^ (k + 1) = (D k₀ * 2 ^ k) * 2 := by rw [pow_succ]; ring
      _ ≤ (D k * 2 ^ k₀) * 2 := Nat.mul_le_mul_right _ ih
      _ = (2 * D k) * 2 ^ k₀ := by ring
      _ ≤ D (k + 1) * 2 ^ k₀ := Nat.mul_le_mul_right _ (D_mono k)

/-- **Lower density of integers descending within `k` Terras steps ≥ 61/64 for EVERY
`k ≥ 13`** — not just the computed level `k = 13`. Combines the computed bound
`D(13) = 7825` (`7825/8192 > 61/64`) with the monotone ladder `D_ratio_ge`, so the
sharpest computed floor propagates to all larger step-budgets with no further `decide`.
Axiom-clean. -/
theorem descBy_density_ge_61_64 (k : Nat) (hk : 13 ≤ k) (p q : Nat)
    (hpq : 64 * p < 61 * q) : density_bounded_below (fun n => DescBy n k) p q := by
  apply descBy_density_general k p q
  rw [goodK_card_eq_D]
  have hD13 : D 13 = 7825 := by rw [← goodK_card_eq_D]; exact goodK13_card
  have h1 : 8192 * p < 7825 * q := by omega
  have hr : 7825 * 2 ^ k ≤ D k * 8192 := by
    have h := D_ratio_ge 13 k hk
    rw [hD13] at h
    have h13 : (2 : Nat) ^ 13 = 8192 := by norm_num
    rwa [h13] at h
  have hpow : 0 < (2 : Nat) ^ k := pow_pos (by norm_num) k
  have hkey : p * 2 ^ k * 8192 < D k * q * 8192 := by
    calc p * 2 ^ k * 8192 = (8192 * p) * 2 ^ k := by ring
      _ < (7825 * q) * 2 ^ k := by gcongr
      _ = (7825 * 2 ^ k) * q := by ring
      _ ≤ (D k * 8192) * q := Nat.mul_le_mul_right _ hr
      _ = D k * q * 8192 := by ring
  exact lt_of_mul_lt_mul_right hkey (Nat.zero_le _)

/-! ## Sharper computed floor at `k = 15`: density `≥ 245/256`

The kernel-`decide` route is exhausted at `k = 13` (`2^15 = 32768` overflows the
kernel evaluator stack; and `D(14) = 2·D(13) = 15650` gives the *same* ratio
`0.9552`, no gain). The first strict improvement past `61/64` is at `k = 15`,
where `D(15) = 31473` and `31473/32768 ≈ 0.96048 > 245/256 = 0.957031`.

The single fact `goodK15_card` uses `native_decide` (the `2^15`-element census is
beyond kernel `decide`); it therefore carries `Lean.ofReduceBool` in its axiom set
— unlike the `≤ 61/64` results above, which stay kernel-axiom-clean. Everything
downstream (`descBy15_density`, `descBy_density_ge_245_256`) is then pure `omega`
+ the monotone ladder, inheriting only that one census axiom. -/

/-- `(GoodK 15).card = 31473` (`native_decide`; `2^15 = 32768`-element census,
beyond kernel `decide`). Carries `Lean.ofReduceBool`. -/
theorem goodK15_card : (GoodK 15).card = 31473 := by
  rw [goodK_card_eq_D]; native_decide

/-- **Lower natural density of integers descending within 15 Terras steps ≥ 245/256.**
Strictly sharper than `descBy13_density` (`61/64 = 0.953125`): `D(15) = 31473`,
`31473/32768 ≈ 0.96048 > 245/256 = 0.957031`. From `256·p < 245·q` we get
`32768·p = 128·(256·p) < 128·245·q = 31360·q < 31473·q`. Uses `goodK15_card`
(`native_decide`). -/
theorem descBy15_density (p q : Nat) (hpq : 256 * p < 245 * q) :
    density_bounded_below (fun n => DescBy n 15) p q := by
  apply descBy_density_general 15 p q
  rw [goodK15_card]
  have h32768 : (2 : Nat) ^ 15 = 32768 := by norm_num
  rw [h32768]
  omega

/-- **Lower density of integers descending within `k` Terras steps ≥ 245/256 for EVERY
`k ≥ 15`** — combines the computed `D(15) = 31473` with the monotone ladder `D_ratio_ge`,
so the sharper floor propagates to all larger step-budgets with no further census.
Inherits the single `Lean.ofReduceBool` axiom from `goodK15_card`. -/
theorem descBy_density_ge_245_256 (k : Nat) (hk : 15 ≤ k) (p q : Nat)
    (hpq : 256 * p < 245 * q) : density_bounded_below (fun n => DescBy n k) p q := by
  apply descBy_density_general k p q
  rw [goodK_card_eq_D]
  have hD15 : D 15 = 31473 := by rw [← goodK_card_eq_D]; exact goodK15_card
  have h1 : 32768 * p < 31473 * q := by omega
  have hr : 31473 * 2 ^ k ≤ D k * 32768 := by
    have h := D_ratio_ge 15 k hk
    rw [hD15] at h
    have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
    rwa [h15] at h
  have hpow : 0 < (2 : Nat) ^ k := pow_pos (by norm_num) k
  have hkey : p * 2 ^ k * 32768 < D k * q * 32768 := by
    calc p * 2 ^ k * 32768 = (32768 * p) * 2 ^ k := by ring
      _ < (31473 * q) * 2 ^ k := by gcongr
      _ = (31473 * 2 ^ k) * q := by ring
      _ ≤ (D k * 32768) * q := Nat.mul_le_mul_right _ hr
      _ = D k * q * 32768 := by ring
  exact lt_of_mul_lt_mul_right hkey (Nat.zero_le _)

end CollatzDescentDensityGeneral
