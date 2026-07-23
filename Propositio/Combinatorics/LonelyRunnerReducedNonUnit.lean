/-
# Lonely Runner `k = 4`: the non-unit case of `ReducedBandPair`

`LonelyRunnerBandPairReduction` reduces the last open link of the honest `k = 4` Lonely
Runner Conjecture (`BandPair`) to the single-multiplier form `ReducedBandPair`:

    ∀ D r, 6 ≤ D → ¬ (D ∣ r) → ∃ k, inBand k D ∧ inBand (r·k) D.

This file proves `ReducedBandPair` **whenever `r` shares a common factor with `D`** (the
"non-unit" case, `¬ IsCoprime r D`). This is exactly the regime where the naive
pigeonhole / counting bound `2·|band| − D` can go negative — yet here it admits a *clean
explicit construction*, so no counting is needed.

## The construction

Write `g = gcd(r, D) ≥ 2`, `r = g·R₀`, `D = g·D₀` with `gcd(R₀, D₀) = 1` and `D₀ ≥ 2`.
The residue `r·k mod D` is always a multiple of `g`, namely `g·(R₀·k mod D₀)`, and — since
`R₀` is a unit mod `D₀` — we can steer `R₀·k mod D₀` to hit any target `c ∈ [0, D₀)`. Pick
`c = ⌊D₀/2⌋`, which lies in the `D₀`-band `[D₀/4, 3D₀/4]`, so `g·c` lies in the `D`-band.
Solving `R₀·k ≡ c (mod D₀)` fixes `k` only modulo `D₀`; because the step `D₀ ≤ D/2` is at
most the band's length, one representative of that class lands in the `D`-band `[D/4, 3D/4]`.
That representative is written down explicitly (`k = base + D₀·(⌊N/(4D₀)⌋ + 1)`), so the
whole proof is a direct verification — no pigeonhole, no `native_decide`, no `sorry`,
no `axiom`.

The remaining (genuinely hard) case of `ReducedBandPair` is the **unit** case
`IsCoprime r D`, which is the true crux of `k = 4` Lonely Runner.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseAComplete

namespace LonelyRunnerReducedNonUnit

open LonelyRunnerFourThreeResidualCaseAComplete

/-- **Non-unit case of `ReducedBandPair`.** If `D ≥ 6`, `D ∤ r`, and `r` is *not* coprime to
`D`, then some `k` puts both `k` and `r·k` in the middle band `[D/4, 3D/4]` mod `D`. -/
theorem reducedBandPair_nonunit (D : ℕ) (r : ℤ) (hD : 6 ≤ D)
    (hnd : ¬ ((D : ℤ) ∣ r)) (hnc : ¬ IsCoprime r (D : ℤ)) :
    ∃ k : ℤ, inBand k D ∧ inBand (r * k) D := by
  have hDpos : (0 : ℤ) < (D : ℤ) := by exact_mod_cast (by omega : 0 < D)
  -- `g = gcd(r, D)`.
  set g : ℕ := Int.gcd r (D : ℤ) with hg
  have hgpos : 0 < g := by
    rw [hg]; rw [Int.gcd_pos_iff]; right
    exact_mod_cast (by omega : (D : ℤ) ≠ 0)
  have hgZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
  -- `g ≠ 1` (that's what "not coprime" means), hence `g ≥ 2`.
  have hgne1 : g ≠ 1 := by
    rw [hg]; intro h; exact hnc (Int.isCoprime_iff_gcd_eq_one.mpr h)
  have hg2 : 2 ≤ g := by omega
  have hg2Z : (2 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg2
  -- Decompose `r = R₀·g`, `D = D₀·g`, `gcd(R₀, D₀) = 1`.
  obtain ⟨R₀, D₀, hcop0, hr_eq, hD_eq⟩ := Int.exists_gcd_one (m := r) (n := (D : ℤ)) hgpos
  rw [← hg] at hr_eq hD_eq
  -- `D₀ > 0`.
  have hD0pos : 0 < D₀ := by nlinarith [hD_eq, hDpos, hgZ]
  -- `D₀ ≥ 2`: else `D = g ∣ r`, contradicting `D ∤ r`.
  have hD0ge2 : 2 ≤ D₀ := by
    by_contra hlt
    have hD01 : D₀ = 1 := by omega
    apply hnd
    have hgr : (g : ℤ) ∣ r := ⟨R₀, by rw [hr_eq]; ring⟩
    rw [hD_eq, hD01, one_mul]; exact hgr
  -- `2·D₀ ≤ D` (the step `4·D₀` is at most `2·D`, the band's `4·length`).
  have hstep : 2 * D₀ ≤ (D : ℤ) := by rw [hD_eq]; nlinarith [hD0pos, hg2Z]
  -- Target residue `c = ⌊D₀/2⌋` in the `D₀`-band.
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ :
      ∃ c : ℤ, D₀ ≤ 4 * c ∧ 4 * c ≤ 3 * D₀ ∧ 0 ≤ c ∧ c < D₀ :=
    ⟨D₀ / 2, by omega, by omega, by omega, by omega⟩
  -- Bezout: `R₀` is a unit mod `D₀`.
  have hcop : IsCoprime R₀ D₀ := Int.isCoprime_iff_gcd_eq_one.mpr hcop0
  obtain ⟨a, b, hab⟩ := hcop
  -- `base` = canonical representative of `R₀⁻¹·c` mod `D₀`.
  set base : ℤ := (a * c) % D₀ with hbase
  have hbase_lo : 0 ≤ base := Int.emod_nonneg _ (ne_of_gt hD0pos)
  have hbase_hi : base < D₀ := Int.emod_lt_of_pos _ hD0pos
  -- `D₀ ∣ (base − a·c)`.
  have hb_mod : D₀ ∣ (base - a * c) := by
    have e : base = a * c - D₀ * ((a * c) / D₀) := by
      have := Int.emod_add_mul_ediv (a * c) D₀; rw [hbase]; linarith
    exact ⟨-((a * c) / D₀), by rw [e]; ring⟩
  -- `R₀·base ≡ c (mod D₀)`.
  have hRbc : D₀ ∣ (R₀ * base - c) := by
    have e1 : D₀ ∣ R₀ * (base - a * c) := Dvd.dvd.mul_left hb_mod R₀
    have e2 : D₀ ∣ (R₀ * (a * c) - c) := ⟨-(b * c), by linear_combination c * hab⟩
    have e3 : R₀ * base - c = R₀ * (base - a * c) + (R₀ * (a * c) - c) := by ring
    rw [e3]; exact dvd_add e1 e2
  have hmodc : (R₀ * base) % D₀ = c := by
    have hmeq : (R₀ * base) % D₀ = c % D₀ :=
      Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using hRbc.neg_right)
    rw [hmeq, Int.emod_eq_of_lt hc3 hc4]
  -- Placement: an explicit `k ≡ base (mod D₀)` in the `D`-band.
  set s : ℤ := 4 * D₀ with hs
  have hs_pos : 0 < s := by rw [hs]; positivity
  set N : ℤ := (D : ℤ) - 4 * base with hN
  have hNlo : 0 ≤ N % s := Int.emod_nonneg _ (ne_of_gt hs_pos)
  have hNhi : N % s < s := Int.emod_lt_of_pos _ hs_pos
  have hMrel : s * (N / s) = N - N % s := by
    have := Int.emod_add_mul_ediv N s; linarith
  set k : ℤ := base + D₀ * (N / s + 1) with hk
  -- `D₀ ∣ (k − base)`.
  have hkbase : D₀ ∣ (k - base) := ⟨N / s + 1, by rw [hk]; ring⟩
  -- `4·k = D − (N % s) + s`.
  have h4k : 4 * k = (D : ℤ) - N % s + s := by
    have e : 4 * k = 4 * base + s * (N / s) + s := by rw [hk, hs]; ring
    rw [e, hMrel, hN]; ring
  -- `k` is in `[0, D)` and in the `D`-band.
  have hk_lo : 0 ≤ k := by omega
  have hk_hi : k < (D : ℤ) := by
    have hs2D : s ≤ 2 * (D : ℤ) := by rw [hs]; linarith [hstep]
    omega
  have hkmod : k % (D : ℤ) = k := Int.emod_eq_of_lt hk_lo hk_hi
  have hbandk : (D : ℤ) ≤ 4 * k ∧ 4 * k ≤ 3 * (D : ℤ) := by
    have hs2D : s ≤ 2 * (D : ℤ) := by rw [hs]; linarith [hstep]
    constructor <;> omega
  -- `r·k mod D = g·c`.
  have hkm2 : (R₀ * k) % D₀ = c := by
    have hkc : D₀ ∣ (R₀ * k - c) := by
      have e1 : D₀ ∣ R₀ * (k - base) := Dvd.dvd.mul_left hkbase R₀
      have e3 : R₀ * k - c = R₀ * (k - base) + (R₀ * base - c) := by ring
      rw [e3]; exact dvd_add e1 hRbc
    have hmeq : (R₀ * k) % D₀ = c % D₀ :=
      Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using hkc.neg_right)
    rw [hmeq, Int.emod_eq_of_lt hc3 hc4]
  have hrkmod : (r * k) % (D : ℤ) = (g : ℤ) * c := by
    have erk : r * k = (g : ℤ) * (R₀ * k) := by rw [hr_eq]; ring
    have eD : (D : ℤ) = (g : ℤ) * D₀ := by rw [hD_eq]; ring
    rw [erk, eD, Int.mul_emod_mul_of_pos (R₀ * k) D₀ hgZ, hkm2]
  refine ⟨k, ?_, ?_⟩
  · -- `inBand k D`.
    unfold inBand; rw [hkmod]; exact hbandk
  · -- `inBand (r·k) D`.
    unfold inBand; rw [hrkmod, hD_eq]
    constructor
    · nlinarith [hc1, hgZ]
    · nlinarith [hc2, hgZ]

end LonelyRunnerReducedNonUnit

