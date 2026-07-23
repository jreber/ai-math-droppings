/-
# Lonely Runner `k = 4`: the *unit* band lemma `ReducedBandPairUnit` — the final crux

`LonelyRunnerBandPairRemaining.caseA_of_unit` reduced the *entire* remaining gap of the
honest `k = 4` Lonely Runner Conjecture to the single elementary residue statement
`ReducedBandPairUnit`:

    ∀ D r, 6 ≤ D → ¬ (D ∣ r) → IsCoprime r D → ∃ k, inBand k D ∧ inBand (r·k) D,

i.e. *for every modulus `D ≥ 6` and every unit `r` mod `D`, the middle band `[D/4, 3D/4]`
meets its preimage under `k ↦ r·k`.*

This file proves that statement **unconditionally**, by an explicit closed-form construction
(no pigeonhole — the naive counting bound `2·|band| − D` is negative for `D ≡ 1 mod 4`).

## The construction

Write `c₀ = r mod D ∈ [1, D)`. Using the band's negation symmetry (`inBand x ↔ inBand (−x)`)
replace `c₀` by `c = min(c₀, D − c₀)`, so `1 ≤ c` and `2c ≤ D`. It then suffices to find `n`
with `n` and `c·n` both in the band.

Pick an *odd* multiplier `o` (`o = c` if `c` is odd, else `o = c − 1`) and set
`n = ⌊(o·D + c)/(2c)⌋`. Writing `o·D + c = 2c·n + s` (`0 ≤ s < 2c`):

* Because `o` is odd, `o·D ≡ D (mod 2D)`, so `c·n ≡ (D + c − s)/2 (mod D)`, and
  `2c ≤ D` forces this residue into `(D/4, 3D/4]` — the band, for *any* odd `o`.
* Choosing `o ≈ c` centres `n` itself near `D/2`, landing `n` in the band; the two bounds
  become `c·D + 2c ≤ 2·o·D` and `2·o·D + 2c ≤ 3·c·D`, discharged per parity of `c`.

The single boundary case `c = 2` (where `n ≈ D/4` sits exactly on the band edge) is handled
separately by `n = ⌈D/4⌉`.

Everything is honest: no `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseAComplete
import Propositio.Combinatorics.LonelyRunnerBandPairReduction
import Propositio.Combinatorics.LonelyRunnerBandPairRemaining

namespace LonelyRunnerReducedUnit

open LonelyRunnerFourThreeResidualCaseAComplete LonelyRunnerBandPairReduction
  LonelyRunnerBandPairRemaining

/-- **Negation symmetry of the band.** If `x` is in the middle band mod `D`, so is `-x`
(the band `[D/4, 3D/4]` is symmetric about `D/2`). -/
lemma inBand_neg (x : ℤ) (D : ℕ) (hD : 0 < D) (h : inBand x D) : inBand (-x) D := by
  have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hDne : ((D : ℤ)) ≠ 0 := ne_of_gt hDZ
  obtain ⟨h1, h2⟩ := h
  set ρ : ℤ := x % (D : ℤ) with hρ
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ hDne
  have hρD : ρ < (D : ℤ) := Int.emod_lt_of_pos _ hDZ
  -- `ρ > 0` since `4ρ ≥ D > 0`.
  have hρpos : 0 < ρ := by nlinarith [h1, hDZ]
  -- `(-x) % D = D - ρ`.
  have key : (-x) % (D : ℤ) = (D : ℤ) - ρ := by
    have e : -x = ((D : ℤ) - ρ) + (D : ℤ) * (-(x / (D : ℤ)) - 1) := by
      have hdm := Int.ediv_add_emod x (D : ℤ)  -- (D) * (x / D) + x % D = x
      rw [hρ]; linarith [hdm]
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold inBand
  rw [key]
  constructor
  · nlinarith [h2]
  · nlinarith [h1]

/-- **Boundary case `c = 2`.** With `n = ⌈D/4⌉`, both `n` and `2·n` lie in the band mod `D`. -/
lemma inBand_two (D : ℕ) (hD : 6 ≤ D) : ∃ n : ℤ, inBand n D ∧ inBand (2 * n) D := by
  have hDZ : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  set n : ℤ := ((D : ℤ) + 3) / 4 with hn
  set t : ℤ := ((D : ℤ) + 3) % 4 with ht
  have ht0 : 0 ≤ t := Int.emod_nonneg _ (by norm_num)
  have htlt : t < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hdm : 4 * n + t = (D : ℤ) + 3 := by
    have := Int.ediv_add_emod ((D : ℤ) + 3) 4
    rw [hn, ht]; linarith [this]
  -- `4 * n = D + 3 - t`, so `n` is in `[0, D)` and in the band.
  have h4n : 4 * n = (D : ℤ) + 3 - t := by linarith [hdm]
  have hnlo : 0 ≤ n := by omega
  have hnhi : n < (D : ℤ) := by omega
  have hnmod : n % (D : ℤ) = n := Int.emod_eq_of_lt hnlo hnhi
  -- `2 * n` is in `[0, D)`.
  have h2nlo : 0 ≤ 2 * n := by omega
  have h2nhi : 2 * n < (D : ℤ) := by omega
  have h2nmod : (2 * n) % (D : ℤ) = 2 * n := Int.emod_eq_of_lt h2nlo h2nhi
  refine ⟨n, ?_, ?_⟩
  · unfold inBand; rw [hnmod]; constructor <;> omega
  · unfold inBand; rw [h2nmod]; constructor <;> omega

/-- **The odd-multiplier core.** For `D ≥ 6`, `1 ≤ c`, `2c ≤ D`, an odd `o` satisfying the two
centring bounds, `n = ⌊(o·D + c)/(2c)⌋` puts both `n` and `c·n` in the middle band mod `D`. -/
lemma inBand_of_o (D : ℕ) (c o : ℤ) (hD : 6 ≤ D) (hc : 1 ≤ c) (h2c : 2 * c ≤ (D : ℤ))
    (ho : Odd o) (hlo : c * (D : ℤ) + 2 * c ≤ 2 * o * (D : ℤ))
    (hhi : 2 * o * (D : ℤ) + 2 * c ≤ 3 * (c * (D : ℤ))) :
    ∃ n : ℤ, inBand n D ∧ inBand (c * n) D := by
  have hDZ : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have hcpos : (0 : ℤ) < c := by omega
  have h2cpos : (0 : ℤ) < 2 * c := by omega
  have h2cne : (2 * c) ≠ 0 := ne_of_gt h2cpos
  obtain ⟨j, hj⟩ := ho          -- `o = 2*j + 1`
  set W : ℤ := o * (D : ℤ) + c with hW
  set s : ℤ := W % (2 * c) with hs
  set n : ℤ := W / (2 * c) with hnn
  have hs0 : 0 ≤ s := Int.emod_nonneg _ h2cne
  have hslt : s < 2 * c := Int.emod_lt_of_pos _ h2cpos
  have hWid : (2 * c) * n + s = W := by
    have := Int.ediv_add_emod W (2 * c); rw [hs, hnn]; linarith [this]
  -- `2 * (c * n) = o*D + c - s`.
  have hcn : 2 * (c * n) = o * (D : ℤ) + c - s := by
    have : (2 * c) * n = W - s := by linarith [hWid]
    rw [hW] at this; linarith [this]
  -- Residue of `c*n`: introduce `rr` with `2*rr = D + c - s` and `c*n = j*D + rr`.
  set rr : ℤ := c * n - j * (D : ℤ) with hrrdef
  have hrr2 : 2 * rr = (D : ℤ) + c - s := by
    have hoD : o * (D : ℤ) = 2 * j * (D : ℤ) + (D : ℤ) := by rw [hj]; ring
    rw [hrrdef]; rw [hoD] at hcn; linarith [hcn]
  have hrrlo : 0 < rr := by omega
  have hrrhi : rr < (D : ℤ) := by omega
  have hcneq : c * n = j * (D : ℤ) + rr := by rw [hrrdef]; ring
  have hcnmod : (c * n) % (D : ℤ) = rr := by
    rw [hcneq, add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (le_of_lt hrrlo) hrrhi]
  -- Bounds on `n` itself: `c*(4*n) = 2*o*D + 2c - 2s`, cancel `c`.
  have h4cn : c * (4 * n) = 2 * o * (D : ℤ) + 2 * c - 2 * s := by
    have : 4 * (c * n) = 2 * (o * (D : ℤ) + c - s) := by linarith [hcn]
    linarith [this]
  have hnlo' : c * (D : ℤ) ≤ c * (4 * n) := by nlinarith [hlo, hslt, hs0]
  have hnhi' : c * (4 * n) ≤ c * (3 * (D : ℤ)) := by nlinarith [hhi, hs0, hslt]
  have hn_lo : (D : ℤ) ≤ 4 * n := le_of_mul_le_mul_left hnlo' hcpos
  have hn_hi : 4 * n ≤ 3 * (D : ℤ) := le_of_mul_le_mul_left hnhi' hcpos
  have hnlo0 : 0 ≤ n := by omega
  have hnhiD : n < (D : ℤ) := by omega
  have hnmod : n % (D : ℤ) = n := Int.emod_eq_of_lt hnlo0 hnhiD
  refine ⟨n, ?_, ?_⟩
  · unfold inBand; rw [hnmod]; exact ⟨hn_lo, hn_hi⟩
  · unfold inBand; rw [hcnmod]; constructor
    · omega
    · omega

/-- **Positive core.** For any `1 ≤ c` with `2c ≤ D` (and `D ≥ 6`), some `n` puts both `n` and
`c·n` in the middle band mod `D`. Combines `inBand_of_o` (odd multiplier) with the boundary
lemma `inBand_two`. -/
lemma core_pos (D : ℕ) (c : ℤ) (hD : 6 ≤ D) (hc : 1 ≤ c) (h2c : 2 * c ≤ (D : ℤ)) :
    ∃ n : ℤ, inBand n D ∧ inBand (c * n) D := by
  by_cases hc2 : c = 2
  · subst hc2; exact inBand_two D hD
  · by_cases hodd : Odd c
    · -- `o = c` (odd): centring bounds reduce to `2c ≤ c·D`, i.e. `D ≥ 2`.
      refine inBand_of_o D c c hD hc h2c hodd ?_ ?_
      · nlinarith [hc, (by exact_mod_cast hD : (6 : ℤ) ≤ (D : ℤ))]
      · nlinarith [hc, (by exact_mod_cast hD : (6 : ℤ) ≤ (D : ℤ))]
    · -- `c` even and `≠ 2`, hence `c ≥ 4`; use `o = c − 1`.
      have hc4 : 4 ≤ c := by
        rcases Int.even_or_odd c with he | ho
        · obtain ⟨k, hk⟩ := he; omega
        · exact absurd ho hodd
      have hoodd : Odd (c - 1) := by
        rcases Int.even_or_odd c with he | ho
        · obtain ⟨k, hk⟩ := he; exact ⟨k - 1, by omega⟩
        · exact absurd ho hodd
      have hDZ : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
      -- `D ≥ 8` from `2c ≤ D` and `c ≥ 4`.
      have hD8 : (8 : ℤ) ≤ (D : ℤ) := by linarith [h2c, hc4]
      refine inBand_of_o D c (c - 1) hD hc h2c hoodd ?_ ?_
      · -- `c·D + 2c ≤ 2(c−1)·D`  ⟺  `2c + 2D ≤ c·D`  ⟺  `(c−2)(D−2) ≥ 4`.
        nlinarith [mul_nonneg (by linarith [hc4] : (0:ℤ) ≤ c - 2) (by linarith [hD8] : (0:ℤ) ≤ (D:ℤ) - 2), hc4, hD8]
      · -- `2(c−1)·D + 2c ≤ 3c·D`  ⟺  `2c ≤ c·D + 2D`.
        nlinarith [hc4, hD8, mul_nonneg (by linarith [hc4] : (0:ℤ) ≤ c) (by linarith [hD8] : (0:ℤ) ≤ (D:ℤ))]

/-- **`ReducedBandPairUnit` (the crux), proved.** For every modulus `D ≥ 6` and every `r`
coprime to `D` there is a `k` putting both `k` and `r·k` in the middle band mod `D`.

The proof needs only `¬ (D ∣ r)` (coprimality is not used): reduce `r` to `c₀ = r mod D`,
symmetrise to `c = min(c₀, D − c₀) ≤ D/2`, and invoke `core_pos`. -/
theorem reducedBandPairUnit_proof : ReducedBandPairUnit := by
  intro D r hD hnd _hcop
  have hDZ : (6 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have hDpos : (0 : ℤ) < (D : ℤ) := by linarith
  have hDne : ((D : ℤ)) ≠ 0 := ne_of_gt hDpos
  set c₀ : ℤ := r % (D : ℤ) with hc0
  have hc0lo : 0 ≤ c₀ := Int.emod_nonneg _ hDne
  have hc0hi : c₀ < (D : ℤ) := Int.emod_lt_of_pos _ hDpos
  have hc0ne : c₀ ≠ 0 := by
    intro h
    exact hnd (Int.dvd_of_emod_eq_zero (by rw [hc0] at h; exact h))
  have hc01 : 1 ≤ c₀ := by omega
  -- `D ∣ (r − c₀)`.
  have hdvdrc : (D : ℤ) ∣ (r - c₀) := by
    have := Int.ediv_add_emod r (D : ℤ)   -- D * (r/D) + r%D = r
    exact ⟨r / (D : ℤ), by rw [hc0]; linarith [this]⟩
  by_cases h2 : 2 * c₀ ≤ (D : ℤ)
  · -- `c = c₀`.
    obtain ⟨n, hbn, hbcn⟩ := core_pos D c₀ hD hc01 h2
    refine ⟨n, hbn, ?_⟩
    -- transport `inBand (c₀·n)` to `inBand (r·n)`.
    have hcongr : (D : ℤ) ∣ (r * n - c₀ * n) := by
      obtain ⟨w, hw⟩ := hdvdrc; exact ⟨w * n, by rw [show r * n - c₀ * n = (r - c₀) * n by ring, hw]; ring⟩
    exact (inBand_congr hcongr).mpr hbcn
  · -- `c = D − c₀`, using negation symmetry.
    have h2c0 : (D : ℤ) < 2 * c₀ := by linarith
    set c : ℤ := (D : ℤ) - c₀ with hcdef
    have hc1 : 1 ≤ c := by omega
    have h2c : 2 * c ≤ (D : ℤ) := by rw [hcdef]; linarith
    obtain ⟨n, hbn, hbcn⟩ := core_pos D c hD hc1 h2c
    refine ⟨n, hbn, ?_⟩
    -- `inBand (c·n) → inBand (-(r·n)) → inBand (r·n)`.
    have hcongr : (D : ℤ) ∣ (-(r * n) - c * n) := by
      obtain ⟨w, hw⟩ := hdvdrc
      refine ⟨-(w * n) - n, ?_⟩
      rw [hcdef]
      have : -(r * n) - ((D : ℤ) - c₀) * n = (D : ℤ) * (-n) - (r - c₀) * n := by ring
      rw [this, hw]; ring
    have hneg : inBand (-(r * n)) D := (inBand_congr hcongr).mpr hbcn
    have := inBand_neg (-(r * n)) D (by omega) hneg
    rwa [neg_neg] at this

/-- **`FourThreeResidualCaseA` unconditionally.** Feeding the proved crux into the capstone
reduction closes the last residual of the honest `k = 4` Lonely Runner Conjecture. -/
theorem fourThreeResidualCaseA_final :
    LonelyRunnerFourThreeResidualCaseB.FourThreeResidualCaseA :=
  caseA_of_unit reducedBandPairUnit_proof

end LonelyRunnerReducedUnit
