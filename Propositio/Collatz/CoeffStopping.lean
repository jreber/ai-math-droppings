import Propositio.Collatz.DensityCount
import Propositio.Collatz.NonDescentWeight
import Propositio.Collatz.ParityBijection
import Propositio.Collatz.AlmostAllDescend
import Propositio.Collatz.TailDecayUncond
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Unconditional "almost all integers descend" for the COEFFICIENT stopping time
  (`CollatzCoeffStopping`)

This file proves the **unconditional** Everett–Terras-flavored density theorem for
the **coefficient stopping time** of the Collatz/Terras map.

## The coefficient stopping time vs. the actual stopping time

For the Terras map, `affine_form` gives the exact identity
`2^j · T^j n = 3^(aCoef n j) · n + cCoef n j`, where `aCoef n j` is the number of
odd (`3n+1`) steps among the first `j`.  Two related "stopping" notions arise:

* **Actual stopping time** `σ(n) = ` least `j ≥ 1` with `T^j n < n`.  The bad set
  `{ n : σ(n) > k }` is what the *conditional* capstone
  `CollatzAlmostAllDescend.collatz_almost_all_descend` controls — but the bound
  `weight (Q k n) ≥ minOdd k` for non-descending `n` requires the hard half of the
  descent dichotomy `hpow` (`2^k ≤ 3^(aCoef n k)`), because the `cCoef n k`
  correction term sits between `3^(aCoef) < 2^k` and the genuine `T^k n < n`.

* **Coefficient stopping time** `σ̃(n) = ` least `j ≥ 1` with `3^(aCoef n j) < 2^j`
  (the *expected* multiplicative factor `3^{a_j}/2^j` drops below `1`).  This is the
  natural Terras object: it ignores the additive `cCoef` correction.  The bad set
  `CoeffBad k n := ∀ j, 1 ≤ j → j ≤ k → 2^j ≤ 3^(aCoef n j)` (i.e. `σ̃(n) > k`)
  gives, at `j = k` **directly**, `2^k ≤ 3^(aCoef n k)`, hence
  `minOdd k ≤ aCoef n k` by `minOdd_le_of_two_pow_le` — **no `hpow` hypothesis**.

So the coefficient-bad density is bounded by the heavy-weight parity-vector count
`upperTail k (minOdd k)`, which decays **unconditionally**
(`CollatzTailDecayUncond.upperTail_minOdd_decay`).

## What this is and is not

The headline `coeff_almost_all_descend` is **genuinely unconditional** (no
hypotheses) and **non-vacuous**: `CoeffBad k n` is satisfiable for every `k` — the
coefficient-bad count `coeffBeta k` is `≥ 1` throughout (computed values for
`k = 0..7` are `1,1,1,2,3,4,8,13`), and concretely the residues `7` and `15`
(both `< 2^5`) are coefficient-bad at `k = 5` (`CoeffBad 5 7`, `CoeffBad 5 15`).
So the bad set is a genuinely non-empty, shrinking-density set, not an empty one.
It states that the **density of integers whose
coefficient stopping time exceeds `k` tends to `0`** — equivalently almost every
integer has finite coefficient stopping time `σ̃(n) < ∞`.

It does **NOT** prove the Collatz conjecture, and it does **NOT** upgrade to the
actual stopping time: the gap is exactly the `cCoef`-correction `c_j` between
`3^(aCoef) < 2^j` and `T^j n < n`, which the actual-stopping-time capstone isolates
as the typed hypothesis `hpow`.

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

open Finset
open TerrasDensity (PVEq)
open CollatzDensityCount (aCoef cCoef PVEq_of_mod_eq coef_congr)
open CollatzParityBijection (Q pvMap pvMap_injective)
open CollatzNonDescentWeight (minOdd minOdd_le_of_two_pow_le)
open CollatzBinomialTail (upperTail)
open CollatzAlmostAllDescend (weight aCoef_eq_weight heavySet heavy_card_eq_upperTail)

namespace CollatzCoeffStopping

/-! ## §1  The coefficient-bad predicate and the trivial weight bound -/

/-- **`CoeffBad k n`** — the coefficient stopping time of `n` exceeds `k`:
the expected multiplicative factor `3^(aCoef n j) / 2^j` never drops below `1`
within the first `k` Terras steps.  Equivalently `σ̃(n) > k`. -/
def CoeffBad (k n : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → 2 ^ j ≤ 3 ^ (aCoef n j)

/-- `CoeffBad k n` is decidable: it is a bounded `∀` over `j` with a decidable body,
which `Nat.decidableBallLE` discharges (rewriting the `1 ≤ j → j ≤ k → P j` body to
the `∀ j ≤ k` form). -/
instance (k n : Nat) : Decidable (CoeffBad k n) :=
  decidable_of_iff (∀ j, j ≤ k → 1 ≤ j → 2 ^ j ≤ 3 ^ (aCoef n j))
    ⟨fun h j hj1 hjk => h j hjk hj1, fun h j hjk hj1 => h j hj1 hjk⟩

/-- **`coeffBad_implies_minOdd_le` (the trivial `j = k` instance).**
A coefficient-bad residue (`CoeffBad k n`, `k ≥ 1`) has odd-step count
`aCoef n k ≥ minOdd k` — TRIVIALLY: the `j = k` instance gives
`2^k ≤ 3^(aCoef n k)`, and `minOdd_le_of_two_pow_le` finishes.  **No descent
dichotomy / `hpow` hypothesis is used** — this is the whole point. -/
theorem coeffBad_implies_minOdd_le {k n : Nat} (hbad : CoeffBad k n) (hk : 1 ≤ k) :
    minOdd k ≤ aCoef n k :=
  minOdd_le_of_two_pow_le k (aCoef n k) (hbad k hk (le_refl k))

/-- `CoeffBad` depends only on `n mod 2^k`: it is a statement about residue classes.
(Each `aCoef n j` with `j ≤ k` depends only on `n mod 2^k` via `coef_congr`.) -/
theorem coeffBad_congr {k m n : Nat} (h : m % 2 ^ k = n % 2 ^ k) :
    CoeffBad k m ↔ CoeffBad k n := by
  have hkey : ∀ j, j ≤ k → aCoef m j = aCoef n j := by
    intro j hj
    have hmn : PVEq m n k := PVEq_of_mod_eq m n k h
    have hPV : PVEq m n j := fun i hi => hmn i (by omega)
    exact (coef_congr j m n hPV).1
  constructor
  · intro hbad j hj1 hjk; rw [← hkey j hjk]; exact hbad j hj1 hjk
  · intro hbad j hj1 hjk; rw [hkey j hjk]; exact hbad j hj1 hjk

/-! ## §2  The coefficient-bad count is bounded by the binomial upper tail -/

/-- **`coeffBeta k`** — the number of residues `r < 2^k` that are coefficient-bad:
`σ̃(r) > k`.  Since `CoeffBad k` is residue-invariant, this counts residue classes
mod `2^k`, so `coeffBeta k / 2^k` is the density of coefficient-bad integers. -/
def coeffBeta (k : Nat) : Nat :=
  (Finset.univ.filter (fun r : Fin (2 ^ k) => CoeffBad k r.val)).card

/-- **`coeffBeta_le_binom_tail` (the key count bound, mirroring
`beta_le_binom_tail`).**

`coeffBeta k ≤ upperTail k (minOdd k) = ∑_{i ≥ minOdd k} C(k,i)` for `k ≥ 1`.

Each coefficient-bad residue `r` has `aCoef r.val k ≥ minOdd k`
(`coeffBad_implies_minOdd_le`, the trivial `j = k` instance — NO `hpow`), so its
parity vector `pvMap k r = Q k r.val` has Hamming weight `≥ minOdd k`.  Since
`pvMap k` is injective, the coefficient-bad residues inject into the heavy-weight
vectors, whose count is `upperTail k (minOdd k)` (`heavy_card_eq_upperTail`).

This is the UNCONDITIONAL analogue of `beta_le_binom_tail`: the only difference is
that the weight bound here comes for free from the definition of `CoeffBad`, whereas
`beta_le_binom_tail` needs the descent-dichotomy hypothesis `hpow`. -/
theorem coeffBeta_le_binom_tail (k : Nat) (hk : 1 ≤ k) :
    coeffBeta k ≤ upperTail k (minOdd k) := by
  rw [coeffBeta, ← heavy_card_eq_upperTail]
  -- inject the coefficient-bad residues into heavySet via pvMap k
  apply Finset.card_le_card_of_injOn (pvMap k)
  · -- MapsTo : r coefficient-bad → pvMap k r ∈ heavySet
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    have hbad : CoeffBad k r.val := hr.2
    -- TRIVIAL weight bound: coeff-bad ⟹ minOdd k ≤ aCoef r.val k (j = k instance).
    have hge : minOdd k ≤ aCoef r.val k := coeffBad_implies_minOdd_le hbad hk
    -- pvMap k r = Q k r.val, and weight (Q k r.val) = aCoef r.val k.
    have hw : weight (pvMap k r) = aCoef r.val k := by
      unfold pvMap
      rw [← aCoef_eq_weight]
    rw [Finset.mem_coe]
    unfold heavySet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hw]; exact hge
  · -- InjOn : pvMap k is injective everywhere ⟹ injective on the bad set.
    intro a _ b _ hab
    exact pvMap_injective k hab

/-! ## §3  HEADLINE — the UNCONDITIONAL coefficient-stopping density theorem -/

/-- **`coeff_almost_all_descend` (HEADLINE, UNCONDITIONAL).**

    Tendsto (fun k => coeffBeta k / 2^k) atTop (𝓝 0).

The **density of integers whose coefficient stopping time `σ̃(n)` exceeds `k`
tends to `0`** — equivalently, the density of integers with finite coefficient
stopping time tends to `1`: *almost every integer has `3^(aCoef n j) < 2^j` for
some `j` (its expected Terras factor eventually drops below `1`).*

This is the natural Terras object, and unlike the actual-stopping-time capstone
`CollatzAlmostAllDescend.collatz_almost_all_descend` it has **NO hypotheses**: the
weight bound `aCoef n k ≥ minOdd k` for a coefficient-bad residue is the trivial
`j = k` instance of the definition (`coeffBad_implies_minOdd_le`), needing no
descent dichotomy `hpow`.  The tail decay `upperTail k (minOdd k)/2^k → 0` is itself
unconditional (`CollatzTailDecayUncond.upperTail_minOdd_decay`).

> Non-vacuous: `CoeffBad k n` is satisfiable for every `k` (`coeffBeta k ≥ 1`
> throughout; e.g. residues `7, 15 < 2^5` are coefficient-bad at `k = 5`), so the
> theorem is not a vacuous statement about an empty bad set.

> This does **NOT** prove the Collatz conjecture, and it does **NOT** upgrade to the
> *actual* stopping time `T^j n < n`; that upgrade is exactly the `cCoef`-correction
> gap isolated as the typed hypothesis `hpow` in the actual-stopping-time capstone.

Proof: `squeeze_zero` with `coeffBeta_le_binom_tail` (for `k ≥ 1`; `k = 0` handled
separately) and `upperTail_minOdd_decay`. -/
theorem coeff_almost_all_descend :
    Filter.Tendsto (fun k => (coeffBeta k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
  -- The analytic tail decay is unconditional.
  have htail : Filter.Tendsto
      (fun k => (upperTail k (minOdd k) : ℝ) / 2 ^ k) Filter.atTop (nhds 0) :=
    CollatzTailDecayUncond.upperTail_minOdd_decay
  -- Nat-level bound coeffBeta k ≤ upperTail k (minOdd k) for all k.
  have hbound : ∀ k, coeffBeta k ≤ upperTail k (minOdd k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · -- k = 0 : coeffBeta 0 ≤ 2^0 = 1 = upperTail 0 (minOdd 0).
      subst hk0
      have hut : upperTail 0 (minOdd 0) = 1 := by decide
      rw [hut]
      calc coeffBeta 0 ≤ (Finset.univ : Finset (Fin (2 ^ 0))).card := by
              rw [coeffBeta]; exact Finset.card_filter_le _ _
        _ = 1 := by simp
    · exact coeffBeta_le_binom_tail k hk1
  -- Squeeze: 0 ≤ coeffBeta k / 2^k ≤ upperTail k (minOdd k)/2^k → 0.
  apply squeeze_zero (g := fun k => (upperTail k (minOdd k) : ℝ) / 2 ^ k)
  · intro k; positivity
  · intro k
    have hcast : (coeffBeta k : ℝ) ≤ (upperTail k (minOdd k) : ℝ) := by
      exact_mod_cast hbound k
    gcongr
  · exact htail

end CollatzCoeffStopping
