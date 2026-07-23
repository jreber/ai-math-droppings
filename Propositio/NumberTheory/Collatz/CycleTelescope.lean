import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.LyapunovCascade
import Propositio.NumberTheory.Collatz.CascadeCycles
import Propositio.NumberTheory.Collatz.H5

/-!
# General telescoped additive identity for the compressed Collatz map

This file proves the **general** telescoped additive identity

    2^(S L) · cc^[L] n = 3^L · n + Steiner n L

that underlies every ad-hoc per-length telescoping in `CollatzThreeCycleExclusion`
and `CollatzFiveSixSevenCycleExclusion`.  Those files each hand-unrolled the
telescoping for a fixed `L`; this file establishes it for all `L : Nat` by a
clean induction, so downstream cycle-exclusion work can import a single reusable
lemma rather than repeating the derivation.

## Definitions

Given `n : Nat` and writing `nᵢ = cc^[i] n`, `aᵢ = v₂(3·nᵢ + 1)`:

* `S n i` — partial sum of the per-step 2-adic valuations:
  `S n i = Σ j ∈ Finset.range i, v₂(3·cc^[j] n + 1)`.
  So `S n 0 = 0` and `S n (i+1) = S n i + aᵢ`.

* `Steiner n L` — the "Steiner numerator", defined recursively:
  `Steiner n 0 = 0`, `Steiner n (L+1) = 3 · Steiner n L + 2^(S n L)`.
  This is the closed-form accumulator that appears on the RHS of the identity.

## Main results

1. `telescope_identity` (for all `n L : Nat`):
   `2^(S n L) · cc^[L] n = 3^L · n + Steiner n L`

2. `cycle_telescope_identity` (for odd `n`, `L ≥ 1`, `cc^[L] n = n`):
   `2^(S n L) · n = 3^L · n + Steiner n L`

3. `cycle_steiner_dvd` (for odd `n`, `L ≥ 1`, nontrivial cycle):
   `(2^(S n L) - 3^L) ∣ Steiner n L`

   Combined with `cc_cycle_three_pow_lt` (giving `3^L < 2^(S n L)`) this allows
   the Steiner finite divisibility check to be invoked without re-deriving the
   telescoped relation.
-/

namespace CollatzCycleTelescope

open TerrasDensity (cc)
open scoped BigOperators

/-- Local abbreviation for the project's `Odd` (`∃ k, n = 2k+1`), distinct from
mathlib's `_root_.Odd`. -/
local notation "Odd" => TerrasDensity.Odd

/-! ## Partial-sum and Steiner-numerator definitions -/

/-- `S n i` is the sum of per-step 2-adic valuations for the first `i` iterates
of `cc` starting at `n`:

    S n i = Σ j ∈ Finset.range i, v₂(3 · cc^[j] n + 1).

So `S n 0 = 0` and `S n (i+1) = S n i + v₂(3 · cc^[i] n + 1)`. -/
def S (n : Nat) (i : Nat) : Nat :=
  ∑ j ∈ Finset.range i, padicValNat 2 (3 * cc^[j] n + 1)

/-- `Steiner n L` is the recursive Steiner numerator:

    Steiner n 0     = 0
    Steiner n (L+1) = 3 · Steiner n L + 2^(S n L). -/
def Steiner (n : Nat) : Nat → Nat
  | 0     => 0
  | L + 1 => 3 * Steiner n L + 2 ^ S n L

/-! ## Key lemmas about S -/

@[simp]
theorem S_zero (n : Nat) : S n 0 = 0 := by
  simp [S]

theorem S_succ (n : Nat) (i : Nat) :
    S n (i + 1) = S n i + padicValNat 2 (3 * cc^[i] n + 1) := by
  simp [S, Finset.sum_range_succ]

/-! ## Key lemmas about Steiner -/

@[simp]
theorem Steiner_zero (n : Nat) : Steiner n 0 = 0 := by
  simp [Steiner]

theorem Steiner_succ (n : Nat) (L : Nat) :
    Steiner n (L + 1) = 3 * Steiner n L + 2 ^ S n L := by
  simp [Steiner]

/-! ## Main telescope identity -/

/-- **Telescope identity (main lemma).**

For any `n L : Nat`:

    2^(S n L) · cc^[L] n = 3^L · n + Steiner n L.

This is the additive form of the cycle identity obtained by telescoping the
per-step exact identity `2^{aᵢ} · cc^[i+1] n = 3 · cc^[i] n + 1`
(`CollatzCascadeCycles.pow_v2_mul_iterate`) across `L` steps. -/
theorem telescope_identity (n L : Nat) :
    2 ^ S n L * cc^[L] n = 3 ^ L * n + Steiner n L := by
  induction L with
  | zero =>
    simp [S_zero, Steiner_zero]
  | succ L ih =>
    -- LHS: 2^(S n (L+1)) * cc^[L+1] n
    -- S n (L+1) = S n L + a_L, so 2^(S n (L+1)) = 2^(S n L) * 2^a_L
    rw [S_succ, pow_add]
    -- cc^[L+1] n = cc (cc^[L] n) = cc^[L+1] n, use pow_v2_mul_iterate
    -- We have: 2^(S n L) * (2^a_L * cc^[L+1] n)
    --        = 2^(S n L) * (3 * cc^[L] n + 1)   [by pow_v2_mul_iterate]
    --        = 3 * (2^(S n L) * cc^[L] n) + 2^(S n L)
    --        = 3 * (3^L * n + Steiner n L) + 2^(S n L)   [by IH]
    --        = 3^(L+1) * n + Steiner n (L+1)
    have hstep := CollatzCascadeCycles.pow_v2_mul_iterate n L
    -- hstep : 2^(padicValNat 2 (3 * cc^[L] n + 1)) * cc^[L+1] n = 3 * cc^[L] n + 1
    rw [Steiner_succ]
    -- Goal: 2^(S n L) * 2^(padicValNat 2 (3 * cc^[L] n + 1)) * cc^[L+1] n
    --     = 3^(L+1) * n + (3 * Steiner n L + 2^(S n L))
    -- Rearrange multiplication
    have hrearrange : 2 ^ S n L * 2 ^ padicValNat 2 (3 * cc^[L] n + 1) * cc^[L + 1] n
        = 2 ^ S n L * (2 ^ padicValNat 2 (3 * cc^[L] n + 1) * cc^[L + 1] n) := by ring
    rw [hrearrange, hstep]
    -- Now: 2^(S n L) * (3 * cc^[L] n + 1) = 3^(L+1) * n + (3 * Steiner n L + 2^(S n L))
    -- Use IH: 2^(S n L) * cc^[L] n = 3^L * n + Steiner n L
    -- 2^(S n L) * (3 * cc^[L] n + 1)
    --   = 3 * (2^(S n L) * cc^[L] n) + 2^(S n L)
    --   = 3 * (3^L * n + Steiner n L) + 2^(S n L)  [by ih]
    --   = 3^(L+1) * n + (3 * Steiner n L + 2^(S n L))
    have hrw : 2 ^ S n L * (3 * cc^[L] n + 1)
        = 3 * (2 ^ S n L * cc^[L] n) + 2 ^ S n L := by ring
    rw [hrw, ih]
    rw [pow_succ]
    ring

/-! ## Cyclic corollaries -/

set_option linter.unusedVariables false in
/-- **Cyclic corollary 1.**

For odd `n`, `L ≥ 1`, `cc^[L] n = n` (an `L`-step cycle):

    2^(S n L) · n = 3^L · n + Steiner n L.

This is immediate from `telescope_identity` with `cc^[L] n = n`.
(`hodd` and `hL` are in the signature for API consistency with the divisibility
corollary and with `CollatzCascadeCycles`; only `hcyc` is needed in the proof.) -/
theorem cycle_telescope_identity (n : Nat) (hodd : Odd n) (L : Nat) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) :
    2 ^ S n L * n = 3 ^ L * n + Steiner n L := by
  have h := telescope_identity n L
  rw [hcyc] at h
  exact h

/-- **Cyclic corollary 2 (Steiner divisibility).**

For odd `n`, `L ≥ 1`, nontrivial `L`-step cycle of `cc` (some element `> 1`):

    (2^(S n L) - 3^L) ∣ Steiner n L.

The key step: `cc_cycle_three_pow_lt` gives `3^L < 2^(S n L)`, so the
Nat-subtraction `2^(S n L) - 3^L` is positive; and from `cycle_telescope_identity`,

    (2^(S n L) - 3^L) · n = Steiner n L,

so `n` witnesses the divisibility. -/
theorem cycle_steiner_dvd (n : Nat) (hodd : Odd n) (L : Nat) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n)
    (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    (2 ^ S n L - 3 ^ L) ∣ Steiner n L := by
  -- Get 3^L < 2^(S n L) from the cycle constraint
  have hlt : 3 ^ L < 2 ^ S n L := by
    have := CollatzCascadeCycles.cc_cycle_three_pow_lt n L hodd hcyc hL
    -- The S in CollatzCascadeCycles uses the same sum expression; bridge definitionally
    simp only [S]
    exact this
  -- From cycle_telescope_identity: 2^(S n L) * n = 3^L * n + Steiner n L
  have hid := cycle_telescope_identity n hodd L hL hcyc
  -- Rearrange: (2^(S n L) - 3^L) * n = Steiner n L
  -- From hid: 2^(S n L) * n = 3^L * n + Steiner n L
  -- So: 2^(S n L) * n - 3^L * n = Steiner n L
  -- i.e. (2^(S n L) - 3^L) * n = Steiner n L  (Nat subtraction is safe since 3^L < 2^(S n L))
  have hfactor : (2 ^ S n L - 3 ^ L) * n = Steiner n L := by
    have hge : 3 ^ L ≤ 2 ^ S n L := Nat.le_of_lt hlt
    have : (2 ^ S n L - 3 ^ L) * n = 2 ^ S n L * n - 3 ^ L * n :=
      Nat.sub_mul (2 ^ S n L) (3 ^ L) n
    rw [this]
    omega
  exact ⟨n, hfactor.symm⟩

end CollatzCycleTelescope

-- Axiom checks: only [propext, Classical.choice, Quot.sound] are permitted.
#print axioms CollatzCycleTelescope.telescope_identity
#print axioms CollatzCycleTelescope.cycle_telescope_identity
#print axioms CollatzCycleTelescope.cycle_steiner_dvd
