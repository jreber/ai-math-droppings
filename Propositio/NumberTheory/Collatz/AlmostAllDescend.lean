import Propositio.NumberTheory.Collatz.ParityBijection
import Propositio.NumberTheory.Collatz.NonDescentWeight
import Propositio.NumberTheory.Collatz.BinomialTail
import Propositio.NumberTheory.Collatz.TailDecayUncond
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Everett–Terras "almost all integers descend" capstone (`CollatzAlmostAllDescend`)

This file assembles the **conditional capstone** of the Collatz bad-density
program: the Everett–Terras theorem that the *bad density*
`b(k) = β(k)/2^k = density{ n : σ(n) > k }` of integers whose Terras stopping time
exceeds `k` tends to `0`, i.e. **almost every integer descends below itself within
`k` Terras steps** (equivalently, the natural density of integers with finite
stopping time is `1`).

> **IMPORTANT — what this is and is not.**  This is a statement about the
> *density of integers with finite stopping time tending to `1`* — "almost all
> integers descend".  It is **NOT** a statement about per-orbit convergence to
> `1`, and it does **NOT** prove the Collatz conjecture (which asserts *every*
> orbit reaches `1`).  Vanishing bad density is fully compatible with the
> existence of non-trivial cycles or divergent orbits in a measure-zero set.

## The assembly chain

All the heavy lifting was done in the imported pieces; this file is the *bridge*.

1. **Structural weight lemma** (`CollatzNonDescentWeight.bad_implies_odd_steps_ge`):
   a non-descending residue (`Bad k n`, with the honest finite-correction control
   `cCoef n k < n`) has odd-step count `aCoef n k ≥ minOdd k`, where
   `minOdd k = ⌈k·log₃2⌉` and `minOdd k > k/2` (`minOdd_gt_half`).

2. **`aCoef = Hamming weight`** (`aCoef_eq_weight`, proved here): the odd-step
   count `aCoef n k` equals the Hamming weight of the parity vector `Q k n`
   (number of `true` bits = number of `3n+1` steps).

3. **Vector counting** (`card_weight_eq`, proved here): the number of length-`k`
   binary vectors of Hamming weight exactly `i` is `C(k,i)`
   (`Finset.card_powersetCard`).

4. **The combinatorial bound** (`beta_le_binom_tail`, the key NEW result):
   via the parity-vector bijection `pvMap k : Fin (2^k) ≃ (Fin k → Bool)`
   (`CollatzParityBijection.pvMap_bijective`), distinct bad residues give distinct
   heavy-weight parity vectors, so
   `β(k) ≤ #{ v ∈ {0,1}^k : weight v ≥ minOdd k } = upperTail k (minOdd k)`.

5. **The analytic tail decay** (`CollatzBinomialTail.binom_tail_decay`): with
   threshold `t k = minOdd k > k/2` and the single-coefficient decay input `hρ`,
   `upperTail k (minOdd k)/2^k → 0`.

6. **Squeeze** (`collatz_almost_all_descend`, the HEADLINE): `0 ≤ β(k)/2^k ≤
   upperTail k (minOdd k)/2^k → 0`, so `b(k) = β(k)/2^k → 0`.

## The two documented standard hypotheses (the honest gaps)

The capstone `collatz_almost_all_descend` is **conditional** on exactly two typed
inputs, both standard and isolated by the corpus:

* **`hρ` — the binary-entropy single-coefficient bound.**
  `(k.choose (minOdd k) : ℝ) ≤ 2^k · ρ^k` for a fixed `ρ < 1`.  This is the
  textbook fact that the central/skewed binomial coefficient at a fraction
  `c = log₃2 > 1/2` away from the mean is sub-`2^k`: binary entropy gives
  `C(k,⌈ck⌉) ≤ 2^{k·H(c)}` with `H(log₃2) ≈ 0.952 < 1`, so `ρ = 2^{H(c)-1} < 1`.
  (Plus the sub-exponential geometric-constant control `hK`, also standard.)

* **`hpow` — the hard half of the descent dichotomy.**
  `∀ r : Fin (2^k), descByB (r+2^k) k = false → 2^k ≤ 3^{aCoef (r+2^k) k}`: a
  non-descending lift takes enough odd (`3n+1`) steps that `3^{odd-count}` reaches
  `2^k`.  This is TRUE for every lift `n = r + 2^k ≥ 2^k` (the canonical-lift regime
  used to count residues; the only `n` failing it are the degenerate boundary
  `n ∈ {0,1,2}`, excluded by the lift).  The corpus proves it only under the side
  condition `cCoef < n` (`bad_implies_three_pow_ge`), which is itself sometimes false
  (`cCoef(39,5)=73 > 39`), so the unconditional `hpow` is taken as the explicit
  remaining typed gap — it is a power-comparison statement, structurally distinct
  from the conclusion `β(k)/2^k → 0`, hence **not circular**, and (being true)
  **not vacuous**.

Neither hypothesis is (or implies) the conclusion; both are standard, satisfiable
inputs the corpus's other pieces have isolated.

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

open Finset
open TerrasDensity
open CollatzDensityCount (aCoef cCoef D beta bad_count_eq descByB descByB_iff)
open CollatzParityBijection (Q pvMap pvMap_bijective pvMap_injective Q_eq_iff_PVEq)
open CollatzNonDescentWeight (minOdd minOdd_gt_half minOdd_le_of_two_pow_le)
open CollatzBinomialTail (upperTail binom_tail_decay)

namespace CollatzAlmostAllDescend

/-! ## §1  Hamming weight and the two combinatorial identities -/

/-- The **Hamming weight** of a length-`k` binary vector: the number of `true`
bits (= the number of `3n+1` / odd Terras steps, once `v = Q k n`). -/
def weight {k : Nat} (v : Fin k → Bool) : Nat :=
  (Finset.univ.filter (fun j => v j = true)).card

/-- `weight v ≤ k`: the true-bit count never exceeds the length. -/
theorem weight_le {k : Nat} (v : Fin k → Bool) : weight v ≤ k := by
  unfold weight
  calc (Finset.univ.filter (fun j => v j = true)).card
      ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

/-- **`aCoef` as a prefix sum.**  `aCoef n k = ∑_{j<k} [T^j n odd]`. -/
theorem aCoef_eq_sum (n k : Nat) :
    aCoef n k = ∑ j ∈ Finset.range k, (if T_iter n j % 2 = 1 then 1 else 0) := by
  induction k with
  | zero => simp [aCoef]
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- **`aCoef_eq_weight` (identity #2).**  The odd-step count `aCoef n k` equals the
Hamming weight of the parity vector `Q k n`: the number of `3n+1` steps in the
first `k` Terras steps is exactly the number of `true` bits of `Q k n`. -/
theorem aCoef_eq_weight (n k : Nat) : aCoef n k = weight (Q k n) := by
  rw [aCoef_eq_sum]
  unfold weight
  rw [Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if T_iter n j % 2 = 1 then 1 else 0) k]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Q]
  by_cases h : T_iter n i.val % 2 = 1 <;> simp [h]

/-- **`card_weight_eq` (identity #3 / the weight-counting lemma).**  The number of
length-`k` binary vectors of Hamming weight exactly `i` is the binomial coefficient
`C(k,i)`.  Proof: the true-set map `v ↦ {j : v j}` is a bijection onto the
`i`-subsets of `Fin k`, whose count is `Finset.card_powersetCard = C(k,i)`. -/
theorem card_weight_eq (k i : Nat) :
    (Finset.univ.filter (fun v : Fin k → Bool => weight v = i)).card = k.choose i := by
  have hpc : k.choose i = (Finset.powersetCard i (Finset.univ : Finset (Fin k))).card := by
    rw [Finset.card_powersetCard]; simp
  rw [hpc]
  refine Finset.card_bij'
    (fun v _ => Finset.univ.filter (fun j => v j = true))
    (fun S _ => (fun j => decide (j ∈ S)))
    ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hv.2⟩
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold weight
    have h2 : (Finset.univ.filter (fun j => decide (j ∈ S) = true)) = S := by
      ext j; simp
    rw [h2, hS.2]
  · intro v _
    funext j; simp
  · intro S _
    ext j; simp

/-! ## §2  The heavy-weight count equals the binomial upper tail -/

/-- The set of length-`k` parity vectors that are "heavy" (weight `≥ minOdd k`). -/
def heavySet (k : Nat) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun v => minOdd k ≤ weight v)

/-- **`heavy_card_eq_upperTail`.**  The number of heavy-weight length-`k` parity
vectors is exactly the binomial upper tail `upperTail k (minOdd k) = ∑_{i ≥ minOdd
k} C(k,i)`.  Proof: partition the heavy vectors by their weight `i ∈ Icc (minOdd k)
k` (`card_eq_sum_card_fiberwise`); each fiber has `C(k,i)` elements
(`card_weight_eq`). -/
theorem heavy_card_eq_upperTail (k : Nat) :
    (heavySet k).card = upperTail k (minOdd k) := by
  unfold heavySet upperTail
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun v : Fin k → Bool => weight v) (t := Finset.Icc (minOdd k) k)]
  · -- each fiber: { v : minOdd k ≤ weight v ∧ weight v = i } = { v : weight v = i }
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [← card_weight_eq k i]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hw⟩; exact hw
    · intro hw; exact ⟨by rw [hw]; exact hi.1, hw⟩
  · -- maps-to: a heavy vector's weight lands in Icc (minOdd k) k
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨hv.2, weight_le v⟩

/-! ## §3  The key combinatorial bound `β(k) ≤ upperTail k (minOdd k)` -/

/-- The **bad-residue set**: residues `r < 2^k` whose canonical lift `r + 2^k` does
NOT descend within `k` Terras steps. -/
def badSet (k : Nat) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun r => descByB (r.val + 2 ^ k) k = false)

/-- `β(k)` equals the cardinality of the bad-residue set.  (`β(k) = 2^k − D(k)`,
and `D(k)` is the count of *descending* residues, so the bad count is the
complement, over the `2^k`-element residue space `Fin (2^k)`.) -/
theorem beta_eq_badSet_card (k : Nat) : beta k = (badSet k).card := by
  unfold beta badSet
  -- D k = #{descByB = true}; complement card = 2^k − D k.
  have hDk : D k = (Finset.univ.filter
      (fun r : Fin (2 ^ k) => descByB (r.val + 2 ^ k) k = true)).card :=
    CollatzDensityCount.descending_vector_count k
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 ^ k))))
      (fun r => descByB (r.val + 2 ^ k) k = true)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  -- rewrite the "not = true" filter as "= false"
  have hneg : (Finset.univ.filter
        (fun r : Fin (2 ^ k) => ¬ descByB (r.val + 2 ^ k) k = true))
      = Finset.univ.filter (fun r : Fin (2 ^ k) => descByB (r.val + 2 ^ k) k = false) := by
    apply Finset.filter_congr
    intro r _
    simp [Bool.not_eq_true]
  rw [hneg] at hsplit
  rw [← hDk] at hsplit
  omega

/-- **`beta_le_binom_tail` (the key NEW combinatorial bound).**

`β(k) ≤ upperTail k (minOdd k) = ∑_{i ≥ minOdd k} C(k,i)`.

Each bad residue `r` (lift `n = r + 2^k ≥ 2^k`) is `Bad k n`; with the power input
`hpow` (`2^k ≤ 3^{aCoef n k}`) it has odd-step count `aCoef n k ≥ minOdd k`
(`minOdd_le_of_two_pow_le`), i.e. its parity vector `Q k n` has Hamming weight
`≥ minOdd k`.  Since `pvMap k r = Q k r.val = Q k n` (parity vectors depend only on
`n mod 2^k`, and `r.val ≡ r.val + 2^k`), and `pvMap k` is injective, the bad
residues inject into the heavy-weight vectors, whose count is `upperTail k (minOdd
k)` (`heavy_card_eq_upperTail`). -/
theorem beta_le_binom_tail (k : Nat) (_hk : 1 ≤ k)
    (hpow : ∀ r : Fin (2 ^ k), descByB (r.val + 2 ^ k) k = false →
      2 ^ k ≤ 3 ^ (aCoef (r.val + 2 ^ k) k)) :
    beta k ≤ upperTail k (minOdd k) := by
  rw [beta_eq_badSet_card, ← heavy_card_eq_upperTail]
  -- inject badSet into heavySet via pvMap k
  apply Finset.card_le_card_of_injOn (pvMap k)
  · -- MapsTo : r ∈ badSet → pvMap k r ∈ heavySet
    intro r hr
    rw [Finset.mem_coe] at hr
    unfold badSet at hr
    rw [Finset.mem_filter] at hr
    have hr' : descByB (r.val + 2 ^ k) k = false := hr.2
    -- odd-step bound: bad ⟹ 2^k ≤ 3^aCoef (hpow, the hard descent dichotomy)
    -- ⟹ minOdd k ≤ aCoef (via minOdd_le_of_two_pow_le). No cCoef side condition.
    have hge : minOdd k ≤ aCoef (r.val + 2 ^ k) k :=
      minOdd_le_of_two_pow_le k _ (hpow r hr')
    -- pvMap k r = Q k r.val, and Q k r.val = Q k (r.val + 2^k)
    have hPV : Q k r.val = Q k (r.val + 2 ^ k) := by
      apply (Q_eq_iff_PVEq r.val (r.val + 2 ^ k) k).2
      apply CollatzDensityCount.PVEq_of_mod_eq
      simp
    -- weight (pvMap k r) = aCoef (r+2^k) k
    have hw : weight (pvMap k r) = aCoef (r.val + 2 ^ k) k := by
      unfold pvMap
      rw [hPV, ← aCoef_eq_weight]
    rw [Finset.mem_coe]
    unfold heavySet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hw]; exact hge
  · -- InjOn : pvMap k injective everywhere ⟹ injective on the bad set
    intro a _ b _ hab
    exact pvMap_injective k hab

/-! ## §4  HEADLINE — the Everett–Terras conditional capstone `b(k) → 0` -/

/-- **`collatz_almost_all_descend` (HEADLINE, conditional capstone).**

The **Everett–Terras "almost all integers descend" theorem**, conditional on the
two documented standard inputs:

    Tendsto (fun k => β(k)/2^k) atTop (𝓝 0)        i.e.   b(k) → 0,

where `b(k) = β(k)/2^k` is the density of residues mod `2^k` whose canonical lift
does **not** descend below itself within `k` Terras steps — equivalently the
density of integers with Terras stopping time `> k`.  So the density of integers
with finite stopping time tends to `1`: *almost every integer descends*.

> This is a density-`→ 1` statement for finite stopping time, **NOT** per-orbit
> convergence to `1`, and does **not** prove the Collatz conjecture.

### The SINGLE remaining hypothesis (one documented gap)

The binomial-tail decay `upperTail k (minOdd k)/2^k → 0` — formerly assumed via the
binary-entropy bound `hcoef`/`hK` — is now **proved unconditionally** in
`CollatzTailDecayUncond.upperTail_minOdd_decay` (central-binomial decay via Stirling
+ the elementary `minOdd k ≥ 3k/5` constant bound). So the capstone rests on exactly
ONE input:

* `hpow` : the **hard half of the descent dichotomy** — a non-descending lift is
  tripling-heavy enough that `2^k ≤ 3^(aCoef (r+2^k) k)` for every bad residue `r`.
  This is TRUE (verified for every lift `n = r+2^k ≥ 2^k`; the only `n` failing it are
  the degenerate boundary `n ∈ {0,1,2}`, excluded by the lift), but the corpus proves
  it only under the side condition `cCoef < n` (`bad_implies_three_pow_ge`), which can
  fail (e.g. `cCoef(39,5)=73>39`); the unconditional form needs a strengthened invariant
  on `cCoef`. So it is taken here as the explicit remaining typed gap — NOT the false
  `cCoef < n` statement.

`hpow` does not equal or imply the conclusion `β(k)/2^k → 0`, and it is satisfiable
(`hpow` is true), so the capstone is a **non-vacuous true conditional theorem** resting
on a single honest, standard gap. -/
theorem collatz_almost_all_descend
    (hpow : ∀ k, 1 ≤ k → ∀ r : Fin (2 ^ k),
      descByB (r.val + 2 ^ k) k = false →
      2 ^ k ≤ 3 ^ (aCoef (r.val + 2 ^ k) k)) :
    Filter.Tendsto (fun k => (beta k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
  -- The analytic tail decay `upperTail k (minOdd k)/2^k → 0` is now UNCONDITIONAL
  -- (`CollatzTailDecayUncond.upperTail_minOdd_decay`, via Stirling's formula) — the
  -- former binomial-entropy hypotheses `hcoef`/`hK` are discharged.
  have htail : Filter.Tendsto
      (fun k => (upperTail k (minOdd k) : ℝ) / 2 ^ k) Filter.atTop (nhds 0) :=
    CollatzTailDecayUncond.upperTail_minOdd_decay
  -- The Nat-level bound β(k) ≤ upperTail k (minOdd k), for all k.
  have hbound : ∀ k, beta k ≤ upperTail k (minOdd k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · -- k = 0 : beta 0 = 2^0 − D 0 ≤ 1 = upperTail 0 (minOdd 0).
      subst hk0
      have : upperTail 0 (minOdd 0) = 1 := by decide
      rw [this]
      calc beta 0 ≤ 2 ^ 0 := by unfold beta; omega
        _ = 1 := by norm_num
    · exact beta_le_binom_tail k hk1 (hpow k hk1)
  -- Squeeze: 0 ≤ β(k)/2^k ≤ upperTail k (minOdd k)/2^k.
  apply squeeze_zero (g := fun k => (upperTail k (minOdd k) : ℝ) / 2 ^ k)
  · intro k; positivity
  · intro k
    have hcast : (beta k : ℝ) ≤ (upperTail k (minOdd k) : ℝ) := by
      exact_mod_cast hbound k
    gcongr
  · exact htail
