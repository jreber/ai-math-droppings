/-
# Exponential decay of the upper binomial tail (`CollatzBinomialTail`)

For a fixed fraction `c > 1/2`, the *upper binomial tail*
  `S(k,c) = #{ S ⊆ Fin k : c·k ≤ |S| } = ∑_{i ≥ ⌈ck⌉} C(k,i)`
is an exponentially small share of `2^k`:  `S(k,c)/2^k → 0`.

This is the analytic input to the Everett–Terras "almost all Collatz orbits
descend" theorem.  The Collatz survivor fraction `b(k)` is bounded by
`S(k, log₃2)/2^k` (a parity vector that does not descend in `k` Terras steps must
carry `≥ k·log₃2 ≈ 0.6309·k` odd steps — see `CollatzNonDescentWeight`), and
`log₃2 > 1/2`, so this file's bound feeds `b(k) → 0`.

## Route (elementary, no real entropy needed for the geometric core)

Past the middle the binomial coefficients decrease geometrically.  Writing
`t > k/2`, for every `i ≥ t` the consecutive ratio satisfies
  `C(k,i+1)/C(k,i) = (k−i)/(i+1) ≤ (k−t)/(t+1) =: r < 1`.
Hence `C(k,t+m) ≤ C(k,t)·rᵐ` and, summing the geometric series,
  `S(k,t) = ∑_{i=t}^{k} C(k,i) ≤ C(k,t)/(1−r) = C(k,t)·(t+1)/(2t−k+1)`.

So the whole tail is dominated by a single coefficient `C(k,t)` times an
explicit constant.  The remaining `→ 0` is then the central/skewed
single-coefficient decay `C(k,⌈ck⌉)/2^k → 0`, supplied here through the explicit
hypothesis `hρ : (C(k,⌈ck⌉) : ℝ) ≤ 2^k · ρ^k` (`ρ < 1`); see `binom_tail_decay`.

## Results

* `binom_tail_ratio`         — `C(k,i+1)·(i+1) = C(k,i)·(k−i)`  (mathlib recurrence, repackaged)
* `binom_choose_succ_le`     — `C(k,i+1) ≤ C(k,i)` for `i ≥ k/2`  (tail decreasing past the middle)
* `binom_geom_step` (ℝ)      — `(C(k,i+1):ℝ) ≤ r · C(k,i)` for `i ≥ t`, `r = (k−t)/(t+1)`
* `binom_pow_bound` (ℝ)      — `(C(k,t+m):ℝ) ≤ C(k,t) · rᵐ`
* `binom_tail_geometric` (ℝ) — `(S(k,t):ℝ) ≤ C(k,t) · (1−r)⁻¹`  (HEADLINE #2)
* `binom_tail_decay`         — `S(k,⌈ck⌉)/2^k → 0` from single-coefficient decay (HEADLINE #3)
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic

open Finset

namespace CollatzBinomialTail

/-- Upper tail count: number of `i`-subsets of `Fin k` of size `t ≤ i ≤ k`,
summed.  Equivalently `#{ S ⊆ Fin k : t ≤ |S| }`. -/
def upperTail (k t : ℕ) : ℕ := ∑ i ∈ Finset.Icc t k, k.choose i

/-! ### Numerical sanity check (`c = 0.63`)

The last column is `S(k,⌈0.63 k⌉)/2^k` in per-mille; it decays geometrically. -/
-- 171, 131, 100, 40, 32, 25, 11  →  geometric decay confirmed (verified by #eval during
-- development; the per-mille share of 2^k for c=0.63, k=10..70).

/-! ### #1 — the consecutive ratio -/

/-- The binomial recurrence in product form: `C(k,i+1)·(i+1) = C(k,i)·(k−i)`.
This is `Nat.choose_succ_right_eq`, repackaged under our naming. -/
theorem binom_tail_ratio (k i : ℕ) :
    k.choose (i + 1) * (i + 1) = k.choose i * (k - i) :=
  Nat.choose_succ_right_eq k i

/-- Past the middle the tail is **decreasing**: for `i ≥ k/2` (equivalently
`k ≤ 2i+1`, i.e. `k − i ≤ i + 1`) we have `C(k,i+1) ≤ C(k,i)`. -/
theorem binom_choose_succ_le {k i : ℕ} (hi : k ≤ 2 * i + 1) :
    k.choose (i + 1) ≤ k.choose i := by
  have hki : k - i ≤ i + 1 := by omega
  -- C(k,i+1)·(i+1) = C(k,i)·(k−i) ≤ C(k,i)·(i+1)
  have key : k.choose (i + 1) * (i + 1) ≤ k.choose i * (i + 1) := by
    rw [binom_tail_ratio]
    exact Nat.mul_le_mul_left _ hki
  exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos i)

/-! ### #2 — the geometric per-coefficient bound and the closed tail sum (over ℝ) -/

/-- One geometric step over ℝ.  Fix a threshold `t` with `k < 2t+1` (so
`t > k/2`).  Set `r = (k−t)/(t+1) < 1`.  Then for every `i ≥ t`,
`(C(k,i+1):ℝ) ≤ r · C(k,i)`.

The monotonicity `(k−i)/(i+1) ≤ (k−t)/(t+1)` for `i ≥ t` is what makes the
single ratio `r` valid for the whole tail. -/
theorem binom_geom_step {k t : ℕ} (i : ℕ) (hti : t ≤ i) :
    (k.choose (i + 1) : ℝ)
      ≤ ((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) * (k.choose i : ℝ) := by
  have hi1pos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  have ht1pos : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos t
  -- The exact ratio identity in ℝ: C(k,i+1)·(i+1) = C(k,i)·(k−i).
  have hrec : (k.choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ)
      = (k.choose i : ℝ) * ((k - i : ℕ) : ℝ) := by
    exact_mod_cast binom_tail_ratio k i
  -- Step 1: C(k,i+1) = C(k,i)·(k−i)/(i+1).
  have hstep : (k.choose (i + 1) : ℝ)
      = (k.choose i : ℝ) * (((k - i : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ)) := by
    rw [mul_div_assoc']
    rw [eq_div_iff hi1pos.ne']
    linarith [hrec]
  rw [hstep]
  rw [mul_comm (((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ)) (k.choose i : ℝ)]
  -- Reduce to (k−i)/(i+1) ≤ (k−t)/(t+1), times the nonneg coefficient C(k,i).
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ hi1pos ht1pos]
  -- (k−i)·(t+1) ≤ (k−t)·(i+1) as naturals (then cast):
  -- k−i ≤ k−t (since t ≤ i) and t+1 ≤ i+1, so the product only grows.
  have hnat : (k - i) * (t + 1) ≤ (k - t) * (i + 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_left hti k) (by omega)
  calc ((k - i : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ)
      = (((k - i) * (t + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (((k - t) * (i + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((k - t : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ) := by push_cast; ring

/-- Iterated geometric bound: `(C(k,t+m):ℝ) ≤ C(k,t)·rᵐ`, `r = (k−t)/(t+1)`. -/
theorem binom_pow_bound {k t : ℕ} (m : ℕ) :
    (k.choose (t + m) : ℝ)
      ≤ (k.choose t : ℝ) * (((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ)) ^ m := by
  set r : ℝ := ((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) with hr
  have hrnonneg : 0 ≤ r := by rw [hr]; positivity
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : (k.choose ((t + m) + 1) : ℝ) ≤ r * (k.choose (t + m) : ℝ) := by
        rw [hr]; exact binom_geom_step (k := k) (t := t) (t + m) (Nat.le_add_right t m)
      calc (k.choose (t + (m + 1)) : ℝ)
          = (k.choose ((t + m) + 1) : ℝ) := by rw [Nat.add_succ]
        _ ≤ r * (k.choose (t + m) : ℝ) := hstep
        _ ≤ r * ((k.choose t : ℝ) * r ^ m) := mul_le_mul_of_nonneg_left ih hrnonneg
        _ = (k.choose t : ℝ) * r ^ (m + 1) := by ring

/-- Geometric partial sum bound: for `0 ≤ r < 1`, `∑_{m<n} rᵐ ≤ (1−r)⁻¹`. -/
theorem geom_partial_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ m ∈ Finset.range n, r ^ m ≤ (1 - r)⁻¹ := by
  have hpos : 0 < 1 - r := by linarith
  rw [geom_sum_eq (by linarith : r ≠ 1)]
  have heq : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [heq, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hpos]
  nlinarith [pow_nonneg h0 n]

/-! ### #2 (HEADLINE) — the closed geometric bound on the whole tail -/

/-- **Geometric tail bound.**  Fix a threshold `t` with `k < 2t+1` (so `t > k/2`).
With `r = (k−t)/(t+1) < 1`, the entire upper tail is dominated by the single
boundary coefficient `C(k,t)` times the geometric constant `(1−r)⁻¹`:
  `(S(k,t) : ℝ) = ∑_{i=t}^{k} C(k,i) ≤ C(k,t) · (1−r)⁻¹`.
Equivalently `S(k,t) ≤ C(k,t)·(t+1)/(2t−k+1)`. -/
theorem binom_tail_geometric {k t : ℕ} (hk : k < 2 * t + 1) :
    (upperTail k t : ℝ)
      ≤ (k.choose t : ℝ) * (1 - ((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ))⁻¹ := by
  set r : ℝ := ((k - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) with hr
  have hrnonneg : 0 ≤ r := by rw [hr]; positivity
  -- r < 1 because k − t < t + 1 (from k < 2t+1).
  have hrlt : r < 1 := by
    rw [hr, div_lt_one (by exact_mod_cast Nat.succ_pos t)]
    have : k - t < t + 1 := by omega
    exact_mod_cast this
  -- Reindex Icc t k = Ico t (k+1), then m ↦ t+m over range (k+1−t).
  have hIcc : Finset.Icc t k = Finset.Ico t (k + 1) := by
    ext x; simp
  have hreindex : (upperTail k t : ℝ)
      = ∑ m ∈ Finset.range (k + 1 - t), (k.choose (t + m) : ℝ) := by
    unfold upperTail
    rw [hIcc]
    push_cast
    rw [Finset.sum_Ico_eq_sum_range (fun i => (k.choose i : ℝ)) t (k + 1)]
  rw [hreindex]
  -- Termwise: C(k,t+m) ≤ C(k,t)·rᵐ.
  calc ∑ m ∈ Finset.range (k + 1 - t), (k.choose (t + m) : ℝ)
      ≤ ∑ m ∈ Finset.range (k + 1 - t), (k.choose t : ℝ) * r ^ m := by
        apply Finset.sum_le_sum
        intro m _
        rw [hr]; exact binom_pow_bound m
    _ = (k.choose t : ℝ) * ∑ m ∈ Finset.range (k + 1 - t), r ^ m := by
        rw [Finset.mul_sum]
    _ ≤ (k.choose t : ℝ) * (1 - r)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (geom_partial_le hrnonneg hrlt _)
        positivity

/-! ### #3 (HEADLINE) — the decay `S(k,t)/2^k → 0`

The geometric bound (#2) reduces the tail's `→0` to the single-coefficient decay
`C(k,⌈ck⌉)/2^k → 0` (the central/skewed binomial coefficient is sub-`2^k`).  We
package that remaining input as the hypothesis `hρ` below.  Concretely, for a
fixed `c` with `1/2 < c < 1`, binary-entropy gives `C(k,⌈ck⌉) ≤ 2^{k·H(c)}` with
`H(c) < 1`, i.e. `C(k,⌈ck⌉) ≤ 2^k · ρ^k` for `ρ = 2^{H(c)−1} < 1` — exactly
`hρ`.  We do **not** reprove the entropy bound here (see the file header); we
show it *closes the limit*, which is the analytic content needed downstream. -/

/-- **Tail decay (headline).**  Let `t : ℕ → ℕ` be thresholds with `t k > k/2`
eventually (`hk`), and suppose the boundary coefficient is sub-`2^k`:
`C(k, t k) ≤ 2^k · ρ^k` for some fixed `ρ < 1` and a geometric-constant factor
`K k = (1 − (k − t k)/(t k + 1))⁻¹` that grows only sub-exponentially, captured
by `hbound : K k ≤ B` for a fixed `B`.  Then `S(k, t k)/2^k → 0`.

This is the clean `Tendsto … (𝓝 0)` form: it follows from `binom_tail_geometric`
(`S ≤ C(k,t)·K`) and `C(k,t)·K/2^k ≤ ρ^k · B → 0`. -/
theorem binom_tail_decay
    (t : ℕ → ℕ) (ρ B : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hk : ∀ k, k < 2 * t k + 1)
    (hcoef : ∀ k, (k.choose (t k) : ℝ) ≤ 2 ^ k * ρ ^ k)
    (hK : ∀ k, (1 - ((k - t k : ℕ) : ℝ) / ((t k + 1 : ℕ) : ℝ))⁻¹ ≤ B) :
    Filter.Tendsto (fun k => (upperTail k (t k) : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
  -- 0 ≤ S/2^k ≤ ρ^k · B, and ρ^k·B → 0.
  have hKpos : ∀ k, 0 ≤ (1 - ((k - t k : ℕ) : ℝ) / ((t k + 1 : ℕ) : ℝ))⁻¹ := by
    intro k
    have hrlt : ((k - t k : ℕ) : ℝ) / ((t k + 1 : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast Nat.succ_pos (t k))]
      have : k - t k < t k + 1 := by have := hk k; omega
      exact_mod_cast this
    exact inv_nonneg.mpr (by linarith)
  -- The squeeze upper bound g k = ρ^k · B → 0.
  have hg : Filter.Tendsto (fun k => ρ ^ k * B) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun k : ℕ => ρ ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h0 : (0 : ℝ) = 0 * B := by ring
    rw [h0]
    exact this.mul_const B
  -- Squeeze: 0 ≤ S/2^k ≤ ρ^k·B.
  apply squeeze_zero (fun k => by positivity)
  · intro k
    have h2pos : (0 : ℝ) < 2 ^ k := by positivity
    -- S/2^k ≤ (C(k,t)·K)/2^k ≤ (2^k·ρ^k·K)/2^k = ρ^k·K ≤ ρ^k·B.
    rw [div_le_iff₀ h2pos]
    calc (upperTail k (t k) : ℝ)
        ≤ (k.choose (t k) : ℝ) * (1 - ((k - t k : ℕ) : ℝ) / ((t k + 1 : ℕ) : ℝ))⁻¹ :=
          binom_tail_geometric (hk k)
      _ ≤ (2 ^ k * ρ ^ k) * B := by
          apply mul_le_mul (hcoef k) (hK k) (hKpos k)
          positivity
      _ = ρ ^ k * B * 2 ^ k := by ring
  · exact hg

/-! ### #4 (STRETCH) — the Collatz bridge for `c = log₃2`

The Everett–Terras program bounds the *survivor fraction*
  `b(k) := #{ parity vectors v ∈ {0,1}^k that do NOT descend in k Terras steps} / 2^k`.
By the structural weight lemma (`CollatzNonDescentWeight`), a non-descending
vector must carry `a := (#odd steps) ≥ k·log₃2` odd steps, since the multiplicative
gain `3^a / 2^k ≥ 1` forces `3^a ≥ 2^k`, i.e. `a ≥ k·log₃2 ≈ 0.6309·k`.  Hence the
non-descenders inject into the upper tail at threshold `t(k) = ⌈k·log₃2⌉`:
  `b(k) · 2^k ≤ #{ v : |v| ≥ ⌈k·log₃2⌉ } = S(k, log₃2) = upperTail k ⌈k·log₃2⌉`,
so `b(k) ≤ upperTail k (t k) / 2^k`.

Since `log₃2 = log 2 / log 3 ≈ 0.6309 > 1/2`, every such threshold satisfies
`t(k) > k/2`, exactly the hypothesis `hk : k < 2·(t k)+1` of `binom_tail_geometric`
and `binom_tail_decay`.  Feeding the single-coefficient decay
`C(k, ⌈k·log₃2⌉) ≤ 2^k · ρ^k` (`ρ = 2^{H(log₃2)−1} < 1`, binary entropy
`H(0.6309) ≈ 0.952 < 1`) into `binom_tail_decay` yields
  `upperTail k (t k) / 2^k → 0`,  hence  `b(k) → 0`,
the "almost all Collatz orbits descend" conclusion.

The threshold's `t k > k/2` property is fully witnessed in mathlib-ℕ terms: the
rational under-approximation `t(k) = ⌈0.63·k⌉` already gives `2·t k + 1 > k`
for all `k` — the only inequality the geometric machinery needs. -/

/-- A concrete admissible threshold family `t(k) = ⌈0.63 k⌉ = (63k+99)/100` (ℕ
ceiling), used in the `#eval` sanity check above.  It satisfies `k < 2·t(k)+1`
for every `k` — the `> k/2` hypothesis of `binom_tail_geometric` /
`binom_tail_decay` — because `0.63 > 1/2`.  (`0.63` under-approximates
`log₃2 ≈ 0.6309`, so the real Collatz threshold is even larger.) -/
theorem threshold063_gt_half (k : ℕ) : k < 2 * ((63 * k + 99) / 100) + 1 := by
  -- n = 100·(n/100) + n%100 with n%100 < 100, where n = 63k+99.
  have hdm := Nat.div_add_mod (63 * k + 99) 100
  have hmod : (63 * k + 99) % 100 < 100 := Nat.mod_lt _ (by norm_num)
  omega

end CollatzBinomialTail
