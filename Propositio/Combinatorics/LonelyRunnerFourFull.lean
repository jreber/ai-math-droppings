/-
# Lonely Runner Conjecture, `k = 4`: the "gcd-pair" case (3 relative speeds, bound `1/4`)

This file attacks the honest `k = 4` Lonely Runner statement (3 distinct nonzero integer
relative speeds `v1, v2, v3`, target bound `1/4`), tracked as
`conj-2026-07-09-lonelyrunner-k4-true`. Per the failed-attempt record
(`docs/kb/failed/2026-07-09__conj-2026-07-05-007__general-k4-and-naming.json`), neither
the naive 3-variable Bézout generalization of the `k = 3` proof (`LonelyRunnerSmallK.core`)
nor a union-bound covering argument works. The Barajas–Serra "Prime Filtering Lemma" route
suggested for the fully general case is a genuine research-level construction; after
independent derivation (not reconstruction of that specific paper) this file proves a new,
honest, unconditional **partial** result covering an infinite, non-magnitude-based family
of triples, structurally different from and strictly incomparable to the earlier
`LonelyRunnerFour.lonely_runner_four_dominant` (which needs a size gap between speeds).

## What is proved: the gcd-pair construction

**Idea.** Given two of the three speeds `a, b` (`a ≠ b`), let `g = gcd(a, b)`. Apply the
`k = 3` result (`lonely_runner_three`) to `(a, b)` to get `t0` with both at distance `≥ 1/3`
(strictly more slack than the `1/4` target). Now perturb `t0` by multiples of `1/g`: since
`g ∣ a` and `g ∣ b`, this shift changes `a·t` and `b·t` only by *integers*, so their
`nid`-distance is untouched (`nid` is integer-periodic — `nid_add_intCast`). Meanwhile the
*third* speed `c`'s value `c·t` moves through a coset of the size-`M` subgroup
`(1/M)ℤ/ℤ ⊆ ℝ/ℤ`, where `M = g / gcd(c, g)`. Whenever `gcd(a,b) ∤ c`, this `M ≥ 2`, and a
direct pigeonhole/grid argument (`nid_grid_exists`) shows *some* shift in this coset lands
`c·t` at distance `≥ 1/4` from the nearest integer — with room to spare since `1/M ≤ 1/2`
exactly matches the width of the "bad" zone's complement. A Bézout identity for
`gcd(c, g)` (mirroring the `k = 3` proof's own Bézout step) converts the abstract coset
index into an explicit integer shift.

This closes the **honest `k = 4` statement whenever some pair `(a,b)` among the three speeds
satisfies BOTH `|a| ≠ |b|` (needed to invoke the `k = 3` base case, `hab` below) AND
`gcd(|a|,|b|) ∤` (the third speed's magnitude) (`hnd` below)** —
`lonely_runner_four_gcd_pair` (positive-integer form) and `lonely_runner_four_gcd_case`
(general nonzero-integer form).

**Caution on the residual (corrected after panel review):** an earlier draft of this
docstring claimed the residual open case is *exactly* the pairwise-coprime triples. That
is FALSE — it silently dropped the `|a| ≠ |b|` (`hab`) requirement, which is a genuine
extra restriction inherited from the `k = 3` base case (`lonely_runner_three` needs its two
speeds literally distinct as integers, not just as magnitudes). Concrete counterexample to
the false claim: `(v1,v2,v3) = (4,-4,6)`. This triple is NOT pairwise coprime after
reduction (`gcd(2,2,3)` reduces it to `(2,-2,3)`, and `gcd(2,2)=2≠1`), yet no relabelling
satisfies both `hab` and `hnd` simultaneously: the `(v1,v2)` pairing has `|v1|=|v2|=4`
(fails `hab`); both other pairings have `gcd(4,6)=2 ∣ 4` (fails `hnd`). So the true residual
left open by this file is **at least** the pairwise-coprime triples **and also** triples
like `(4,-4,6)` where every valid gcd-non-dividing pair happens to have equal magnitudes —
a strictly larger (and less cleanly characterized) open set than originally claimed. This
file does NOT attempt to characterize the residual precisely; it only proves the two
theorems below exactly as stated, for the reader to apply hypothesis-by-hypothesis.
Genuinely closing the general `k = 4` statement is exactly where the real
Betke–Wills/Barajas–Serra content lives and is **not** resolved here.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerSmallK

namespace LonelyRunnerFourFull

open LonelyRunnerSmallK

/-- `nid` is integer-periodic: shifting by an integer leaves the nearest-integer distance
unchanged. -/
lemma nid_add_intCast (x : ℝ) (n : ℤ) : nid (x + (n : ℝ)) = nid x := by
  unfold nid
  have h : ((round (x + (n : ℝ)) : ℤ) : ℝ) = (round x : ℝ) + (n : ℝ) := by
    rw [round_add_intCast]; push_cast; ring
  have e : x + (n : ℝ) - ((round (x + (n : ℝ)) : ℤ) : ℝ) = x - (round x : ℝ) := by
    rw [h]; ring
  rw [e]

/-- **Grid pigeonhole lemma.** For any real `x0` and any modulus `M ≥ 2`, some multiple
`k/M` of the grid spacing `1/M` shifts `x0` to nearest-integer distance `≥ 1/4`. This is
the discrete analogue of `LonelyRunnerFour.nid_shift_exists`: since the "bad" zone has
total measure exactly `1/2` and the grid spacing `1/M ≤ 1/2`, the grid cannot avoid the
good zone `[1/4, 3/4]` entirely. -/
lemma nid_grid_exists (M : ℕ) (hM : 2 ≤ M) (x0 : ℝ) :
    ∃ k : ℤ, (1 : ℝ) / 4 ≤ nid (x0 + (k : ℝ) / (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMinv : (1 : ℝ) / (M : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hMpos (by norm_num)]
    linarith
  set x0f := Int.fract x0 with hx0f
  have hf0 : 0 ≤ x0f := Int.fract_nonneg x0
  have hf1 : x0f < 1 := Int.fract_lt_one x0
  -- helper: once we know `x0f + K/M ∈ [0,1)`, `fract (x0 + K/M) = x0f + K/M`.
  have hfract : ∀ K : ℤ, 0 ≤ x0f + (K : ℝ) / (M : ℝ) → x0f + (K : ℝ) / (M : ℝ) < 1 →
      Int.fract (x0 + (K : ℝ) / (M : ℝ)) = x0f + (K : ℝ) / (M : ℝ) := by
    intro K h0 h1
    have hbase : x0f + (⌊x0⌋ : ℝ) = x0 := Int.fract_add_floor x0
    have e : x0 + (K : ℝ) / (M : ℝ) = (x0f + (K : ℝ) / (M : ℝ)) + (⌊x0⌋ : ℝ) := by
      linarith [hbase]
    rw [e, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨h0, h1⟩
  rcases lt_or_ge x0f (1 / 4 : ℝ) with h1 | h1
  · -- shift up: x0f < 1/4
    set realK : ℝ := (M : ℝ) * (1 / 4 - x0f) with hrealK
    have hrealKpos : 0 < realK := mul_pos hMpos (by linarith)
    set k : ℤ := ⌈realK⌉ with hkdef
    have hk_ge : realK ≤ (k : ℝ) := Int.le_ceil realK
    have hk_lt : (k : ℝ) < realK + 1 := Int.ceil_lt_add_one realK
    refine ⟨k, ?_⟩
    have hkM_ge : (1 / 4 - x0f : ℝ) ≤ (k : ℝ) / (M : ℝ) := by
      rw [le_div_iff₀ hMpos]
      rw [hrealK] at hk_ge; linarith [hk_ge]
    have hkM_lt : (k : ℝ) / (M : ℝ) < (1 / 4 - x0f) + 1 / (M : ℝ) := by
      rw [div_lt_iff₀ hMpos]
      rw [hrealK] at hk_lt
      have : (k : ℝ) < (M : ℝ) * (1 / 4 - x0f) + 1 := hk_lt
      have hexp : ((1 / 4 - x0f) + 1 / (M : ℝ)) * (M : ℝ)
          = (M : ℝ) * (1 / 4 - x0f) + 1 := by field_simp
      rw [hexp]; exact this
    have hlow : (1 : ℝ) / 4 ≤ x0f + (k : ℝ) / (M : ℝ) := by linarith
    have hhigh : x0f + (k : ℝ) / (M : ℝ) < 3 / 4 := by linarith
    have hfr := hfract k (by linarith) (by linarith)
    rw [nid_eq, hfr]
    exact le_min hlow (by linarith)
  · rcases lt_or_ge (3 / 4 : ℝ) x0f with h2 | h2
    · -- shift down: x0f > 3/4
      set realK : ℝ := (M : ℝ) * (x0f - 3 / 4) with hrealK
      have hrealKpos : 0 < realK := mul_pos hMpos (by linarith)
      set k : ℤ := ⌈realK⌉ with hkdef
      have hk_ge : realK ≤ (k : ℝ) := Int.le_ceil realK
      have hk_lt : (k : ℝ) < realK + 1 := Int.ceil_lt_add_one realK
      have hkM_ge : (x0f - 3 / 4 : ℝ) ≤ (k : ℝ) / (M : ℝ) := by
        rw [le_div_iff₀ hMpos]
        rw [hrealK] at hk_ge; linarith [hk_ge]
      have hkM_lt : (k : ℝ) / (M : ℝ) < (x0f - 3 / 4) + 1 / (M : ℝ) := by
        rw [div_lt_iff₀ hMpos]
        rw [hrealK] at hk_lt
        have : (k : ℝ) < (M : ℝ) * (x0f - 3 / 4) + 1 := hk_lt
        have hexp : ((x0f - 3 / 4) + 1 / (M : ℝ)) * (M : ℝ)
            = (M : ℝ) * (x0f - 3 / 4) + 1 := by field_simp
        rw [hexp]; exact this
      -- work with `K := -k` directly, expressed via its own cast from the start
      refine ⟨-k, ?_⟩
      have hcast : (((-k : ℤ)) : ℝ) / (M : ℝ) = -((k : ℝ) / (M : ℝ)) := by push_cast; ring
      have hlow : (1 : ℝ) / 4 < x0f + (((-k : ℤ)) : ℝ) / (M : ℝ) := by rw [hcast]; linarith
      have hhigh : x0f + (((-k : ℤ)) : ℝ) / (M : ℝ) ≤ 3 / 4 := by rw [hcast]; linarith
      have hfr := hfract (-k) (by linarith) (by linarith)
      rw [nid_eq, hfr]
      exact le_min (by linarith) (by linarith)
    · -- already good: 1/4 ≤ x0f ≤ 3/4
      refine ⟨0, ?_⟩
      have : x0 + ((0 : ℤ) : ℝ) / (M : ℝ) = x0 := by push_cast; ring
      rw [this, nid_eq]
      exact le_min h1 (by linarith)

/-- Isolated numeric fact, proved outside any cluttered `let`-bound `gcd`/`div` context so
that `omega` sees a clean linear goal. -/
lemma two_le_of_ne_zero_one (M : ℕ) (h0 : M ≠ 0) (h1 : M ≠ 1) : 2 ≤ M := by omega

/-- **The gcd-pair construction, positive-integer form.** Given positive distinct `a ≠ b`
and a third positive `c` such that `gcd(a,b)` does *not* divide `c`, there is a time `t`
with `nid(a·t), nid(b·t), nid(c·t)` all `≥ 1/4`. -/
theorem lonely_runner_four_gcd_pair (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (_hc : 1 ≤ c)
    (hab : a ≠ b) (hnd : ¬ (Nat.gcd a b ∣ c)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((a : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((b : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((c : ℝ) * t) := by
  set g : ℕ := Nat.gcd a b with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (by omega)
  set d : ℕ := Nat.gcd c g with hddef
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right c hgpos
  have hdg : d ∣ g := Nat.gcd_dvd_right c g
  have hdneg : d ≠ g := by
    intro he
    exact hnd (he ▸ Nat.gcd_dvd_left c g)
  have hdlt : d < g := lt_of_le_of_ne (Nat.le_of_dvd hgpos hdg) hdneg
  set M : ℕ := g / d with hMdef
  have hMd : M * d = g := Nat.div_mul_cancel hdg
  have hM0 : M ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hMd; omega
  have hM1 : M ≠ 1 := by
    intro h; rw [h, Nat.one_mul] at hMd; omega
  have hM2 : 2 ≤ M := two_le_of_ne_zero_one M hM0 hM1
  -- Step 1: the k=3 result for the fixed pair (a,b), with slack 1/3 > 1/4.
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hbZ : (b : ℤ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have habZ : (a : ℤ) ≠ (b : ℤ) := by exact_mod_cast hab
  obtain ⟨t0, ht1, ht2⟩ := lonely_runner_three (a : ℤ) (b : ℤ) haZ hbZ habZ
  have ht1' : (1 : ℝ) / 3 ≤ nid ((a : ℝ) * t0) := by push_cast at ht1; exact ht1
  have ht2' : (1 : ℝ) / 3 ≤ nid ((b : ℝ) * t0) := by push_cast at ht2; exact ht2
  -- Step 2: Bézout identity for d = gcd(c, g).
  have hgcdZ : Int.gcd (c : ℤ) (g : ℤ) = d := by rw [Int.gcd_natCast_natCast]
  have hbez : (d : ℤ) = (c : ℤ) * Int.gcdA (c : ℤ) (g : ℤ) + (g : ℤ) * Int.gcdB (c : ℤ) (g : ℤ) := by
    have h := Int.gcd_eq_gcd_ab (c : ℤ) (g : ℤ)
    rw [hgcdZ] at h
    exact_mod_cast h
  set X : ℤ := Int.gcdA (c : ℤ) (g : ℤ) with hXdef
  set Y : ℤ := Int.gcdB (c : ℤ) (g : ℤ) with hYdef
  -- Step 3: the grid pigeonhole for the third speed `c`.
  obtain ⟨k, hk⟩ := nid_grid_exists M hM2 ((c : ℝ) * t0)
  set j : ℤ := k * X with hjdef
  set t : ℝ := t0 + (j : ℝ) / (g : ℝ) with htdef
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgR
  refine ⟨t, ?_, ?_, ?_⟩
  · -- a·t = a·t0 + integer
    have hga : g ∣ a := Nat.gcd_dvd_left a b
    obtain ⟨a', ha'⟩ := hga
    have e : (a : ℝ) * t = (a : ℝ) * t0 + ((a' : ℤ) * j : ℤ) := by
      rw [htdef, ha']
      push_cast
      field_simp
    rw [e, nid_add_intCast]
    linarith [ht1']
  · -- b·t = b·t0 + integer
    have hgb : g ∣ b := Nat.gcd_dvd_right a b
    obtain ⟨b', hb'⟩ := hgb
    have e : (b : ℝ) * t = (b : ℝ) * t0 + ((b' : ℤ) * j : ℤ) := by
      rw [htdef, hb']
      push_cast
      field_simp
    rw [e, nid_add_intCast]
    linarith [ht2']
  · -- c·t = c·t0 + k/M + integer
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
    have hbezR : (d : ℝ) = (c : ℝ) * (X : ℝ) + (g : ℝ) * (Y : ℝ) := by exact_mod_cast hbez
    have hdMeqR : (M : ℝ) * (d : ℝ) = (g : ℝ) := by exact_mod_cast hMd
    have hcX : (c : ℝ) * (X : ℝ) = (d : ℝ) - (g : ℝ) * (Y : ℝ) := by linarith [hbezR]
    have keyEq : (M : ℝ) * ((c : ℝ) * ((k : ℝ) * (X : ℝ))) + (M : ℝ) * ((k : ℝ) * (Y : ℝ)) * (g : ℝ)
        = (k : ℝ) * (g : ℝ) := by
      calc (M : ℝ) * ((c : ℝ) * ((k : ℝ) * (X : ℝ))) + (M : ℝ) * ((k : ℝ) * (Y : ℝ)) * (g : ℝ)
          = (k : ℝ) * ((M : ℝ) * ((c : ℝ) * (X : ℝ))) + (M : ℝ) * (k : ℝ) * (Y : ℝ) * (g : ℝ) := by
            ring
        _ = (k : ℝ) * ((M : ℝ) * ((d : ℝ) - (g : ℝ) * (Y : ℝ)))
            + (M : ℝ) * (k : ℝ) * (Y : ℝ) * (g : ℝ) := by rw [hcX]
        _ = (k : ℝ) * ((M : ℝ) * (d : ℝ)) - (k : ℝ) * (M : ℝ) * (g : ℝ) * (Y : ℝ)
            + (M : ℝ) * (k : ℝ) * (Y : ℝ) * (g : ℝ) := by ring
        _ = (k : ℝ) * (g : ℝ) - (k : ℝ) * (M : ℝ) * (g : ℝ) * (Y : ℝ)
            + (M : ℝ) * (k : ℝ) * (Y : ℝ) * (g : ℝ) := by rw [hdMeqR]
        _ = (k : ℝ) * (g : ℝ) := by ring
    have e : (c : ℝ) * t = ((c : ℝ) * t0 + (k : ℝ) / (M : ℝ)) + ((-(k * Y) : ℤ) : ℝ) := by
      rw [htdef, hjdef]
      push_cast
      rw [mul_add, ← mul_div_assoc]
      have hdiv : (c : ℝ) * ((k : ℝ) * (X : ℝ)) / (g : ℝ)
          = (k : ℝ) / (M : ℝ) + (-((k : ℝ) * (Y : ℝ))) := by
        field_simp
        linear_combination keyEq
      rw [hdiv]
      ring
    rw [e, nid_add_intCast]
    exact hk

/-- **The gcd-pair construction, general nonzero-integer form.** Three distinct nonzero
integer speeds `v1, v2, v3` (`v1, v2` required to differ even in magnitude — the natural
"generic pair" restriction) such that `gcd(|v1|, |v2|)` does *not* divide `|v3|`: there is a
time `t` with `nid(vi·t) ≥ 1/4` for all three `i`. This is the honest `k = 4` Lonely Runner
statement (target bound `1/4`, 3 relative speeds), proved unconditionally whenever this
gcd-pair non-degeneracy condition holds for *some* choice of which speed is "third" — by
symmetry this lemma may be applied with any relabelling of `v1, v2, v3`. -/
theorem lonely_runner_four_gcd_case (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (hab : v1.natAbs ≠ v2.natAbs)
    (hnd : ¬ (Nat.gcd v1.natAbs v2.natAbs ∣ v3.natAbs)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * t) := by
  have ha1 : 1 ≤ v1.natAbs := by
    have : v1.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h1
    omega
  have ha2 : 1 ≤ v2.natAbs := by
    have : v2.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h2
    omega
  have ha3 : 1 ≤ v3.natAbs := by
    have : v3.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h3
    omega
  obtain ⟨t, ht1, ht2, ht3⟩ :=
    lonely_runner_four_gcd_pair v1.natAbs v2.natAbs v3.natAbs ha1 ha2 ha3 hab hnd
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [nid_natAbs_mul]; exact ht1
  · rw [nid_natAbs_mul]; exact ht2
  · rw [nid_natAbs_mul]; exact ht3

end LonelyRunnerFourFull
