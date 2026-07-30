/-
# Maximal-segment door parity: T-junctions provably do not change boundary parity

## Motivation and the precise gap this addresses

`MonskyDissectionBoundaryScope`'s own scope note documents a genuine counterexample
to the naive equivalence "`MonskySpernerParity.mult inc e = 1` (i.e. `e` is a
combinatorial *boundary* edge of the abstract door-counting engine) `⟺` `e` is a
genuine `SameSide` edge on the unit square's perimeter": split the unit square by the
main diagonal `(0,0)–(1,1)` into a triangle `A`, then further subdivide the other half
via a Steiner point `M` on the diagonal into two triangles `B`, `C`. Then the diagonal
is covered by *three* raw edges — `A`'s full edge `s((0,0),(1,1))` and the two half
edges `s((0,0),M)`, `s(M,(1,1))` of `B`, `C` — and *each* has multiplicity exactly `1`,
despite being interior, not perimeter.

This raises a real worry for the "maximal boundary segment" reformulation floated by
`conj-2026-07-19-004` and the frontier note `monsky_hbdry_coordinate_bridge_2026_07_29`
(route (b)): `MonskySpernerParity.boundary (incS S) (doorSet S)` — the abstract engine's
`mult = 1`-filtered set that `hbdry` must be odd on — can contain such spurious interior
edges alongside genuine perimeter ones. For `hbdry` to be provable in general, these
spurious contributions would need to always cancel out **in parity** against the
genuine perimeter contribution captured by `MonskyBoundaryOddness.boundary_doors_odd`.

**Is that cancellation actually true, or can an adversarial T-junction break it?**
Naively it looks fragile: on a *general* 3-colouring, splitting a two-point edge
`P–Q` (say coloured `1`, `2` — a genuine `{1,2}`-door) into `P–R–Q` via a middle point
`R` of colour `0` kills the door entirely (`pairIs12` needs literally colours `{1,2}`,
and neither sub-edge `P–R`, `R–Q` has that pattern) — so the "before" door-count is `1`
and the "after" is `0`: NOT parity-preserving in general. If such an `R` could occur as
a genuine T-junction point on a line through a real `{1,2}`-door edge of a Monsky
dissection, `hbdry` would be **false** for the abstract engine, and this whole line of
attack would be dead.

## The resolution: `no_dichromatic_line` rules out the adversarial case

The key fact that saves the argument is already proved in this tree:
`MonskyRainbowDetCorrected.no_dichromatic_line_real` — **no straight line meets all
three colour classes** of `MonskyBoundaryOddness.col`'s corrected (Aigner–Ziegler/Fan)
convention. Consequently, if `P` has colour `1` and `Q` has colour `2` (so `P–Q` is a
door), **any** third point `R` on the line through `P` and `Q` is forced to avoid
colour `0` — the adversarial `R` above is geometrically impossible. More generally, any
finite family of *collinear* points avoids at least one of the three colours
(`collinear_avoids_one_color` below), and this is enough to make the door-count parity
along the whole collinear path depend *only* on its two extreme endpoints, regardless
of how many intermediate (T-junction) points subdivide it — exactly the "maximal
segment" invariance that `conj-2026-07-19-004` conjectured, now made precise and
proved: `collinear_path_doorParity`.

The concrete corollary matching `MonskyDissectionBoundaryScope`'s own counterexample
pattern is `tjunction_doorness_sum_even`: for collinear `A`, `M`, `B`, the sum of the
three raw-edge door-indicators (`A–B` as a single edge, plus `A–M` and `M–B` as the
T-junction's two sub-edges) is always **even** — so this specific spurious-interior
scenario contributes nothing to `boundary.card`'s parity, exactly resolving the worry
the scope note raised.

## What this file does NOT close

This file supplies the load-bearing **mathematical fact** that a maximal-segment
reformulation of `hbdry` would need (endpoint-determined, subdivision-invariant door
parity on collinear points) — but it does **not** assemble the full planar-subdivision
argument needed to discharge `hbdry` in `MonskyThreeColorDoors.exists_rainbow_of_odd_
boundary` for a general `MonskyDissectionHlocal.IsDissection S`. That assembly would
still need, for an *arbitrary* dissection:

1. A partition of the dissection's full raw edge set `MonskyDissectionHlocal.allEdges S`
   into maximal collinear groups (one group per maximal line segment actually realised
   by the dissection's geometry);
2. A proof that raw edges within one such group are always *compatible* with a single
   linear order along that line — i.e. that a dissection genuinely cannot exhibit two
   edges on the same line that partially overlap without nesting (a genuine geometric
   consequence of `IsDissection.interiorDisjoint`/`covers`, not proved here, and not
   otherwise available in this tree — this is the "planar-subdivision machinery" the
   frontier note flags as missing); and
3. Identifying exactly the four groups corresponding to the unit square's four sides
   with `MonskyBoundaryOddness`'s `bx`/`ry`/`tx`/`ly` sequences, so that
   `boundary_doors_odd` supplies the odd total while every other (interior) group
   contributes an even total via the theorem proved here.

Step 2 in particular is a nontrivial planar-geometry fact about `Finset`-of-triangles
dissections that this file does not attempt; `collinear_path_doorParity` is proved for
an *arbitrary* finite sequence of collinear points, taking their pairwise adjacency (in
the induced linear order) as *given* by the sequence's indexing, not derived from
`IsDissection`. So `hbdry` remains open after this file — but the specific "does an
adversarial T-junction break the parity" question the counterexample raised is
answered: **no, it cannot**, and the reason (`no_dichromatic_line`) is now a proved
Lean theorem, not a hope.

Axiom-clean throughout: only elementary order/algebra (`ring`, real inequalities via
`not_and_or`/`not_lt`/`not_le`), `Finset`/`ZMod 2`/`Fin` bookkeeping, and the already
axiom-clean imported Monsky machinery (`MonskyBoundaryOddness`, `MonskyRainbowDetCorrected`,
`MonskyThreeColorDoors`); no `sorry`, no project `axiom`, no `native_decide`.
-/

import Propositio.Geometry.Monsky.MonskyBoundaryOddness
import Propositio.Geometry.Monsky.MonskyRainbowDetCorrected
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskyDichromaticLineReal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MonskyBoundarySegmentParity

open MonskyBoundaryOddness MonskyThreeColorDoors MonskyDichromaticLineReal

/-! ## Part 1: extracting the raw valuation hypotheses from a `col` value

`MonskyBoundaryOddness.col` is defined by a nested `if`; these three lemmas invert
that definition, recovering the defining valuation inequalities from each of the three
possible output values. -/

/-- If a point is coloured `0`, both its coordinates have `ν < 1` (the strict
colour-0 regime of `MonskyBoundaryOddness.col`'s Aigner-Ziegler/Fan convention). -/
lemma col_eq_zero_imp {x y : ℝ} (h : col x y = 0) : νR x < 1 ∧ νR y < 1 := by
  unfold col at h
  split_ifs at h with h1 h2
  · exact h1
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- If a point is coloured `1`, it satisfies the (non-strict) colour-1 regime. -/
lemma col_eq_one_imp {x y : ℝ} (h : col x y = 1) : 1 ≤ νR x ∧ νR y ≤ νR x := by
  unfold col at h
  split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · exact h2
  · exact absurd h (by decide)

/-- If a point is coloured `2`, it satisfies the (non-strict) colour-2 regime.
The `else`-branch requires deriving this from the *negation* of the first two
conditions (an explicit real-order case split, since neither hypothesis is directly
one of the four `Nondegenerate`-style algebraic facts used elsewhere in this tree). -/
lemma col_eq_two_imp {x y : ℝ} (h : col x y = 2) : 1 ≤ νR y ∧ νR x < νR y := by
  unfold col at h
  split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rcases not_and_or.mp h1 with hx1 | hy1
    · rw [not_lt] at hx1
      rcases not_and_or.mp h2 with hx1' | hxy
      · rw [not_le] at hx1'
        exact absurd hx1' (not_lt.mpr hx1)
      · rw [not_le] at hxy
        exact ⟨le_trans hx1 hxy.le, hxy⟩
    · rw [not_lt] at hy1
      rcases not_and_or.mp h2 with hx1' | hxy
      · rw [not_le] at hx1'
        exact ⟨hy1, lt_of_lt_of_le hx1' hy1⟩
      · rw [not_le] at hxy
        exact ⟨hy1, hxy⟩

/-! ## Part 2: no three colours on a common line

The central geometric fact, a direct corollary of `MonskyRainbowDetCorrected.
no_dichromatic_line_real`: any finite family of collinear points avoids at least one
of the three colours. -/

/-- **Collinear points avoid at least one colour.** For any (possibly infinite-index)
family of points lying on a common line `a·x + b·y = c`, some colour `k : Fin 3` is
never realised among them. This is the precise "no dichromatic line" fact restated as
"the colour-set of a line has size `≤ 2`" — the form actually needed below. -/
theorem collinear_avoids_one_color {ι : Type*}
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (pts : ι → ℝ × ℝ) (hline : ∀ i, a * (pts i).1 + b * (pts i).2 = c) :
    ∃ k : Fin 3, ∀ i, col (pts i).1 (pts i).2 ≠ k := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon 0
  obtain ⟨i1, hi1⟩ := hcon 1
  obtain ⟨i2, hi2⟩ := hcon 2
  obtain ⟨h0x, h0y⟩ := col_eq_zero_imp hi0
  obtain ⟨h1x, h1xy⟩ := col_eq_one_imp hi1
  obtain ⟨h2y, h2yx⟩ := col_eq_two_imp hi2
  exact MonskyRainbowDetCorrected.no_dichromatic_line_real a b c hab
    (pts i0).1 (pts i0).2 (pts i1).1 (pts i1).2 (pts i2).1 (pts i2).2
    h0x h0y h1x h1xy h2y h2yx (hline i0) (hline i1) (hline i2)

/-! ## Part 3: a `{1,2}`-door needs both endpoints to avoid whichever colour is
missing along their line -/

/-- If two colours both avoid a fixed colour `k ∈ {1, 2}`, they cannot form a
`{1,2}`-door (`pairIs12` needs one endpoint to *be* `k`). A finite decidable check. -/
lemma pairIs12_false_of_avoid {a b k : Fin 3} (hk : k = 1 ∨ k = 2)
    (ha : a ≠ k) (hb : b ≠ k) : ¬ pairIs12 a b := by
  rcases hk with rfl | rfl <;> revert a b ha hb <;> decide

/-! ## Part 4: collinear-path door parity, generalised beyond `MonskyBoundaryOddness`'s
fixed-coordinate sides -/

/-- If every point of a path avoids colour `1` or colour `2`, **none** of its edges
can be a door: `sideDoors` is exactly `0`, not merely even. Generalises
`MonskyBoundaryOddness.bottom_sideDoors_eq_zero`/`left_sideDoors_eq_zero` (which are
the special cases `k = 2`/`k = 1` on a fixed coordinate) to an arbitrary point
sequence and either of the two colours. -/
theorem sideDoors_eq_zero_of_avoid {n : ℕ} (xs ys : Fin (n + 1) → ℝ) (k : Fin 3)
    (hk : k = 1 ∨ k = 2) (havoid : ∀ i, col (xs i) (ys i) ≠ k) :
    sideDoors xs ys = 0 := by
  unfold sideDoors
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_false_of_mem
  intro i _ hpair
  exact pairIs12_false_of_avoid hk (havoid i.castSucc) (havoid i.succ) hpair

/-- If every point of a path avoids colour `0`, the `{1,2}`-door count is
endpoint-determined (`pairIs12` of the two extreme colours), via
`MonskyBoundaryOddness.sideDoors_eq_boolParity` restated in `pairIs12` form instead
of the raw Boolean "is it colour 2" tag. -/
theorem sideDoors_parity_of_avoid_zero {n : ℕ} (xs ys : Fin (n + 1) → ℝ)
    (havoid : ∀ i, col (xs i) (ys i) ≠ 0) :
    (sideDoors xs ys : ZMod 2)
      = if pairIs12 (col (xs 0) (ys 0)) (col (xs (Fin.last n)) (ys (Fin.last n)))
          then 1 else 0 := by
  rw [sideDoors_eq_boolParity xs ys havoid]
  by_cases hcase :
      decide (col (xs 0) (ys 0) = 2) = decide (col (xs (Fin.last n)) (ys (Fin.last n)) = 2)
  · rw [if_pos hcase, if_neg]
    intro hp
    exact ((pairIs12_iff_decide_ne _ _ (havoid 0) (havoid (Fin.last n))).mp hp) hcase
  · rw [if_neg hcase, if_pos]
    exact (pairIs12_iff_decide_ne _ _ (havoid 0) (havoid (Fin.last n))).mpr hcase

/-- **Maximal-segment door parity is endpoint-determined.** For any finite sequence
of *collinear* points, the parity of the `{1,2}`-door count along the path depends
only on the two endpoints' colours (via `pairIs12`) — exactly the "single
unsubdivided edge" door indicator. In particular, a T-junction that subdivides one
segment into several collinear sub-edges changes nothing about the total
door-count's PARITY: this is `conj-2026-07-19-004`'s conjectured invariance, made
precise and proved here via `no_dichromatic_line`. -/
theorem collinear_path_doorParity {n : ℕ}
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (xs ys : Fin (n + 1) → ℝ) (hline : ∀ i, a * xs i + b * ys i = c) :
    (sideDoors xs ys : ZMod 2)
      = if pairIs12 (col (xs 0) (ys 0)) (col (xs (Fin.last n)) (ys (Fin.last n)))
          then 1 else 0 := by
  obtain ⟨k, hk⟩ := collinear_avoids_one_color a b c hab (fun i => (xs i, ys i)) hline
  fin_cases k
  · exact sideDoors_parity_of_avoid_zero xs ys hk
  · have hzero := sideDoors_eq_zero_of_avoid xs ys 1 (Or.inl rfl) hk
    rw [hzero, if_neg]
    · simp
    · exact pairIs12_false_of_avoid (Or.inl rfl) (hk 0) (hk (Fin.last n))
  · have hzero := sideDoors_eq_zero_of_avoid xs ys 2 (Or.inr rfl) hk
    rw [hzero, if_neg]
    · simp
    · exact pairIs12_false_of_avoid (Or.inr rfl) (hk 0) (hk (Fin.last n))

/-! ## Part 5: the concrete T-junction cancellation, matching
`MonskyDissectionBoundaryScope`'s own counterexample pattern -/

/-- **A T-junction subdividing a segment into two collinear pieces changes nothing
about the total door-count PARITY relative to treating it as one edge.**
Concretely: if `A`, `M`, `B` are collinear, the {1,2}-doorness of the single edge
`(A,B)` and the SUM of the {1,2}-doorness of the two sub-edges `(A,M)`, `(M,B)` add
up to an EVEN total. This directly answers the worry raised by
`MonskyDissectionBoundaryScope`'s diagonal/Steiner-point counterexample: even though
`(A,B)`, `(A,M)`, `(M,B)` can each individually have `MonskySpernerParity.mult = 1`
(each used by a different triangle: `A` uses the diagonal directly, `M`'s two
neighbours each use one half), their combined contribution to a `mult = 1`-filtered
door count is parity-neutral, so it cannot flip `hbdry`'s parity relative to the pure
four-sides count of `MonskyBoundaryOddness.boundary_doors_odd`. -/
theorem tjunction_doorness_sum_even
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (Ax Ay Mx My Bx By : ℝ)
    (hA : a * Ax + b * Ay = c) (hM : a * Mx + b * My = c) (hB : a * Bx + b * By = c) :
    Even ((if pairIs12 (col Ax Ay) (col Bx By) then 1 else 0)
        + (if pairIs12 (col Ax Ay) (col Mx My) then 1 else 0)
        + (if pairIs12 (col Mx My) (col Bx By) then 1 else 0)) := by
  set xs : Fin 3 → ℝ := ![Ax, Mx, Bx] with hxs
  set ys : Fin 3 → ℝ := ![Ay, My, By] with hys
  have hline : ∀ i : Fin 3, a * xs i + b * ys i = c := by
    intro i
    fin_cases i <;> simp [hxs, hys, hA, hM, hB]
  have hpar := collinear_path_doorParity a b c hab xs ys hline
  have hsd : sideDoors xs ys
      = (if pairIs12 (col (xs 0) (ys 0)) (col (xs 1) (ys 1)) then 1 else 0)
        + (if pairIs12 (col (xs 1) (ys 1)) (col (xs 2) (ys 2)) then 1 else 0) := by
    unfold sideDoors
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
    rw [Finset.filter_insert, Finset.filter_singleton]
    split_ifs with h0 h1 h1 <;> simp_all [Fin.castSucc, Fin.succ]
  have hx0 : xs 0 = Ax := rfl
  have hx1 : xs 1 = Mx := rfl
  have hx2 : xs 2 = Bx := rfl
  have hy0 : ys 0 = Ay := rfl
  have hy1 : ys 1 = My := rfl
  have hy2 : ys 2 = By := rfl
  have hlast0 : xs (Fin.last 2) = Bx := hx2
  have hlast1 : ys (Fin.last 2) = By := hy2
  rw [hlast0, hlast1, hx0, hy0] at hpar
  rw [hsd, hx0, hy0, hx1, hy1, hx2, hy2] at hpar
  -- `hpar : (natsum : ZMod 2) = if pairIs12 (col Ax Ay) (col Bx By) then 1 else 0`
  -- and the `if`-branch matches the target's leading summand, so the natural-number
  -- claim reduces to `d0 + d1 + d2 ≡ 2*d0 ≡ 0 (mod 2)`.
  set d1 : ℕ := if pairIs12 (col Ax Ay) (col Mx My) then 1 else 0 with hd1
  set d2 : ℕ := if pairIs12 (col Mx My) (col Bx By) then 1 else 0 with hd2
  set d0 : ℕ := if pairIs12 (col Ax Ay) (col Bx By) then 1 else 0 with hd0
  have hd0cast : ((d0 : ℕ) : ZMod 2)
      = if pairIs12 (col Ax Ay) (col Bx By) then (1 : ZMod 2) else 0 := by
    rw [hd0]; split_ifs <;> simp
  have hZ : ((d1 + d2 : ℕ) : ZMod 2) = ((d0 : ℕ) : ZMod 2) := by
    rw [hd0cast]; exact hpar
  have hzero : ((d0 + d1 + d2 : ℕ) : ZMod 2) = 0 := by
    have hstep : ((d0 + (d1 + d2) : ℕ) : ZMod 2) = ((d0 : ℕ) : ZMod 2) + ((d0 : ℕ) : ZMod 2) := by
      rw [Nat.cast_add, hZ]
    rw [show d0 + d1 + d2 = d0 + (d1 + d2) from by ring, hstep]
    have h2 : ((d0 : ℕ) : ZMod 2) + ((d0 : ℕ) : ZMod 2) = 2 * ((d0 : ℕ) : ZMod 2) := by ring
    rw [h2, show (2 : ZMod 2) = 0 from by decide, zero_mul]
  exact ZMod.natCast_eq_zero_iff_even.mp hzero

end MonskyBoundarySegmentParity
