/-
# The unit square's boundary has an odd number of {1,2}-colour doors

This file supplies the concrete geometric content standing behind the
`hbdry` hypothesis of `MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`:
for a genuine 2-adic 3-colouring of `ℝ × ℝ`, the four sides of the unit
square `[0,1]²`, however finely subdivided by a triangulation's boundary
vertices, together carry an *odd* number of `{1,2}`-colour "doors"
(`MonskyThreeColorDoors.pairIs12`).

## Sourcing the corner-colouring convention

`MonskyDichromaticLineReal`'s documented colour convention

* colour 0 : `ν x ≤ 1 ∧ ν y ≤ 1`
* colour 1 : `1 < ν x ∧ ν y ≤ ν x`
* colour 2 : `1 < ν y ∧ ν x < ν y`

is **degenerate at the unit square's corners**: since `ν 0 = 0 ≤ 1` and
`ν 1 = 1 ≤ 1`, all four corners `(0,0), (1,0), (1,1), (0,1)` satisfy colour
0's (non-strict) inequalities and collapse to a single colour — this is
exactly the trap flagged in `conj-2026-07-09-006`.

The primary source (Monsky 1970, via Aigner–Ziegler *Proofs from THE BOOK*,
"One square and an odd number of triangles"; cross-checked here against
Roger Fan's expository write-up, *Monsky's Theorem*, March 2022, §3.1,
which reproduces the Aigner–Ziegler coloring verbatim in terms of the
2-adic *absolute value* `|·|₂ = ν`) states the coloring as

```
(x, y) is coloured
  blue   if |x|₂ ≥ |y|₂  and |x|₂ ≥ 1
  green  if |x|₂ <  |y|₂  and |y|₂ ≥ 1
  red    if |x|₂ < 1      and |y|₂ < 1
```

i.e., in `ν`-notation (`ν = |·|₂`, matching this repo's multiplicative
convention exactly):

* colour 0 (red)  : `ν x < 1 ∧ ν y < 1`            (**strict** on colour 0)
* colour 1 (blue) : `1 ≤ ν x ∧ ν y ≤ ν x`           (**non-strict** threshold)
* colour 2 (green): `1 ≤ ν y ∧ ν x < ν y`           (**non-strict** threshold)

The fix relative to `MonskyDichromaticLineReal` is exactly to swap which of
the two "regimes" (colour 0 vs colours 1/2) gets the strict inequality at
the `ν = 1` threshold. This one-line correction, sourced and hand-verified
against the corner computation in Fan's Lemma 3.4 proof (which explicitly
states "(0,0) is red, (1,0) and (1,1) are blue, and (0,1) is green"),
resolves the degeneracy: with the corrected convention,
`col 0 0 = 0`, `col 1 0 = 1`, `col 1 1 = 1`, `col 0 1 = 2` — four
genuinely non-degenerate corner colours (see `col_origin`, `col_10`,
`col_11`, `col_01` below).

(Separately: `rainbow_det_valuation` in `MonskyDichromaticLineReal`, which
depends on the colour-1/2 vertices having the *strict* `1 < ν` inequality,
remains provable after this correction — the strictness needed for each
of its five off-diagonal domination steps can be supplied instead by the
(now strict) colour-0 hypotheses `ν x0 < 1`/`ν y0 < 1`, hand-checked but
not re-proved in this file, which is scoped to `hbdry` only.)

## The boundary-oddness argument

With the corrected convention, direct computation (no case-work on the
"other" coordinate needed, since colour 0 requires *both* coordinates
`< 1` while colours 1/2 only ever *reference* the coordinate that is
pinned to the edge) shows:

* the **bottom** edge (`y = 0`) never sees colour 2 (`col_bottom_ne_two`);
* the **left** edge (`x = 0`) never sees colour 1 (`col_left_ne_one`);
* the **right** edge (`x = 1`) never sees colour 0 (`col_right_ne_zero`) —
  every point is coloured 1 or 2;
* the **top** edge (`y = 1`) never sees colour 0 (`col_top_ne_zero`) —
  every point is coloured 1 or 2.

Hence the bottom and left edges contribute **zero** `{1,2}`-doors
structurally (no vertex on them can be an endpoint of such a door), while
the right and top edges are genuine 2-colourings of `{1, 2}`, to which
`MonskyPathParity.door_card_parity` applies directly (via the Boolean
encoding "is this vertex colour 2?"). The right edge's endpoints
`(1,0), (1,1)` are *both* colour 1 (even contribution); the top edge's
endpoints `(1,1), (0,1)` are colours 1 and 2 respectively (odd
contribution). Total: `0 + even + odd + 0 = odd`.

`boundary_doors_odd` assembles this into the final statement: for *any*
four finite point-sequences forming the bottom/right/top/left sides of a
triangulation's boundary (matching up at the four actual corners), the
total `{1,2}`-door count is odd.
-/

import Propositio.Geometry.Monsky.MonskyDichromaticLineReal
import Propositio.Geometry.Monsky.MonskyThreeColorDoors
import Propositio.Geometry.Monsky.MonskyPathParity
import Propositio.Geometry.Monsky.MonskySpernerParity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

namespace MonskyBoundaryOddness

open MonskyDichromaticLineReal MonskyThreeColorDoors

/-! ## The corrected, non-degenerate 3-colouring -/

/-- The corrected Monsky 3-colouring of `ℝ × ℝ` (curried), sourced from
Aigner–Ziegler / Fan §3.1 (see the file docstring): colour 0 is the
*strict* `ν < 1` regime, colours 1/2 the *non-strict* `ν ≥ 1` regime. This
is the fix to the degenerate convention documented in
`MonskyDichromaticLineReal`. -/
noncomputable def col (x y : ℝ) : Fin 3 :=
  open Classical in
  if νR x < 1 ∧ νR y < 1 then 0
  else if 1 ≤ νR x ∧ νR y ≤ νR x then 1
  else 2

/-- `0 < 1` in `ΓR`, needed repeatedly below: witnessed by `νR 2 < 1`
together with `0 ≤ νR 2`. -/
lemma zero_lt_one_ΓR : (0 : ΓR) < 1 :=
  lt_of_le_of_lt zero_le' νR_spec.1

lemma νR_one_eq_one : νR 1 = 1 := νR.map_one

/-- `¬ (1 : ΓR) ≤ 0`, the key fact making colours 1/2's threshold
condition `1 ≤ ν _` fail whenever the coordinate in question is `0`. -/
lemma one_not_le_zero_ΓR : ¬ (1 : ΓR) ≤ 0 := not_le.mpr zero_lt_one_ΓR

/-! ## Corner computations -/

lemma col_origin : col 0 0 = 0 := by
  unfold col
  simp only [νR.map_zero]
  rw [if_pos ⟨zero_lt_one_ΓR, zero_lt_one_ΓR⟩]

lemma col_10 : col 1 0 = 1 := by
  unfold col
  simp only [νR.map_zero, νR_one_eq_one]
  rw [if_neg (by simp), if_pos ⟨le_refl 1, zero_le'⟩]

lemma col_11 : col 1 1 = 1 := by
  unfold col
  simp only [νR_one_eq_one]
  rw [if_neg (by simp), if_pos ⟨le_refl 1, le_refl 1⟩]

lemma col_01 : col 0 1 = 2 := by
  unfold col
  simp only [νR.map_zero, νR_one_eq_one]
  rw [if_neg (by simp), if_neg (fun h => one_not_le_zero_ΓR h.1)]

/-! ## Per-side structural facts -/

/-- The left edge (`x = 0`) never has colour 1: colour 1 needs `1 ≤ ν x`,
impossible since `ν 0 = 0 < 1`. Holds for *every* `y`, no case-work. -/
lemma col_left_ne_one (y : ℝ) : col 0 y ≠ 1 := by
  unfold col
  simp only [νR.map_zero]
  split_ifs with h1 h2
  · decide
  · exact absurd h2.1 one_not_le_zero_ΓR
  · decide

/-- The bottom edge (`y = 0`) never has colour 2: colour 2 needs `1 ≤ ν y`,
impossible since `ν 0 = 0 < 1`. Holds for *every* `x`, no case-work. -/
lemma col_bottom_ne_two (x : ℝ) : col x 0 ≠ 2 := by
  unfold col
  simp only [νR.map_zero]
  split_ifs with h1 h2
  · decide
  · decide
  · exfalso
    apply h2
    exact ⟨not_lt.mp (fun hlt => h1 ⟨hlt, zero_lt_one_ΓR⟩), zero_le'⟩

/-- The right edge (`x = 1`) never has colour 0: colour 0 needs `ν x < 1`,
impossible since `ν 1 = 1`. Holds for *every* `y`, no case-work. -/
lemma col_right_ne_zero (y : ℝ) : col 1 y ≠ 0 := by
  unfold col
  simp only [νR_one_eq_one]
  rw [if_neg (by simp)]
  split_ifs <;> decide

/-- The top edge (`y = 1`) never has colour 0: colour 0 needs `ν y < 1`,
impossible since `ν 1 = 1`. Holds for *every* `x`, no case-work. -/
lemma col_top_ne_zero (x : ℝ) : col x 1 ≠ 0 := by
  unfold col
  simp only [νR_one_eq_one]
  rw [if_neg (by simp)]
  split_ifs <;> decide

/-! ## Doors along a single side, and the finite `{1,2}`-vs-Bool bridge -/

/-- The number of `{1,2}`-colour doors among the `n` edges of a length-`n`
path of real plane points, given as separate `x`/`y` coordinate sequences
(avoiding `Prod` projections, which do not `rw`-reduce well against `col`'s
`if`-conditions). -/
noncomputable def sideDoors {n : ℕ} (xs ys : Fin (n + 1) → ℝ) : ℕ :=
  (Finset.univ.filter
    (fun i : Fin n => pairIs12 (col (xs i.castSucc) (ys i.castSucc))
      (col (xs i.succ) (ys i.succ)))).card

/-- On colours restricted to `{1, 2}` (i.e. `≠ 0`), the `{1,2}`-door
predicate coincides with disagreement of the Boolean "is it colour 2?"
tag. A finite check over `Fin 3 × Fin 3`. -/
lemma pairIs12_iff_decide_ne (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    pairIs12 a b ↔ decide (a = 2) ≠ decide (b = 2) := by
  revert a b; decide

/-- **The Bool-path reduction.** For a side all of whose points avoid
colour 0, the `{1,2}`-door count reduces (mod 2) to whether the two
endpoints agree on "is it colour 2?" — via `MonskyPathParity.door_card_parity`
applied to the Boolean tag `fun j => decide (col (xs j) (ys j) = 2)`. -/
lemma sideDoors_eq_boolParity {n : ℕ} (xs ys : Fin (n + 1) → ℝ)
    (hnz : ∀ i, col (xs i) (ys i) ≠ 0) :
    (sideDoors xs ys : ZMod 2)
      = if decide (col (xs 0) (ys 0) = 2)
          = decide (col (xs (Fin.last n)) (ys (Fin.last n)) = 2) then 0 else 1 := by
  have hfilter :
      (Finset.univ.filter (fun i : Fin n =>
          pairIs12 (col (xs i.castSucc) (ys i.castSucc)) (col (xs i.succ) (ys i.succ))))
        = Finset.univ.filter (fun i : Fin n =>
            (fun j => decide (col (xs j) (ys j) = 2)) i.castSucc
              ≠ (fun j => decide (col (xs j) (ys j) = 2)) i.succ) := by
    apply Finset.filter_congr
    intro i _
    simp only
    exact pairIs12_iff_decide_ne _ _ (hnz i.castSucc) (hnz i.succ)
  show ((Finset.univ.filter (fun i : Fin n =>
      pairIs12 (col (xs i.castSucc) (ys i.castSucc)) (col (xs i.succ) (ys i.succ)))).card
      : ZMod 2) = _
  rw [hfilter]
  exact MonskyPathParity.door_card_parity (fun j => decide (col (xs j) (ys j) = 2))

/-! ## The four sides -/

/-- The bottom side (`y = 0`) contributes **zero** `{1,2}`-doors, exactly
(not just mod 2): no vertex there is ever colour 2. -/
lemma bottom_sideDoors_eq_zero {n : ℕ} (bx : Fin (n + 1) → ℝ) :
    sideDoors bx (fun _ => (0 : ℝ)) = 0 := by
  unfold sideDoors
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_false_of_mem
  intro i _ hpair
  rcases hpair with ⟨-, hb⟩ | ⟨ha, -⟩
  · exact col_bottom_ne_two (bx i.succ) hb
  · exact col_bottom_ne_two (bx i.castSucc) ha

/-- The left side (`x = 0`) contributes **zero** `{1,2}`-doors, exactly:
no vertex there is ever colour 1. -/
lemma left_sideDoors_eq_zero {n : ℕ} (ly : Fin (n + 1) → ℝ) :
    sideDoors (fun _ => (0 : ℝ)) ly = 0 := by
  unfold sideDoors
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_false_of_mem
  intro i _ hpair
  rcases hpair with ⟨ha, -⟩ | ⟨-, hb⟩
  · exact col_left_ne_one (ly i.castSucc) ha
  · exact col_left_ne_one (ly i.succ) hb

/-- The right side (`x = 1`, endpoints `(1,0) → (1,1)`, both colour 1)
contributes an **even** number of `{1,2}`-doors. -/
lemma right_sideDoors_zmod {n : ℕ} (ry : Fin (n + 1) → ℝ)
    (h0 : ry 0 = 0) (hL : ry (Fin.last n) = 1) :
    (sideDoors (fun _ => (1 : ℝ)) ry : ZMod 2) = 0 := by
  rw [sideDoors_eq_boolParity (fun _ => (1 : ℝ)) ry (fun i => col_right_ne_zero (ry i))]
  rw [h0, hL, col_10, col_11]
  decide

/-- The top side (`y = 1`, endpoints `(1,1) → (0,1)`, colours 1 then 2)
contributes an **odd** number of `{1,2}`-doors. -/
lemma top_sideDoors_zmod {n : ℕ} (tx : Fin (n + 1) → ℝ)
    (h0 : tx 0 = 1) (hL : tx (Fin.last n) = 0) :
    (sideDoors tx (fun _ => (1 : ℝ)) : ZMod 2) = 1 := by
  rw [sideDoors_eq_boolParity tx (fun _ => (1 : ℝ)) (fun i => col_top_ne_zero (tx i))]
  rw [h0, hL, col_11, col_01]
  decide

/-! ## Assembly: the full boundary has an odd `{1,2}`-door count -/

/-- **The unit square's boundary has an odd number of `{1,2}`-colour
doors.** For any four finite point-sequences forming the bottom, right,
top and left sides of a triangulation's boundary — matching up at the
four actual corners `(0,0), (1,0), (1,1), (0,1)` — the total number of
`{1,2}`-colour doors among the four sides' edges is odd. This is the
concrete geometric content of the `hbdry` hypothesis of
`MonskyThreeColorDoors.exists_rainbow_of_odd_boundary`. -/
theorem boundary_doors_odd
    {nb nr nt nl : ℕ}
    (bx : Fin (nb + 1) → ℝ) (_hbx0 : bx 0 = 0) (_hbxL : bx (Fin.last nb) = 1)
    (ry : Fin (nr + 1) → ℝ) (hry0 : ry 0 = 0) (hryL : ry (Fin.last nr) = 1)
    (tx : Fin (nt + 1) → ℝ) (htx0 : tx 0 = 1) (htxL : tx (Fin.last nt) = 0)
    (ly : Fin (nl + 1) → ℝ) (_hly0 : ly 0 = 1) (_hlyL : ly (Fin.last nl) = 0) :
    Odd (sideDoors bx (fun _ => (0 : ℝ)) + sideDoors (fun _ => (1 : ℝ)) ry
      + sideDoors tx (fun _ => (1 : ℝ)) + sideDoors (fun _ => (0 : ℝ)) ly) := by
  classical
  have hb : sideDoors bx (fun _ => (0 : ℝ)) = 0 := bottom_sideDoors_eq_zero bx
  have hl : sideDoors (fun _ => (0 : ℝ)) ly = 0 := left_sideDoors_eq_zero ly
  have hr := right_sideDoors_zmod ry hry0 hryL
  have ht := top_sideDoors_zmod tx htx0 htxL
  have hcast :
      ((sideDoors bx (fun _ => (0 : ℝ)) + sideDoors (fun _ => (1 : ℝ)) ry
        + sideDoors tx (fun _ => (1 : ℝ)) + sideDoors (fun _ => (0 : ℝ)) ly : ℕ) : ZMod 2) = 1 := by
    push_cast
    rw [hb, hl, hr, ht]
    ring
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have heven :
      ((sideDoors bx (fun _ => (0 : ℝ)) + sideDoors (fun _ => (1 : ℝ)) ry
        + sideDoors tx (fun _ => (1 : ℝ)) + sideDoors (fun _ => (0 : ℝ)) ly : ℕ) : ZMod 2) = 0 := by
    rw [MonskySpernerParity.nat_cast_zmod_two_eq_ite_odd, if_neg (Nat.not_odd_iff_even.mpr hne)]
  rw [hcast] at heven
  exact absurd heven (by decide)

end MonskyBoundaryOddness
