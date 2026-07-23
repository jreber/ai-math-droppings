/-
# Boundary composition: chaining `MonskyPathParity` paths into a `MonskySpernerParity` boundary

This file composes the two combinatorial engines that already landed:

* `MonskySpernerParity.rainbow_card_parity` — the number of *rainbow* triangles
  is congruent mod 2 to the number of *boundary* door-edges, for an abstract
  triangle-incidence structure `inc : T → Finset E` and door set `door : Finset E`.
* `MonskyPathParity.door_card_parity` — for a single 2-coloured path of
  `n + 1` vertices, the number of "doors" (colour changes) is congruent mod 2
  to whether the two endpoints agree.

Neither engine alone determines whether a *polygon* boundary (assembled from
several sides, each a path) has an odd or even total door-count: that is
exactly the missing link for Monsky's theorem, where the boundary of the unit
square is split into 4 sides. This file supplies that link, still with **zero
geometry** — everything here is an abstract statement about a `k`-indexed
family of paths and their corner colours.

## The key composition

Suppose the boundary consists of `k` sides, side `i` being a path
`c i : Fin (n i + 1) → Bool` of `n i + 1` vertices. Write `corner : Fin (k+1)
→ Bool` for the sequence of `k + 1` "corner" colours, with side `i`'s two
endpoints being `corner i.castSucc` (start) and `corner i.succ` (end) — i.e.
the corner sequence is itself a length-`k` path threading through the sides.

Then (`chained_door_card_parity`):

`(total door count over the k sides : ZMod 2) = if corner 0 = corner (Fin.last k) then 0 else 1`.

This is proved by **applying `door_card_parity` twice**, at two different
scales:

1. *Micro scale.* Apply `door_card_parity` to each side `c i` individually;
   this reduces the total door count's parity to the parity of the number of
   sides `i` whose two corner-endpoints `corner i.castSucc`, `corner i.succ`
   disagree (`chained_door_card_parity_aux`, a direct sum-of-`door_card_parity`
   telescoping argument, generalizing `door_card_parity` from a single path to
   a `k`-indexed family of paths).
2. *Meta scale.* The `k`-indexed "does side `i` see disagreeing corners"
   count is *itself* exactly the door-count of the single path `corner : Fin
   (k + 1) → Bool` (viewing the corner sequence as one path of `k` edges).
   Applying `door_card_parity` to `corner` collapses it to a comparison of
   the two extreme corners `corner 0` and `corner (Fin.last k)`.

Chaining these two applications of the *same* lemma at different scales is
the genuinely new content of this file: the sides' interior structure
disappears entirely, and the boundary parity is pinned down purely by the
first and last corner colours of the corner-path.

## Discharging to `rainbow_card_parity`

`rainbow_nonempty_of_chained_boundary` closes the loop: if in addition the
`k`-sides' combined door-edge-set can be identified with `MonskySpernerParity`'s
`boundary inc door` (an explicit cardinality hypothesis `hcard`, deliberately
left abstract — discharging it requires the actual geometric identification
of path-edges with `E`-edges, out of scope here, same as the file's own
remark about `MonskyDichromaticLine`), and the two extreme corners disagree,
then `rainbow inc door` is nonempty.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Propositio.Geometry.Monsky.MonskySpernerParity
import Propositio.Geometry.Monsky.MonskyPathParity

namespace MonskyBoundaryComposition

open Finset

/-- The door-count of a single path (same expression as the LHS of
`MonskyPathParity.door_card_parity`), spelled out as a standalone definition
so we can sum it over an index `i : Fin k`. -/
def pathDoorCount {n : ℕ} (c : Fin (n + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => c j.castSucc ≠ c j.succ)).card

@[simp] lemma pathDoorCount_apply {n : ℕ} (c : Fin (n + 1) → Bool) :
    pathDoorCount c = (Finset.univ.filter (fun j : Fin n => c j.castSucc ≠ c j.succ)).card := rfl

/-- **Step 1 (micro scale): sum `door_card_parity` over `k` sides.**

For a `k`-indexed family of paths `c i : Fin (n i + 1) → Bool`, the total
door-count over all `k` sides is congruent mod 2 to the number of sides whose
two endpoints disagree. This is a direct generalization of
`MonskyPathParity.door_card_parity` from one path to `k` paths: apply it
pointwise and sum in `ZMod 2`. -/
theorem chained_door_card_parity_aux {k : ℕ} (n : Fin k → ℕ)
    (c : ∀ i : Fin k, Fin (n i + 1) → Bool) :
    ((∑ i : Fin k, pathDoorCount (c i) : ℕ) : ZMod 2)
      = ((Finset.univ.filter (fun i : Fin k => c i 0 ≠ c i (Fin.last (n i)))).card : ZMod 2) := by
  classical
  push_cast
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [pathDoorCount_apply, MonskyPathParity.door_card_parity (c i)]
  by_cases h : c i 0 = c i (Fin.last (n i))
  · simp [h]
  · simp [h]

/-- **Step 2 (meta scale) + assembly.**

Suppose additionally the `k` sides are threaded end-to-end by a single
"corner path" `corner : Fin (k + 1) → Bool`: side `i` starts at
`corner i.castSucc` and ends at `corner i.succ`. Then the total door-count
over all `k` sides is congruent mod 2 to whether the *first* and *last*
corners of the whole chain agree — the interior sides and interior corners
drop out entirely. This is `door_card_parity` applied a *second* time, now to
the corner sequence itself viewed as a length-`k` path. -/
theorem chained_door_card_parity {k : ℕ} (n : Fin k → ℕ)
    (c : ∀ i : Fin k, Fin (n i + 1) → Bool) (corner : Fin (k + 1) → Bool)
    (hstart : ∀ i : Fin k, c i 0 = corner i.castSucc)
    (hend : ∀ i : Fin k, c i (Fin.last (n i)) = corner i.succ) :
    ((∑ i : Fin k, pathDoorCount (c i) : ℕ) : ZMod 2)
      = if corner 0 = corner (Fin.last k) then 0 else 1 := by
  rw [chained_door_card_parity_aux n c]
  have hfilt :
      (Finset.univ.filter (fun i : Fin k => c i 0 ≠ c i (Fin.last (n i))))
        = Finset.univ.filter (fun i : Fin k => corner i.castSucc ≠ corner i.succ) := by
    apply Finset.filter_congr
    intro i _
    rw [hstart i, hend i]
  rw [hfilt]
  exact MonskyPathParity.door_card_parity corner

/-- **Discharging to `MonskySpernerParity.rainbow_card_parity`.**

If the `k`-side chain's combined door-edges are identified (`hcard`, an
explicit hypothesis standing in for the geometric edge-correspondence, left
abstract as in the rest of this development) with
`MonskySpernerParity.boundary inc door`, and the two extreme corners of the
chain disagree, then the boundary door-count is odd, hence — by
`rainbow_card_parity` — the rainbow triangles are odd in number, hence
nonempty. This is the exact combinatorial shape of the last step of Monsky's
theorem: an odd number of rainbow triangles forces at least one to exist. -/
theorem rainbow_nonempty_of_chained_boundary
    {T E : Type*} [Fintype T] [DecidableEq E]
    (inc : T → Finset E) (door : Finset E)
    (hmult : ∀ e ∈ door, MonskySpernerParity.mult inc e = 1
      ∨ MonskySpernerParity.mult inc e = 2)
    {k : ℕ} (n : Fin k → ℕ) (c : ∀ i : Fin k, Fin (n i + 1) → Bool)
    (corner : Fin (k + 1) → Bool)
    (hstart : ∀ i : Fin k, c i 0 = corner i.castSucc)
    (hend : ∀ i : Fin k, c i (Fin.last (n i)) = corner i.succ)
    (hcard : (MonskySpernerParity.boundary inc door).card = ∑ i : Fin k, pathDoorCount (c i))
    (hdiff : corner 0 ≠ corner (Fin.last k)) :
    (MonskySpernerParity.rainbow inc door).Nonempty := by
  classical
  have hpar := chained_door_card_parity n c corner hstart hend
  rw [if_neg hdiff] at hpar
  have hbnd : ((MonskySpernerParity.boundary inc door).card : ZMod 2) = 1 := by
    rw [hcard]; exact hpar
  have hrb := MonskySpernerParity.rainbow_card_parity inc door hmult
  have h2 : ((MonskySpernerParity.rainbow inc door).card : ZMod 2) = 1 := hrb.trans hbnd
  have hodd : Odd (MonskySpernerParity.rainbow inc door).card := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have heven : ((MonskySpernerParity.rainbow inc door).card : ZMod 2) = 0 := by
      rw [MonskySpernerParity.nat_cast_zmod_two_eq_ite_odd]
      rw [if_neg (Nat.not_odd_iff_even.mpr hne)]
    rw [heven] at h2
    exact absurd h2 (by decide)
  have hmod : (MonskySpernerParity.rainbow inc door).card % 2 = 1 := Nat.odd_iff.mp hodd
  have hne0 : (MonskySpernerParity.rainbow inc door).card ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  exact Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
