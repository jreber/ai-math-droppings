/-
# 1D path door-parity lemma (discrete Sperner/IVT parity)

This is the classical 1-dimensional discrete Sperner/IVT parity fact: walking
a path of `n + 1` two-coloured vertices `0, 1, ..., n`, the parity of the
number of "doors" (adjacent pairs whose colours differ) is determined purely
by whether the two endpoints agree, independent of everything in between.

**Claim (`door_card_parity`).** For `c : Fin (n + 1) → Bool` a two-valued
colouring of the vertices of a length-`n` path,

`((Finset.univ.filter (fun i : Fin n => c i.castSucc ≠ c i.succ)).card : ZMod 2)
  = if c 0 = c (Fin.last n) then 0 else 1`.

This is the exact combinatorial engine needed to show the unit square's
boundary has an *odd* number of door-edges for Monsky's theorem: each side of
the square is a 2-coloured path (by `MonskyDichromaticLine.no_dichromatic_line`,
no side sees all 3 colours) with differently-coloured endpoints, so summing
this lemma over the 4 sides pins the parity of the total boundary door-count
from the 4 corner colours alone (feeding `MonskySpernerParity.rainbow_card_parity`'s
`boundary.card`), without ever touching the interior triangulation. (This
lemma is conceptually upstream of / complementary to `MonskySpernerParity`,
which is about the *triangle* side of the door-counting argument; this file
is purely about a single *path*, with no triangles at all.)

## Proof idea (telescoping sum in `ZMod 2`)

Encode `c` as `g : Fin (n+1) → ZMod 2` via `colorVal`, extend it to
`h : ℕ → ZMod 2` (values above `n` are irrelevant), and observe that the
door-indicator at edge `i : Fin n` is exactly `h (i+1) - h i` computed in
`ZMod 2` (in `ZMod 2`, `x - y = x + y` is the "differ" indicator when
`x, y ∈ {0, 1}`). Summing over `i ∈ Finset.range n` telescopes
(`Finset.sum_range_sub`, mathlib's `to_additive` companion of
`Finset.prod_range_div`) to `h n - h 0 = g (Fin.last n) - g 0`, which is
exactly `if c 0 = c (Fin.last n) then 0 else 1`. No hand-rolled induction on
`n` is needed: the induction is already inside `Finset.sum_range_sub`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic

namespace MonskyPathParity

open Finset

/-- The `ZMod 2` encoding of a `Bool` colour: `true ↦ 1`, `false ↦ 0`. -/
def colorVal (b : Bool) : ZMod 2 := if b then 1 else 0

/-- **1D path door-parity lemma** (discrete Sperner/IVT parity).

For a two-valued colouring `c` of the `n + 1` vertices of a path, the number
of "doors" — adjacent index pairs `i` where `c i.castSucc ≠ c i.succ` — is
congruent mod 2 to whether the two endpoints of the path differ. -/
theorem door_card_parity {n : ℕ} (c : Fin (n + 1) → Bool) :
    ((Finset.univ.filter (fun i : Fin n => c i.castSucc ≠ c i.succ)).card : ZMod 2)
      = if c 0 = c (Fin.last n) then 0 else 1 := by
  classical
  set g : Fin (n + 1) → ZMod 2 := fun i => colorVal (c i) with hg
  set h : ℕ → ZMod 2 := fun k => if hk : k < n + 1 then g ⟨k, hk⟩ else 0 with hh
  -- `h` restricted to `Fin (n+1)`-indices recovers `g`.
  have h_eq : ∀ i : Fin (n + 1), h i.val = g i := by
    intro i
    rw [hh]
    dsimp only
    rw [dif_pos i.isLt]
  have h0 : h 0 = g 0 := by
    have := h_eq (0 : Fin (n + 1))
    simpa using this
  have hn : h n = g (Fin.last n) := by
    have := h_eq (Fin.last n)
    simpa [Fin.val_last] using this
  have hcast : ∀ i : Fin n, h i.val = g i.castSucc := by
    intro i
    have := h_eq i.castSucc
    rwa [Fin.val_castSucc] at this
  have hsucc : ∀ i : Fin n, h (i.val + 1) = g i.succ := by
    intro i
    have := h_eq i.succ
    rwa [Fin.val_succ] at this
  -- Telescoping sum in `ZMod 2` (the induction lives here, in mathlib).
  have htel : ∑ i ∈ Finset.range n, (h (i + 1) - h i) = h n - h 0 :=
    Finset.sum_range_sub h n
  -- Reindex the range-sum as a sum over `Fin n`.
  have hreindex :
      ∑ i : Fin n, (h (i.val + 1) - h i.val) = ∑ i ∈ Finset.range n, (h (i + 1) - h i) :=
    Fin.sum_univ_eq_sum_range (fun k => h (k + 1) - h k) n
  -- Pointwise: the summand at edge `i` is exactly the door indicator.
  have hpt : ∀ i : Fin n,
      h (i.val + 1) - h i.val = if c i.castSucc ≠ c i.succ then (1 : ZMod 2) else 0 := by
    intro i
    rw [hsucc i, hcast i]
    simp only [hg, colorVal]
    rcases hcs : c i.castSucc <;> rcases hsc : c i.succ <;> simp
  have hLHS :
      ((Finset.univ.filter (fun i : Fin n => c i.castSucc ≠ c i.succ)).card : ZMod 2)
        = ∑ i : Fin n, (h (i.val + 1) - h i.val) := by
    rw [Finset.natCast_card_filter]
    exact Finset.sum_congr rfl (fun i _ => (hpt i).symm)
  rw [hLHS, hreindex, htel, hn, h0]
  simp only [hg, colorVal]
  rcases hc0 : c 0 <;> rcases hcl : c (Fin.last n) <;> simp

end MonskyPathParity
