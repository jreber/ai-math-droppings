/-
# The genuine 3-colour door-counting identity for Monsky's theorem

`MonskySpernerParity.rainbow_card_parity` proves, for an *abstract* triangle
incidence `inc : T → Finset E` and an *opaque* door set `door : Finset E`, that

  `#{t | Odd (inc t ∩ door).card}  ≡  #(boundary door)   (mod 2)`

where a triangle is counted on the left exactly when it has an **odd number of
door-edges**.  The abstraction says nothing about colours: `door` is just some
finite set of edges.

**Correction to an earlier characterization of this gap:** a prior session's
recon (reported informally, not as a docstring claim in any committed file —
checked directly, no such remark exists in `MonskyBoundaryComposition.lean`
or elsewhere in the repo) had suggested the 3-colour structure might force a
genuinely new combinatorial argument beyond the existing 2-Bool engines. That
concern turns out to be unfounded on the **triangle** side specifically (it
may still be real for the boundary/path side and for the geometric edge
correspondence — see the scope note below): this file shows the abstraction
is *already correct* for a genuine 3-colouring, provided the door set is
instantiated correctly:

> Take `door` to be the set of edges whose two endpoints carry colours **exactly
> `{1, 2}`** (Monsky's classical "1-2 door" — *not* "any two different
> colours").

The crux is the purely finite **3-colour door identity** (`Fin 3`, 27 cases,
`decide`):

  `Odd (doorCount12 a b c)  ↔  a, b, c are pairwise distinct`

i.e. a triangle has an *odd* number of `{1,2}`-edges **iff** its three vertices
realise all three colours (it is *rainbow*).  Every non-rainbow triangle has a
repeated colour and therefore an *even* number (`0` or `2`) of `{1,2}`-edges —
which is exactly the "each non-rainbow triangle contributes an even door-count"
fact that makes the classical Sperner argument work in its original 3-colour
form.

Consequences proved here:

* `odd_doorCount12_iff_rainbow3` — the crux identity (finite check).
* `triEdgeInter_card` — a *concrete* `Sym2`-edge model: for a triangle with
  three distinct vertices `a b c`, the number of its `{1,2}`-door edges equals
  `doorCount12 (col a) (col b) (col c)` (no abstract hypothesis — genuinely
  computed from a per-edge colour characterisation of `door`).
* `rainbow_eq_threeColored` — under a local hypothesis identifying, per
  triangle, `(inc t ∩ door).card` with `doorCount12` of its vertex colours, the
  engine's `rainbow inc door` set is **exactly** the set of genuinely
  3-coloured ("rainbow") triangles.
* `threeColored_card_parity` — hence `#(3-coloured triangles) ≡ #(boundary
  door) (mod 2)`: the real 3-colour Sperner door-counting conclusion, obtained
  by *reusing* `MonskySpernerParity.rainbow_card_parity` unchanged.

This answers "does the 2-Bool engine already handle a real 3-colouring?" in
the affirmative for the **pure combinatorics of the triangle side only**:
`rainbow_card_parity` is reusable as-is there; only the choice of `door`
(the `{1,2}`-edge set) and the local card identity `triEdgeInter_card` are
new. It does **not** close the full open Monsky gap: `exists_rainbow_of_odd_
boundary`'s hypotheses `hlocal`, `hmult`, `hbdry` are left as genuine,
undischarged hypotheses standing in for (respectively) the geometric edge
correspondence of an actual triangulation, the boundary/interior edge
multiplicity fact, and the boundary door-count actually being odd (the
path/corner argument of `MonskyBoundaryComposition` plus the no-dichromatic-
line fact) — none of that geometric work is done here.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2
import Propositio.Geometry.Monsky.MonskySpernerParity

namespace MonskyThreeColorDoors

open Finset

/-! ## The purely finite 3-colour door identity (`Fin 3`) -/

/-- The classical "1-2 door" predicate on an *ordered* colour pair: the two
colours are exactly `{1, 2}` (in either order).  This is symmetric in its two
arguments (`pairIs12_symm`), so it descends to unordered edges. -/
def pairIs12 (a b : Fin 3) : Prop := (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

instance : DecidablePred (fun p : Fin 3 × Fin 3 => pairIs12 p.1 p.2) := by
  intro p; unfold pairIs12; infer_instance

instance (a b : Fin 3) : Decidable (pairIs12 a b) := by unfold pairIs12; infer_instance

lemma pairIs12_symm (a b : Fin 3) : pairIs12 a b ↔ pairIs12 b a := by
  unfold pairIs12; tauto

/-- The number of `{1,2}`-door edges among the three edges of a triangle whose
vertices carry colours `a, b, c`.  (Edges `(a,b)`, `(b,c)`, `(a,c)`.) -/
def doorCount12 (a b c : Fin 3) : ℕ :=
  (if pairIs12 a b then 1 else 0)
    + (if pairIs12 b c then 1 else 0)
    + (if pairIs12 a c then 1 else 0)

/-- A triangle is *rainbow* when its three vertex-colours are pairwise distinct
(equivalently, realise all of `{0,1,2}` since there are only three colours). -/
def rainbow3 (a b c : Fin 3) : Prop := a ≠ b ∧ b ≠ c ∧ a ≠ c

instance (a b c : Fin 3) : Decidable (rainbow3 a b c) := by unfold rainbow3; infer_instance

/-- **The 3-colour door identity (crux).**  A triangle has an *odd* number of
`{1,2}`-door edges **iff** it is rainbow (all three vertex colours distinct).

Proof: a finite check over all `3^3 = 27` colour triples.  This is the exact
combinatorial content the pure 2-Bool abstraction was feared to miss: every
non-rainbow triple (with a repeated colour) yields `0` or `2` door-edges (even),
and every rainbow triple yields exactly `1` (odd). -/
theorem odd_doorCount12_iff_rainbow3 (a b c : Fin 3) :
    Odd (doorCount12 a b c) ↔ rainbow3 a b c := by
  revert a b c; decide

/-! ## A concrete `Sym2`-edge triangle model -/

variable {V : Type*} [DecidableEq V]

/-- The three edges of a triangle with vertices `a b c`, as unordered pairs. -/
def triEdges (a b c : V) : Finset (Sym2 V) := {s(a, b), s(b, c), s(a, c)}

/-- **Concrete local door-count.**  Suppose `door : Finset (Sym2 V)` collects
exactly the edges whose two endpoints carry colours `{1,2}` (hypothesis
`hdoor`), and `col : V → Fin 3` is the 3-colouring.  Then for a triangle with
three **distinct** vertices `a b c`, the number of its edges lying in `door`
equals `doorCount12 (col a) (col b) (col c)`.

This is the geometric identity that instantiates the abstract engine: no
hand-waving, the count is computed directly from the per-edge colour
characterisation of `door` and the distinctness of the three vertices. -/
lemma triEdgeInter_card (col : V → Fin 3) (door : Finset (Sym2 V))
    (hdoor : ∀ x y : V, s(x, y) ∈ door ↔ pairIs12 (col x) (col y))
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (triEdges a b c ∩ door).card = doorCount12 (col a) (col b) (col c) := by
  classical
  have hfilter : triEdges a b c ∩ door
      = (triEdges a b c).filter (fun e => e ∈ door) := by
    rw [Finset.filter_mem_eq_inter]
  rw [hfilter, Finset.card_filter]
  -- the three triangle edges are pairwise distinct (distinct vertices)
  have e_ab_bc : s(a, b) ≠ s(b, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hab h1
    · exact hac h1
  have e_ab_ac : s(a, b) ≠ s(a, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hbc h2
    · exact hac h1
  have e_bc_ac : s(b, c) ≠ s(a, c) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hab h1.symm
    · exact hbc h1
  -- expand the explicit 3-element sum
  have hbc_ne : s(b, c) ∉ ({s(a, c)} : Finset (Sym2 V)) :=
    Finset.notMem_singleton.mpr e_bc_ac
  have hab_ne : s(a, b) ∉ ({s(b, c), s(a, c)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨e_ab_bc, e_ab_ac⟩
  unfold triEdges
  rw [Finset.sum_insert hab_ne, Finset.sum_insert hbc_ne, Finset.sum_singleton]
  -- rewrite each door-membership via the colour characterisation
  simp only [hdoor a b, hdoor b c, hdoor a c, doorCount12]
  omega

/-! ## Reusing the Sperner engine for the genuine 3-colouring -/

variable {T : Type*} [Fintype T]

/-- **The engine's `rainbow` set is exactly the genuinely 3-coloured triangles.**

Let `inc : T → Finset (Sym2 V)` be a triangle-incidence, `door` the `{1,2}`-edge
set, and `vcol : T → Fin 3 × Fin 3 × Fin 3` the three vertex-colours of each
triangle.  Assume the local door-count identity `hlocal` (supplied concretely by
`triEdgeInter_card` for a `Sym2` triangulation).  Then
`MonskySpernerParity.rainbow inc door` — the triangles the engine counts (odd
door-edge-count) — is *exactly* the set of rainbow (3-coloured) triangles.

This is the concrete statement that the 2-Bool "odd-door" abstraction of
`rainbow_card_parity` already captures genuine 3-colouredness. -/
theorem rainbow_eq_threeColored
    (inc : T → Finset (Sym2 V)) (door : Finset (Sym2 V))
    (vcol : T → Fin 3 × Fin 3 × Fin 3)
    (hlocal : ∀ t : T,
      (inc t ∩ door).card = doorCount12 (vcol t).1 (vcol t).2.1 (vcol t).2.2) :
    MonskySpernerParity.rainbow inc door
      = Finset.univ.filter (fun t => rainbow3 (vcol t).1 (vcol t).2.1 (vcol t).2.2) := by
  classical
  rw [MonskySpernerParity.rainbow_apply]
  apply Finset.filter_congr
  intro t _
  rw [hlocal t]
  exact odd_doorCount12_iff_rainbow3 _ _ _

/-- **The genuine 3-colour Sperner door-counting conclusion.**

Under the same setup, the number of *3-coloured (rainbow)* triangles is
congruent mod 2 to the number of *boundary* `{1,2}`-door edges:

  `#(3-coloured triangles)  ≡  #(boundary door)   (mod 2)`.

Obtained by *reusing* `MonskySpernerParity.rainbow_card_parity` unchanged, after
identifying its opaque `rainbow` set with the real 3-coloured triangles via
`rainbow_eq_threeColored`.  This is the triangle side of Monsky's argument in
its original 3-colour form (no 2-colour reduction). -/
theorem threeColored_card_parity
    (inc : T → Finset (Sym2 V)) (door : Finset (Sym2 V))
    (vcol : T → Fin 3 × Fin 3 × Fin 3)
    (hlocal : ∀ t : T,
      (inc t ∩ door).card = doorCount12 (vcol t).1 (vcol t).2.1 (vcol t).2.2)
    (hmult : ∀ e ∈ door, MonskySpernerParity.mult inc e = 1
      ∨ MonskySpernerParity.mult inc e = 2) :
    ((Finset.univ.filter
        (fun t => rainbow3 (vcol t).1 (vcol t).2.1 (vcol t).2.2)).card : ZMod 2)
      = ((MonskySpernerParity.boundary inc door).card : ZMod 2) := by
  rw [← rainbow_eq_threeColored inc door vcol hlocal]
  exact MonskySpernerParity.rainbow_card_parity inc door hmult

/-- **An odd boundary door-count forces a genuine rainbow (3-coloured)
triangle.**  This is the final combinatorial punchline of the triangle side: if
the number of boundary `{1,2}`-edges is odd, then at least one triangle in the
triangulation realises all three colours.  (The boundary being odd is supplied,
in Monsky's proof, by the path/corner argument of `MonskyBoundaryComposition`
together with the no-dichromatic-line fact.) -/
theorem exists_rainbow_of_odd_boundary
    (inc : T → Finset (Sym2 V)) (door : Finset (Sym2 V))
    (vcol : T → Fin 3 × Fin 3 × Fin 3)
    (hlocal : ∀ t : T,
      (inc t ∩ door).card = doorCount12 (vcol t).1 (vcol t).2.1 (vcol t).2.2)
    (hmult : ∀ e ∈ door, MonskySpernerParity.mult inc e = 1
      ∨ MonskySpernerParity.mult inc e = 2)
    (hbdry : Odd (MonskySpernerParity.boundary inc door).card) :
    ∃ t : T, rainbow3 (vcol t).1 (vcol t).2.1 (vcol t).2.2 := by
  classical
  have hpar := threeColored_card_parity inc door vcol hlocal hmult
  have hb1 : ((MonskySpernerParity.boundary inc door).card : ZMod 2) = 1 := by
    rw [MonskySpernerParity.nat_cast_zmod_two_eq_ite_odd, if_pos hbdry]
  rw [hb1] at hpar
  -- the rainbow filter has odd (hence nonzero) card
  set S := Finset.univ.filter (fun t => rainbow3 (vcol t).1 (vcol t).2.1 (vcol t).2.2)
  have hodd : Odd S.card := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have : (S.card : ZMod 2) = 0 := by
      rw [MonskySpernerParity.nat_cast_zmod_two_eq_ite_odd,
        if_neg (Nat.not_odd_iff_even.mpr hne)]
    rw [this] at hpar
    exact absurd hpar (by decide)
  have hpos : 0 < S.card := by
    rcases hodd with ⟨m, hm⟩; omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

end MonskyThreeColorDoors
