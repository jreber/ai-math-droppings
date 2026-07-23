/-
# A segment cannot be a full edge of three pairwise-interior-disjoint triangles

This is a **Monsky-independent, reusable planar local-geometry lemma**
(`docs/kb/conjectures/conj-2026-07-09-018.json`): for any finite family of
nondegenerate triangles in the real plane with PAIRWISE DISJOINT INTERIORS,
no line segment can be a full edge of three (or more) distinct triangles in
the family.

## Formalization choices

Points are pairs of real coordinates, following the convention already used
throughout the Monsky files (`MonskyRainbowDetCorrected`,
`MonskyDichromaticLineReal`) rather than an abstract `ℝ × ℝ`/`Affine.Triangle`
package — this keeps every algebraic step a plain real-number identity
provable by `ring`/`field_simp`, with no vector-space/module typeclass
friction. (`Mathlib.Geometry.Polygon.Basic`, the newly-vendored A. M. Berns
file, was checked: it supplies `Polygon`/`edgeSet`/`Affine.Triangle`
interconversion but no interior/disjointness content, so it would only add
packaging overhead here, not proof content.)

* `cross2 Ax Ay Bx By Cx Cy` — twice the signed area of the triangle
  `(Ax,Ay) (Bx,By) (Cx,Cy)` (the cross product of `B - A` and `C - A`).
* `Nondegenerate` — the three vertices are not collinear (`cross2 ≠ 0`).
* `TriInt` — the *open* barycentric interior: points that are a *strictly*
  positive convex combination of the three vertices. This is the standard
  characterization of a triangle's topological interior, but stated purely
  algebraically (no `convexHull`/`interior` topology needed).

## The mathematical content

The key **local** lemma, `exists_common_interior_point`, is the heart of the
file: if two triangles share the edge `(A,B)` and their apexes `C`, `C'` lie
on the *same side* of line `AB` (i.e. `cross2 A B C` and `cross2 A B C'` have
the same sign), their interiors overlap — witnessed by an explicit point

  `P(y) = A + (1/2)(B - A) + y(C - A)`   for a suitable small `y > 0`,

i.e. a point slightly off the midpoint of `AB`, displaced towards `C`. This
point always lies in `TriInt A B C` (its barycentric coordinates w.r.t.
`A,B,C` are exactly `(1/2 - y, 1/2, y)`, positive for `y ∈ (0, 1/2)`,
*independent of any sign condition*). The nontrivial part is that the *same*
point also lies in `TriInt A B C'`: its barycentric coordinates w.r.t.
`A,B,C'` are computed via the 2D Cramer's-rule identity `cramer_coord`
(solving `d = β' u + γ' v'` for a basis `u = B-A, v' = C'-A` using cross
products), and turn out to be affine in `y` with value `(1/2, 1/2, 0)` at
`y = 0` — so for `y` small enough (an explicit, algebraically constructed
threshold, no compactness/continuity argument needed) all three stay
strictly positive.

Given three pairwise-interior-disjoint triangles sharing a common full edge
`(A,B)` with apexes `C1, C2, C3`, a sign pigeonhole (3 nonzero reals, only 2
possible signs) forces two of the three apexes onto the same side, and
`exists_common_interior_point` then produces a point in both of those two
triangles' interiors — contradicting pairwise-interior-disjointness. This is
`no_three_triangles_share_full_edge`, with the "multiplicity ≤ 2" corollary
`card_le_two_of_shared_full_edge` for an arbitrary finite family.

Axiom-clean: only elementary real-number algebra (`ring`, `field_simp`,
`nlinarith`) and `Finset.two_lt_card_iff`; no additional axioms beyond the
ambient `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MonskyEdgeMultiplicityAtMostTwo

/-- Twice the signed area of the triangle with vertices `(Ax,Ay) (Bx,By)
(Cx,Cy)`: the cross product of `B - A` and `C - A`. -/
def cross2 (Ax Ay Bx By Cx Cy : ℝ) : ℝ :=
  (Bx - Ax) * (Cy - Ay) - (Cx - Ax) * (By - Ay)

/-- A triangle is *nondegenerate* iff its three vertices are not collinear,
i.e. the signed-area cross product is nonzero. -/
def Nondegenerate (Ax Ay Bx By Cx Cy : ℝ) : Prop := cross2 Ax Ay Bx By Cx Cy ≠ 0

/-- The **open barycentric interior** of the triangle `(Ax,Ay) (Bx,By)
(Cx,Cy)`: points expressible as a *strictly* positive convex combination of
the three vertices. -/
def TriInt (Ax Ay Bx By Cx Cy Px Py : ℝ) : Prop :=
  ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧
    Px = a * Ax + b * Bx + c * Cx ∧ Py = a * Ay + b * By + c * Cy

/-! ## The 2D Cramer's-rule identity -/

/-- **Cramer's rule via cross products, in coordinates.** Solving
`(vx,vy) = β' • (ux,uy) + γ' • (v'x,v'y)` for the basis `(ux,uy), (v'x,v'y)`
(linearly independent since the cross product `ux*v'y - v'x*uy` is nonzero)
gives `β' = cross(v,v')/D'`, `γ' = cross(u,v)/D'` where `D' = cross(u,v')`.
This lemma packages the resulting identity, purely algebraically. -/
private lemma cramer_coord (ux uy vx vy v'x v'y : ℝ)
    (hD' : ux * v'y - v'x * uy ≠ 0) :
    ((vx * v'y - v'x * vy) / (ux * v'y - v'x * uy)) * ux
        + ((ux * vy - vx * uy) / (ux * v'y - v'x * uy)) * v'x = vx ∧
    ((vx * v'y - v'x * vy) / (ux * v'y - v'x * uy)) * uy
        + ((ux * vy - vx * uy) / (ux * v'y - v'x * uy)) * v'y = vy := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD']
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD']
    ring

/-! ## The key local lemma -/

/-- **Two triangles sharing an edge, apexes on the same side, have
overlapping interiors.** If `(A,B,C)` and `(A,B,C')` are nondegenerate
triangles sharing the edge `(A,B)`, and `C`, `C'` lie on the same side of
line `AB` (their signed-area cross products with `A,B` have the same sign),
then `TriInt A B C` and `TriInt A B C'` share a point. -/
theorem exists_common_interior_point
    (Ax Ay Bx By Cx Cy C'x C'y : ℝ)
    (hnd : Nondegenerate Ax Ay Bx By Cx Cy)
    (hnd' : Nondegenerate Ax Ay Bx By C'x C'y)
    (hsign : 0 < cross2 Ax Ay Bx By Cx Cy * cross2 Ax Ay Bx By C'x C'y) :
    ∃ Px Py : ℝ, TriInt Ax Ay Bx By Cx Cy Px Py ∧ TriInt Ax Ay Bx By C'x C'y Px Py := by
  have hD : cross2 Ax Ay Bx By Cx Cy ≠ 0 := hnd
  have hD' : cross2 Ax Ay Bx By C'x C'y ≠ 0 := hnd'
  have hD'' : (Bx - Ax) * (C'y - Ay) - (C'x - Ax) * (By - Ay) ≠ 0 := hD'
  -- the two cross-ratios controlling the barycentric coordinates of the
  -- witness point w.r.t. the *second* triangle
  set k1 : ℝ := cross2 Ax Ay Cx Cy C'x C'y / cross2 Ax Ay Bx By C'x C'y with hk1_def
  set k2 : ℝ := cross2 Ax Ay Bx By Cx Cy / cross2 Ax Ay Bx By C'x C'y with hk2_def
  set S : ℝ := |k1| + |k1 + k2| + 3 with hS_def
  have hS3 : (3 : ℝ) ≤ S := by
    have h1 := abs_nonneg k1
    have h2 := abs_nonneg (k1 + k2)
    rw [hS_def]; linarith
  have hSpos : 0 < S := by linarith
  set y : ℝ := 1 / (2 * S) with hy_def
  have hypos : 0 < y := by rw [hy_def]; positivity
  have hyS : y * S = 1 / 2 := by rw [hy_def]; field_simp
  have hy_half : y < 1 / 2 := by nlinarith
  have hk1S : |k1| < S := by
    rw [hS_def]; have := abs_nonneg (k1 + k2); linarith
  have hk1k2S : |k1 + k2| < S := by
    rw [hS_def]; have := abs_nonneg k1; linarith
  have hyk1' : |y * k1| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hypos]
    nlinarith [mul_pos hypos (show (0:ℝ) < S - |k1| by linarith)]
  have hyk1k2' : |y * (k1 + k2)| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hypos]
    nlinarith [mul_pos hypos (show (0:ℝ) < S - |k1 + k2| by linarith)]
  obtain ⟨hyk1_lo, hyk1_hi⟩ := abs_lt.mp hyk1'
  obtain ⟨hyk1k2_lo, hyk1k2_hi⟩ := abs_lt.mp hyk1k2'
  have hk2pos : 0 < k2 := by
    rw [hk2_def, div_pos_iff]
    rcases mul_pos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  -- the Cramer identity, instantiated at u = B-A, v = C-A, v' = C'-A
  obtain ⟨hidx, hidy⟩ := cramer_coord (Bx - Ax) (By - Ay) (Cx - Ax) (Cy - Ay)
    (C'x - Ax) (C'y - Ay) hD''
  have hidx' : k1 * (Bx - Ax) + k2 * (C'x - Ax) = Cx - Ax := by
    rw [hk1_def, hk2_def]; exact hidx
  have hidy' : k1 * (By - Ay) + k2 * (C'y - Ay) = Cy - Ay := by
    rw [hk1_def, hk2_def]; exact hidy
  refine ⟨Ax + (1/2) * (Bx - Ax) + y * (Cx - Ax),
    Ay + (1/2) * (By - Ay) + y * (Cy - Ay), ?_, ?_⟩
  · exact ⟨1/2 - y, 1/2, y, by linarith, by norm_num, hypos, by ring, by ring, by ring⟩
  · refine ⟨1/2 - y * (k1 + k2), 1/2 + y * k1, y * k2,
      by linarith, by linarith, by positivity, by ring, ?_, ?_⟩
    · linear_combination (-y) * hidx'
    · linear_combination (-y) * hidy'

/-! ## The main theorem -/

/-- **A segment cannot be a full edge of three pairwise-interior-disjoint
triangles.** If `(A,B,C1)`, `(A,B,C2)`, `(A,B,C3)` are nondegenerate
triangles all sharing the full edge `(A,B)`, and their interiors are
pairwise disjoint, that is a contradiction. -/
theorem no_three_triangles_share_full_edge
    (Ax Ay Bx By C1x C1y C2x C2y C3x C3y : ℝ)
    (hnd1 : Nondegenerate Ax Ay Bx By C1x C1y)
    (hnd2 : Nondegenerate Ax Ay Bx By C2x C2y)
    (hnd3 : Nondegenerate Ax Ay Bx By C3x C3y)
    (hdisj12 : ∀ Px Py, ¬ (TriInt Ax Ay Bx By C1x C1y Px Py ∧
        TriInt Ax Ay Bx By C2x C2y Px Py))
    (hdisj13 : ∀ Px Py, ¬ (TriInt Ax Ay Bx By C1x C1y Px Py ∧
        TriInt Ax Ay Bx By C3x C3y Px Py))
    (hdisj23 : ∀ Px Py, ¬ (TriInt Ax Ay Bx By C2x C2y Px Py ∧
        TriInt Ax Ay Bx By C3x C3y Px Py)) :
    False := by
  have hx1 : cross2 Ax Ay Bx By C1x C1y ≠ 0 := hnd1
  have hx2 : cross2 Ax Ay Bx By C2x C2y ≠ 0 := hnd2
  have hx3 : cross2 Ax Ay Bx By C3x C3y ≠ 0 := hnd3
  -- pigeonhole: among three nonzero reals, some two have the same sign
  have hpigeon : 0 < cross2 Ax Ay Bx By C1x C1y * cross2 Ax Ay Bx By C2x C2y ∨
      0 < cross2 Ax Ay Bx By C1x C1y * cross2 Ax Ay Bx By C3x C3y ∨
      0 < cross2 Ax Ay Bx By C2x C2y * cross2 Ax Ay Bx By C3x C3y := by
    rcases lt_or_gt_of_ne hx1 with h1 | h1 <;> rcases lt_or_gt_of_ne hx2 with h2 | h2 <;>
      rcases lt_or_gt_of_ne hx3 with h3 | h3
    all_goals
      first
        | exact Or.inl (mul_pos_of_neg_of_neg h1 h2)
        | exact Or.inl (mul_pos h1 h2)
        | exact Or.inr (Or.inl (mul_pos_of_neg_of_neg h1 h3))
        | exact Or.inr (Or.inl (mul_pos h1 h3))
        | exact Or.inr (Or.inr (mul_pos_of_neg_of_neg h2 h3))
        | exact Or.inr (Or.inr (mul_pos h2 h3))
  rcases hpigeon with h12 | h13 | h23
  · obtain ⟨Px, Py, h1, h2⟩ := exists_common_interior_point Ax Ay Bx By C1x C1y C2x C2y hnd1 hnd2 h12
    exact hdisj12 Px Py ⟨h1, h2⟩
  · obtain ⟨Px, Py, h1, h3⟩ := exists_common_interior_point Ax Ay Bx By C1x C1y C3x C3y hnd1 hnd3 h13
    exact hdisj13 Px Py ⟨h1, h3⟩
  · obtain ⟨Px, Py, h2, h3⟩ := exists_common_interior_point Ax Ay Bx By C2x C2y C3x C3y hnd2 hnd3 h23
    exact hdisj23 Px Py ⟨h2, h3⟩

/-! ## Corollary: multiplicity at most 2, for an arbitrary finite family -/

/-- **Equivalent "multiplicity" statement.** For any finite family of
nondegenerate triangles all sharing a common full edge `(A,B)` (with `C t`
the third vertex of triangle `t`), pairwise interior-disjoint, the family has
at most `2` members. -/
theorem card_le_two_of_shared_full_edge
    {T : Type*} [Fintype T]
    (Ax Ay Bx By : ℝ) (Cx Cy : T → ℝ)
    (hnd : ∀ t, Nondegenerate Ax Ay Bx By (Cx t) (Cy t))
    (hdisj : ∀ t₁ t₂ : T, t₁ ≠ t₂ →
      ∀ Px Py, ¬ (TriInt Ax Ay Bx By (Cx t₁) (Cy t₁) Px Py ∧
                   TriInt Ax Ay Bx By (Cx t₂) (Cy t₂) Px Py)) :
    Fintype.card T ≤ 2 := by
  by_contra hcard
  push Not at hcard
  have h3 : 2 < (Finset.univ : Finset T).card := by
    simpa [Finset.card_univ] using hcard
  obtain ⟨t1, t2, t3, -, -, -, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp h3
  exact no_three_triangles_share_full_edge Ax Ay Bx By
    (Cx t1) (Cy t1) (Cx t2) (Cy t2) (Cx t3) (Cy t3)
    (hnd t1) (hnd t2) (hnd t3)
    (fun Px Py h => hdisj t1 t2 h12 Px Py h)
    (fun Px Py h => hdisj t1 t3 h13 Px Py h)
    (fun Px Py h => hdisj t2 t3 h23 Px Py h)

end MonskyEdgeMultiplicityAtMostTwo
