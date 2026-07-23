import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Max

/-!
# The Sylvester–Gallai theorem

Any finite set of points in the real plane `ℝ²` that is not contained in a single line
admits an *ordinary line*: a line through exactly two of the points.

We model the plane as `EuclideanSpace ℝ (Fin 2)` and encode "the line through `a` and `b`
is ordinary" as: `a ≠ b` and every point `c ∈ P` collinear with `{a, b}` already equals
`a` or `b`.

The proof is Kelly's minimal-distance argument, recast in pure coordinates.  For a flag
`(a, b, c)` with `c` off the line `ab` we minimise the squared distance
`cross a b c ^ 2 / nsq a b` from `c` to that line; the minimising line is ordinary, because
if it carried a third point one could build a strictly closer flag.

Main result: `SG.sylvester_gallai`.
-/

namespace SG

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the triangle `a b c`; vanishes iff the three points are
collinear. -/
def cross (a b c : Pt) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- Squared Euclidean distance between `a` and `b`, written directly in coordinates. -/
def nsq (a b : Pt) : ℝ :=
  (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2

lemma pt_ext {a b : Pt} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  ext i; fin_cases i
  · exact h0
  · exact h1

/-- Coordinate `0` of a parametrised point on the line `ab`. -/
lemma coord0 (r : ℝ) (a b : Pt) : (r • (b - a) +ᵥ a) 0 = r * (b 0 - a 0) + a 0 := rfl

/-- Coordinate `1` of a parametrised point on the line `ab`. -/
lemma coord1 (r : ℝ) (a b : Pt) : (r • (b - a) +ᵥ a) 1 = r * (b 1 - a 1) + a 1 := rfl

/-! ### Basic facts about `nsq` -/

lemma nsq_nonneg (a b : Pt) : 0 ≤ nsq a b := by
  unfold nsq; positivity

lemma nsq_eq_zero {a b : Pt} (h : nsq a b = 0) : a = b := by
  unfold nsq at h
  have h0 : b 0 - a 0 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
  have h1 : b 1 - a 1 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
  exact pt_ext (by linarith) (by linarith)

lemma nsq_pos {a b : Pt} (h : a ≠ b) : 0 < nsq a b :=
  lt_of_le_of_ne (nsq_nonneg a b) (fun he => h (nsq_eq_zero he.symm))

lemma cross_ne_imp_ne {a b c : Pt} (h : cross a b c ≠ 0) : a ≠ b := by
  intro hab; subst hab; exact h (by simp [cross])

/-! ### The collinearity ↔ determinant bridge -/

/-- A point on the line through `a` and `b` (`b ≠ a`) is `r • (b - a) +ᵥ a` for some `r`. -/
lemma cross_zero_repr {a b p : Pt} (hba : b ≠ a) (h : cross a b p = 0) :
    ∃ r : ℝ, p = r • (b - a) +ᵥ a := by
  have hne : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hba (pt_ext (by linarith [hcon.1]) (by linarith [hcon.2]))
  have hcross : (b 0 - a 0) * (p 1 - a 1) = (b 1 - a 1) * (p 0 - a 0) := by
    have h' := h; simp only [cross] at h'; linarith
  have e0 : (b - a) 0 = b 0 - a 0 := rfl
  have e1 : (b - a) 1 = b 1 - a 1 := rfl
  rcases hne with h0 | h1
  · refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
    apply pt_ext
    · show p 0 = (p 0 - a 0) / (b 0 - a 0) * (b - a) 0 + a 0
      rw [e0]; field_simp; ring
    · show p 1 = (p 0 - a 0) / (b 0 - a 0) * (b - a) 1 + a 1
      rw [e1]; field_simp; nlinarith [hcross]
  · refine ⟨(p 1 - a 1) / (b 1 - a 1), ?_⟩
    apply pt_ext
    · show p 0 = (p 1 - a 1) / (b 1 - a 1) * (b - a) 0 + a 0
      rw [e0]; field_simp; nlinarith [hcross]
    · show p 1 = (p 1 - a 1) / (b 1 - a 1) * (b - a) 1 + a 1
      rw [e1]; field_simp; ring

/-- Three points are collinear iff the `cross` determinant vanishes. -/
lemma collinear_iff_cross (a b c : Pt) :
    Collinear ℝ ({a, b, c} : Set Pt) ↔ cross a b c = 0 := by
  constructor
  · intro h
    rw [collinear_iff_of_mem (show a ∈ ({a, b, c} : Set Pt) by simp)] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨rb, hb⟩ := hv b (by simp)
    obtain ⟨rc, hc⟩ := hv c (by simp)
    have hb0 : b 0 = rb * v 0 + a 0 := by rw [hb]; rfl
    have hb1 : b 1 = rb * v 1 + a 1 := by rw [hb]; rfl
    have hc0 : c 0 = rc * v 0 + a 0 := by rw [hc]; rfl
    have hc1 : c 1 = rc * v 1 + a 1 := by rw [hc]; rfl
    simp only [cross, hb0, hb1, hc0, hc1]; ring
  · intro h
    by_cases hba : b = a
    · subst hba
      rw [Set.insert_idem]; exact collinear_pair ℝ b c
    · rw [collinear_iff_of_mem (show a ∈ ({a, b, c} : Set Pt) by simp)]
      refine ⟨b - a, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpa | hpb | hpc
      · subst hpa; exact ⟨0, by apply pt_ext <;> simp⟩
      · subst hpb; exact ⟨1, by apply pt_ext <;> simp⟩
      · subst hpc; exact cross_zero_repr hba h

/-! ### The pure-arithmetic core of Kelly's argument -/

/-- Two reals on the same closed side of the origin: the one farther out gives the
inequality.  Phrased so each disjunct says "`u` is at least as far from `t = 0` as `v`". -/
lemma same_sign (p q : ℝ) (h : 0 ≤ p * q) :
    (p - q) ^ 2 ≤ p ^ 2 ∨ (q - p) ^ 2 ≤ q ^ 2 := by
  rcases le_total (q ^ 2) (p ^ 2) with hle | hle
  · left; nlinarith [h, hle, sq_nonneg (p - q), sq_nonneg (p + q)]
  · right; nlinarith [h, hle, sq_nonneg (p - q), sq_nonneg (p + q)]

/-- Among three distinct reals, some ordered pair `(u, v)` has `(u - v)^2 ≤ (u - t)^2`:
the pigeonhole step (two of the points lie on the same side of the foot `t`). -/
lemma pick (t x y z : ℝ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ u v : ℝ, (u = x ∨ u = y ∨ u = z) ∧ (v = x ∨ v = y ∨ v = z) ∧
      u ≠ v ∧ (u - v) ^ 2 ≤ (u - t) ^ 2 := by
  have hsign : (0 ≤ (x - t) * (y - t)) ∨ (0 ≤ (x - t) * (z - t)) ∨ (0 ≤ (y - t) * (z - t)) := by
    rcases le_total (x - t) 0 with hx | hx <;>
    rcases le_total (y - t) 0 with hy | hy <;>
    rcases le_total (z - t) 0 with hz | hz
    all_goals first
      | (left; nlinarith) | (right; left; nlinarith) | (right; right; nlinarith)
  rcases hsign with hs | hs | hs
  · rcases same_sign (x - t) (y - t) hs with hh | hh
    · exact ⟨x, y, Or.inl rfl, Or.inr (Or.inl rfl), hxy, by nlinarith [hh]⟩
    · exact ⟨y, x, Or.inr (Or.inl rfl), Or.inl rfl, fun h => hxy h.symm, by nlinarith [hh]⟩
  · rcases same_sign (x - t) (z - t) hs with hh | hh
    · exact ⟨x, z, Or.inl rfl, Or.inr (Or.inr rfl), hxz, by nlinarith [hh]⟩
    · exact ⟨z, x, Or.inr (Or.inr rfl), Or.inl rfl, fun h => hxz h.symm, by nlinarith [hh]⟩
  · rcases same_sign (y - t) (z - t) hs with hh | hh
    · exact ⟨y, z, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hyz, by nlinarith [hh]⟩
    · exact ⟨z, y, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), fun h => hyz h.symm, by nlinarith [hh]⟩

/-- The arithmetic heart.  With `D = |b-a|² > 0`, `K·D - I² = cross² > 0` (Lagrange),
the three line-parameters `0, 1, L` distinct, there are parameters `rR ≠ rQ` of two of the
points with `D·(rR-rQ)² < K - 2·rR·I + rR²·D` — i.e. `|RQ|² < |cR|²`. -/
lemma core (D I K L : ℝ) (hD : 0 < D) (hcross : 0 < K * D - I ^ 2)
    (hL0 : L ≠ 0) (hL1 : L ≠ 1) :
    ∃ rR rQ : ℝ, (rR = 0 ∨ rR = 1 ∨ rR = L) ∧ (rQ = 0 ∨ rQ = 1 ∨ rQ = L) ∧
      rR ≠ rQ ∧ D * (rR - rQ) ^ 2 < K - 2 * rR * I + rR ^ 2 * D := by
  obtain ⟨u, v, hu, hv, huv, hle⟩ :=
    pick (I / D) 0 1 L (by norm_num) (by simpa using hL0.symm) (fun h => hL1 h.symm)
  have hDle : D * (u - v) ^ 2 ≤ D * (u - I / D) ^ 2 := mul_le_mul_of_nonneg_left hle hD.le
  have hexp : D * (u - I / D) ^ 2 = D * u ^ 2 - 2 * u * I + D * (I / D) ^ 2 := by
    field_simp; ring
  have hKt : D * (I / D) ^ 2 < K := by
    have he : D * (I / D) ^ 2 = I ^ 2 / D := by field_simp
    rw [he, div_lt_iff₀ hD]; nlinarith [hcross]
  exact ⟨u, v, hu, hv, huv, by linarith [hDle, hexp, hKt]⟩

/-! ### The Sylvester–Gallai theorem -/

/-- A non-collinear finite set carries a non-degenerate flag (three non-collinear points). -/
lemma exists_flag {P : Finset Pt} (hP : ¬ Collinear ℝ (↑P : Set Pt)) :
    ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, cross a b c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hP
  by_cases hP2 : ∃ a ∈ P, ∃ b ∈ P, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hP2
    rw [collinear_iff_of_mem (show a ∈ (↑P : Set Pt) from Finset.mem_coe.mpr ha)]
    refine ⟨b - a, ?_⟩
    intro p hp
    have hpP : p ∈ P := Finset.mem_coe.mp hp
    exact cross_zero_repr (fun h => hab h.symm) (hcon a ha b hb p hpP)
  · push_neg at hP2
    have hsub : (↑P : Set Pt).Subsingleton := fun x hx y hy =>
      hP2 x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy)
    rcases hsub.eq_empty_or_singleton with h | ⟨a, h⟩
    · rw [h]; exact collinear_empty ℝ Pt
    · rw [h]; exact collinear_singleton ℝ a

/-- **Sylvester–Gallai.**  Any finite set of points in the real plane that is not collinear
admits an ordinary line: there are two distinct points `a, b ∈ P` such that every point of
`P` lying on the line `ab` is `a` or `b`. -/
theorem sylvester_gallai {P : Finset Pt} (hP : ¬ Collinear ℝ (↑P : Set Pt)) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
      ∀ c ∈ P, Collinear ℝ ({a, b, c} : Set Pt) → c = a ∨ c = b := by
  classical
  -- the finite set of non-degenerate flags `(a, b, c)`
  set S : Finset (Pt × Pt × Pt) :=
    (P ×ˢ P ×ˢ P).filter (fun t => cross t.1 t.2.1 t.2.2 ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨a, ha, b, hb, c, hc, hcr⟩ := exists_flag hP
    exact ⟨(a, b, c), by
      simp only [hS, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, hb, hc⟩, hcr⟩⟩
  obtain ⟨t0, ht0S, ht0min⟩ :=
    S.exists_min_image (fun t => cross t.1 t.2.1 t.2.2 ^ 2 / nsq t.1 t.2.1) hSne
  obtain ⟨⟨haP, hbP, hcP⟩, hcr0⟩ :=
    (by simpa only [hS, Finset.mem_filter, Finset.mem_product] using ht0S :
      ((t0.1 ∈ P ∧ t0.2.1 ∈ P ∧ t0.2.2 ∈ P) ∧ cross t0.1 t0.2.1 t0.2.2 ≠ 0))
  set a := t0.1 with ha
  set b := t0.2.1 with hb
  set c := t0.2.2 with hc
  have hab : a ≠ b := cross_ne_imp_ne hcr0
  refine ⟨a, haP, b, hbP, hab, ?_⟩
  intro cp hcpP hcol
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨hcpa, hcpb⟩ := hcontra
  -- `cp` lies on line `ab` and differs from both `a` and `b`
  have hcrcp : cross a b cp = 0 := (collinear_iff_cross a b cp).mp hcol
  obtain ⟨L, hLrepr⟩ := cross_zero_repr (fun h => hab h.symm) hcrcp
  -- parameter of `cp`; `L ≠ 0` (≠ a), `L ≠ 1` (≠ b)
  have hL0 : L ≠ 0 := by
    intro h; apply hcpa; rw [hLrepr, h]; simp
  have hL1 : L ≠ 1 := by
    intro h; apply hcpb; rw [hLrepr, h]; show (1 : ℝ) • (b - a) +ᵥ a = b
    simp
  -- abbreviations for the core
  set D := nsq a b with hD'
  set I := (b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) with hI'
  set K := nsq a c with hK'
  have hDpos : 0 < D := nsq_pos hab
  have hcrossId : cross a b c ^ 2 = K * D - I ^ 2 := by
    simp only [cross, nsq, hK', hD', hI']; ring
  have hcrosssq : 0 < cross a b c ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hcr0))
  have hKDI : 0 < K * D - I ^ 2 := by rw [← hcrossId]; exact hcrosssq
  obtain ⟨rR, rQ, hrR, hrQ, hrne, hcoreIneq⟩ := core D I K L hDpos hKDI hL0 hL1
  -- build the two points `R, Q` from their parameters
  obtain ⟨R, hRdef⟩ : ∃ R : Pt, R = rR • (b - a) +ᵥ a := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Pt, Q = rQ • (b - a) +ᵥ a := ⟨_, rfl⟩
  have hR0 : R 0 = rR * (b 0 - a 0) + a 0 := by rw [hRdef]; exact coord0 rR a b
  have hR1 : R 1 = rR * (b 1 - a 1) + a 1 := by rw [hRdef]; exact coord1 rR a b
  have hQ0 : Q 0 = rQ * (b 0 - a 0) + a 0 := by rw [hQdef]; exact coord0 rQ a b
  have hQ1 : Q 1 = rQ * (b 1 - a 1) + a 1 := by rw [hQdef]; exact coord1 rQ a b
  -- membership of `R` and `Q` in `P`
  have hpoint : ∀ r : ℝ, (r = 0 ∨ r = 1 ∨ r = L) → r • (b - a) +ᵥ a ∈ P := by
    intro r hr
    rcases hr with h | h | h
    · rw [h]; simpa using haP
    · rw [h]; show (1 : ℝ) • (b - a) +ᵥ a ∈ P; simpa using hbP
    · rw [h, ← hLrepr]; exact hcpP
  have hRP : R ∈ P := by rw [hRdef]; exact hpoint rR hrR
  have hQP : Q ∈ P := by rw [hQdef]; exact hpoint rQ hrQ
  -- coordinate identities
  have hnsqRQ : nsq R Q = D * (rR - rQ) ^ 2 := by
    simp only [nsq, hR0, hR1, hQ0, hQ1, hD']; ring
  have hnsqcR : nsq c R = K - 2 * rR * I + rR ^ 2 * D := by
    simp only [nsq, hR0, hR1, hK', hI', hD']; ring
  have hcrCRQ : cross c R Q = (rQ - rR) * cross a b c := by
    simp only [cross, hR0, hR1, hQ0, hQ1]; ring
  -- the new flag is non-degenerate and strictly closer
  have hcRpos : 0 < nsq c R := by
    rw [hnsqcR]; linarith [hcoreIneq, mul_nonneg hDpos.le (sq_nonneg (rR - rQ))]
  have hcrCRQne : cross c R Q ≠ 0 := by
    rw [hcrCRQ]
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => hrne h.symm)) hcr0
  -- `(c, R, Q) ∈ S`
  have hmemS : (c, R, Q) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hcP, hRP, hQP⟩, hcrCRQne⟩
  -- strict decrease, contradicting minimality
  have hstrict :
      cross c R Q ^ 2 / nsq c R < cross a b c ^ 2 / nsq a b := by
    rw [div_lt_div_iff₀ hcRpos hDpos]
    have hkey : (rR - rQ) ^ 2 * nsq a b < nsq c R := by
      rw [← hD', hnsqcR]; nlinarith [hcoreIneq]
    have hsqeq : cross c R Q ^ 2 = (rR - rQ) ^ 2 * cross a b c ^ 2 := by
      rw [hcrCRQ]; ring
    calc cross c R Q ^ 2 * nsq a b
        = cross a b c ^ 2 * ((rR - rQ) ^ 2 * nsq a b) := by rw [hsqeq]; ring
      _ < cross a b c ^ 2 * nsq c R := mul_lt_mul_of_pos_left hkey hcrosssq
  have hmin := ht0min (c, R, Q) hmemS
  exact absurd hstrict (not_lt.mpr hmin)

end SG
