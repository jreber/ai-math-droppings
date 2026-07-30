import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Kionke's Lemma 1: directed points cannot have cyclic trajectories

This file formalizes **Lemma 1** of Steffen Kionke, "A geometric approach to
divergent points of higher dimensional Collatz mappings", Monatsh. Math. 182
(2017) 851-863, arXiv:1511.05893, for the concrete rank-2 example the paper
uses throughout (Example 1 / Example 2: the Collatz map extended to `ℤ[√2]`,
written in coordinates `(a,b) ↦ a + b√2`).

**Paper statement (Lemma 1, relatively-prime-type generalized Collatz map
`T = T_{d,m,r}`):** *Every point `x ≠ 0` that lies on a semipermeable
hyperplane does not have a cyclic `T`-trajectory.*

Here "semipermeable hyperplane" (Definition 1) is the kernel of a linear form
`Φ` that is *strictly positive* on the set of shift vectors `S_r` (i.e.
`Φ(v) > 0` for every nonzero `v ∈ S_r`); a point lying on such a hyperplane is
called *directed* (Definition 2).

**Provenance.** This file reproduces the necessary vocabulary from scratch
rather than importing it: the `Point`, `CollatzMapZ2`, `sqrtTwoCollartzMap`
definitions match the unmerged prior artifact
`lean4/CollatzMultidimKionkeDivergenceCone.lean` (commit `f8350a6` on branch
`worktree-agent-ae3687b5a856223da`), which was never merged to `main` and
still contains `sorry`s in its own headline theorem (see
`docs/kb/failed/2026-07-29__conj-2026-07-19-001__kionke_divergence_cone_full_theorem.json`).
`IsDirected` is renamed `IsKionkeDirectedPt` here since Mathlib already has an
unrelated `IsDirected` (for directed preorders).

## Main result

`kionke_lemma1_sqrtTwo`: for the concrete `ℤ[√2]` Collatz map, no point that
is *directed* for the shift-vector set `sqrtTwoShiftVectors` has a periodic
`T`-trajectory. (By Example 2 in the paper, the directed points here are
exactly the nonzero points in the open second/fourth quadrants — the "tame
cone" of that example.)

## Proof idea (Kionke's own argument, equation (1) in the paper)

Along a trajectory `x_0 = x, x_1, x_2, …` with `x_0` on the semipermeable
hyperplane `ker Φ`, the recursion
`2·Φ(x_{i+1}) = m_{c_i}·Φ(x_i) + Φ(r_{c_i})`
(where `c_i` is the parity class of `x_i` and `(m_{c_i}, r_{c_i})` the
matching multiplier/shift pair) shows:

* `Φ(x_i) ≥ 0` for every `i` (all four multipliers `1, 3, 3, 9` are positive
  and all four shift vectors have `Φ ≥ 0`, by induction from `Φ(x_0) = 0`);
* once `Φ(x_i) > 0` it stays positive forever after (same recursion, strict
  case);
* if `Φ(x_i) = 0` for *every* `i`, then `Φ(r_{c_i}) = 0` for every `i`, which
  (since `Φ` is strictly positive on the three nonzero shift vectors
  `(1,0), (0,1), (3,1)`) forces `r_{c_i} = (0,0) = r₀` for every `i`, i.e.
  every iterate lies in the "both coordinates even" class. There the map is
  exactly `x ↦ x/2` on each coordinate, so `x_i = 2·x_{i+1}` exactly, for
  every `i`; a nonzero integer cannot be halved exactly forever (elementary
  infinite descent on `natAbs`), contradicting `x ≠ 0`.

Combining: `Φ` is somewhere nonzero along the orbit, hence eventually
strictly positive forever after some index `j`. If `x` were periodic with
period `n > 0`, then `x` would recur at every multiple of `n`, in particular
at some multiple `n·t ≥ j`, forcing `Φ(x) = Φ(x_{n·t}) > 0` — contradicting
`Φ(x) = 0`.
-/

namespace CollatzMultidimKionkeLemma1

-- ===== Vocabulary (matches the unmerged prior artifact) =====

/-- A point in the rank-2 free abelian group ℤ². -/
def Point := ℤ × ℤ

/-- Embedding a rank-2 lattice point into ℝ². -/
def Point.embed : Point → ℝ × ℝ := fun p => (↑p.1, ↑p.2)

/-- Iteration of a map `n` times: `mapPower T n x` applies `T` first, then
recurses (matching Kionke's `T^k(x)`). -/
def mapPower (T : Point → Point) : ℕ → Point → Point
  | 0, x => x
  | n + 1, x => mapPower T n (T x)

/-- A generalized Collatz map on ℤ², relatively-prime type, with the four
parity classes that arise for `d = 2` (`Λ/dΛ ≅ (ZMod 2) × (ZMod 2)`). -/
structure CollatzMapZ2 where
  d : ℕ
  hd : d ≥ 2
  m₀ : ℤ
  m₁ : ℤ
  m₂ : ℤ
  m₃ : ℤ
  hm₀ : m₀ ≠ 0
  hm₁ : m₁ ≠ 0
  hm₂ : m₂ ≠ 0
  hm₃ : m₃ ≠ 0
  hcop₀ : Int.gcd (↑d) m₀ = 1
  hcop₁ : Int.gcd (↑d) m₁ = 1
  hcop₂ : Int.gcd (↑d) m₂ = 1
  hcop₃ : Int.gcd (↑d) m₃ = 1
  r₀ : ℤ × ℤ
  r₁ : ℤ × ℤ
  r₂ : ℤ × ℤ
  r₃ : ℤ × ℤ

/-- Apply a `CollatzMapZ2` to a point based on parity of coordinates. -/
def CollatzMapZ2.apply (T : CollatzMapZ2) (p : Point) : Point :=
  let (a, b) := p
  let pa := a % 2
  let pb := b % 2
  if pa = 0 && pb = 0 then
    let (ra, rb) := T.r₀
    ((T.m₀ * a + ra) / (T.d : ℤ), (T.m₀ * b + rb) / (T.d : ℤ))
  else if pa ≠ 0 && pb = 0 then
    let (ra, rb) := T.r₁
    ((T.m₁ * a + ra) / (T.d : ℤ), (T.m₁ * b + rb) / (T.d : ℤ))
  else if pa = 0 && pb ≠ 0 then
    let (ra, rb) := T.r₂
    ((T.m₂ * a + ra) / (T.d : ℤ), (T.m₂ * b + rb) / (T.d : ℤ))
  else
    let (ra, rb) := T.r₃
    ((T.m₃ * a + ra) / (T.d : ℤ), (T.m₃ * b + rb) / (T.d : ℤ))

/-- The concrete `ℤ[√2]` Collatz map from Kionke's Example 1: `C² : Λ → Λ`
where `C(z) = z/√2` if `√2 ∣ z` and `C(z) = (3z+1)/√2` otherwise, written in
the `(1,√2)`-basis. -/
def sqrtTwoCollartzMap : CollatzMapZ2 :=
  { d := 2
    hd := by norm_num
    m₀ := 1
    m₁ := 3
    m₂ := 3
    m₃ := 9
    hm₀ := by norm_num
    hm₁ := by norm_num
    hm₂ := by norm_num
    hm₃ := by norm_num
    hcop₀ := by decide
    hcop₁ := by decide
    hcop₂ := by decide
    hcop₃ := by decide
    r₀ := (0, 0)
    r₁ := (1, 0)
    r₂ := (0, 1)
    r₃ := (3, 1) }

/-- The shift vectors for the `ℤ[√2]` map (`S_r` in the paper). -/
def sqrtTwoShiftVectors : Set (ℝ × ℝ) :=
  fun v => v = (0, 0) ∨ v = (1, 0) ∨ v = (0, 1) ∨ v = (3, 1)

-- ===== Semipermeable hyperplanes / directed points (Definitions 1, 2) =====

/-- The linear form `Φ_{a,b}(x,y) = a x + b y`. -/
def Phi (a b : ℝ) (v : ℝ × ℝ) : ℝ := a * v.1 + b * v.2

/-- A linear form `Φ_{a,b}` is *strictly positive* for a set `S` (Definition 1)
if `Φ(w) > 0` for every nonzero `w ∈ S`. -/
def StrictlyPositiveFor (a b : ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ v ∈ S, v ≠ (0, 0) → Phi a b v > 0

/-- A point `x` is *directed* for a shift-vector set `S` (Definition 2) if it
lies on a semipermeable hyperplane, i.e. in the kernel of some linear form
that is strictly positive for `S`. (Named `IsKionkeDirectedPt`, not
`IsDirected`, since Mathlib already uses that name for directed preorders.) -/
def IsKionkeDirectedPt (S : Set (ℝ × ℝ)) (x : Point) : Prop :=
  ∃ a b : ℝ, StrictlyPositiveFor a b S ∧ Phi a b (Point.embed x) = 0

-- ===== `mapPower` iterate-successor lemma =====

/-- `T` applied `i+1` times equals `T` applied once to the result of `i`
iterations (the "apply-last" form, needed since `mapPower`'s own recursion is
stated "apply-first"). -/
lemma mapPower_succ_apply' (T : Point → Point) (i : ℕ) (y : Point) :
    mapPower T (i + 1) y = T (mapPower T i y) := by
  induction i generalizing y with
  | zero => rfl
  | succ k ih =>
      show mapPower T (k + 1) (T y) = T (mapPower T (k + 1) y)
      rw [ih (T y)]
      rfl

-- ===== Exact per-class formulas for `sqrtTwoCollartzMap.apply` =====

lemma apply_class0 (a b : ℤ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    sqrtTwoCollartzMap.apply (a, b) = (a / 2, b / 2) := by
  simp only [CollatzMapZ2.apply, sqrtTwoCollartzMap, ha, hb]
  norm_num

lemma apply_class1 (a b : ℤ) (ha : a % 2 ≠ 0) (hb : b % 2 = 0) :
    sqrtTwoCollartzMap.apply (a, b) = ((3 * a + 1) / 2, 3 * b / 2) := by
  simp only [CollatzMapZ2.apply, sqrtTwoCollartzMap]
  have e1 : (a % 2 = 0 && b % 2 = 0) = false := by simp [ha, hb]
  have e2 : (a % 2 ≠ 0 && b % 2 = 0) = true := by simp [ha, hb]
  simp only [e1, e2]
  norm_num

lemma apply_class2 (a b : ℤ) (ha : a % 2 = 0) (hb : b % 2 ≠ 0) :
    sqrtTwoCollartzMap.apply (a, b) = (3 * a / 2, (3 * b + 1) / 2) := by
  simp only [CollatzMapZ2.apply, sqrtTwoCollartzMap]
  have e1 : (a % 2 = 0 && b % 2 = 0) = false := by simp [ha, hb]
  have e2 : (a % 2 ≠ 0 && b % 2 = 0) = false := by simp [ha, hb]
  have e3 : (a % 2 = 0 && b % 2 ≠ 0) = true := by simp [ha, hb]
  simp only [e1, e2, e3]
  norm_num

lemma apply_class3 (a b : ℤ) (ha : a % 2 ≠ 0) (hb : b % 2 ≠ 0) :
    sqrtTwoCollartzMap.apply (a, b) = ((9 * a + 3) / 2, (9 * b + 1) / 2) := by
  simp only [CollatzMapZ2.apply, sqrtTwoCollartzMap]
  have e1 : (a % 2 = 0 && b % 2 = 0) = false := by simp [ha, hb]
  have e2 : (a % 2 ≠ 0 && b % 2 = 0) = false := by simp [ha, hb]
  have e3 : (a % 2 = 0 && b % 2 ≠ 0) = false := by simp [ha, hb]
  simp only [e1, e2, e3]
  norm_num

-- ===== The recursion identity (equation (1) in the paper), per class =====

lemma phi_recursion_class0 (a b : ℝ) (x y : ℤ) (hx : x % 2 = 0) (hy : y % 2 = 0) :
    (2 : ℝ) * Phi a b (Point.embed (sqrtTwoCollartzMap.apply (x, y)))
      = 1 * Phi a b (Point.embed (x, y)) + Phi a b (0, 0) := by
  have happly := apply_class0 x y hx hy
  rw [happly]
  have h2x : (2 : ℤ) ∣ x := by omega
  have h2y : (2 : ℤ) ∣ y := by omega
  have ex : (2 : ℤ) * (x / 2) = x := Int.mul_ediv_cancel' h2x
  have ey : (2 : ℤ) * (y / 2) = y := Int.mul_ediv_cancel' h2y
  have exR : (2 : ℝ) * ((x / 2 : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast ex
  have eyR : (2 : ℝ) * ((y / 2 : ℤ) : ℝ) = (y : ℝ) := by exact_mod_cast ey
  simp only [Point.embed, Phi]
  linear_combination a * exR + b * eyR

lemma phi_recursion_class1 (a b : ℝ) (x y : ℤ) (hx : x % 2 ≠ 0) (hy : y % 2 = 0) :
    (2 : ℝ) * Phi a b (Point.embed (sqrtTwoCollartzMap.apply (x, y)))
      = 3 * Phi a b (Point.embed (x, y)) + Phi a b (1, 0) := by
  have happly := apply_class1 x y hx hy
  rw [happly]
  have h2x : (2 : ℤ) ∣ (3 * x + 1) := by omega
  have h2y : (2 : ℤ) ∣ (3 * y) := by omega
  have ex : (2 : ℤ) * ((3 * x + 1) / 2) = 3 * x + 1 := Int.mul_ediv_cancel' h2x
  have ey : (2 : ℤ) * (3 * y / 2) = 3 * y := Int.mul_ediv_cancel' h2y
  have exR : (2 : ℝ) * (((3 * x + 1) / 2 : ℤ) : ℝ) = 3 * (x : ℝ) + 1 := by exact_mod_cast ex
  have eyR : (2 : ℝ) * ((3 * y / 2 : ℤ) : ℝ) = 3 * (y : ℝ) := by exact_mod_cast ey
  simp only [Point.embed, Phi]
  linear_combination a * exR + b * eyR

lemma phi_recursion_class2 (a b : ℝ) (x y : ℤ) (hx : x % 2 = 0) (hy : y % 2 ≠ 0) :
    (2 : ℝ) * Phi a b (Point.embed (sqrtTwoCollartzMap.apply (x, y)))
      = 3 * Phi a b (Point.embed (x, y)) + Phi a b (0, 1) := by
  have happly := apply_class2 x y hx hy
  rw [happly]
  have h2x : (2 : ℤ) ∣ (3 * x) := by omega
  have h2y : (2 : ℤ) ∣ (3 * y + 1) := by omega
  have ex : (2 : ℤ) * (3 * x / 2) = 3 * x := Int.mul_ediv_cancel' h2x
  have ey : (2 : ℤ) * ((3 * y + 1) / 2) = 3 * y + 1 := Int.mul_ediv_cancel' h2y
  have exR : (2 : ℝ) * ((3 * x / 2 : ℤ) : ℝ) = 3 * (x : ℝ) := by exact_mod_cast ex
  have eyR : (2 : ℝ) * (((3 * y + 1) / 2 : ℤ) : ℝ) = 3 * (y : ℝ) + 1 := by exact_mod_cast ey
  simp only [Point.embed, Phi]
  linear_combination a * exR + b * eyR

lemma phi_recursion_class3 (a b : ℝ) (x y : ℤ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0) :
    (2 : ℝ) * Phi a b (Point.embed (sqrtTwoCollartzMap.apply (x, y)))
      = 9 * Phi a b (Point.embed (x, y)) + Phi a b (3, 1) := by
  have happly := apply_class3 x y hx hy
  rw [happly]
  have h2x : (2 : ℤ) ∣ (9 * x + 3) := by omega
  have h2y : (2 : ℤ) ∣ (9 * y + 1) := by omega
  have ex : (2 : ℤ) * ((9 * x + 3) / 2) = 9 * x + 3 := Int.mul_ediv_cancel' h2x
  have ey : (2 : ℤ) * ((9 * y + 1) / 2) = 9 * y + 1 := Int.mul_ediv_cancel' h2y
  have exR : (2 : ℝ) * (((9 * x + 3) / 2 : ℤ) : ℝ) = 9 * (x : ℝ) + 3 := by exact_mod_cast ex
  have eyR : (2 : ℝ) * (((9 * y + 1) / 2 : ℤ) : ℝ) = 9 * (y : ℝ) + 1 := by exact_mod_cast ey
  simp only [Point.embed, Phi]
  linear_combination a * exR + b * eyR

-- Values of Φ on the four shift vectors: zero at r₀, positive at r₁, r₂, r₃
-- (the latter directly from strict positivity of Φ on the nonzero elements
-- of `sqrtTwoShiftVectors`, of which `(1,0), (0,1), (3,1)` are members).

lemma phi_00_zero (a b : ℝ) : Phi a b (0, 0) = 0 := by simp [Phi]

lemma phi_10_pos (a b : ℝ) (hpos : StrictlyPositiveFor a b sqrtTwoShiftVectors) :
    0 < Phi a b (1, 0) := hpos (1, 0) (by right; left; rfl) (by simp)

lemma phi_01_pos (a b : ℝ) (hpos : StrictlyPositiveFor a b sqrtTwoShiftVectors) :
    0 < Phi a b (0, 1) := hpos (0, 1) (by right; right; left; rfl) (by simp)

lemma phi_31_pos (a b : ℝ) (hpos : StrictlyPositiveFor a b sqrtTwoShiftVectors) :
    0 < Phi a b (3, 1) := hpos (3, 1) (by right; right; right; rfl) (by simp)

-- ===== Infinite-descent helper: a nonzero integer cannot be halved forever =====

/-- If `f : ℕ → ℤ` satisfies `f i = 2 * f (i+1)` for every `i`, then `f 0 = 0`.
(A nonzero integer cannot be exactly halved infinitely often.) -/
lemma no_infinite_exact_halving (f : ℕ → ℤ) (hstep : ∀ i, f i = 2 * f (i + 1))
    (h0 : f 0 ≠ 0) : False := by
  set g : ℕ → ℕ := fun i => (f i).natAbs with hg
  have hgstep : ∀ i, g i = 2 * g (i + 1) := by
    intro i
    have hfi := hstep i
    simp only [hg]
    rw [hfi, Int.natAbs_mul]
    norm_num
  have hallpos : ∀ i, g i ≠ 0 := by
    intro i
    induction i with
    | zero => simp only [hg]; exact Int.natAbs_ne_zero.mpr h0
    | succ k ih =>
        intro hcontra
        apply ih
        rw [hgstep k, hcontra, Nat.mul_zero]
  have hbound : ∀ i, g i + i ≤ g 0 := by
    intro i
    induction i with
    | zero => simp
    | succ k ih =>
        have hk1 : g (k + 1) ≠ 0 := hallpos (k + 1)
        have heqk : g k = 2 * g (k + 1) := hgstep k
        omega
  have hfin := hbound (g 0 + 1)
  have hne := hallpos (g 0 + 1)
  omega

-- ===== Lemma 1 =====

/-- **Kionke's Lemma 1**, for `sqrtTwoCollartzMap`: every nonzero point that
is directed for `sqrtTwoShiftVectors` does not have a cyclic (periodic)
`T`-trajectory. -/
theorem kionke_lemma1_sqrtTwo (x : Point) (hx : x ≠ (0, 0))
    (hdir : IsKionkeDirectedPt sqrtTwoShiftVectors x) :
    ¬ ∃ n : ℕ, n > 0 ∧ mapPower sqrtTwoCollartzMap.apply n x = x := by
  obtain ⟨a, b, hpos, hphi0⟩ := hdir
  rintro ⟨n, hn, hcycle⟩
  -- Φ is nonnegative along the whole orbit.
  have hnonneg : ∀ i, 0 ≤ Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply i x)) := by
    intro i
    induction i with
    | zero => simpa [mapPower] using le_of_eq hphi0.symm
    | succ k ih =>
        rw [mapPower_succ_apply' sqrtTwoCollartzMap.apply k x]
        set q := mapPower sqrtTwoCollartzMap.apply k x with hq
        obtain ⟨p1, p2⟩ := q
        rcases Int.emod_two_eq p1 with h1 | h1 <;> rcases Int.emod_two_eq p2 with h2 | h2
        · have hrec := phi_recursion_class0 a b p1 p2 h1 h2
          rw [phi_00_zero] at hrec
          nlinarith [hrec, ih]
        · have h2' : p2 % 2 ≠ 0 := by omega
          have hrec := phi_recursion_class2 a b p1 p2 h1 h2'
          have := phi_01_pos a b hpos
          nlinarith [hrec, ih, this]
        · have h1' : p1 % 2 ≠ 0 := by omega
          have hrec := phi_recursion_class1 a b p1 p2 h1' h2
          have := phi_10_pos a b hpos
          nlinarith [hrec, ih, this]
        · have h1' : p1 % 2 ≠ 0 := by omega
          have h2' : p2 % 2 ≠ 0 := by omega
          have hrec := phi_recursion_class3 a b p1 p2 h1' h2'
          have := phi_31_pos a b hpos
          nlinarith [hrec, ih, this]
  -- Once positive, Φ stays positive along the orbit.
  have hgrow : ∀ i, 0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply i x)) →
      0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply (i + 1) x)) := by
    intro i hi
    rw [mapPower_succ_apply' sqrtTwoCollartzMap.apply i x]
    set q := mapPower sqrtTwoCollartzMap.apply i x with hq
    obtain ⟨p1, p2⟩ := q
    rcases Int.emod_two_eq p1 with h1 | h1 <;> rcases Int.emod_two_eq p2 with h2 | h2
    · have hrec := phi_recursion_class0 a b p1 p2 h1 h2
      rw [phi_00_zero] at hrec
      nlinarith [hrec, hi]
    · have h2' : p2 % 2 ≠ 0 := by omega
      have hrec := phi_recursion_class2 a b p1 p2 h1 h2'
      have := phi_01_pos a b hpos
      nlinarith [hrec, hi, this]
    · have h1' : p1 % 2 ≠ 0 := by omega
      have hrec := phi_recursion_class1 a b p1 p2 h1' h2
      have := phi_10_pos a b hpos
      nlinarith [hrec, hi, this]
    · have h1' : p1 % 2 ≠ 0 := by omega
      have h2' : p2 % 2 ≠ 0 := by omega
      have hrec := phi_recursion_class3 a b p1 p2 h1' h2'
      have := phi_31_pos a b hpos
      nlinarith [hrec, hi, this]
  have hstay : ∀ j, 0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply j x)) →
      ∀ k, j ≤ k → 0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply k x)) := by
    intro j hj k hk
    induction k, hk using Nat.le_induction with
    | base => exact hj
    | succ m _ ih => exact hgrow m ih
  by_cases hallzero : ∀ i, Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply i x)) = 0
  · -- Φ vanishes on the whole orbit: every iterate is in class 0, giving exact
    -- halving forever, which is impossible for the nonzero point x.
    have hclass0 : ∀ i, mapPower sqrtTwoCollartzMap.apply i x
        = (2 * (mapPower sqrtTwoCollartzMap.apply (i + 1) x).1,
           2 * (mapPower sqrtTwoCollartzMap.apply (i + 1) x).2) := by
      intro i
      rw [mapPower_succ_apply' sqrtTwoCollartzMap.apply i x]
      set q := mapPower sqrtTwoCollartzMap.apply i x with hq
      have hval0 : Phi a b (Point.embed q) = 0 := by rw [hq]; exact hallzero i
      have hval1 : Phi a b (Point.embed (sqrtTwoCollartzMap.apply q)) = 0 := by
        rw [hq, ← mapPower_succ_apply' sqrtTwoCollartzMap.apply i x]; exact hallzero (i + 1)
      obtain ⟨p1, p2⟩ := q
      rcases Int.emod_two_eq p1 with h1 | h1 <;> rcases Int.emod_two_eq p2 with h2 | h2
      · have happly := apply_class0 p1 p2 h1 h2
        rw [happly]
        have h2x : (2 : ℤ) ∣ p1 := by omega
        have h2y : (2 : ℤ) ∣ p2 := by omega
        have ex : (2 : ℤ) * (p1 / 2) = p1 := Int.mul_ediv_cancel' h2x
        have ey : (2 : ℤ) * (p2 / 2) = p2 := Int.mul_ediv_cancel' h2y
        exact Prod.ext ex.symm ey.symm
      · exfalso
        have h2' : p2 % 2 ≠ 0 := by omega
        have hrec := phi_recursion_class2 a b p1 p2 h1 h2'
        rw [hval0, hval1] at hrec
        have hp := phi_01_pos a b hpos
        simp only [mul_zero, zero_add] at hrec
        linarith [hrec, hp]
      · exfalso
        have h1' : p1 % 2 ≠ 0 := by omega
        have hrec := phi_recursion_class1 a b p1 p2 h1' h2
        rw [hval0, hval1] at hrec
        have hp := phi_10_pos a b hpos
        simp only [mul_zero, zero_add] at hrec
        linarith [hrec, hp]
      · exfalso
        have h1' : p1 % 2 ≠ 0 := by omega
        have h2' : p2 % 2 ≠ 0 := by omega
        have hrec := phi_recursion_class3 a b p1 p2 h1' h2'
        rw [hval0, hval1] at hrec
        have hp := phi_31_pos a b hpos
        simp only [mul_zero, zero_add] at hrec
        linarith [hrec, hp]
    have hx12 : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx (Prod.ext hcon.1 hcon.2)
    rcases hx12 with h1 | h2
    · exact no_infinite_exact_halving (fun i => (mapPower sqrtTwoCollartzMap.apply i x).1)
        (fun i => (Prod.ext_iff.mp (hclass0 i)).1) (by simpa [mapPower] using h1)
    · exact no_infinite_exact_halving (fun i => (mapPower sqrtTwoCollartzMap.apply i x).2)
        (fun i => (Prod.ext_iff.mp (hclass0 i)).2) (by simpa [mapPower] using h2)
  · -- Φ is nonzero somewhere along the orbit, hence eventually strictly
    -- positive forever: but x is periodic, so Φ(x) would have to be
    -- positive too, contradicting Φ(x) = 0.
    push_neg at hallzero
    obtain ⟨j, hj⟩ := hallzero
    have hjpos : 0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply j x)) :=
      lt_of_le_of_ne (hnonneg j) (Ne.symm hj)
    have hperiodic : ∀ k, mapPower sqrtTwoCollartzMap.apply (n + k) x
        = mapPower sqrtTwoCollartzMap.apply k x := by
      intro k
      induction k with
      | zero => simpa using hcycle
      | succ m ih =>
          have h1 : n + (m + 1) = (n + m) + 1 := by ring
          rw [h1, mapPower_succ_apply' sqrtTwoCollartzMap.apply (n + m) x, ih,
            ← mapPower_succ_apply' sqrtTwoCollartzMap.apply m x]
    have hperiodicT : ∀ t, mapPower sqrtTwoCollartzMap.apply (n * t) x = x := by
      intro t
      induction t with
      | zero => rfl
      | succ m ih =>
          have h2 : n * (m + 1) = n + n * m := by ring
          rw [h2, hperiodic (n * m), ih]
    have hnj : j ≤ n * j := by nlinarith [hn]
    have hpos_at_nj : 0 < Phi a b (Point.embed (mapPower sqrtTwoCollartzMap.apply (n * j) x)) :=
      hstay j hjpos (n * j) hnj
    rw [hperiodicT j] at hpos_at_nj
    linarith [hpos_at_nj, hphi0]

end CollatzMultidimKionkeLemma1
