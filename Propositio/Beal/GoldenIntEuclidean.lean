import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic

/-!
# `ℤ[φ]` as its own type, and its `EuclideanDomain` structure

This file formalizes the ring of integers `ℤ[φ] = 𝓞(ℚ(√5))` of the real quadratic field
`ℚ(√5)` (`φ = (1+√5)/2` the golden ratio, `φ² = φ + 1`) as a standalone Lean structure
`GoldenInt`, and proves the classical fact that it is a **Euclidean domain** with respect
to the (absolute value of the) field norm `N(a + b·φ) = a² + ab - b²`.

This is the concrete-`ℤ`-coordinate analogue of mathlib's `Zsqrtd` (`Mathlib.NumberTheory.
Zsqrtd.Basic`), adapted to `ℤ[φ]` rather than `ℤ[√d]` — `φ ∉ ℤ[√5]` (the minimal order), so
`Zsqrtd 5` is *not* this ring (it is an index-2 subring), and we build the multiplication
table directly from `φ² = φ + 1` rather than from `√d² = d`.

`BealFundamentalUnitPell.lean` and `FermatLastTheoremFiveCaseTwoNorm.lean` already work with
the concrete real-number model `a + b·φ ∈ ℝ` (via `Real.goldenRatio`/`Real.goldenConj`) and its
norm form `norm_form_identity : (a+bφ)(a+bψ) = a²+ab-b²`, but have **no ring-theoretic
structure** (no `Dvd`/`GCD`/`EuclideanDomain` instance) for the *type* `ℤ[φ]` itself — this
file supplies exactly that missing piece. We reuse the conventions of those files (same norm
form, same `(a,b) ↦ a+b·φ` embedding) but do not import them, to keep this file self-contained;
every real-number fact we need (`goldenRatio_sq`, `goldenRatio_irrational`, etc.) is re-derived
directly from `Mathlib.NumberTheory.Real.GoldenRatio`.

## Main results (proved, axiom-clean, no `sorry`)

* `GoldenInt` — the structure `⟨a, b⟩` representing `a + b·φ`, with `Add`/`Neg`/`Sub`/`Mul`/
  `Zero`/`One` instances matching `φ² = φ + 1`.
* `instCommRing : CommRing GoldenInt` — full commutative ring structure (built by the same
  `ext <;> ring` recipe `Zsqrtd.commRing` uses).
* `norm` — the field norm `N(a+bφ) = a²+ab-b²`, and:
  - `norm_mul : norm (x * y) = norm x * norm y` (multiplicativity, pure `ring`).
  - `norm_conj : norm (conj z) = norm z`.
  - `mul_conj_eq_ofInt : z * conj z = ofInt (norm z)` — the key ring identity that lets the
    norm do Euclidean division.
  - `norm_eq_zero_iff : norm z = 0 ↔ z = 0` (uses `Real.goldenRatio_irrational` /
    `Real.goldenConj_irrational` from mathlib).
* `exists_int_approx` — the classical real-analysis lemma behind "`ℤ[φ]` is norm-Euclidean":
  for any reals `p q`, there are integers `m n` with `|N(p-m, q-n)| ≤ 5/16 < 1`.
* `exists_div_smaller_remainder` — **the hard mathematical core**: for `α β : GoldenInt` with
  `β ≠ 0`, there exist `γ ρ` with `α = β * γ + ρ` and `(norm ρ).natAbs < (norm β).natAbs`.
* `instEuclideanDomain : EuclideanDomain GoldenInt` — the full mathlib typeclass, built from
  `exists_div_smaller_remainder` via classical choice.

No `sorry`, no project `axiom` anywhere in this file.
-/

open Real
open scoped goldenRatio

noncomputable section

/-- `GoldenInt` represents an element `a + b·φ` of `ℤ[φ] = 𝓞(ℚ(√5))`, with `φ = (1+√5)/2`
the golden ratio (`φ² = φ + 1`). Compare `Zsqrtd d` (`a + b·√d`) — this is genuinely a
different ring: `φ ∉ ℤ[√5] = Zsqrtd 5` (the golden ratio is not in the minimal quadratic
order; `ℤ[φ]` is its index-2 overring, the actual ring of integers of `ℚ(√5)`). -/
@[ext]
structure GoldenInt where
  /-- The rational-integer part (coefficient of `1`). -/
  a : ℤ
  /-- The coefficient of `φ`. -/
  b : ℤ
  deriving DecidableEq

namespace GoldenInt

/-- The embedding of `ℤ` into `ℤ[φ]` as `n ↦ n + 0·φ`. -/
def ofInt (n : ℤ) : GoldenInt := ⟨n, 0⟩

@[simp] theorem a_ofInt (n : ℤ) : (ofInt n).a = n := rfl
@[simp] theorem b_ofInt (n : ℤ) : (ofInt n).b = 0 := rfl

instance : Zero GoldenInt := ⟨ofInt 0⟩
instance : One GoldenInt := ⟨ofInt 1⟩
instance : Inhabited GoldenInt := ⟨0⟩

@[simp] theorem a_zero : (0 : GoldenInt).a = 0 := rfl
@[simp] theorem b_zero : (0 : GoldenInt).b = 0 := rfl
@[simp] theorem a_one : (1 : GoldenInt).a = 1 := rfl
@[simp] theorem b_one : (1 : GoldenInt).b = 0 := rfl

instance : Add GoldenInt := ⟨fun z w => ⟨z.a + w.a, z.b + w.b⟩⟩

@[simp] theorem add_def (x y x' y' : ℤ) : (⟨x, y⟩ + ⟨x', y'⟩ : GoldenInt) = ⟨x + x', y + y'⟩ := rfl
@[simp] theorem a_add (z w : GoldenInt) : (z + w).a = z.a + w.a := rfl
@[simp] theorem b_add (z w : GoldenInt) : (z + w).b = z.b + w.b := rfl

instance : Neg GoldenInt := ⟨fun z => ⟨-z.a, -z.b⟩⟩

@[simp] theorem a_neg (z : GoldenInt) : (-z).a = -z.a := rfl
@[simp] theorem b_neg (z : GoldenInt) : (-z).b = -z.b := rfl

/-- Multiplication matching `φ² = φ + 1`:
`(a+bφ)(a'+b'φ) = aa' + (ab'+a'b)φ + bb'φ² = (aa'+bb') + (ab'+a'b+bb')φ`. -/
instance : Mul GoldenInt := ⟨fun z w => ⟨z.a * w.a + z.b * w.b, z.a * w.b + w.a * z.b + z.b * w.b⟩⟩

@[simp] theorem a_mul (z w : GoldenInt) : (z * w).a = z.a * w.a + z.b * w.b := rfl
@[simp] theorem b_mul (z w : GoldenInt) : (z * w).b = z.a * w.b + w.a * z.b + z.b * w.b := rfl

instance instAddCommGroup : AddCommGroup GoldenInt := by
  refine
  { add := (· + ·)
    zero := 0
    neg := Neg.neg
    sub := fun a b => a + -b
    nsmul := @nsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec GoldenInt ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

@[simp] theorem a_sub (z w : GoldenInt) : (z - w).a = z.a - w.a := by
  show (z + -w).a = z.a - w.a; simp [sub_eq_add_neg]
@[simp] theorem b_sub (z w : GoldenInt) : (z - w).b = z.b - w.b := by
  show (z + -w).b = z.b - w.b; simp [sub_eq_add_neg]

instance instAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { instAddCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

instance instCommRing : CommRing GoldenInt := by
  refine
  { instAddGroupWithOne with
    mul := (· * ·)
    npow := @npowRec GoldenInt ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

instance : Nontrivial GoldenInt := ⟨(1 : GoldenInt), 0, by
  intro h
  have h1 : (1 : GoldenInt).a = (0 : GoldenInt).a := by rw [h]
  simp at h1⟩

/-! ## The Galois conjugate (`φ ↦ ψ = 1 - φ`) -/

/-- The conjugate `a + bφ ↦ a + bψ = (a+b) - b·φ` (using `ψ = 1 - φ`). -/
def conj (z : GoldenInt) : GoldenInt := ⟨z.a + z.b, -z.b⟩

@[simp] theorem a_conj (z : GoldenInt) : (conj z).a = z.a + z.b := rfl
@[simp] theorem b_conj (z : GoldenInt) : (conj z).b = -z.b := rfl

@[simp] theorem conj_conj (z : GoldenInt) : conj (conj z) = z := by ext <;> simp [conj]

theorem conj_add (z w : GoldenInt) : conj (z + w) = conj z + conj w := by
  ext <;> simp [conj] <;> ring

theorem conj_mul (z w : GoldenInt) : conj (z * w) = conj z * conj w := by
  ext <;> simp [conj] <;> ring

/-! ## The field norm `N(a+bφ) = a² + ab - b²` -/

/-- The field norm `N(a + b·φ) = a² + ab - b²`. -/
def norm (z : GoldenInt) : ℤ := z.a ^ 2 + z.a * z.b - z.b ^ 2

@[simp] theorem norm_zero : norm (0 : GoldenInt) = 0 := by simp [norm]
@[simp] theorem norm_one : norm (1 : GoldenInt) = 1 := by simp [norm]

/-- **Multiplicativity of the norm.** Pure polynomial identity — the classical fact that
the norm form of a quadratic ring is multiplicative. -/
theorem norm_mul (z w : GoldenInt) : norm (z * w) = norm z * norm w := by
  simp only [norm, a_mul, b_mul]; ring

/-- The norm is invariant under conjugation. -/
theorem norm_conj (z : GoldenInt) : norm (conj z) = norm z := by
  simp only [norm, a_conj, b_conj]; ring

/-- **Key ring identity.** `z * conj z = ofInt (norm z)` — literally, not just up to
embedding into `ℝ`. This is what lets the norm drive Euclidean division. -/
theorem mul_conj_eq_ofInt (z : GoldenInt) : z * conj z = ofInt (norm z) := by
  ext <;> simp [norm, conj] <;> ring

/-! ## The real embedding, and irrationality-based facts about the norm -/

/-- The embedding `a + b·φ ∈ ℤ[φ] ↦ a + b·φ ∈ ℝ`. -/
def toReal (z : GoldenInt) : ℝ := (z.a : ℝ) + (z.b : ℝ) * φ

theorem toReal_mul (z w : GoldenInt) : toReal (z * w) = toReal z * toReal w := by
  simp only [toReal, a_mul, b_mul]
  have hsq : φ ^ 2 = φ + 1 := goldenRatio_sq
  push_cast
  generalize hx : φ = x at hsq ⊢
  linear_combination (-(z.b : ℝ) * (w.b : ℝ)) * hsq

theorem toReal_conj (z : GoldenInt) : toReal (conj z) = (z.a : ℝ) + (z.b : ℝ) * ψ := by
  have hsum : φ + ψ = 1 := goldenRatio_add_goldenConj
  simp only [toReal, a_conj, b_conj]
  push_cast
  linear_combination (z.b : ℝ) * hsum

/-- `a + b·φ = 0` (with `a b : ℤ`) forces `a = b = 0`: if `b ≠ 0` this would exhibit `φ` as
a rational number, contradicting `Real.goldenRatio_irrational`. -/
theorem eq_zero_of_toReal_eq_zero (a b : ℤ) (h : (a : ℝ) + (b : ℝ) * φ = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hφeq : φ = -(a : ℝ) / (b : ℝ) := by
      rw [eq_div_iff hbR]
      linear_combination h
    have hφ : φ = ((-(a : ℚ) / (b : ℚ) : ℚ) : ℝ) := by rw [hφeq]; push_cast; ring
    exact goldenRatio_irrational ⟨_, hφ.symm⟩

/-- Same as `eq_zero_of_toReal_eq_zero`, for the conjugate `ψ`. -/
theorem eq_zero_of_toReal_conj_eq_zero (a b : ℤ) (h : (a : ℝ) + (b : ℝ) * ψ = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hψeq : ψ = -(a : ℝ) / (b : ℝ) := by
      rw [eq_div_iff hbR]
      linear_combination h
    have hψ : ψ = ((-(a : ℚ) / (b : ℚ) : ℚ) : ℝ) := by rw [hψeq]; push_cast; ring
    exact goldenConj_irrational ⟨_, hψ.symm⟩

theorem toReal_eq_zero_iff (z : GoldenInt) : toReal z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := eq_zero_of_toReal_eq_zero z.a z.b h
    ext <;> simp [ha, hb]
  · intro h; subst h; simp [toReal]

/-- **`norm z = 0 ↔ z = 0`.** The nontrivial direction uses irrationality of `φ`/`ψ`. -/
theorem norm_eq_zero_iff (z : GoldenInt) : norm z = 0 ↔ z = 0 := by
  constructor
  · intro hN
    have hprod : toReal z * toReal (conj z) = 0 := by
      have heq := mul_conj_eq_ofInt z
      have hcast : toReal (z * conj z) = toReal (ofInt (norm z)) := by rw [heq]
      rw [toReal_mul] at hcast
      simpa [hN, toReal, ofInt] using hcast
    rcases mul_eq_zero.mp hprod with h | h
    · exact (toReal_eq_zero_iff z).mp h
    · rw [toReal_conj] at h
      obtain ⟨ha, hb⟩ := eq_zero_of_toReal_conj_eq_zero z.a z.b h
      ext <;> simp [ha, hb]
  · intro h; subst h; simp

theorem norm_ne_zero_of_ne_zero {z : GoldenInt} (hz : z ≠ 0) : norm z ≠ 0 := by
  intro h; exact hz ((norm_eq_zero_iff z).mp h)

/-! ## The rounding lemma: `ℤ[φ]` is norm-Euclidean -/

/-- **The classical rounding lemma behind "`ℤ[φ]` is norm-Euclidean".** For any real `p, q`,
there are integers `m, n` such that the norm form `N(p - m, q - n) = (p-m)^2+(p-m)(q-n)-(q-n)^2`
has absolute value at most `5/16 < 1`. Proof: round `q` to `n`, set `t = q - n` (`|t| ≤ 1/2`),
then round `p + t/2` to `m`, set `s = p - m` (so `|s + t/2| ≤ 1/2`). Then
`N(s,t) = s²+st-t² = (s+t/2)² - (5/4)t² ∈ [-5/16, 1/4]`. -/
theorem exists_int_approx (p q : ℝ) :
    ∃ m n : ℤ,
      |((p - (m : ℝ)) ^ 2 + (p - (m : ℝ)) * (q - (n : ℝ)) - (q - (n : ℝ)) ^ 2)| ≤ 5 / 16 := by
  set n : ℤ := round q with hn_def
  set t : ℝ := q - (n : ℝ) with ht_def
  have ht : |t| ≤ 1 / 2 := abs_sub_round q
  set m : ℤ := round (p + t / 2) with hm_def
  set s : ℝ := p - (m : ℝ) with hs_def
  have hst : |s + t / 2| ≤ 1 / 2 := by
    have hr := abs_sub_round (p + t / 2)
    have heq : s + t / 2 = (p + t / 2) - (m : ℝ) := by rw [hs_def]; ring
    rw [heq]; exact hr
  refine ⟨m, n, ?_⟩
  have hst' := abs_le.mp hst
  have ht' := abs_le.mp ht
  have h1 : (s + t / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := sq_le_sq' hst'.1 hst'.2
  have h2 : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := sq_le_sq' ht'.1 ht'.2
  have hnorm_eq : s ^ 2 + s * t - t ^ 2 = (s + t / 2) ^ 2 - (5 / 4) * t ^ 2 := by ring
  show |s ^ 2 + s * t - t ^ 2| ≤ 5 / 16
  rw [hnorm_eq, abs_le]
  constructor <;> nlinarith [h1, h2]

/-! ## The hard mathematical core: division with strictly smaller remainder -/

/-- **`ℤ[φ]` is norm-Euclidean.** For `α β : GoldenInt` with `β ≠ 0`, there exist `γ ρ` with
`α = β * γ + ρ` and `(norm ρ).natAbs < (norm β).natAbs`. This is the classical fact (going
back to the Fibonacci/golden-ratio continued fraction) that the ring of integers of `ℚ(√5)`
is Euclidean with respect to (the absolute value of) its field norm. -/
theorem exists_div_smaller_remainder (α β : GoldenInt) (hβ : β ≠ 0) :
    ∃ γ ρ : GoldenInt, α = β * γ + ρ ∧ (norm ρ).natAbs < (norm β).natAbs := by
  set Nβ : ℤ := norm β with hNβ_def
  have hNβ_ne : Nβ ≠ 0 := norm_ne_zero_of_ne_zero hβ
  have hNβR_ne : (Nβ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hNβ_ne
  set c : GoldenInt := α * conj β with hc_def
  set p : ℝ := (c.a : ℝ) / (Nβ : ℝ) with hp_def
  set q : ℝ := (c.b : ℝ) / (Nβ : ℝ) with hq_def
  obtain ⟨m, n, hmn⟩ := exists_int_approx p q
  set γ : GoldenInt := ⟨m, n⟩ with hγ_def
  set ρ : GoldenInt := α - β * γ with hρ_def
  refine ⟨γ, ρ, by rw [hρ_def]; ring, ?_⟩
  set δ : GoldenInt := c - (ofInt Nβ) * γ with hδ_def
  have hργ : ρ * conj β = δ := by
    have hβconj : β * conj β = ofInt Nβ := mul_conj_eq_ofInt β
    have hexpand : (α - β * γ) * conj β = α * conj β - γ * (β * conj β) := by ring
    rw [hδ_def, hρ_def, hc_def, hexpand, hβconj]
    ring
  have hnormρ : norm ρ * Nβ = norm δ := by
    have hm2 := norm_mul ρ (conj β)
    rw [hργ] at hm2
    rw [hm2, norm_conj]
  have hδa : δ.a = c.a - Nβ * m := by simp [hδ_def, ofInt, γ]
  have hδb : δ.b = c.b - Nβ * n := by simp [hδ_def, ofInt, γ]
  have hcast : (norm δ : ℝ) =
      (Nβ : ℝ) ^ 2 * ((p - (m : ℝ)) ^ 2 + (p - (m : ℝ)) * (q - (n : ℝ)) - (q - (n : ℝ)) ^ 2) := by
    have haR : (δ.a : ℝ) = (Nβ : ℝ) * (p - (m : ℝ)) := by
      rw [hδa]; push_cast; rw [hp_def]; field_simp
    have hbR : (δ.b : ℝ) = (Nβ : ℝ) * (q - (n : ℝ)) := by
      rw [hδb]; push_cast; rw [hq_def]; field_simp
    show ((δ.a ^ 2 + δ.a * δ.b - δ.b ^ 2 : ℤ) : ℝ) = _
    push_cast
    rw [haR, hbR]; ring
  have hXbound := abs_le.mp hmn
  have hNβsq_nonneg : (0 : ℝ) ≤ (Nβ : ℝ) ^ 2 := sq_nonneg _
  have hupper : (norm δ : ℝ) ≤ (Nβ : ℝ) ^ 2 * (5 / 16) := by
    rw [hcast]; exact mul_le_mul_of_nonneg_left hXbound.2 hNβsq_nonneg
  have hlower : -((Nβ : ℝ) ^ 2 * (5 / 16)) ≤ (norm δ : ℝ) := by
    rw [hcast]
    have hh := mul_le_mul_of_nonneg_left hXbound.1 hNβsq_nonneg
    nlinarith [hh]
  have hupperZ : 16 * norm δ ≤ 5 * Nβ ^ 2 := by
    have hR : (16 : ℝ) * (norm δ : ℝ) ≤ 5 * (Nβ : ℝ) ^ 2 := by nlinarith [hupper]
    exact_mod_cast hR
  have hlowerZ : -(5 * Nβ ^ 2) ≤ 16 * norm δ := by
    have hR : -(5 * (Nβ : ℝ) ^ 2) ≤ 16 * (norm δ : ℝ) := by nlinarith [hlower]
    exact_mod_cast hR
  have h16abs : |16 * norm δ| ≤ 5 * Nβ ^ 2 := abs_le.mpr ⟨hlowerZ, hupperZ⟩
  have h16abs' : 16 * |norm δ| ≤ 5 * Nβ ^ 2 := by
    rwa [abs_mul, show |(16 : ℤ)| = 16 from by norm_num] at h16abs
  have hNβ_pos : 0 < |Nβ| := abs_pos.mpr hNβ_ne
  have hNβsq_eq : Nβ ^ 2 = |Nβ| * |Nβ| := by rw [← sq_abs]; ring
  have habs_eq : |norm ρ| * |Nβ| = |norm δ| := by rw [← abs_mul, hnormρ]
  have hcombined : 16 * (|norm ρ| * |Nβ|) ≤ 5 * (|Nβ| * |Nβ|) := by
    calc 16 * (|norm ρ| * |Nβ|) = 16 * |norm δ| := by rw [habs_eq]
      _ ≤ 5 * Nβ ^ 2 := h16abs'
      _ = 5 * (|Nβ| * |Nβ|) := by rw [hNβsq_eq]
  have hstep : 16 * (|norm ρ| * |Nβ|) < 16 * (|Nβ| * |Nβ|) := by nlinarith [hcombined, hNβ_pos]
  have hfin : |norm ρ| < |Nβ| := by
    by_contra hcon
    push_neg at hcon
    have hm3 : |Nβ| * |Nβ| ≤ |norm ρ| * |Nβ| := mul_le_mul_of_nonneg_right hcon (le_of_lt hNβ_pos)
    nlinarith [hstep, hm3]
  have hcast1 : |norm ρ| = ((norm ρ).natAbs : ℤ) := Int.abs_eq_natAbs (norm ρ)
  have hcast2 : |Nβ| = (Nβ.natAbs : ℤ) := Int.abs_eq_natAbs Nβ
  rw [hcast1, hcast2] at hfin
  exact_mod_cast hfin

/-! ## The `EuclideanDomain` instance -/

/-- The Euclidean division `quotient` function (defined by classical choice out of
`exists_div_smaller_remainder`). -/
noncomputable def quotient (a b : GoldenInt) : GoldenInt :=
  if h : b = 0 then 0 else (exists_div_smaller_remainder a b h).choose

/-- The Euclidean division `remainder` function. -/
noncomputable def remainder (a b : GoldenInt) : GoldenInt :=
  if h : b = 0 then a else (exists_div_smaller_remainder a b h).choose_spec.choose

theorem quotient_zero (a : GoldenInt) : quotient a 0 = 0 := by simp [quotient]

theorem div_spec (a b : GoldenInt) (h : b ≠ 0) :
    a = b * quotient a b + remainder a b ∧
      (norm (remainder a b)).natAbs < (norm b).natAbs := by
  unfold quotient remainder
  rw [dif_neg h, dif_neg h]
  exact (exists_div_smaller_remainder a b h).choose_spec.choose_spec

theorem quotient_mul_add_remainder_eq (a b : GoldenInt) :
    b * quotient a b + remainder a b = a := by
  by_cases h : b = 0
  · subst h; simp [quotient, remainder]
  · exact (div_spec a b h).1.symm

/-- The well-founded "smaller norm" relation driving the Euclidean algorithm. -/
def r (x y : GoldenInt) : Prop := (norm x).natAbs < (norm y).natAbs

theorem r_wellFounded : WellFounded r := by
  have : r = InvImage (· < · : ℕ → ℕ → Prop) (fun x => (norm x).natAbs) := rfl
  rw [this]
  exact InvImage.wf _ Nat.lt_wfRel.wf

theorem remainder_lt (a : GoldenInt) {b : GoldenInt} (hb : b ≠ 0) : r (remainder a b) b :=
  (div_spec a b hb).2

theorem mul_left_not_lt (a : GoldenInt) {b : GoldenInt} (hb : b ≠ 0) : ¬ r (a * b) a := by
  have hNb_ne : norm b ≠ 0 := norm_ne_zero_of_ne_zero hb
  have hNb_pos : 1 ≤ (norm b).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hNb_ne)
  have heq : (norm (a * b)).natAbs = (norm a).natAbs * (norm b).natAbs := by
    rw [norm_mul, Int.natAbs_mul]
  show ¬ (norm (a * b)).natAbs < (norm a).natAbs
  rw [heq]
  intro hcon
  nlinarith [Nat.mul_le_mul_left (norm a).natAbs hNb_pos]

noncomputable instance instEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := quotient
  quotient_zero := quotient_zero
  remainder := remainder
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq
  r := r
  r_wellFounded := r_wellFounded
  remainder_lt := remainder_lt
  mul_left_not_lt := mul_left_not_lt

end GoldenInt

end
