/-
# A 2-adic valuation on ℝ (the algebraic backbone of Monsky's theorem)

Monsky's theorem (a unit square cannot be dissected into an odd number of
triangles of equal area) rests on a non-trivial **2-adic valuation on `ℝ`**, used
to 3-colour the plane.  The existence of such a valuation is *not* elementary: it
relies on the general fact that a local subring of a field is dominated by a
valuation subring (the Chevalley/Zorn extension theorem), which mathlib provides
as `LocalSubring.exists_le_valuationSubring`.

This file builds a genuine `Valuation ℝ Γ` (`Γ` a `LinearOrderedCommGroupWithZero`)
which is **2-adic** on the integers:

* `exists_two_adic_valuation_on_real` — the minimal statement: there is a genuine
  valuation `ν` on `ℝ` with `ν 2 < 1` (so `2` is a non-unit; the valuation is
  non-trivial in the 2-adic direction).

* `exists_two_adic_valuation_on_real_strong` — the genuinely *2-adic* statement:
  there is a valuation `ν` on `ℝ` with `ν 2 < 1` **and** `ν n = 1` for every odd
  integer `n`.  The second clause (odd integers are units) is exactly what
  distinguishes the 2-adic valuation from a `p`-adic one for some other prime.

The construction never builds a valuation by hand.  For the strong theorem it
dominates the local ring `ℤ_(2)` (= `ℤ` localized at the prime `(2)`, realized
inside `ℝ` via `LocalSubring.ofPrime`) by a valuation subring `Bv` of `ℝ`, and
reads off `Bv.valuation`.  Because the domination is a *local* ring homomorphism,
the maximal ideal `(2)` of `ℤ_(2)` stays inside the maximal ideal of `Bv` (giving
`ν 2 < 1`), while the units of `ℤ_(2)` (the odd integers) stay units of `Bv`
(giving `ν n = 1`).
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Real.Basic

namespace MonskyTwoAdic

open scoped Classical

/-! ## The integer subring of `ℝ` -/

/-- The image of `ℤ` inside `ℝ`, as a subring.  It is (ring-)isomorphic to `ℤ`. -/
noncomputable def intSubring : Subring ℝ := (Int.castRingHom ℝ).range

@[simp] lemma mem_intSubring {x : ℝ} : x ∈ intSubring ↔ ∃ k : ℤ, (k : ℝ) = x := by
  simp [intSubring, RingHom.mem_range]

@[simp] lemma coe_two_intSubring : ((2 : intSubring) : ℝ) = 2 := by norm_cast

/-- `2` is **not** a unit of the integer subring of `ℝ` (its inverse `1/2` is not
an integer).  This is the input that makes the minimal valuation non-trivial. -/
lemma two_not_isUnit_intSubring : ¬ IsUnit (2 : intSubring) := by
  rintro ⟨u, hu⟩
  have hmulR : (((u : intSubring)) : ℝ) * (((↑u⁻¹ : intSubring)) : ℝ) = 1 := by
    have h := congrArg (fun a : intSubring => (a : ℝ)) u.mul_inv
    push_cast at h
    simpa using h
  rw [hu, coe_two_intSubring] at hmulR
  obtain ⟨k, hk⟩ := (mem_intSubring).1 ((↑u⁻¹ : intSubring)).2
  rw [← hk] at hmulR
  have hcast : ((2 * k : ℤ) : ℝ) = (1 : ℝ) := by push_cast; linarith [hmulR]
  have h2k : (2 * k : ℤ) = 1 := by exact_mod_cast hcast
  omega

/-! ## Minimal statement: a non-trivial valuation with `ν 2 < 1` -/

/--
**There is a non-trivial 2-adic valuation on `ℝ`.**

There exist a linearly ordered commutative group with zero `Γ` and a genuine
valuation `ν : ℝ → Γ` (satisfying all of mathlib's `Valuation` axioms) such that
`ν 2 < 1`, i.e. `2` is a non-unit.  This is the algebraic backbone of Monsky's
theorem.  The valuation is obtained by dominating the proper ideal `(2)` of the
integer subring of `ℝ` by a valuation subring of `ℝ`. -/
theorem exists_two_adic_valuation_on_real :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (ν : Valuation ℝ Γ),
      ν 2 < 1 := by
  set I : Ideal intSubring := Ideal.span {(2 : intSubring)} with hI_def
  have hI_ne_top : I ≠ ⊤ := by
    rw [hI_def, Ne, Ideal.span_singleton_eq_top]
    exact two_not_isUnit_intSubring
  obtain ⟨B, _hAB, hsub⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := intSubring) I hI_ne_top
  have h2_mem : (2 : ℝ) ∈ B.nonunits := by
    apply hsub
    refine ⟨(2 : intSubring), Ideal.mem_span_singleton_self _, ?_⟩
    simp
  refine ⟨B.ValueGroup, inferInstance, B.valuation, ?_⟩
  have := (B.mem_nonunits_iff).1 h2_mem
  simpa using this

/-! ## Strong statement: genuinely 2-adic (odd integers are units)

We realize `ℤ_(2)` inside `ℝ` and dominate it by a valuation subring `Bv`. -/

/-- A ring isomorphism `ℤ ≃+* intSubring` (the integer subring of `ℝ`). -/
noncomputable def e : ℤ ≃+* intSubring :=
  RingEquiv.ofBijective (Int.castRingHom ℝ).rangeRestrict
    ⟨fun a b h => by
        have h2 : (Int.castRingHom ℝ) a = (Int.castRingHom ℝ) b := congrArg Subtype.val h
        simpa using h2,
     (Int.castRingHom ℝ).rangeRestrict_surjective⟩

@[simp] lemma coe_e (k : ℤ) : ((e k : intSubring) : ℝ) = (k : ℝ) := rfl

lemma e_symm_e (k : ℤ) : (e.symm : intSubring →+* ℤ) (e k) = k := by simp

/-- The prime ideal of the integer subring of `ℝ` corresponding to `(2) ⊂ ℤ`. -/
noncomputable def P : Ideal intSubring :=
  Ideal.comap (e.symm : intSubring →+* ℤ) (Ideal.span {(2 : ℤ)})

instance : (P).IsPrime := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two
  exact Ideal.comap_isPrime _ _

lemma two_mem_P : (2 : intSubring) ∈ P := by
  have h2 : (2 : intSubring) = e 2 := by rw [map_ofNat]
  rw [h2, P, Ideal.mem_comap, e_symm_e, Ideal.mem_span_singleton]

/-- An odd integer is **not** in the prime `(2)`: it is a unit of `ℤ_(2)`. -/
lemma e_odd_notMem_P (n : ℤ) (hn : Odd n) : e n ∉ P := by
  rw [P, Ideal.mem_comap, e_symm_e, Ideal.mem_span_singleton]
  intro hdvd
  obtain ⟨m, hm⟩ := hn
  obtain ⟨j, hj⟩ := hdvd
  omega

/-- A valuation subring of `ℝ` dominating the local ring `ℤ_(2) = ofPrime intSubring P`. -/
noncomputable def Bv : ValuationSubring ℝ :=
  ((LocalSubring.ofPrime intSubring P).exists_le_valuationSubring).choose

lemma Bv_spec : (LocalSubring.ofPrime intSubring P) ≤ Bv.toLocalSubring :=
  ((LocalSubring.ofPrime intSubring P).exists_le_valuationSubring).choose_spec

/-- The underlying subring `ℤ_(2)` of `ℝ`. -/
@[reducible] noncomputable def Aloc : Subring ℝ :=
  (LocalSubring.ofPrime intSubring P).toSubring

lemma coe_algMap (x : intSubring) : ((algebraMap intSubring Aloc x : Aloc) : ℝ) = (x : ℝ) := rfl

lemma intSubring_le_Bv (x : intSubring) : (x : ℝ) ∈ Bv := by
  have h1 : (x : ℝ) ∈ Aloc := LocalSubring.le_ofPrime intSubring P x.2
  exact (Bv_spec.1) h1

/-- If `x` is a unit of `ℤ_(2)` (i.e. `x ∉ (2)`) then it is a unit of the
dominating valuation subring, so `Bv.valuation x = 1`. -/
lemma val_eq_one_of_notMem (x : intSubring) (hx : x ∉ P) :
    Bv.valuation (x : ℝ) = 1 := by
  have hunit_loc : IsUnit (algebraMap intSubring Aloc x) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Aloc P x).2 hx
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 hunit_loc
  have hbR : (x : ℝ) * ((b : Aloc) : ℝ) = 1 := by
    have := congrArg (fun t : Aloc => (t : ℝ)) hb
    simpa [coe_algMap] using this
  have hx0 : (x : ℝ) ≠ 0 := by
    rintro h0
    apply hx
    have hx00 : x = 0 := by apply Subtype.ext; simpa using h0
    simp [hx00]
  have hbinv : ((b : Aloc) : ℝ) = (x : ℝ)⁻¹ := by
    field_simp at hbR ⊢; linarith [hbR]
  have hx_mem : (x : ℝ) ∈ Bv := intSubring_le_Bv x
  have hinv_mem : (x : ℝ)⁻¹ ∈ Bv := by
    have hbmem : ((b : Aloc) : ℝ) ∈ Bv := Bv_spec.1 b.2
    rwa [hbinv] at hbmem
  have hle1 : Bv.valuation (x : ℝ) ≤ 1 := (Bv.valuation_le_one_iff _).2 hx_mem
  have hle2 : (Bv.valuation (x : ℝ))⁻¹ ≤ 1 := by
    have := (Bv.valuation_le_one_iff _).2 hinv_mem
    rwa [map_inv₀] at this
  have hv0 : Bv.valuation (x : ℝ) ≠ 0 := by
    simpa [Valuation.zero_iff] using hx0
  have h1le : (1 : Bv.ValueGroup) ≤ Bv.valuation (x : ℝ) :=
    (inv_le_one₀ (zero_lt_iff.mpr hv0)).1 hle2
  exact le_antisymm hle1 h1le

/-- If `x` lies in the prime `(2)` (and is nonzero) then `x` is a non-unit of the
dominating valuation subring, so `Bv.valuation x < 1`. -/
lemma val_lt_one_of_mem (x : intSubring) (hx : x ∈ P) (hx0 : (x : ℝ) ≠ 0) :
    Bv.valuation (x : ℝ) < 1 := by
  obtain ⟨hsub, hlocal⟩ := Bv_spec
  haveI : IsLocalHom (Subring.inclusion hsub) := hlocal
  rw [← Bv.mem_nonunits_iff, Bv.mem_nonunits_iff_or]
  right
  intro hw
  have hxmem : (x : ℝ) ∈ Bv := intSubring_le_Bv x
  have hmul : (⟨(x : ℝ), hxmem⟩ : Bv.toSubring) * ⟨(x : ℝ)⁻¹, hw⟩ = 1 := by
    apply Subtype.ext
    push_cast
    field_simp
  have hxunit_B : IsUnit (⟨(x : ℝ), hxmem⟩ : Bv.toSubring) := IsUnit.of_mul_eq_one _ hmul
  have hid : (⟨(x : ℝ), hxmem⟩ : Bv.toSubring)
      = Subring.inclusion hsub (algebraMap intSubring Aloc x) := by
    apply Subtype.ext
    simp [coe_algMap]
  rw [hid] at hxunit_B
  have hxunit_loc : IsUnit (algebraMap intSubring Aloc x) :=
    IsUnit.of_map (Subring.inclusion hsub) _ hxunit_B
  have hcompl : x ∈ P.primeCompl :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Aloc P x).1 hxunit_loc
  exact hcompl hx

/--
**There is a genuinely 2-adic valuation on `ℝ`.**

There exist a linearly ordered commutative group with zero `Γ` and a genuine
valuation `ν : ℝ → Γ` such that

* `ν 2 < 1` (the prime `2` is a non-unit), and
* `ν n = 1` for every **odd** integer `n` (odd integers are units).

The second clause makes the valuation honestly *2-adic*: it agrees with the
2-adic valuation on units of `ℤ_(2)`, ruling out any other prime.  This is the
backbone used in Monsky's 3-colouring of the plane. -/
theorem exists_two_adic_valuation_on_real_strong :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (ν : Valuation ℝ Γ),
      ν 2 < 1 ∧ ∀ n : ℤ, Odd n → ν (n : ℝ) = 1 := by
  refine ⟨Bv.ValueGroup, inferInstance, Bv.valuation, ?_, ?_⟩
  · have h := val_lt_one_of_mem (2 : intSubring) two_mem_P (by simp)
    simpa using h
  · intro n hn
    have h := val_eq_one_of_notMem (e n) (e_odd_notMem_P n hn)
    simpa using h

end MonskyTwoAdic
