import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic
import Propositio.Beal.KummerLambda4Congruence
import Propositio.Beal.LambdaNormBridge

/-!
# The full λ⁴ Kummer characterization for `ℚ(ζ₅)`: `φⁿ ≡ 3ⁿ (mod λ⁴) ↔ 5 ∣ n`

This file **composes** the two results that were deliberately left uncomposed:

* `BealKummerLambda4Congruence` works in a bare `CommRing`/`IsDomain` abstraction (no norm
  structure) and supplies the *structural* reduction
  `golden_pow_cong_lambda4_iff_coeff` (ring identity, both directions of the ⟺ hold at the
  bare `CommRing` level, splitting the congruence into a single λ²-coefficient condition) and
  the finite obstruction `obstruction_zmod5`.
* `BealLambdaNormBridge` works in a genuine number field `L` (a 5th cyclotomic extension of
  `ℚ`) and supplies the norm bridge `five_dvd_of_lambda_sq_dvd : λ² ∣ m ⟹ 5 ∣ m` for a
  rational integer `m`, using `N(λ) = 5`.

Composing them yields the genuinely full characterization

  **`(∃ c : L, IsIntegral ℤ c ∧ φⁿ − 3ⁿ = λ⁴·c) ↔ 5 ∣ n`.**

## Why the `IsIntegral ℤ c` conjunct is essential (not cosmetic)

`L` is a *field*.  In a field, "`∃ c : L, y = d·c`" for any fixed `d ≠ 0` is **vacuously
true** for every `y` (take `c = y / d`).  So the bare existential `∃ c : L, φⁿ − 3ⁿ = λ⁴·c`
(with `c` ranging freely over the field, no integrality constraint) holds for *every* `n`,
and an iff against `5 ∣ n` would be simply **false**.  The mathematically meaningful
statement — "`φⁿ ≡ 3ⁿ` modulo `λ⁴` *in the ring of integers* `𝓞(ℚ(ζ₅))`" — requires `c` to be
an algebraic integer.  This is exactly the same distinction the two source files already
flag: `BealLambdaCongruence` notes "The proofs ... produce witnesses `c : K`. For the
meaningful Kummer application we need witnesses `c : 𝓞 K` ... so that divisibility is a
statement in the integer ring, not vacuous in the field" and `BealLambdaNormBridge`'s
`five_dvd_of_lambda_sq_dvd` explicitly carries `(hc : IsIntegral ℤ c)` as a hypothesis for
the same reason. We package the integrality *inside* the existential (`∃ c, IsIntegral ℤ c ∧
...`) rather than switching the ambient type to `𝓞(L)`/`NumberField.RingOfIntegers L`, since
`IsCyclotomicExtension {5} ℚ L` alone does not automatically furnish that typeclass
machinery, and the ⟺'s content is unaffected by this packaging choice.

## Proof strategy

*Bookkeeping device*: everywhere a witness `c` needs to be *produced* and shown integral, we
run the bare-`CommRing` lemmas from `BealKummerLambda4Congruence`/`BealLambdaCongruence` not
at `R = L` (which would only give a field-valued, non-integral witness) but at
`R = ↥(integralClosure ℤ L)`, the integral closure of `ℤ` in `L`. This is itself a
`CommRing` `IsDomain` (subalgebra of a domain, `Subalgebra.isDomain`), so every lemma proved
generically for `[CommRing R] [IsDomain R]` applies verbatim with `η` set to the
integral-closure lift of `ζ` (`ζ` is a root of unity, hence integral over `ℤ`,
`IsPrimitiveRoot.isIntegral`). Every witness produced this way is *automatically* an element
of `↥(integralClosure ℤ L)`, i.e. integral over `ℤ` by construction — no ad hoc tracking of
the recursive definition of the witness is needed. We then push the resulting identity down
to `L` along the inclusion `AlgHom` `(integralClosure ℤ L).val`, using the generic
`RingHomClass`/`AlgHomClass` pushforward lemmas (`map_add`, `map_sub`, `map_mul`, `map_pow`,
`map_one`, `map_ofNat`) — since these are registered for *any* ring-hom-like map, this avoids
hunting down `Subalgebra`-specific (and merely `protected`) coercion lemmas one at a time.

* `⟸` (`5 ∣ n → ...`): apply `BealKummerLambda4Congruence.golden_pow_cong_lambda4_of_five_dvd`
  at `R = ↥(integralClosure ℤ L)`, then push the produced identity to `L`.

* `⟹` (the hard direction): from the hypothesis `∃ c, IsIntegral ℤ c ∧ φⁿ − 3ⁿ = λ⁴·c`,
  obtain an *integral* comparison witness `d₀ : ↥(integralClosure ℤ L)` for the exact
  expansion `φⁿ − 3ⁿ = λ²·(n·3ⁿ⁻¹·ζ⁴) + λ⁴·d₀` (`BealLambdaCongruence.phi_pow_mod_lambda4_ring`
  at `R = ↥(integralClosure ℤ L)`, pushed to `L`). Subtracting from the hypothesis gives
  `λ²·(n·3ⁿ⁻¹·ζ⁴) = λ⁴·c'` with `c' := c − d₀` **integral** (`IsIntegral.sub`). Since `L` is a
  field and `λ = 1 − ζ ≠ 0` (as `ζ ≠ 1`), cancel one copy of `λ²` (`mul_left_cancel₀`) to get
  `n·3ⁿ⁻¹·ζ⁴ = λ²·c'`. Multiply both sides by `ζ` (using `ζ⁵ = 1`, i.e. `ζ·ζ⁴ = 1`) to absorb
  the unit `ζ⁴` into the witness: `n·3ⁿ⁻¹ = λ²·(ζ·c')`, with `ζ·c'` integral
  (`IsIntegral.mul`). This is *exactly* the hypothesis shape of
  `BealLambdaNormBridge.five_dvd_of_lambda_sq_dvd` (after matching `n·3ⁿ⁻¹ : L`, a rational
  integer cast, to `algebraMap ℚ L ((n * 3 ^ (n - 1) : ℤ) : ℚ)`), giving
  `5 ∣ (n * 3 ^ (n - 1) : ℤ)`. Finally, since `Nat.Coprime 5 3` and hence
  `Nat.Coprime 5 (3 ^ (n - 1))`, `5 ∣ n * 3 ^ (n - 1) → 5 ∣ n`
  (`Nat.Coprime.dvd_of_dvd_mul_right`).

All results below are axiom-clean: `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`.
-/

namespace BealLambda4FullCharacterization

variable {L : Type*} [Field L] [Algebra ℚ L] [IsCyclotomicExtension {5} ℚ L]

/-! ## 0. The integral-closure lift of `ζ`, and its basic facts -/

/-- `ζ` lifted to the integral closure of `ℤ` in `L`: a genuine ring element with
`IsIntegral ℤ ζ` bundled in, so the `CommRing`/`IsDomain`-level lemmas of
`BealKummerLambda4Congruence`/`BealLambdaCongruence` can be run at
`R = ↥(integralClosure ℤ L)` and every produced witness is automatically integral. -/
noncomputable def etaLift {ζ : L} (hζ : IsPrimitiveRoot ζ 5) : ↥(integralClosure ℤ L) :=
  ⟨ζ, hζ.isIntegral (by norm_num)⟩

theorem etaLift_coe {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    ((etaLift hζ : ↥(integralClosure ℤ L)) : L) = ζ := rfl

theorem etaLift_pow_five {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    (etaLift hζ : ↥(integralClosure ℤ L)) ^ 5 = 1 := by
  apply Subtype.ext
  have h := congrArg ((integralClosure ℤ L).val) (rfl : etaLift hζ ^ 5 = etaLift hζ ^ 5)
  simp only [Subalgebra.val_apply, map_pow] at h
  simpa [etaLift, hζ.pow_eq_one] using h

theorem etaLift_ne_one {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    (etaLift hζ : ↥(integralClosure ℤ L)) ≠ 1 := by
  intro h
  apply hζ.ne_one (by norm_num)
  have := congrArg ((integralClosure ℤ L).val) h
  simpa [etaLift] using this

/-! ## 1. The ⟸ direction: `5 ∣ n → ∃ c, IsIntegral ℤ c ∧ φⁿ − 3ⁿ = λ⁴·c` -/

theorem golden_pow_cong_lambda4_of_five_dvd_integral {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (hdvd : 5 ∣ n) :
    ∃ c : L, IsIntegral ℤ c ∧
      (1 + ζ + ζ ^ 4) ^ n - (3 : L) ^ n = (1 - ζ) ^ 4 * c := by
  obtain ⟨d, hd⟩ := BealKummerLambda4Congruence.golden_pow_cong_lambda4_of_five_dvd
    (etaLift_pow_five hζ) (etaLift_ne_one hζ) n hdvd
  refine ⟨(d : L), d.2, ?_⟩
  have h := congrArg ((integralClosure ℤ L).val) hd
  simp only [Subalgebra.val_apply, map_sub, map_add, map_pow, map_mul, map_one,
    map_ofNat] at h
  simpa [etaLift_coe] using h

/-! ## 2. The exact expansion, pushed down to `L` with an integral witness -/

/-- `φⁿ − 3ⁿ = λ²·(n·3ⁿ⁻¹·ζ⁴) + λ⁴·d₀` in `L`, with `d₀` an *algebraic integer*
(`IsIntegral ℤ d₀`). This is `BealLambdaCongruence.phi_pow_mod_lambda4_ring` run at
`R = ↥(integralClosure ℤ L)` and pushed down. -/
theorem phi_pow_mod_lambda4_integral {ζ : L} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ∃ d0 : L, IsIntegral ℤ d0 ∧
      (1 + ζ + ζ ^ 4) ^ n - (3 : L) ^ n =
        (1 - ζ) ^ 2 * ((n : L) * (3 : L) ^ (n - 1) * ζ ^ 4) + (1 - ζ) ^ 4 * d0 := by
  obtain ⟨d0, hd0⟩ := BealLambdaCongruence.phi_pow_mod_lambda4_ring
    (etaLift_pow_five hζ) (etaLift_ne_one hζ) n
  refine ⟨(d0 : L), d0.2, ?_⟩
  have h := congrArg ((integralClosure ℤ L).val) hd0
  simp only [Subalgebra.val_apply, map_sub, map_add, map_pow, map_mul, map_one,
    map_ofNat, map_natCast] at h
  simpa [etaLift_coe] using h

/-! ## 3. The ⟹ direction -/

theorem five_dvd_of_golden_pow_cong_lambda4 {ζ : L} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ)
    (c : L) (hcI : IsIntegral ℤ c)
    (hc : (1 + ζ + ζ ^ 4) ^ n - (3 : L) ^ n = (1 - ζ) ^ 4 * c) : 5 ∣ n := by
  -- Step 1: subtract off the exact-expansion identity to isolate the λ²-coefficient.
  obtain ⟨d0, hd0I, hd0⟩ := phi_pow_mod_lambda4_integral hζ n
  set c' : L := c - d0 with hc'_def
  have hc'I : IsIntegral ℤ c' := hcI.sub hd0I
  have hstep1 : (1 - ζ) ^ 2 * ((n : L) * (3 : L) ^ (n - 1) * ζ ^ 4) = (1 - ζ) ^ 4 * c' := by
    have hc4 : (1 - ζ) ^ 4 = (1 - ζ) ^ 2 * (1 - ζ) ^ 2 := by ring
    rw [hc'_def, hc4]
    linear_combination hc - hd0
  -- Step 2: cancel one copy of `(1-ζ)^2` (nonzero since `ζ ≠ 1`).
  have hζne1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hne0 : (1 - ζ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hζne1))
  have hstep2 : (n : L) * (3 : L) ^ (n - 1) * ζ ^ 4 = (1 - ζ) ^ 2 * c' := by
    have heq : (1 - ζ) ^ 2 * ((n : L) * (3 : L) ^ (n - 1) * ζ ^ 4) =
        (1 - ζ) ^ 2 * ((1 - ζ) ^ 2 * c') := by rw [hstep1]; ring
    exact mul_left_cancel₀ hne0 heq
  -- Step 3: absorb the unit `ζ⁴` (multiply through by `ζ`, using `ζ⁵ = 1`).
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  set c'' : L := ζ * c' with hc''_def
  have hc''I : IsIntegral ℤ c'' := (hζ.isIntegral (by norm_num)).mul hc'I
  have hstep3 : (n : L) * (3 : L) ^ (n - 1) = (1 - ζ) ^ 2 * c'' := by
    have hmul := congrArg (ζ * ·) hstep2
    simp only at hmul
    rw [hc''_def]
    linear_combination hmul - (n : L) * (3 : L) ^ (n - 1) * h5
  -- Step 4: match to the norm-bridge's `algebraMap ℚ L` shape and apply it.
  have hmatch : algebraMap ℚ L (((n : ℤ) * 3 ^ (n - 1) : ℤ) : ℚ) = (1 - ζ) ^ 2 * c'' := by
    rw [← hstep3]
    push_cast
    simp
  have hdvdZ : (5 : ℤ) ∣ ((n : ℤ) * 3 ^ (n - 1)) :=
    BealLambdaNormBridge.five_dvd_of_lambda_sq_dvd hζ ((n : ℤ) * 3 ^ (n - 1)) c'' hc''I hmatch
  -- Step 5: descend to ℕ and strip the coprime factor `3^(n-1)`.
  have hdvdN : 5 ∣ n * 3 ^ (n - 1) := by
    have : ((5 : ℕ) : ℤ) ∣ ((n * 3 ^ (n - 1) : ℕ) : ℤ) := by
      push_cast
      exact hdvdZ
    exact_mod_cast this
  have hcop : Nat.Coprime 5 (3 ^ (n - 1)) := (by norm_num : Nat.Coprime 5 3).pow_right _
  exact hcop.dvd_of_dvd_mul_right hdvdN

/-! ## 4. The full characterization -/

/-- **The full λ⁴ Kummer characterization for `ℚ(ζ₅)`**:

  `(∃ c : L, IsIntegral ℤ c ∧ φⁿ − 3ⁿ = λ⁴·c) ↔ 5 ∣ n`,

where `φ = 1 + ζ + ζ⁴` is the golden unit and `λ = 1 − ζ`. This is the composition of the
bare-`CommRing` structural reduction in `BealKummerLambda4Congruence` with the genuine
number-field norm bridge in `BealLambdaNormBridge`, specialized to `L = ℚ(ζ₅)` (or any field
that is a 5th cyclotomic extension of `ℚ` with a chosen primitive root `ζ`). -/
theorem golden_pow_cong_lambda4_iff_five_dvd {ζ : L} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (∃ c : L, IsIntegral ℤ c ∧
      (1 + ζ + ζ ^ 4) ^ n - (3 : L) ^ n = (1 - ζ) ^ 4 * c) ↔ 5 ∣ n := by
  constructor
  · rintro ⟨c, hcI, hc⟩
    exact five_dvd_of_golden_pow_cong_lambda4 hζ n c hcI hc
  · exact golden_pow_cong_lambda4_of_five_dvd_integral hζ n

#print axioms etaLift_pow_five
#print axioms etaLift_ne_one
#print axioms golden_pow_cong_lambda4_of_five_dvd_integral
#print axioms phi_pow_mod_lambda4_integral
#print axioms five_dvd_of_golden_pow_cong_lambda4
#print axioms golden_pow_cong_lambda4_iff_five_dvd

end BealLambda4FullCharacterization
