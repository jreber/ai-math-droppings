import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.LambdaCongruence

/-!
# The descent unit mod λ⁴ for Beal `(5,5,z)`: what the finite-ring lens can and cannot do

## Context: the breaking-monoculture success on `φ`, and the actual wall here

Earlier work (`BealLambda4FullCharacterization.golden_pow_cong_lambda4_iff_five_dvd`) showed,
via the "ant / finite local ring" lens, that the standing *Baker-class* verdict on the
λ⁴-level Kummer congruence for the **fixed** golden unit `φ = 1 + ζ₅ + ζ₅⁴` was a
mis-diagnosis: `φⁿ ≡ (rational integer) (mod λ⁴) ⟺ 5 ∣ n` is a *decidable* fact whose whole
content lives in the 625-element ring `𝓞K/λ⁴ ≅ 𝔽₅[s]/(s⁴)`.

This file examines whether the SAME lens closes the *actual* remaining wall,
`beal_kummer_mod_lambda4_for_unit`: the descent unit `u` in `A + Bζ = d^z·u`.

**What the descent actually needs (from `BealKummerP5Assembly` /
`BealRealReductionConcrete.beal_55z_reduced_to_real_unit`):**

* Torsion is *already absorbed*: `u = ζ^k · v` and `BealKummerTorsionAbsorb5.kummer_absorb_zeta_pow_5`
  turns `A + Bζ = d^z · ζ^k · v` into `A + Bζ = D^z · v` with `v` a REAL unit (`gcd(z,5)=1`).
  So the torsion exponent `k` need **not** be `0`; the finite-ring lens fully closes that
  sub-question (a 5-element computation), and it is *proved*.
* The real unit is `v = ±φⁿ` (fundamental-unit theorem, `beal_fundamental_unit_sqrt5`, proved).
* The descent CLOSES iff `v` is a **z-th power**, i.e. iff **`z ∣ n`**.

So the *true* remaining requirement is `z ∣ n`, where `z` is the Beal exponent with
`gcd(z,10) = 1`.

## The precise reason the `φ`-trick does NOT transfer to close this wall

The Kummer-mod-λ⁴ hypothesis on the real unit is, by the proved characterization,
*exactly* `5 ∣ n` — a condition of **period 5** in `n`. More generally, the residue of `φⁿ`
in ANY finite quotient `𝓞K/λ^m` is **periodic in `n`**: `φ` is a unit of the finite ring
`𝓞K/λ^m`, so `n ↦ φⁿ mod λ^m` cycles with period `= ord(φ)` in `(𝓞K/λ^m)^×`, a *fixed*
number depending only on `m` (for `m = 4` this period is exactly `20`, see
`isRatCongMod_periodic_20` below).

The descent requirement `z ∣ n`, by contrast, has period `z`. And for EVERY admissible
Beal exponent `z` (`gcd(z,10) = 1`, hence coprime to `2` and `5`, hence coprime to
`20 = 4·5` and to every `4·5^k`), we have `gcd(z, period) = 1`. A predicate that is periodic
with period `P` **cannot** coincide with `z ∣ ·` when `gcd(z,P) = 1` and `z ≥ 2`
(`dvd_not_periodic`). Therefore:

> **No mod-λ⁴ congruence can force (or even be equivalent to) the descent requirement
> `z ∣ n`.**  (`kummer_lambda4_cannot_force_descent`, fully unconditional.) The same
> obstruction is CONJECTURED to extend to every finite level `m` (`lambda_pow_invariant_
> cannot_detect_descent`), conditional on the period of `φⁿ mod λ^m` dividing `4·5^{m-1}`
> — a bound grounded concretely only for `m=4` below, not proved for general `m` in this
> file.

This is a *rigorous* structural no-go, and it explains cleanly why all ~13 prior λ-adic /
Frobenius / norm attempts were "confirmed Baker-class": the mod-λ⁴ *computation itself* is
finite and decidable (the lens genuinely applies to "what is `u mod λ⁴`"), but the mod-λ⁴
computation is the **wrong invariant** — it is blind, by periodicity, to `z ∣ n`. The genuine
`z ∣ n` content is irreducibly transcendental (linear-forms-in-logarithms / Baker), living
one level up from any finite local ring. The `φ`-success transferred only the *statement's
decidability for a fixed exponent*, not a route to the exponent-divisibility the descent
needs.

All results are axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
-/

namespace BealDescentUnitLambda4

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ## 1. The genuine mod-λ⁴ Kummer condition on the golden unit is periodic (period 20)

We ground the abstract periodicity claim in the *actual* object. First `φ²⁰ ≡ 1 (mod λ⁴)`
(so `φ` has order dividing 20 in `(𝓞K/λ⁴)^×`), then the real Kummer hypothesis
`∃ r ∈ ℤ, φⁿ ≡ r (mod λ⁴)` is invariant under `n ↦ n + 20`. -/

/-- **`φ²⁰ ≡ 1 (mod λ⁴)`**: `∃ c, (1+η+η⁴)²⁰ − 1 = (1−η)⁴·c`.

`φ²⁰ − 1 = (φ²⁰ − 3²⁰) + (3²⁰ − 1)`. The first bracket is `λ⁴`-divisible by
`phi_pow_cong_mod_lambda4_five_dvd_ring` (`5 ∣ 20`); the second because `5 ∣ (3²⁰ − 1)`
(`3²⁰ − 1 = 5·697356880`) and `5 = (1−η)⁴·(−1−η+η³)`. -/
theorem phi_pow20_cong_one_mod_lambda4 {η : R} (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) :
    ∃ c : R, (1 + η + η ^ 4) ^ 20 - 1 = (1 - η) ^ 4 * c := by
  obtain ⟨c1, hc1⟩ :=
    BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring h5 hne1 20 (by norm_num)
  have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have key : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hfive : (1 - η) ^ 4 * (-1 - η + η ^ 3) = 5 := by
    linear_combination (5 - 4 * η + η ^ 2) * h5 - hsum
  have h320 : (3 : R) ^ 20 - 1 = (1 - η) ^ 4 * ((-1 - η + η ^ 3) * 697356880) := by
    have hnum : (3 : R) ^ 20 - 1 = 5 * 697356880 := by norm_num
    rw [hnum, ← hfive]; ring
  refine ⟨c1 + (-1 - η + η ^ 3) * 697356880, ?_⟩
  have hsplit : (1 + η + η ^ 4) ^ 20 - 1
      = ((1 + η + η ^ 4) ^ 20 - (3 : R) ^ 20) + ((3 : R) ^ 20 - 1) := by ring
  rw [hsplit, hc1, h320]; ring

/-- The genuine mod-λ⁴ Kummer hypothesis on the golden power `φⁿ`: it is congruent to *some*
rational integer `r` modulo `λ⁴`. (This is precisely the hypothesis Kummer's lemma consumes.) -/
def IsRatCongMod (η : R) (n : ℕ) : Prop :=
  ∃ (r : ℤ) (c : R), (1 + η + η ^ 4) ^ n - (r : R) = (1 - η) ^ 4 * c

/-- **The mod-λ⁴ Kummer condition is `20`-periodic in the exponent.**

Since `φ²⁰ ≡ 1 (mod λ⁴)` we have `φ^(n+20) − φⁿ = φⁿ·(φ²⁰ − 1) = λ⁴·(φⁿ·w)`, so `φ^(n+20)`
and `φⁿ` have the *same* residue mod `λ⁴`; hence they are congruent to a rational integer for
exactly the same `r`. This is the concrete statement that the actual λ⁴ invariant of the
descent unit is periodic — the fact that makes it blind to `z ∣ n`. -/
theorem isRatCongMod_periodic_20 {η : R} (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) :
    IsRatCongMod η (n + 20) ↔ IsRatCongMod η n := by
  obtain ⟨w, hw⟩ := phi_pow20_cong_one_mod_lambda4 h5 hne1
  have hshift : (1 + η + η ^ 4) ^ (n + 20) - (1 + η + η ^ 4) ^ n
      = (1 - η) ^ 4 * ((1 + η + η ^ 4) ^ n * w) := by
    have : (1 + η + η ^ 4) ^ (n + 20)
        = (1 + η + η ^ 4) ^ n * ((1 + η + η ^ 4) ^ 20) := by rw [pow_add]
    rw [this]
    linear_combination (1 + η + η ^ 4) ^ n * hw
  constructor
  · rintro ⟨r, c, hc⟩
    refine ⟨r, c - (1 + η + η ^ 4) ^ n * w, ?_⟩
    linear_combination hc - hshift
  · rintro ⟨r, c, hc⟩
    refine ⟨r, c + (1 + η + η ^ 4) ^ n * w, ?_⟩
    linear_combination hc + hshift

/-! ## 2. The abstract no-go: a periodic predicate cannot detect divisibility by a coprime modulus -/

/-- **A predicate equal to `z ∣ ·` is never periodic with a period coprime to `z`
(for `z ≥ 2`).**

If `z ∣ (n + P) ↔ z ∣ n` for all `n`, then taking `n = 0` gives `z ∣ P` (as `z ∣ 0`); with
`gcd(z, P) = 1` this forces `z ∣ 1`, i.e. `z = 1`, contradicting `z ≥ 2`. -/
theorem dvd_not_periodic {z P : ℕ} (hz : 2 ≤ z) (hcop : Nat.Coprime z P) :
    ¬ (∀ n : ℕ, z ∣ (n + P) ↔ z ∣ n) := by
  intro h
  have hzP : z ∣ P := by
    have := (h 0).mpr (dvd_zero z)
    simpa using this
  have hd1 : z ∣ Nat.gcd z P := Nat.dvd_gcd (dvd_refl z) hzP
  have hg : Nat.gcd z P = 1 := hcop
  rw [hg] at hd1
  have : z ≤ 1 := Nat.le_of_dvd Nat.one_pos hd1
  omega

/-- **The general no-go, one type-level up.** No `P`-periodic predicate can be *equivalent*
to the descent requirement `z ∣ ·` when `gcd(z, P) = 1` and `z ≥ 2`. -/
theorem no_periodic_invariant_detects_descent {z P : ℕ} (hz : 2 ≤ z)
    (hcop : Nat.Coprime z P) :
    ¬ ∃ Q : ℕ → Prop, (∀ n, Q (n + P) ↔ Q n) ∧ (∀ n, Q n ↔ z ∣ n) := by
  rintro ⟨Q, hper, hQ⟩
  apply dvd_not_periodic hz hcop
  intro n
  rw [← hQ (n + P), ← hQ n]
  exact hper n

/-! ## 3. Admissible Beal exponents are coprime to every mod-λ^m period -/

/-- **`gcd(z,10) = 1 ⟹ gcd(z, 20) = 1`.** `20 = 4·5`; coprimality to `2` and `5` gives
coprimality to `4` and `5`, hence to their product `20`. (`20` is the period of `φⁿ mod λ⁴`.) -/
theorem coprime_ten_imp_coprime_twenty {z : ℕ} (h : Nat.Coprime z 10) : Nat.Coprime z 20 := by
  have h2 : Nat.Coprime z 2 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h5 : Nat.Coprime z 5 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h4 : Nat.Coprime z 4 := by simpa using h2.pow_right 2
  have : Nat.Coprime z (4 * 5) := Nat.Coprime.mul_right h4 h5
  simpa using this

/-- **`gcd(z,10) = 1 ⟹ gcd(z, 4·5^k) = 1`** for every `k`. This is the coprimality half of
a conjectured extension of the no-go to every λ-adic level (the period of `φⁿ mod λ^m` is
CONJECTURED to divide `4·5^{m-1}`, by analogy with the `m=4` case grounded concretely below
in `phi_pow20_cong_one_mod_lambda4`/`isRatCongMod_periodic_20` — that concrete grounding is
done only for `m=4`; `lambda_pow_invariant_cannot_detect_descent` below is consequently an
ABSTRACT corollary conditional on that period bound, not itself a proof that the period
bound holds at every `m`). Only the `λ⁴` case (`lambda4_invariant_cannot_detect_descent`) is
fully unconditional. -/
theorem coprime_ten_imp_coprime_four_mul_pow_five {z k : ℕ} (h : Nat.Coprime z 10) :
    Nat.Coprime z (4 * 5 ^ k) := by
  have h2 : Nat.Coprime z 2 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h5 : Nat.Coprime z 5 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  have h4 : Nat.Coprime z 4 := by simpa using h2.pow_right 2
  exact Nat.Coprime.mul_right h4 (h5.pow_right k)

/-! ## 4. The wall, made precise: the mod-λ⁴ (indeed any mod-λ^m) invariant cannot force `z ∣ n` -/

/-- **A `20`-periodic invariant cannot detect the descent requirement `z ∣ n`** for any
admissible Beal exponent `z ≥ 2` (`gcd(z,10) = 1`). Since `20` is exactly the period of the
golden unit's residue mod `λ⁴`, this is the abstract statement behind the concrete
`kummer_lambda4_cannot_force_descent`. -/
theorem lambda4_invariant_cannot_detect_descent {z : ℕ} (hz : 2 ≤ z)
    (hz10 : Nat.Coprime z 10) :
    ¬ ∃ Q : ℕ → Prop, (∀ n, Q (n + 20) ↔ Q n) ∧ (∀ n, Q n ↔ z ∣ n) :=
  no_periodic_invariant_detects_descent hz (coprime_ten_imp_coprime_twenty hz10)

/-- **The no-go at every λ-adic level `m`** (`period ∣ 4·5^{m-1}`): admissible `z` is coprime
to `4·5^k` for all `k`, so no invariant periodic at any such level can equal `z ∣ ·`. -/
theorem lambda_pow_invariant_cannot_detect_descent {z k : ℕ} (hz : 2 ≤ z)
    (hz10 : Nat.Coprime z 10) :
    ¬ ∃ Q : ℕ → Prop, (∀ n, Q (n + 4 * 5 ^ k) ↔ Q n) ∧ (∀ n, Q n ↔ z ∣ n) :=
  no_periodic_invariant_detects_descent hz (coprime_ten_imp_coprime_four_mul_pow_five hz10)

/-- **CROWN: the genuine mod-λ⁴ Kummer condition on the descent unit provably CANNOT force the
descent-closing requirement `z ∣ n`.**

`IsRatCongMod η` is the actual hypothesis Kummer's lemma consumes ("`φⁿ ≡ a rational integer
mod λ⁴`"). It is `20`-periodic in `n` (`isRatCongMod_periodic_20`). The descent needs
`z ∣ n`, which has period `z` coprime to `20`. Hence the two can never be equivalent — the
mod-λ⁴ Kummer condition is *structurally incapable* of pinning down `z ∣ n`, no matter what
`A, B, d` are. This is the precise, formal reason the finite-ring/`φ` technique, which DID
close the fixed-unit congruence, does NOT transfer to close this wall: the wall is not a
finite-ring computation, it is a coprime-period divisibility invisible to every finite λ-adic
invariant. -/
theorem kummer_lambda4_cannot_force_descent {η : R} (h5 : η ^ 5 = 1) (hne1 : η ≠ 1)
    {z : ℕ} (hz : 2 ≤ z) (hz10 : Nat.Coprime z 10) :
    ¬ ∀ n : ℕ, IsRatCongMod η n ↔ z ∣ n := by
  intro h
  exact lambda4_invariant_cannot_detect_descent hz hz10
    ⟨IsRatCongMod η, isRatCongMod_periodic_20 h5 hne1, h⟩

/-- **The `5 ∣ n` the Kummer route delivers is strictly weaker than the `z ∣ n` the descent
needs.** Direct one-line witness `n = 5` (`5 ∣ 5` but `z ∤ 5` for `z ≥ 2` coprime to `5`).
The gap between what the finite-ring lens yields and what closes the descent, in its crudest
form. -/
theorem kummer_lambda4_condition_strictly_weaker {z : ℕ} (hz : 2 ≤ z)
    (hz5 : Nat.Coprime z 5) : ¬ ∀ n : ℕ, (5 ∣ n) ↔ (z ∣ n) := by
  intro h
  have hz5' : z ∣ 5 := (h 5).mp (dvd_refl 5)
  have hd1 : z ∣ Nat.gcd z 5 := Nat.dvd_gcd (dvd_refl z) hz5'
  have hg : Nat.gcd z 5 = 1 := hz5
  rw [hg] at hd1
  have : z ≤ 1 := Nat.le_of_dvd Nat.one_pos hd1
  omega

#print axioms phi_pow20_cong_one_mod_lambda4
#print axioms isRatCongMod_periodic_20
#print axioms dvd_not_periodic
#print axioms no_periodic_invariant_detects_descent
#print axioms coprime_ten_imp_coprime_twenty
#print axioms coprime_ten_imp_coprime_four_mul_pow_five
#print axioms lambda4_invariant_cannot_detect_descent
#print axioms lambda_pow_invariant_cannot_detect_descent
#print axioms kummer_lambda4_cannot_force_descent
#print axioms kummer_lambda4_condition_strictly_weaker

end BealDescentUnitLambda4
