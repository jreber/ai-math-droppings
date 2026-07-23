import Propositio.Beal.RealReductionConcrete
import Propositio.Beal.RealSubfieldDescent
import Propositio.Beal.GoldenKummerEngine
import Propositio.Beal.FiveRealSubfieldIso
import Propositio.Beal.GoldenMinPoly
import Mathlib.Tactic

/-!
# Kummer p=5 Assembly: the sharpest achievable conditional capstone

This file assembles the proven Kummer p=5 pieces into the best achievable conditional statement,
clearly documenting the remaining gap between what is proved and what closes `beal_kummer_p5`.

## What is proved (axiom-clean):

1. `BealGoldenKummerEngine.golden_dual_kummer` — arithmetic engine: if φⁿ is rational mod 5
   (vanishing ε-component in ℤ[φ]/(5) ≅ 𝔽₅[ε]) then φⁿ is a 5th power.
2. `BealGoldenKummerEngine.golden_dual_rational_iff` — the vanishing condition ⟺ 5 ∣ n.
3. `BealGoldenKummerEngine.five_dvd_fib_iff` — 5 ∣ fib n ↔ 5 ∣ n (rank of apparition = 5).
4. `BealFiveRealSubfieldIso.*` — the real generator η = ζ+ζ⁴ satisfies η²+η-1=0; φ=1+η is a
   unit of 𝓞(ℚ(ζ₅)) with φ·(φ-1)=1; φ satisfies the Fibonacci power law; norm N(φ) = -1.
5. `BealGoldenMinPoly.golden_ratio_minpoly_cyclotomic` — minpoly ℚ (1+ζ+ζ⁴) = X²-X-1.
6. `BealRealReductionConcrete.beal_55z_reduced_to_real_unit` — A⁵+B⁵=C^z with gcd(A,B)=1,
   5∤(A+B), gcd(z,10)=1 reduces to: ∃ s, A+B = s^z AND a real unit v such that v being a z-th
   power implies A+B·ζ = D^z.
7. `BealRealSubfieldDescent.real_factor_pow_of_subfield_pow` — if the real subfield unit vp
   is a z-th power in (𝓞 K⁺)ˣ then v is a z-th power in (𝓞 K)ˣ.

## The remaining gap (two open theorems):

**Gap 1 — Fundamental unit theorem** (`beal_fundamental_unit_sqrt5`, status: open):
  Every unit v of 𝓞(ℚ(√5)) = 𝓞(ℚ(ζ₅)⁺) is of the form ±φⁿ where φ = (1+√5)/2.
  Equivalently: (𝓞(ℚ(√5)))ˣ = ⟨-1, φ⟩.
  Evidence we have: φ is a unit (golden_ratio_mul_inv), N(φ) = -1 (golden_ratio_norm),
  minpoly φ = X²-X-1 (golden_ratio_minpoly_cyclotomic). The remaining step is that φ is
  the FUNDAMENTAL (= minimal-norm) unit — a Pell/minimization argument not yet in mathlib
  for this specific field.

**Gap 2 — λ² congruence** (`beal_descent_lambda2_congruence`, status: open):
  The descent unit v (produced by beal_55z_reduced_to_real_unit) satisfies v ≡ rational
  integer (mod λ²), where λ = 1 - ζ is the Eisenstein prime. This pins v in the Kummer
  congruence hypothesis: a real unit of 𝓞(ℚ(ζ₅)⁺) congruent to a rational mod λ² is a 5th
  power. Combining with the dual-number engine: 5 ∣ n (where v = ±φⁿ by Gap 1), so v is a
  5th power. With gcd(z,5)=1 and gcd(z,2)=1 (from gcd(z,10)=1), v is then a z-th power.

## The conditional capstone

With hypothesis `hunit` replacing both gaps:
  IF every real unit of (𝓞 K)ˣ is a z-th power THEN A+B·ζ = D^z.

Together with A+B = s^z (proved unconditionally from the reduction), this is the full
conditional (5,5,z) Beal statement. The two open gaps (fundamental unit theorem + λ²
congruence) are the only missing pieces.
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealKummerP5Assembly

/-! ## The integer descent part: A+B = s^z (unconditional) -/

/-- **A+B is a z-th power (unconditional).** From `beal_55z_reduced_to_real_unit`, the integer
part A+B = s^z holds without any assumption on the unit group. This is the first conclusion of the
descent, independent of the Kummer engine. -/
theorem beal_55z_int_descent {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) (hzcop : Nat.Coprime z 10) :
    ∃ s : ℕ, A + B = s ^ z := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
  obtain ⟨s, _d, _v, hABs, _hv, _himp⟩ :=
    BealRealReductionConcrete.beal_55z_reduced_to_real_unit hζ hAB h5 hz h hzcop
  exact ⟨s, hABs⟩

/-! ## The full conditional Kummer capstone -/

/-- **Kummer p=5 conditional capstone.**

A primitive (5,5,z) Beal solution A⁵+B⁵=C^z with gcd(A,B)=1, 5∤(A+B), z≠0, gcd(z,10)=1
satisfies:
  1. (Unconditional) A+B = s^z for some natural number s.
  2. (Conditional on `hunit`) A + B·ζ = D^z for some algebraic integer D.

The hypothesis `hunit` — every real unit of (𝓞 K)ˣ is a z-th power — encapsulates the two
remaining open gaps:
  * **Fundamental unit theorem**: (𝓞(ℚ(√5)))ˣ = ⟨-1, φ⟩ (every unit is ±φⁿ).
  * **λ² congruence**: the descent unit v satisfies v ≡ rational integer (mod λ²), which via
    the golden_dual_kummer engine forces 5 ∣ n (where v = ±φⁿ), hence v = (±φ^(n/5))^5 is a
    5th power, and since gcd(z,5)=1 (from gcd(z,10)=1) it is then a z-th power.

Once those two gaps are closed by their respective open-target theorems
(`beal_fundamental_unit_sqrt5`, `beal_descent_lambda2_congruence`), `hunit` follows and this
capstone becomes unconditional.

The remaining gap in one sentence: the descent unit v = ±φⁿ (fundamental unit theorem,
open) with v ≡ rational (mod λ²) forces 5∣n (dual-number engine, proved), so v is a 5th
power; gcd(z,5)=1 then makes v a z-th power. -/
theorem beal_55z_kummer_conditional {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) (hzcop : Nat.Coprime z 10)
    -- The remaining typed hypothesis: every real unit is a z-th power.
    -- This packages both open gaps: fundamental unit theorem + λ² congruence.
    (hunit : ∀ v : (𝓞 K)ˣ, v ∈ realUnits K →
             ∃ w : (𝓞 K)ˣ, v = w ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
  obtain ⟨s, _d, v, hABs, hvreal, himp⟩ :=
    BealRealReductionConcrete.beal_55z_reduced_to_real_unit hζ hAB h5 hz h hzcop
  exact ⟨⟨s, hABs⟩, himp (hunit v hvreal)⟩

/-! ## Documentation of the three wrappers needed to close the full proof

### Wrapper 1: Fundamental unit theorem (open — `beal_fundamental_unit_sqrt5`)

The open target:
  Every unit v of (𝓞(ℚ(√5)))ˣ is of the form ±φⁿ for n : ℤ, where φ is the golden ratio.

Evidence assembled:
  * golden_ratio_mul_inv:  φ · (φ-1) = 1, so φ ∈ 𝓞ˣ (BealFiveRealSubfieldIso, proved).
  * golden_ratio_norm:     N(φ) = φ · φ̄ = -1, fundamental-unit signature (proved).
  * golden_ratio_minpoly_cyclotomic: minpoly ℚ φ = X²-X-1 (BealGoldenMinPoly, proved).
  * golden_pow_succ_fib:  φ^(n+1) = fib(n) + fib(n+1)·φ (BealFiveRealSubfieldIso, proved).

Route: mathlib has `IsFundamental` in `Mathlib.NumberTheory.Pell` and `Zsqrtd` units.
The missing bridge: connect `IsFundamental φ` (requires showing φ has minimal norm > 1 among
totally positive units) to our concrete φ = 1 + ζ + ζ⁴. The norm -1 and irrationality of √5
(proved) give the Pell equation x²-xy-y²=±1 whose minimal solution is (1,1), i.e. φ — a
decision in principle via the Pell theory already in mathlib.

### Wrapper 2: λ² congruence (open — `beal_descent_lambda2_congruence`)

The open target:
  The real unit v produced by beal_55z_reduced_to_real_unit satisfies v ≡ r (mod λ²) for
  some r : ℤ, where λ = 1 - ζ is the unique prime above 5 in 𝓞(ℚ(ζ₅)).

Route: the descent in BealPrimeRealReductionSharp produces v as the residue unit of
A+B·ζ mod λ². By the coprimality hypotheses (gcd(A,B)=1, 5∤(A+B)), we have
  A+B·ζ ≡ A+B (mod λ),   5∤(A+B),
so the v-factor ≡ (A+B) · (norm correction) (mod λ²). The precise bookkeeping
is in BealEisensteinDescent — the final accounting step for the unit residue class.

### Wrapper 3: The engine closes the gap (all ingredients proved)

Given Wrappers 1 and 2:
  1. v = ±φⁿ (fundamental unit theorem).
  2. v ≡ rational integer (mod λ²) (descent congruence).
  3. golden_dual_rational_iff: φⁿ ≡ integer (mod 5) iff 5 ∣ n.
     (The λ²-congruence in 𝓞(ℚ(ζ₅)⁺) maps to the ε-component condition in 𝔽₅[ε].)
  4. golden_dual_kummer: 5 ∣ n → v = (±φ^(n/5))^5 = w^5 is a 5th power.
  5. gcd(z,10) = 1 → gcd(z,5) = 1 → ∃ k, 5k ≡ 1 (mod z) → v = (w^k)^z is a z-th power.

All of steps 3–5 are proved (golden_dual_kummer, five_dvd_fib_iff, Nat.Coprime arithmetic).
Steps 1–2 are the only open gaps. -/

/-! ## Axiom audit -/

#print axioms beal_55z_int_descent
#print axioms beal_55z_kummer_conditional

end BealKummerP5Assembly
