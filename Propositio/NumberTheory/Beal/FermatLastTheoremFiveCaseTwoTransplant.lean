import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwo
import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwoNorm

/-!
# FLT-5 Case II: transplanting the `5`-adic factorization into `ℤ[φ]`

`FermatLastTheoremFiveCaseTwo.case2_core` proves the classical `5`-adic factorization of
Case II purely over `ℤ`: for pairwise coprime `x, y, z` with `x^5+y^5=z^5`, `z ≠ 0`, `5 ∣ z`,
either

* `x + y = 5·d⁵` and `Φ(x,y) = 5^(5n+4)·e⁵`, or
* `x + y = 5^(5n+4)·d⁵` and `Φ(x,y) = 5·e⁵`

where `Φ(x,y) = x⁴ - x³y + x²y² - xy³ + y⁴`. Separately, `FermatLastTheoremFiveCaseTwoNorm`
proves that `Φ(x,y)` is *literally* a product `(a₁+b·φ)·(a₂+b·φ)` in the concrete `a+b·φ ∈ ℝ`
model of `ℤ[φ]` (`case2_phi_factorization`, with `a₁ = -(x²+xy+y²)`, `a₂ = xy`, `b = x²+y²`).

This file performs the substitution the Case-II descent postmortem
(`docs/kb/failed/2026-07-12__fermatLastTheoremFive_caseTwo_descent.json`) calls "transplanting
the factorization into `ℤ[φ]`": combining the two facts above to exhibit the *specific* product
`(a₁+bφ)(a₂+bφ)` as *equal to* `5^k·e⁵` (as a real number, `k ∈ {1, 5n+4}`), for the `x, y, z`
of an actual (hypothetical) Case-II solution. This is the concrete bridge fact the future
unit-pinning + descent step will need as its starting point.

## Main result

`case2_norm_transplant` : under the `case2_core` hypotheses, there exist `n : ℕ`, `d e : ℤ`
such that (writing `a₁ = -(x²+xy+y²)`, `a₂ = xy`, `b = x²+y²`) either

* `x + y = 5·d⁵` and `(a₁+bφ)(a₂+bφ) = 5^(5n+4)·e⁵`, or
* `x + y = 5^(5n+4)·d⁵` and `(a₁+bφ)(a₂+bφ) = 5·e⁵`.

`case2_norm_eq` : the sharper, **pure-`ℤ`** form of the same fact — no real-number casts, no
`φ` at all — that is the actual load-bearing statement for a future valuation-theory module:
under the `case2_core` hypotheses, writing `N(a,b) := a² + a·b − b²` for the (integer-valued)
norm form of `BealFundamentalUnitPell.norm_form_identity`, there exist `n : ℕ`, `d e : ℤ` such
that either

* `x + y = 5·d⁵` and `N(a₁, b) = -(5^(5n+4)·e⁵)`, or
* `x + y = 5^(5n+4)·d⁵` and `N(a₁, b) = -(5·e⁵)`

(with `a₁ = -(x²+xy+y²)`, `b = x²+y²` as above). This says: **a single, concrete element
`a₁+b·φ ∈ ℤ[φ]` has norm exactly `∓5^k·e⁵`** — the natural starting point for pinning its
prime/unit factorization in a future session.

## What this does NOT yet do (honest scope note)

This is still purely a bookkeeping/gluing step. It does **not** attempt to pin the factor
`a₁+b·φ` (or `a₂+b·φ`) as a unit times a fifth power via
`BealFundamentalUnitPell.beal_fundamental_unit_sqrt5` — that requires a genuine
divisibility/valuation theory for the ramified prime `√5 = 2φ-1` in `ℤ[φ]` (i.e. peeling the
exact power of `√5` dividing `a₁+bφ` off before applying unique factorization to what remains),
which is not built anywhere in this repository and is flagged in the postmortem as the actual
hard remaining content (Legendre's 1825 contribution). Building that valuation theory concretely
enough to avoid the abstract `NumberField`/`RingOfIntegers` machinery (per the explicit scoping
instruction) is the next unit of work.

**No `sorry`, no project axiom.**
-/

namespace FermatLastTheoremFiveCaseTwo

open BealFundamentalUnitPell Real FermatLastTheoremFiveCaseTwoNorm

/-- **The `5`-adic factorization, transplanted into `ℤ[φ]`.** Under the `case2_core`
hypotheses, the quartic-cofactor factor `(a₁+bφ)(a₂+bφ)` (with `a₁ = -(x²+xy+y²)`, `a₂ = xy`,
`b = x²+y²`) is literally equal, as a real number, to `5^k·e⁵` — matched with the corresponding
`5`-power in `x+y`, exactly as in `case2_core`. -/
theorem case2_norm_transplant {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hz0 : z ≠ 0) (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (n : ℕ) (d e : ℤ),
      (x + y = 5 * d ^ 5 ∧
        (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) *
            (((x * y : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) =
          ((5 ^ (5 * n + 4) * e ^ 5 : ℤ) : ℝ)) ∨
      (x + y = 5 ^ (5 * n + 4) * d ^ 5 ∧
        (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) *
            (((x * y : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) =
          ((5 * e ^ 5 : ℤ) : ℝ)) := by
  obtain ⟨n, d, e, hcase⟩ := case2_core hxy hyz hxz hz0 heq h5z
  have hprod := case2_phi_factorization x y
  rcases hcase with ⟨hxy5, hPhi⟩ | ⟨hxy5, hPhi⟩
  · refine ⟨n, d, e, Or.inl ⟨hxy5, ?_⟩⟩
    rw [hprod]
    exact_mod_cast hPhi
  · refine ⟨n, d, e, Or.inr ⟨hxy5, ?_⟩⟩
    rw [hprod]
    exact_mod_cast hPhi

/-- **The `5`-adic factorization, transplanted into `ℤ[φ]` — pure-`ℤ` form.** Under the
`case2_core` hypotheses, the norm `N(a₁,b) = a₁²+a₁·b-b²` of the concrete element `a₁+b·φ`
(with `a₁ = -(x²+xy+y²)`, `b = x²+y²`) is exactly `∓5^k·e⁵`, matched with the corresponding
`5`-power in `x+y`, exactly as in `case2_core`. No real-number casts or `φ` appear in the
statement — this is the natural handoff point for a future divisibility/valuation-theoretic
treatment of `ℤ[φ]`. -/
theorem case2_norm_eq {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hz0 : z ≠ 0) (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (n : ℕ) (d e : ℤ),
      (x + y = 5 * d ^ 5 ∧
        (-(x ^ 2 + x * y + y ^ 2)) ^ 2 + (-(x ^ 2 + x * y + y ^ 2)) * (x ^ 2 + y ^ 2)
            - (x ^ 2 + y ^ 2) ^ 2 = -(5 ^ (5 * n + 4) * e ^ 5)) ∨
      (x + y = 5 ^ (5 * n + 4) * d ^ 5 ∧
        (-(x ^ 2 + x * y + y ^ 2)) ^ 2 + (-(x ^ 2 + x * y + y ^ 2)) * (x ^ 2 + y ^ 2)
            - (x ^ 2 + y ^ 2) ^ 2 = -(5 * e ^ 5)) := by
  obtain ⟨n, d, e, hcase⟩ := case2_core hxy hyz hxz hz0 heq h5z
  have hnorm := case2_phi_eq_neg_norm x y
  rcases hcase with ⟨hxy5, hPhi⟩ | ⟨hxy5, hPhi⟩
  · exact ⟨n, d, e, Or.inl ⟨hxy5, by rw [hnorm, hPhi]⟩⟩
  · exact ⟨n, d, e, Or.inr ⟨hxy5, by rw [hnorm, hPhi]⟩⟩

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo
#print axioms case2_norm_transplant
#print axioms case2_norm_eq
end AxiomCheck
