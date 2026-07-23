import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwoDescentPin
import Mathlib.Tactic

/-!
# FLT-5 Case II — the descent recombination equation (reading γ back to integers)

`FermatLastTheoremFiveCaseTwoDescentPin.caseTwoFactorL_eq_pm_sqrt5_mul_fifth` pinned the concrete
Case-II factor as `caseTwoFactorL x y = ±(√5 · γ⁵)` for some `γ ∈ ℤ[φ]`. The classical descent's
next move is to *read `γ`'s integer coordinates `(p, q) = (γ.a, γ.b)` back into a relation among
smaller integers*. This file does exactly the concrete recombination step: it expands both sides
of the pin in the `ℤ[φ]`-coordinate basis `{1, φ}` and extracts the resulting **integer** identity.

## What this file proves (all sorry-free, axiom-clean)

* `a_pow_five`, `b_pow_five` — the explicit coordinate polynomials of a fifth power in `ℤ[φ]`:
  for `γ = p + qφ`,
  - `(γ⁵).a = p⁵ + 10p³q² + 10p²q³ + 10pq⁴ + 3q⁵`,
  - `(γ⁵).b = 5q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`  — note the automatic factor `5q`.
  (Verified pure `ℤ[φ]`-ring identities via the `Mul` instance `⟨ac+bd, ad+bc+bd⟩`.)

* `descent_eq_of_pin_pos` / `descent_eq_of_pin_neg` — from `caseTwoFactorL x y = ±(√5·γ⁵)`, matching
  the two coordinates of `caseTwoFactorL x y = ⟨-(x²+xy+y²), x²+y²⟩` against `±(√5·γ⁵)` and solving the
  resulting 2×2 linear system for `(γ⁵).a, (γ⁵).b` gives, after substituting `b_pow_five`, the
  **descent equation**
  `(x+y)² = ∓ 25·q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`.
  (Concretely: the linear system forces `5·(γ⁵).b = ∓(x+y)²`, and `(γ⁵).b = 5q·Q₄(p,q)`.)

* `caseTwo_descent_equation` — **headline**: for *any* genuine Case-II solution (`IsCoprime x y`,
  `x⁵+y⁵=z⁵`, `z≠0`, `5∣z`), there exist integers `p, q` with
  `(x+y)² = ± 25·q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`.
  Assembled directly from the capstone `caseTwoFactorL_eq_pm_sqrt5_mul_fifth`.

* `caseTwo_descent_equation_div5` — the same divided through by `25` using `5∣(x+y)`:
  writing `x+y = 5w`, `w² = ± q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`.

## Honest scope note — what remains for the infinite descent

`caseTwo_descent_equation_div5` is the concrete Diophantine consequence of the whole `ℤ[φ]`
unit-and-fifth-power pin: `w² = ± q·Q₄(p,q)` with `w = (x+y)/5` and `Q₄ = p⁴+2p³q+4p²q²+3pq³+q⁴`.
The remaining **classical (Dirichlet/Legendre 1825) content, not proved here**, is to turn this into a
strictly smaller instance of the *same* problem and close a well-founded recursion. The obstacle is
real and is exactly why exponent 5 is harder than exponent 3:

1. `w² = ± q·Q₄(p,q)` is a **square** equation, not another `X⁵+Y⁵=Z⁵`. The descent for `p=5` is not a
   direct fifth-power descent (as it is for `p=3` in `ℤ[ω]`); it runs on an *auxiliary* quadratic form
   `w² = ± q·Q₄`. One must first show `gcd(q, Q₄(p,q)) = 1` (this needs `gcd(p,q)=1`, i.e. `γ`
   primitive — **not yet extracted** from the pin; the pin currently only gives `√5 ∤ γ`), then peel
   the square: `q = ±s²·(unit)` and `Q₄ = ±t²·(unit)`.
2. `Q₄(p,q) = norm(γ)² + 5pq²(p+q)` (a verified identity — see the scope comment at end of file), so
   `Q₄` being (up to sign) a square couples back to `norm(γ)`. The classical argument re-expresses
   `Q₄`'s square-ness as a *new* pair `(p', q')` of strictly smaller height than `(p, q)` satisfying an
   equation of the same shape, giving the descent. Formalizing that re-expression (Dirichlet's genuinely
   novel step) is the outstanding work.

So: the algebraic recombination — the part that reads `γ` back to an integer equation — is **complete
and verified here**. The number-theoretic descent on `w² = ±q·Q₄` (primitivity of `γ`, coprimality of
`q` and `Q₄`, and the height-decreasing re-parametrization) is the remaining, unattempted piece.

**No `sorry`, no project axiom.**
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne GoldenInt

/-! ## Explicit fifth-power coordinates in `ℤ[φ]` -/

/-- First coordinate of a fifth power: `(γ⁵).a = p⁵ + 10p³q² + 10p²q³ + 10pq⁴ + 3q⁵`
(`p = γ.a`, `q = γ.b`). Pure `ℤ[φ]`-ring identity from `Mul = ⟨ac+bd, ad+bc+bd⟩`. -/
theorem a_pow_five (γ : GoldenInt) :
    (γ ^ 5).a =
      γ.a ^ 5 + 10 * γ.a ^ 3 * γ.b ^ 2 + 10 * γ.a ^ 2 * γ.b ^ 3
        + 10 * γ.a * γ.b ^ 4 + 3 * γ.b ^ 5 := by
  simp only [pow_succ, pow_zero, one_mul, a_mul, b_mul]; ring

/-- Second coordinate of a fifth power: `(γ⁵).b = 5q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`
(`p = γ.a`, `q = γ.b`). The factor `5q` is automatic — this is the source of the `5 ∣ (γ⁵).b`
fact and, via the pin, of `25 ∣ (x+y)²`. -/
theorem b_pow_five (γ : GoldenInt) :
    (γ ^ 5).b =
      5 * γ.b * (γ.a ^ 4 + 2 * γ.a ^ 3 * γ.b + 4 * γ.a ^ 2 * γ.b ^ 2
        + 3 * γ.a * γ.b ^ 3 + γ.b ^ 4) := by
  simp only [pow_succ, pow_zero, one_mul, a_mul, b_mul]; ring

/-! ## The descent equation from the pin -/

/-- **Descent equation, `+√5` branch.** From `caseTwoFactorL x y = √5·γ⁵`, matching coordinates of
`caseTwoFactorL x y = ⟨-(x²+xy+y²), x²+y²⟩` against `√5·γ⁵` forces `5·(γ⁵).b = -(x+y)²`; with
`(γ⁵).b = 5·γ.b·Q₄(γ.a,γ.b)` this is `(x+y)² = -25·γ.b·Q₄(γ.a,γ.b)`. -/
theorem descent_eq_of_pin_pos {x y : ℤ} {γ : GoldenInt}
    (h : caseTwoFactorL x y = sqrt5 * γ ^ 5) :
    (x + y) ^ 2 =
      -(25 * γ.b * (γ.a ^ 4 + 2 * γ.a ^ 3 * γ.b + 4 * γ.a ^ 2 * γ.b ^ 2
        + 3 * γ.a * γ.b ^ 3 + γ.b ^ 4)) := by
  have ha := congrArg GoldenInt.a h
  have hb := congrArg GoldenInt.b h
  simp only [a_caseTwoFactorL, b_caseTwoFactorL, a_mul, b_mul, a_sqrt5, b_sqrt5,
    pow_succ, pow_zero, one_mul] at ha hb
  nlinarith [ha, hb]

/-- **Descent equation, `-√5` branch.** From `caseTwoFactorL x y = -(√5·γ⁵)`, the same coordinate
match gives `5·(γ⁵).b = (x+y)²`, hence `(x+y)² = 25·γ.b·Q₄(γ.a,γ.b)`. -/
theorem descent_eq_of_pin_neg {x y : ℤ} {γ : GoldenInt}
    (h : caseTwoFactorL x y = -(sqrt5 * γ ^ 5)) :
    (x + y) ^ 2 =
      25 * γ.b * (γ.a ^ 4 + 2 * γ.a ^ 3 * γ.b + 4 * γ.a ^ 2 * γ.b ^ 2
        + 3 * γ.a * γ.b ^ 3 + γ.b ^ 4) := by
  have ha := congrArg GoldenInt.a h
  have hb := congrArg GoldenInt.b h
  simp only [a_caseTwoFactorL, b_caseTwoFactorL, a_mul, b_mul, a_sqrt5, b_sqrt5, a_neg, b_neg,
    pow_succ, pow_zero, one_mul] at ha hb
  nlinarith [ha, hb]

/-! ## Assembled descent equation for a genuine solution -/

/-- **Headline — the Case-II descent equation.** For any genuine Case-II solution (coprime `x, y`,
`x⁵+y⁵=z⁵`, `z ≠ 0`, `5 ∣ z`), there are integers `p, q` (the `ℤ[φ]`-coordinates of the pinned `γ`)
with `(x+y)² = ± 25·q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`. This reads the abstract `±√5·γ⁵` pin back
into an explicit integer Diophantine relation — the algebraic core of the classical descent. -/
theorem caseTwo_descent_equation {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (p q : ℤ),
      (x + y) ^ 2 = 25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) ∨
      (x + y) ^ 2 =
        -(25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4)) := by
  obtain ⟨γ, hγ⟩ := caseTwoFactorL_eq_pm_sqrt5_mul_fifth hxy hz0 heq h5z
  refine ⟨γ.a, γ.b, ?_⟩
  rcases hγ with h | h
  · exact Or.inr (descent_eq_of_pin_pos h)
  · exact Or.inl (descent_eq_of_pin_neg h)

/-- **Descent equation, divided form.** Since `5 ∣ (x+y)` for a Case-II solution, write `x+y = 5w`;
then `w² = ± q·(p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴)`. This is the clean auxiliary equation on which the
remaining classical descent runs (see the scope note in the module docstring). -/
theorem caseTwo_descent_equation_div5 {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (w p q : ℤ),
      x + y = 5 * w ∧
      (w ^ 2 = q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) ∨
       w ^ 2 = -(q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4))) := by
  obtain ⟨w, hw⟩ := five_dvd_add_of_solution heq h5z
  obtain ⟨p, q, hpq⟩ := caseTwo_descent_equation hxy hz0 heq h5z
  refine ⟨w, p, q, hw, ?_⟩
  set Q4 := p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4 with hQ4
  have h25 : (5 * w) ^ 2 = 25 * w ^ 2 := by ring
  rcases hpq with h | h
  · left
    rw [hw, h25] at h
    have : (25 : ℤ) * w ^ 2 = 25 * (q * Q4) := by rw [h]; ring
    exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) this
  · right
    rw [hw, h25] at h
    have : (25 : ℤ) * w ^ 2 = 25 * (-(q * Q4)) := by rw [h]; ring
    exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) this

/-! ## Auxiliary identity coupling `Q₄` to `norm γ` (for the next session's descent) -/

/-- `Q₄(p,q) = norm(γ)² + 5·p·q²·(p+q)` for `γ = p + qφ` (`p = γ.a`, `q = γ.b`). This is the
coupling the remaining descent uses: it ties the quartic cofactor of the descent equation back to
the norm of the pinned element. Pure integer ring identity (`norm γ = p² + pq − q²`). -/
theorem q4_eq_normSq_add {γ : GoldenInt} :
    γ.a ^ 4 + 2 * γ.a ^ 3 * γ.b + 4 * γ.a ^ 2 * γ.b ^ 2 + 3 * γ.a * γ.b ^ 3 + γ.b ^ 4
      = (norm γ) ^ 2 + 5 * γ.a * γ.b ^ 2 * (γ.a + γ.b) := by
  have hn : norm γ = γ.a ^ 2 + γ.a * γ.b - γ.b ^ 2 := rfl
  rw [hn]; ring

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo
#print axioms a_pow_five
#print axioms b_pow_five
#print axioms descent_eq_of_pin_pos
#print axioms descent_eq_of_pin_neg
#print axioms caseTwo_descent_equation
#print axioms caseTwo_descent_equation_div5
#print axioms q4_eq_normSq_add
end AxiomCheck
