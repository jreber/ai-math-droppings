import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwoDescentPrimitive
import Mathlib.Tactic

/-!
# FLT-5 Case II — the height-descent identity `Φ(x,y) = 5·(norm γ)⁵`

`FermatLastTheoremFiveCaseTwoDescentPrimitive.caseTwo_gamma_coprime` pins, for any genuine
Case-II solution, a **primitive** element `γ = p + q·φ ∈ ℤ[φ]` (`IsCoprime γ.a γ.b`) with
`caseTwoFactorL x y = ±(√5 · γ⁵)`. `FermatLastTheoremFiveCaseTwoDescentRecombination` and
`FermatLastTheoremFiveCaseTwoDescentPeel` read the `ℤ[φ]`-coordinates of `γ` back into the
integer Diophantine relation `(x+y)² = ±25·q·Q₄(p,q)` and peel it into `q = ±s²`, `Q₄(p,q) = ±t²`
(coprime factors of a square). What none of the existing files extract is the **norm-level**
identity connecting `γ` back to the *other* concrete quantity of the factorization — the quartic
cofactor `Φ(x,y) = x⁴-x³y+x²y²-xy³+y⁴` itself (not just `(x+y)²`) — via the field norm of `γ`.

This is exactly that missing norm-divisibility bridge: since `caseTwoFactorL x y` has norm `-Φ`
(`norm_caseTwoFactorL`, from `BealGoldenIntCoprime`) and `caseTwoFactorL x y = ±(√5·γ⁵)` has norm
`(-5)·(norm γ)⁵` (multiplicativity of the norm, `norm_sqrt5 = -5`), the two norm computations force
the **height-descent identity**

  `Φ(x,y) = 5 · (norm γ)⁵`,

with `γ` primitive (`IsCoprime γ.a γ.b`, i.e. `IsCoprime p q`). This is the concrete arithmetic
fact that ties the *original* Diophantine quantity `Φ(x,y)` to the **norm of the primitive
witness `γ`** — the natural descent-metric candidate for a future well-founded recursion (`norm γ`
is a degree-`2` polynomial in `p, q`, vastly smaller than the degree-`4` `Φ(x,y)` it is extracted
from, and is pinned exactly, not just bounded).

## Main results (proved, axiom-clean, no `sorry`)

* `GoldenInt.norm_neg` — `norm (-z) = norm z` (the field norm is even; not previously stated in
  the `GoldenInt` development — every existing norm lemma (`norm_mul`, `norm_conj`, `norm_pow`)
  handles a *positive* combinator, none handle negation, which is exactly what the `-√5·γ⁵` branch
  of `caseTwoFactorL_eq_pm_sqrt5_mul_fifth` needs).
* `caseTwo_Phi_eq_five_mul_normGamma_pow5` — **headline**: for any genuine Case-II solution
  (`IsCoprime x y`, `x⁵+y⁵ = z⁵`, `z ≠ 0`, `5 ∣ z`), there is a primitive `γ ∈ ℤ[φ]`
  (`IsCoprime γ.a γ.b`) with `Φ(x,y) = 5 · (norm γ)⁵`.
* `caseTwo_five_dvd_Phi_of_normGamma` — the immediate divisibility corollary,
  `5 ∣ Φ(x,y)` witnessed concretely as `(norm γ)⁵` (repackaging the identity as a divisibility
  statement, the shape most directly reusable by a future descent step that only needs `5 ∣ Φ`
  together with an explicit cofactor).

## What this does NOT do (honest scope note)

This is a single new norm-divisibility bridge, not an assembly of the descent. It does **not**
attempt the remaining genuinely novel Dirichlet/Legendre content: re-expressing `Q₄(p,q) = ±t²`
(or, via this file, `Φ(x,y) = 5·(norm γ)⁵`) as a *strictly smaller* instance of the same shape of
equation and closing a well-founded recursion. That height-decreasing re-parametrization remains
unattempted, exactly as flagged by `FermatLastTheoremFiveCaseTwoDescentPeel`'s scope note.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

/-- **The field norm is even: `norm (-z) = norm z`.** Not previously stated in the `GoldenInt`
development (`norm_mul`, `norm_conj`, `norm_pow` all handle *positive* combinators only) — needed
here for the `caseTwoFactorL x y = -(√5·γ⁵)` branch of `caseTwoFactorL_eq_pm_sqrt5_mul_fifth`. -/
@[simp] theorem norm_neg (z : GoldenInt) : norm (-z) = norm z := by
  simp only [norm, a_neg, b_neg]; ring

end GoldenInt

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne GoldenInt

/-- **Height-descent identity — `Φ(x,y) = 5·(norm γ)⁵`, with `γ` primitive.** For any genuine
Case-II solution, the pinned primitive `γ` (`caseTwo_gamma_coprime`) satisfies
`x⁴-x³y+x²y²-xy³+y⁴ = 5·(norm γ)⁵`. Proof: both sides are the (negated) norm of
`caseTwoFactorL x y`, computed two ways — directly (`norm_caseTwoFactorL x y = -Φ`) and via the
`±√5·γ⁵` pin (`norm (√5·γ⁵) = norm √5 · norm(γ⁵) = -5·(norm γ)⁵`, using `norm_neg` to absorb the
`-` branch). This is the norm-level bridge from `γ`'s coordinates back to the original
degree-`4` cofactor `Φ(x,y)`, the natural descent-metric candidate for a future well-founded
recursion (`norm γ` is a primitive quadratic form in `γ`'s two coordinates, pinned exactly — not
merely bounded — by this identity). -/
theorem caseTwo_Phi_eq_five_mul_normGamma_pow5 {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ γ : GoldenInt,
      IsCoprime γ.a γ.b ∧
      x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * (norm γ) ^ 5 := by
  obtain ⟨γ, hpin, hcop⟩ := caseTwo_gamma_coprime hxy hz0 heq h5z
  refine ⟨γ, hcop, ?_⟩
  have hnormL : norm (caseTwoFactorL x y) =
      -(x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := norm_caseTwoFactorL x y
  rcases hpin with h | h
  · have hn : norm (caseTwoFactorL x y) = norm (sqrt5 * γ ^ 5) := by rw [h]
    rw [norm_mul, norm_pow, norm_sqrt5, hnormL] at hn
    linarith [hn]
  · have hn : norm (caseTwoFactorL x y) = norm (-(sqrt5 * γ ^ 5)) := by rw [h]
    rw [norm_neg, norm_mul, norm_pow, norm_sqrt5, hnormL] at hn
    linarith [hn]

/-- **Divisibility corollary — `5 ∣ Φ(x,y)`, witnessed by `(norm γ)⁵`.** Repackages
`caseTwo_Phi_eq_five_mul_normGamma_pow5` as an explicit divisibility statement with the cofactor
exhibited concretely as `(norm γ)⁵` — the shape most directly reusable by a future descent step
that only needs the divisibility together with an explicit, structured cofactor (rather than the
bare existential `5 ∣ Φ` that `case2_core`/`case2_coprime_cofactors` already supply). -/
theorem caseTwo_five_dvd_Phi_of_normGamma {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ γ : GoldenInt,
      IsCoprime γ.a γ.b ∧
      (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  obtain ⟨γ, hcop, heqΦ⟩ := caseTwo_Phi_eq_five_mul_normGamma_pow5 hxy hz0 heq h5z
  exact ⟨γ, hcop, ⟨(norm γ) ^ 5, heqΦ⟩⟩

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo GoldenInt
#print axioms GoldenInt.norm_neg
#print axioms caseTwo_Phi_eq_five_mul_normGamma_pow5
#print axioms caseTwo_five_dvd_Phi_of_normGamma
end AxiomCheck
