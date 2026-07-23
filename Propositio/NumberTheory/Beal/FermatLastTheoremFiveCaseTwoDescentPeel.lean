import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwoDescentPrimitive
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# FLT-5 Case II — peeling the square from `w² = ±q·Q₄(p,q)`

`FermatLastTheoremFiveCaseTwoDescentPrimitive.caseTwo_descent_equation_coprime` gives, for any
genuine Case-II solution, integers `(p, q)` with
`(x+y)² = ±25·q·Q₄(p,q)` **and** `IsCoprime q Q₄(p,q)`, where
`Q₄(p,q) = p⁴ + 2p³q + 4p²q² + 3pq³ + q⁴`.

Dividing by `25` (using `5 ∣ (x+y)`, i.e. `x+y = 5w`) turns this into the clean auxiliary equation
`w² = ± q·Q₄(p,q)`. This file performs the classical **"peel the square"** step: from a coprime
product equal to `±` a perfect square, each factor is (up to sign) a perfect square.

## What this file proves (all sorry-free, axiom-clean)

* `peel_pm_square` — pure elementary-`ℤ` fact: if `IsCoprime a b` and `w² = ±(a·b)`, then
  `∃ s, a = ±s²` and `∃ t, b = ±t²`. Wraps mathlib's `Int.sq_of_isCoprime` (coprime factors of a
  perfect square are each `±` a square in `ℤ`) with the sign bookkeeping `(-a)·b = w²` needed to
  absorb the `w² = -(a·b)` branch (the product need not be a literal square, only `±` one).

* `caseTwo_q_and_Q4_each_pm_square` — **headline**: for any genuine Case-II solution
  (`IsCoprime x y`, `x⁵+y⁵ = z⁵`, `z ≠ 0`, `5 ∣ z`), there are integers `p, q, s, t` with
  `IsCoprime q Q₄(p,q)`, `q = ±s²`, and `Q₄(p,q) = ±t²`. This is the Diophantine payload the
  remaining Legendre height-descent consumes.

## Honest scope note — what remains

This closes the "coprime factors of a square" step flagged as outstanding in
`FermatLastTheoremFiveCaseTwoDescentRecombination`'s module docstring. What is still **not** done
here is the genuinely novel Dirichlet/Legendre step: re-expressing the fact that `Q₄(p,q) = ±t²`
(coupled to `norm γ` via `q4_eq_normSq_add`) as a *new* pair `(p', q')` of strictly smaller height
satisfying an equation of the same shape, closing a well-founded recursion. That height-decreasing
re-parametrization is the remaining, unattempted piece.

**No `sorry`, no project axiom.**
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne GoldenInt

/-- **Peel the square from a coprime product.** If `IsCoprime a b` and `w² = ±(a·b)`, then each of
`a` and `b` is `±` a perfect square in `ℤ`. The `+` branch is `Int.sq_of_isCoprime` directly; the
`-` branch absorbs the sign by peeling `(-a)·b = w²` (still a genuine square) and unfolding
`-a = ±s²` back to `a = ±s²`. -/
theorem peel_pm_square {a b w : ℤ} (hcop : IsCoprime a b)
    (hw : w ^ 2 = a * b ∨ w ^ 2 = -(a * b)) :
    (∃ s : ℤ, a = s ^ 2 ∨ a = -s ^ 2) ∧ (∃ t : ℤ, b = t ^ 2 ∨ b = -t ^ 2) := by
  refine ⟨?_, ?_⟩
  · -- the `a` factor
    rcases hw with h | h
    · exact Int.sq_of_isCoprime hcop h.symm
    · obtain ⟨s, hs⟩ :=
        Int.sq_of_isCoprime (a := -a) (b := b) (c := w) hcop.neg_left (by linear_combination -h)
      refine ⟨s, ?_⟩
      rcases hs with h1 | h1
      · exact Or.inr (by linear_combination -h1)
      · exact Or.inl (by linear_combination -h1)
  · -- the `b` factor
    rcases hw with h | h
    · exact Int.sq_of_isCoprime (a := b) (b := a) (c := w) hcop.symm (by linear_combination -h)
    · obtain ⟨t, ht⟩ :=
        Int.sq_of_isCoprime (a := -b) (b := a) (c := w) hcop.symm.neg_left
          (by linear_combination -h)
      refine ⟨t, ?_⟩
      rcases ht with h1 | h1
      · exact Or.inr (by linear_combination -h1)
      · exact Or.inl (by linear_combination -h1)

/-- **Headline — each descent coordinate is `±` a square, WITH the connecting equation
retained.** For any genuine Case-II solution, there are integers `p, q, s, t` such that:
`p, q` are literally the coordinates of the pinned `γ = p+q·φ` from
`caseTwo_descent_equation_coprime` (via the retained descent equation
`(x+y)² = ±25·q·Q₄(p,q)`, connecting `p, q` back to `x, y, z`), `IsCoprime q Q₄(p,q)`,
`q = ±s²`, and `Q₄(p,q) = ±t²` (`Q₄(p,q) = p⁴+2p³q+4p²q²+3pq³+q⁴`).

An earlier draft of this theorem dropped the connecting equation from the conclusion,
making the statement provable by an unrelated constant witness (e.g. `p=1,q=0,s=0,t=1`)
regardless of `x,y,z` — a genuine vacuity bug caught by panel review. This version retains
`(x+y)² = ±25·q·Q₄(p,q)` explicitly, so `p, q` are pinned to the actual solution. -/
theorem caseTwo_q_and_Q4_each_pm_square {x y z : ℤ}
    (hxy : IsCoprime x y) (hz0 : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (p q s t : ℤ),
      ((x + y) ^ 2 = 25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4)
        ∨ (x + y) ^ 2
            = -(25 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4))) ∧
      IsCoprime q (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) ∧
      (q = s ^ 2 ∨ q = -s ^ 2) ∧
      ((p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) = t ^ 2 ∨
       (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4) = -t ^ 2) := by
  obtain ⟨p, q, hdesc, hcop⟩ := caseTwo_descent_equation_coprime hxy hz0 heq h5z
  obtain ⟨w, hw5⟩ := five_dvd_add_of_solution heq h5z
  set Q4 := p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 + 3 * p * q ^ 3 + q ^ 4 with hQ4def
  -- divide the descent equation by 25 to `w² = ± q·Q₄`
  have hwq : w ^ 2 = q * Q4 ∨ w ^ 2 = -(q * Q4) := by
    rcases hdesc with h | h
    · left
      have key : (25 : ℤ) * w ^ 2 = 25 * (q * Q4) := by
        have e : (x + y) ^ 2 = 25 * (q * Q4) := by rw [h]; ring
        rw [hw5] at e; linear_combination e
      exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) key
    · right
      have key : (25 : ℤ) * w ^ 2 = 25 * (-(q * Q4)) := by
        have e : (x + y) ^ 2 = 25 * (-(q * Q4)) := by rw [h]; ring
        rw [hw5] at e; linear_combination e
      exact mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) key
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := peel_pm_square hcop hwq
  exact ⟨p, q, s, t, hdesc, hcop, hs, ht⟩

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo
#print axioms peel_pm_square
#print axioms caseTwo_q_and_Q4_each_pm_square
end AxiomCheck
