import Propositio.NumberTheory.Collatz.CycleTelescope

/-!
# Closed form for the Steiner numerator

The Steiner numerator `Steiner n L` (from `CollatzCycleTelescope`, satisfying `Steiner n 0 = 0`,
`Steiner n (L+1) = 3·Steiner n L + 2^{S n L}`) has the explicit closed form

  `Steiner n L = ∑_{i < L} 3^{L-1-i} · 2^{S n i}`.

This is the reusable explicit numerator behind every later Collatz cycle / divisibility lemma
(a cycle of length `L` forces `(2^{S n L} − 3^L) ∣ Steiner n L`).  Identified by the 8-branch
roadmap (branch B8) as a clean compounding-library win; its payoff for cycle-exclusion still
reduces to the `2^m`-vs-`3^a` wall, but the lemma itself is a few-line induction and axiom-clean.
-/

namespace CollatzCycleTelescope

open scoped BigOperators

/-- **Closed form for the Steiner numerator:** `Steiner n L = ∑_{i<L} 3^{L-1-i}·2^{S n i}`. -/
theorem Steiner_closed_form (n L : Nat) :
    Steiner n L = ∑ i ∈ Finset.range L, 3 ^ (L - 1 - i) * 2 ^ S n i := by
  induction L with
  | zero => simp [Steiner]
  | succ L ih =>
    rw [Steiner_succ, ih, Finset.sum_range_succ, Finset.mul_sum]
    have hlast : (L + 1) - 1 - L = 0 := by omega
    rw [hlast, pow_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have he : (L + 1) - 1 - i = (L - 1 - i) + 1 := by omega
    rw [he, pow_succ]
    ring

end CollatzCycleTelescope
