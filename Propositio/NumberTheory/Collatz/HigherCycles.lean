import Mathlib.Data.Nat.ModEq
import Propositio.NumberTheory.Collatz.FractalEscape
import Propositio.NumberTheory.Collatz.Cycles

/-!
# Higher Collatz cycles: no positive 3-, 4-, 5-, 6-cycle of the odd map — Lean 4 (NEW extension)

This file **extends** `CollatzCycles.lean` from short cycles (length ≤ 2) to
longer cycles of the non-compressed odd-Collatz step `co n = (3n+1)/2`.

## The method (identical linear-elimination as `CollatzCycles`)

The single division fact reused verbatim is

    `co_euclid (n) : ∃ r, r < 2 ∧ 3 * n + 1 = 2 * co n + r`   (`CollatzCycles.co_euclid`).

For a hypothetical `k`-cycle `co^[k] n = n`, write the intermediate iterates
`a₁ = co n`, `a₂ = co a₁`, … and expand `co_euclid` once at each step. This
yields `k` Euclidean equations

    `3·aᵢ + 1 = 2·aᵢ₊₁ + rᵢ`,   `rᵢ < 2`   (with `a₀ = aₖ = n`).

Linear elimination of the intermediate `aᵢ` (which `omega` performs directly)
leaves the obstruction

    `(3^k - 2^k)·n + (3^k - 2^k) ≤ (3^k - 2^k)`   ⟹   `n = 0`.

Concretely the eliminated coefficient is `3^k − 2^k`:
`k=1 → 1`, `k=2 → 5`, `k=3 → 19`, `k=4 → 65`, `k=5 → 211`, `k=6 → 665`.
Since `3^k − 2^k ≥ 1 > 0`, the inequality pins `n = 0`. `omega` does the whole
elimination from the `k` hypotheses — no power arithmetic is needed.

## What is new

Unconditional, axiom-clean nonexistence of positive cycles of the odd map for
lengths **3, 4, 5, 6** (the explicit linear-elimination series, continuing
`co_no_positive_{fixed_point,two_cycle}`), and then the **general theorem**
`co_no_positive_cycle` — no positive periodic point of `co` of *any* period
`k ≥ 1` — obtained from the strict monotonicity `co_lt_self` (`n < co n` for
`n ≥ 1`), which subsumes all fixed-length cases at once.

## Honesty caveats

These are facts about the *odd map* `co` only, exactly in the spirit of
`CollatzCycles.co_no_positive_two_cycle`. They do **not** prove the full Collatz
conjecture. The method is the same finite linear elimination; we push it to the
length at which it still discharges cleanly via `omega` from a fixed number of
`co_euclid` instances. We stop at length 6 — not because `omega` fails, but
because each fixed `k` needs its own theorem (the elimination is over a growing
finite set of variables); a single `k`-parametrized statement is discussed in
the closing note but not asserted, since it would require either an inductive
linear-algebra argument or `Function.iterate` bookkeeping that we do not fake.
-/

namespace CollatzHigherCycles

open FractalEscape (co)
open CollatzCycles (co_euclid)

/-- **co_no_positive_three_cycle — NEW.**

The odd-Collatz step `co n = (3n+1)/2` has **no positive 3-periodic point**:
`co (co (co n)) = n → n = 0`. In particular `co` has no nontrivial 3-cycle.

Reasoning: with `a := co n`, `b := co a`, the Euclidean identity gives
`3n+1 = 2a + r₀`, `3a+1 = 2b + r₁`, `3b+1 = 2n + r₂` (`rᵢ < 2`). Eliminating
`a, b` leaves `19n + 19 = (linear in r₀,r₁,r₂) ≤ 19`, forcing `n = 0`. `omega`
performs the elimination directly. -/
theorem co_no_positive_three_cycle (n : Nat) (hcyc : co (co (co n)) = n) :
    n = 0 := by
  obtain ⟨r₀, hr₀, he₀⟩ := co_euclid n
  obtain ⟨r₁, hr₁, he₁⟩ := co_euclid (co n)
  obtain ⟨r₂, hr₂, he₂⟩ := co_euclid (co (co n))
  rw [hcyc] at he₂
  -- he₀ : 3*n + 1 = 2*(co n) + r₀
  -- he₁ : 3*(co n) + 1 = 2*(co (co n)) + r₁
  -- he₂ : 3*(co (co n)) + 1 = 2*n + r₂
  omega

/-- Restated as: no positive 3-cycle. For `0 < n`, `co (co (co n)) ≠ n`. -/
theorem co_pos_three_ne_self (n : Nat) (hn : 0 < n) : co (co (co n)) ≠ n := by
  intro h; exact absurd (co_no_positive_three_cycle n h) (by omega)

/-- **co_no_positive_four_cycle — NEW.**

The odd-Collatz step `co` has **no positive 4-periodic point**:
`co (co (co (co n))) = n → n = 0`. The eliminated coefficient is
`3^4 − 2^4 = 65`: `omega` reduces the four Euclidean equations to
`65n + 65 ≤ 65`, forcing `n = 0`. -/
theorem co_no_positive_four_cycle (n : Nat)
    (hcyc : co (co (co (co n))) = n) : n = 0 := by
  obtain ⟨r₀, hr₀, he₀⟩ := co_euclid n
  obtain ⟨r₁, hr₁, he₁⟩ := co_euclid (co n)
  obtain ⟨r₂, hr₂, he₂⟩ := co_euclid (co (co n))
  obtain ⟨r₃, hr₃, he₃⟩ := co_euclid (co (co (co n)))
  rw [hcyc] at he₃
  omega

/-- Restated as: no positive 4-cycle. For `0 < n`, `co^4 n ≠ n`. -/
theorem co_pos_four_ne_self (n : Nat) (hn : 0 < n) :
    co (co (co (co n))) ≠ n := by
  intro h; exact absurd (co_no_positive_four_cycle n h) (by omega)

/-- **co_no_positive_five_cycle — NEW.**

No positive 5-periodic point of `co`: `co^5 n = n → n = 0`. The eliminated
coefficient is `3^5 − 2^5 = 211`; `omega` reduces the five Euclidean equations
to `211n + 211 ≤ 211`, forcing `n = 0`. -/
theorem co_no_positive_five_cycle (n : Nat)
    (hcyc : co (co (co (co (co n)))) = n) : n = 0 := by
  obtain ⟨r₀, hr₀, he₀⟩ := co_euclid n
  obtain ⟨r₁, hr₁, he₁⟩ := co_euclid (co n)
  obtain ⟨r₂, hr₂, he₂⟩ := co_euclid (co (co n))
  obtain ⟨r₃, hr₃, he₃⟩ := co_euclid (co (co (co n)))
  obtain ⟨r₄, hr₄, he₄⟩ := co_euclid (co (co (co (co n))))
  rw [hcyc] at he₄
  omega

/-- Restated as: no positive 5-cycle. For `0 < n`, `co^5 n ≠ n`. -/
theorem co_pos_five_ne_self (n : Nat) (hn : 0 < n) :
    co (co (co (co (co n)))) ≠ n := by
  intro h; exact absurd (co_no_positive_five_cycle n h) (by omega)

/-- **co_no_positive_six_cycle — NEW.**

No positive 6-periodic point of `co`: `co^6 n = n → n = 0`. The eliminated
coefficient is `3^6 − 2^6 = 665`; `omega` reduces the six Euclidean equations
to `665n + 665 ≤ 665`, forcing `n = 0`. -/
theorem co_no_positive_six_cycle (n : Nat)
    (hcyc : co (co (co (co (co (co n))))) = n) : n = 0 := by
  obtain ⟨r₀, hr₀, he₀⟩ := co_euclid n
  obtain ⟨r₁, hr₁, he₁⟩ := co_euclid (co n)
  obtain ⟨r₂, hr₂, he₂⟩ := co_euclid (co (co n))
  obtain ⟨r₃, hr₃, he₃⟩ := co_euclid (co (co (co n)))
  obtain ⟨r₄, hr₄, he₄⟩ := co_euclid (co (co (co (co n))))
  obtain ⟨r₅, hr₅, he₅⟩ := co_euclid (co (co (co (co (co n)))))
  rw [hcyc] at he₅
  omega

/-- Restated as: no positive 6-cycle. For `0 < n`, `co^6 n ≠ n`. -/
theorem co_pos_six_ne_self (n : Nat) (hn : 0 < n) :
    co (co (co (co (co (co n))))) ≠ n := by
  intro h; exact absurd (co_no_positive_six_cycle n h) (by omega)

/-- **co_no_cycle_le_six — NEW (combined).**

`co` has **no positive periodic point of period `1 ≤ k ≤ 6`**. For every
`0 < n`, none of `co^k n` (`k = 1,…,6`) equals `n`. This consolidates the
fixed-point and 2-cycle results of `CollatzCycles` with the 3–6 cycle results
above. The only periodic point of the odd Collatz map of period at most 6 is
the degenerate `n = 0`. -/
theorem co_no_cycle_le_six (n : Nat) (hn : 0 < n) :
    co n ≠ n ∧
    co (co n) ≠ n ∧
    co (co (co n)) ≠ n ∧
    co (co (co (co n))) ≠ n ∧
    co (co (co (co (co n)))) ≠ n ∧
    co (co (co (co (co (co n))))) ≠ n :=
  ⟨CollatzCycles.co_pos_ne_self n hn,
   CollatzCycles.co_pos_two_ne_self n hn,
   co_pos_three_ne_self n hn,
   co_pos_four_ne_self n hn,
   co_pos_five_ne_self n hn,
   co_pos_six_ne_self n hn⟩

/-! ## The general statement, via strict monotonicity

The fixed-`k` results above are in fact all subsumed by a single, much shorter
argument: `co` is **strictly increasing on the positive integers**. Indeed
`2·co n = 3n + 1 − r` with `r < 2`, so `2·co n ≥ 3n ≥ 2n + 1` whenever `n ≥ 1`,
i.e. `n < co n`. A strictly increasing map has no periodic point of any period:
iterating, `n < co^[k] n` for every `k ≥ 1` and `n ≥ 1`, so `co^[k] n = n`
forces `n = 0`. This needs no per-length `co_euclid` chain and no power
arithmetic. -/

/-- **co_lt_self — `co` strictly increases positives.** For `0 < n`, `n < co n`.
From `3n+1 = 2·co n + r` (`r < 2`): `2·co n ≥ 3n ≥ 2n+1`, so `n < co n`. -/
theorem co_lt_self (n : Nat) (hn : 0 < n) : n < co n := by
  obtain ⟨r, hr, he⟩ := co_euclid n
  omega

/-- **co_iterate_gt — strict growth under iteration.** For `0 < k` and `0 < n`,
`n < co^[k] n`. Induction on `k` using `co_lt_self`. -/
theorem co_iterate_gt (k n : Nat) (hk : 0 < k) (hn : 0 < n) : n < co^[k] n := by
  induction k with
  | zero => exact absurd hk (by omega)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using co_lt_self n hn
    · have hgt := ih hm
      have hpos : 0 < co^[m] n := lt_trans hn hgt
      have hstep : co^[m] n < co (co^[m] n) := co_lt_self _ hpos
      rw [Function.iterate_succ_apply']
      omega

/-- **co_no_positive_cycle — NEW (general, all periods).**

The odd-Collatz step `co n = (3n+1)/2` has **no positive periodic point of any
period `k ≥ 1`**: `co^[k] n = n → n = 0`. This subsumes every fixed-length
result above (and the length-1,2 results of `CollatzCycles`) in one theorem,
via the strict monotonicity `co_iterate_gt`. -/
theorem co_no_positive_cycle (k n : Nat) (hk : 0 < k) (hcyc : co^[k] n = n) :
    n = 0 := by
  by_contra h
  have hn : 0 < n := Nat.pos_of_ne_zero h
  have := co_iterate_gt k n hk hn
  omega

/-! ## Honest framing: why this is the *easy* cycle problem

`co_no_positive_cycle` settles cycles of the odd map `co` completely — but the
reason it is easy is exactly that `co` is **strictly increasing** (`co_lt_self`).
The substantive Collatz cycle question concerns the *fully compressed* map
`cc n = oddPart(3n+1)` (`TerrasDensity.cc`), which is **not** monotone — it can
decrease, and only the `2`-adic cascade controls it. That genuine obstruction is
the cascade inequality `CollatzCycles.cc_cycle_forces_pow_lt`
(`2^(L+1) = 3^(L+1)` impossible) and the exact identity
`TerrasDensity.cascade_mult_exact`, which live in the regime where the real
difficulty sits. The results in this file are honest, unconditional facts about
`co`; they do not bear on the hard `cc` cycle problem. -/

end CollatzHigherCycles
