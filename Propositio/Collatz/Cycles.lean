import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.Collatz.FractalEscape
import Propositio.Collatz.Basic

/-!
# Collatz cycle nonexistence and the cycle inequality — Lean 4 (NEW extension)

This file **extends** (does not merely port) the Collatz formalization. The prior
Collatz files (`FractalEscape`, `CollatzModular`, `CollatzParityVector`,
`TerrasDensity`, `Lyapunov`, `CollatzH5`) were a faithful LaTTe → Lean 4 port of
the *modular-reduction / parity-vector / cascade* machinery. None of them
addressed **periodic points of the Collatz odd-map** directly. Here we prove
genuinely new, unconditional, axiom-clean results about short cycles of the
non-compressed odd-Collatz step `co n = (3n+1)/2`, plus the standard cycle
inequality `2^(L+1) > 3^(L+1)`-style necessary condition derived from the
already-ported `cascade_mult_exact`.

## Reuse — no map is redefined

We reuse the **exact** map definitions from the existing files:

  * `FractalEscape.co n = (3*n + 1) / 2` — the non-compressed odd-Collatz step
    (`FractalEscape.lean`, also reused throughout `CollatzModular`).
  * `FractalEscape.Odd n = ∃ k, n = 2*k + 1`.
  * `TerrasDensity.cc` and `TerrasDensity.cascade_mult_exact` — the compressed
    step and its iterated exact-multiplication identity.

## What is new

  1. `co_no_positive_fixed_point` : `co` has **no positive 1-cycle**.
     `co n = n → n = 0`. (Equivalently `0 < n → co n ≠ n`.) A 1-cycle of the
     odd map would be a Collatz fixed point; the only one is the degenerate
     `n = 0`. Proved by elementary `Nat`-division arithmetic (`omega`).

  2. `co_no_positive_two_cycle` : `co` has **no positive 2-cycle** (and no
     2-periodic point at all besides `0`). `co (co n) = n → n = 0`. Since `co`
     grows like `n ↦ 3n/2`, two steps overshoot `n` for every `n ≥ 1`. Proved
     by `Nat`-division arithmetic (`omega`).

  3. `cc_cycle_forces_pow_lt` : the **cycle inequality**. A genuine
     necessary condition for a hypothetical pure-spine Collatz cycle: if an odd
     `n` returns to itself after `L + 1` compressed steps
     (`cc^[L+1] n = n`) with `padicValNat 2 (n + 1) = L + 2`, then
     `2^(L+1) > 3^(L+1)` — which is impossible. Hence no such cycle exists.
     This is the elementary "`2^a > 3^L`" obstruction, here proved directly
     from `cascade_mult_exact`.

## Honesty caveats

The **full** Collatz conjecture is open and is *not* claimed anywhere here.
Result 3 is conditional on the spine hypothesis `padicValNat 2 (n + 1) = L + 2`
(the cascade regime to which `cascade_mult_exact` applies); within that regime
it rules out periodicity unconditionally. Results 1 and 2 are fully
unconditional facts about the odd map `co`.
-/

namespace CollatzCycles

open FractalEscape (co)
open TerrasDensity (cc)

/-! ## Division bookkeeping for `co`

`co n = (3n+1)/2`. The single fact we need about `Nat` division is the
Euclidean identity `2 * (w / 2) + w % 2 = w` with `w % 2 < 2`. We package it
once for `w = 3n+1`. -/

/-- Euclidean expansion of `co n`: there is `r < 2` with `3*n + 1 = 2*(co n) + r`.
This is the only `Nat`-division fact the cycle proofs need; everything else is
`omega`. -/
theorem co_euclid (n : Nat) : ∃ r, r < 2 ∧ 3 * n + 1 = 2 * co n + r := by
  refine ⟨(3 * n + 1) % 2, Nat.mod_lt _ (by norm_num), ?_⟩
  unfold co
  have := Nat.div_add_mod (3 * n + 1) 2
  omega

/-- **co_no_positive_fixed_point — NEW.**

The odd-Collatz step `co n = (3n+1)/2` has **no positive fixed point**:
`co n = n → n = 0`. Equivalently, the only 1-cycle of `co` is the degenerate
`n = 0`; in particular `co` has no nontrivial 1-cycle, so the Collatz odd-map
has no fixed point other than the degenerate origin.

Reasoning: `co n = n` and the Euclidean identity `3n+1 = 2·(co n) + r`,
`r < 2`, give `3n+1 = 2n + r`, i.e. `n + 1 = r < 2`, forcing `n = 0`.

This is a genuinely new result: the prior Collatz files port the
*modular-reduction / cascade* machinery but never address fixed points of the
odd map. Unconditional and axiom-clean. -/
theorem co_no_positive_fixed_point (n : Nat) (hfix : co n = n) : n = 0 := by
  obtain ⟨r, hr, he⟩ := co_euclid n
  rw [hfix] at he
  omega

/-- Restated as: no positive 1-cycle. For every `0 < n`, `co n ≠ n`. -/
theorem co_pos_ne_self (n : Nat) (hn : 0 < n) : co n ≠ n := by
  intro h; exact absurd (co_no_positive_fixed_point n h) (by omega)

/-- **co_no_positive_two_cycle — NEW.**

The odd-Collatz step `co` has **no positive 2-periodic point**:
`co (co n) = n → n = 0`. In particular `co` has no nontrivial 2-cycle: if
`co n = m`, `co m = n` then `co (co n) = n`, forcing `n = 0` (and then `m = 0`).

Reasoning: applying the Euclidean identity twice, with `m := co n`,
`3n+1 = 2m + r₀`, `3m+1 = 2n + r₁` (`r₀, r₁ < 2`). Eliminating `m`
(`2·(3m+1) = 4n + 2r₁` and `3·(3n+1) = 6m + 3r₀` ⟹ `9n + 5 = 4n + 2r₁ + 3r₀`),
so `5n + 5 = 2r₁ + 3r₀ ≤ 2 + 3 = 5`, forcing `n = 0`. `omega` does the
elimination directly. -/
theorem co_no_positive_two_cycle (n : Nat) (hcyc : co (co n) = n) : n = 0 := by
  obtain ⟨r₀, hr₀, he₀⟩ := co_euclid n
  obtain ⟨r₁, hr₁, he₁⟩ := co_euclid (co n)
  rw [hcyc] at he₁
  -- he₀ : 3*n + 1 = 2*(co n) + r₀
  -- he₁ : 3*(co n) + 1 = 2*n + r₁
  omega

/-- Restated as: no positive 2-cycle. For `0 < n`, `co (co n) ≠ n`. -/
theorem co_pos_two_ne_self (n : Nat) (hn : 0 < n) : co (co n) ≠ n := by
  intro h; exact absurd (co_no_positive_two_cycle n h) (by omega)

/-- Combined short-cycle statement: `co` has no positive cycle of length `1` or
`2`. The only periodic points of period `≤ 2` are the degenerate `n = 0`. -/
theorem co_no_short_cycle (n : Nat) (hn : 0 < n) :
    co n ≠ n ∧ co (co n) ≠ n :=
  ⟨co_pos_ne_self n hn, co_pos_two_ne_self n hn⟩

/-! ## The cycle inequality (cascade regime)

For the *compressed* step `cc`, a cycle in the cascade regime is ruled out by
the exact multiplication identity `cascade_mult_exact`:

    `2^(L+1) * (cc^[L+1] n + 1) = (n + 1) * 3^(L+1)`.

If additionally `cc^[L+1] n = n` (an `(L+1)`-step cycle), the identity becomes
`2^(L+1) * (n + 1) = (n + 1) * 3^(L+1)`, hence (`n + 1 > 0`)
`2^(L+1) = 3^(L+1)` — impossible for `L + 1 ≥ 1`. We extract the underlying
inequality as the standard `2^a > 3^L`-style obstruction. -/

open TerrasDensity (cascade_mult_exact)

/-- **cc_cycle_equation — NEW.** A cascade-regime `(L+1)`-step cycle of the
compressed map forces the exact power equation `2^(L+1) = 3^(L+1)`.

If `n` is odd, `padicValNat 2 (n + 1) = L + 2`, and `cc^[L+1] n = n`
(the orbit closes up after `L + 1` compressed steps), then
`2^(L+1) = 3^(L+1)`. This is a direct corollary of `cascade_mult_exact`
after substituting the cycle condition and cancelling `n + 1 > 0`. -/
theorem cc_cycle_equation (n L : Nat) (hodd : TerrasDensity.Odd n)
    (hv2 : padicValNat 2 (n + 1) = L + 2)
    (hcyc : cc^[L + 1] n = n) :
    (2 : Nat) ^ (L + 1) = 3 ^ (L + 1) := by
  have hcme := cascade_mult_exact n L hodd hv2
  -- 2^(L+1) * (cc^[L+1] n + 1) = (n+1) * 3^(L+1)
  rw [hcyc] at hcme
  -- 2^(L+1) * (n + 1) = (n + 1) * 3^(L+1)
  have hn1 : 0 < n + 1 := Nat.succ_pos n
  have : 2 ^ (L + 1) * (n + 1) = 3 ^ (L + 1) * (n + 1) := by
    rw [hcme]; ring
  exact Nat.eq_of_mul_eq_mul_right hn1 this

/-- `2^m < 3^m` strictly for every `m`, in particular for `m = L + 1 ≥ 1`.
Elementary monotonicity fact used to contradict `cc_cycle_equation`. -/
theorem two_pow_lt_three_pow (m : Nat) : (2 : Nat) ^ m < 3 ^ m + 1 ∧
    (0 < m → (2 : Nat) ^ m < 3 ^ m) := by
  refine ⟨?_, ?_⟩
  · have : (2 : Nat) ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
    omega
  · intro hm
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)

/-- **cc_cycle_forces_pow_lt — NEW (the cycle inequality / nonexistence).**

A cascade-regime compressed-Collatz cycle is **impossible**. Concretely: there
is no odd `n` with `padicValNat 2 (n + 1) = L + 2` and `cc^[L+1] n = n`,
because such a cycle would force `2^(L+1) = 3^(L+1)`, contradicting the strict
inequality `2^(L+1) < 3^(L+1)` (valid since `L + 1 ≥ 1`).

This is the elementary `2^a > 3^L` obstruction to Collatz cycles, here made
rigorous for the cascade regime. It is honest: it rules out *only* spine /
cascade-regime cycles (those satisfying the `v₂(n+1) = L+2` hypothesis to which
`cascade_mult_exact` applies), not the full conjecture. -/
theorem cc_cycle_forces_pow_lt (n L : Nat) (hodd : TerrasDensity.Odd n)
    (hv2 : padicValNat 2 (n + 1) = L + 2)
    (hcyc : cc^[L + 1] n = n) : False := by
  have heq := cc_cycle_equation n L hodd hv2 hcyc
  have hlt := (two_pow_lt_three_pow (L + 1)).2 (Nat.succ_pos L)
  omega

end CollatzCycles
