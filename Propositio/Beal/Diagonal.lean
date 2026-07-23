import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic

/-!
# Beal's equal-exponent diagonal `(n, n, n)` IS Fermat's Last Theorem for `n`

The Beal conjecture concerns `A^x + B^y = C^z` with `x, y, z ≥ 3`; its **equal-exponent
diagonal** is the special case `x = y = z = n`, i.e. `A^n + B^n = C^n`. This is *exactly*
Fermat's Last Theorem for the exponent `n`. mathlib proves FLT unconditionally for `n = 3`
(`fermatLastTheoremThree`) and `n = 4` (`fermatLastTheoremFour`), and the monotonicity lemma
`FermatLastTheoremFor.mono : m ∣ n → FermatLastTheoremFor m → FermatLastTheoremFor n`
propagates each proven case to *every* multiple of its exponent.

Consequently the Beal equal-exponent case is closed unconditionally for every `n` divisible by
`3` or `4` — the infinite family `3, 4, 6, 8, 9, 12, 15, 16, …`. This is the **only** infinite
family of Beal exponent triples currently closed unconditionally in mathlib (the general Beal
conjecture, with mixed exponents `x, y, z`, remains open).

## Contents
* `beal_diag_three` — `A³ + B³ ≠ C³`, direct from `fermatLastTheoremThree`.
* `beal_diag_four` — `A⁴ + B⁴ ≠ C⁴`, direct from `fermatLastTheoremFour`.
* `beal_diagonal` — **HEADLINE.** For every `n` with `3 ∣ n ∨ 4 ∣ n` and nonzero `A, B, C`,
  `A^n + B^n ≠ C^n`. Proved via `FermatLastTheoremFor.mono`.
* `beal_diagonal_no_coprime_hypothesis` — the diagonal needs no `gcd(A, B, C) = 1` hypothesis,
  because FLT is unconditional.
* `beal_diag_coprime` — the same statement restated with an explicit `Nat.Coprime A B`
  primitivity hypothesis (to match the usual Beal phrasing), derived trivially from
  `beal_diagonal` by discarding the hypothesis.

Key mathlib lemmas relied on:
* `fermatLastTheoremThree : FermatLastTheoremFor 3`.
* `fermatLastTheoremFour : FermatLastTheoremFor 4`.
* `FermatLastTheoremFor.mono : m ∣ n → FermatLastTheoremFor m → FermatLastTheoremFor n`.
* `FermatLastTheoremFor n` unfolds (via `FermatLastTheoremWith ℕ n`) to
  `∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealDiagonal.lean` to typecheck.
-/

namespace BealDiagonal

/-!
## Part 1 — the two base cases, straight from mathlib's proven FLT

`fermatLastTheoremThree : FermatLastTheoremFor 3` and `fermatLastTheoremFour :
FermatLastTheoremFor 4` each unfold (definitionally, via `FermatLastTheoremFor n =
FermatLastTheoremWith ℕ n`) to `∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n`.
The Beal equal-exponent cases at `n = 3` and `n = 4` are therefore *exactly* these theorems,
and they are unconditional: no coprimality or common-factor hypothesis is needed.
-/

/-- **Beal diagonal at `n = 3`**: `A³ + B³ ≠ C³` for nonzero `A, B, C`, straight from
mathlib's `fermatLastTheoremThree`. Unconditional (no coprimality needed). -/
theorem beal_diag_three {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 3 + B ^ 3 ≠ C ^ 3 :=
  fermatLastTheoremThree A B C hA hB hC

/-- **Beal diagonal at `n = 4`**: `A⁴ + B⁴ ≠ C⁴` for nonzero `A, B, C`, straight from
mathlib's `fermatLastTheoremFour`. Unconditional (no coprimality needed). -/
theorem beal_diag_four {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ 4 + B ^ 4 ≠ C ^ 4 :=
  fermatLastTheoremFour A B C hA hB hC

/-!
## Part 2 — the HEADLINE: the diagonal for every multiple of `3` or `4`

`FermatLastTheoremFor.mono (hmn : m ∣ n) : FermatLastTheoremFor m → FermatLastTheoremFor n`
lifts a proven exponent to all of its multiples (because an `n`-th-power solution with `m ∣ n`
is, after regrouping, an `m`-th-power solution). Applying it to `fermatLastTheoremThree` and
`fermatLastTheoremFour` closes the diagonal for the whole infinite family of exponents divisible
by `3` or `4`.
-/

/-- **HEADLINE — Beal's equal-exponent diagonal for every `n` divisible by `3` or `4`.**

For every exponent `n` with `3 ∣ n` or `4 ∣ n`, and every nonzero `A, B, C`,
`A ^ n + B ^ n ≠ C ^ n`. This is Fermat's Last Theorem for `n`, obtained from mathlib's
unconditional `fermatLastTheoremThree` / `fermatLastTheoremFour` by `FermatLastTheoremFor.mono`.
The resulting set of exponents is the infinite family `3, 4, 6, 8, 9, 12, 15, 16, …` — the only
infinite family of Beal exponent triples currently closed unconditionally in mathlib. -/
theorem beal_diagonal {n : ℕ} (hn : 3 ∣ n ∨ 4 ∣ n)
    {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n := by
  rcases hn with h3 | h4
  · exact (fermatLastTheoremThree.mono h3) A B C hA hB hC
  · exact (fermatLastTheoremFour.mono h4) A B C hA hB hC

/-!
## Part 3 — corollaries: no coprimality hypothesis is needed

The Beal conjecture is usually phrased with a primitivity hypothesis `gcd(A, B, C) = 1`. On the
equal-exponent diagonal this hypothesis is *vacuous*: FLT — hence `beal_diagonal` — holds for all
nonzero `A, B, C`, coprime or not. A hypothetical common factor cannot rescue a solution, because
there is none.
-/

/-- **The diagonal needs no coprimality / common-factor hypothesis.**
`beal_diagonal` holds for *all* nonzero `A, B, C` — in particular it holds even when an explicit
primitivity hypothesis `Nat.Coprime A B` is *available but unused*. This records that FLT is
unconditional: the diagonal is closed whether or not `A, B, C` share a common factor. -/
theorem beal_diagonal_no_coprime_hypothesis {n : ℕ} (hn : 3 ∣ n ∨ 4 ∣ n)
    {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (_hcop : Nat.Coprime A B) :
    A ^ n + B ^ n ≠ C ^ n :=
  beal_diagonal hn hA hB hC

/-- **Beal diagonal, primitivity-phrased.** The same statement carrying an explicit
`Nat.Coprime A B` hypothesis to match the usual Beal phrasing; it follows trivially from
`beal_diagonal`, which simply discards the (unnecessary) coprimality assumption. -/
theorem beal_diag_coprime {n : ℕ} (hn : 3 ∣ n ∨ 4 ∣ n)
    {A B C : ℕ} (hcop : Nat.Coprime A B) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    A ^ n + B ^ n ≠ C ^ n :=
  beal_diagonal_no_coprime_hypothesis hn hA hB hC hcop

end BealDiagonal
