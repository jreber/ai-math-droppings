import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.PrimeDescent
import Propositio.NumberTheory.Beal.CyclotomicFactor

/-!
# The `(p, p, z)` cyclotomic descent for higher primes `p ∈ {7,11,13,17,19}`

**NEW mathematics — no LaTTe sibling.** This file extends the `(p, p, z)`
cyclotomic descent (built in `BealPrimeDescent`, `BealPrimeDescentFive`) to the
higher primes `p = 7, 11, 13, 17, 19`. It is the precise documentation of the
boundary between the two halves of the descent for these primes:

* the **elementary prime-sum reduction** `prime_sum_descent_p` holds for *all*
  odd primes, hence for every one of `7, 11, 13, 17, 19` — these are proved here
  unconditionally; and
* the **cyclotomic power-extraction** `Φ_p = tᶻ ⟹ (A + ζ·B) ~ dᶻ` needs the ring
  of integers `𝓞 K = ℤ[ζ_p]` to be a principal ideal ring (Bézout), and **mathlib
  only provides that PID instance for `p = 3` and `p = 5`** (see the investigation
  finding below). So the power-extraction is *not* available for any of
  `7, 11, 13, 17, 19` in this mathlib, and we say so precisely.

## INVESTIGATION finding (mathlib's cyclotomic-PID coverage)

`Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean` provides **exactly two**
`IsPrincipalIdealRing (𝓞 K)` instances for prime cyclotomic fields:

  * `IsCyclotomicExtension.Rat.three_pid`
      `[IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K)`
  * `IsCyclotomicExtension.Rat.five_pid`
      `[IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K)`

The file's module doc states the result `ℤ[ζ_p]` is a PID *holds* for `p ≤ 19`
("but the proof is more and more involved"), yet **only `three_pid` and `five_pid`
are formalized**. There is:

  * **no** general lemma `IsCyclotomicExtension {p} ℚ K → IsPrincipalIdealRing (𝓞 K)`
    quantified over a range `p ≤ 19` (the "p ≤ 19" is a prose remark, not a
    quantified declaration);
  * **no** `seven_pid` / `eleven_pid` / `thirteen_pid` / `seventeen_pid` /
    `nineteen_pid` (grepping the whole mathlib for `*_pid` finds only `three_pid`
    and `five_pid` plus the unrelated `FreeModule/PID` and `Module/PID` API);
  * **no** cyclotomic class-number-`1` results in
    `Mathlib/NumberTheory/NumberField/ClassNumber.lean` beyond the generic
    `classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`
    machinery (which would still need a concrete `classNumber K = 1` input that
    mathlib does not supply for `p ≥ 7`).

**Conclusion.** mathlib's cyclotomic-PID coverage is `{3, 5}` only. Therefore the
cyclotomic power-extraction crux can be closed (as it is in
`BealEisensteinDescent` for `p = 3` and `BealPrimeDescentFive` for `p = 5`) for
**no** prime in `{7, 11, 13, 17, 19}`; for those primes the descent stops, in this
mathlib, at the elementary reduction.

## What this file proves

* **Unconditional, elementary — for ALL of `7, 11, 13, 17, 19`.**
  `prime_sum_descent_seven`, `…_eleven`, `…_thirteen`, `…_seventeen`,
  `…_nineteen`: the `p`-specialization of `BealPrimeDescent.prime_sum_descent`,
  with `Nat.Prime p` by `norm_num` and `Odd p` by `decide`. For coprime `A, B`
  with `p ∤ (A + B)` and `z ≠ 0`, `Aᵖ + Bᵖ = Cᶻ` forces `A + B = sᶻ`,
  `(Φ_p).toNat = tᶻ`, `C = s·t`.

* **Cyclotomic power-extraction — for NONE of them** (no `𝓞 K = ℤ[ζ_p]` PID
  instance in mathlib for `p ≥ 7`). We record the generic Bézout-domain engine
  `power_extraction_of_bezout` (identical to `BealPrimeDescentFive.five_power_extraction`),
  which *would* discharge the crux the moment a `seven_pid`-style instance appears,
  to make the precise gap explicit: it is the PID input, nothing else.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealPrimeDescentHigher.lean` to typecheck (cyclotomic imports ⟹ slow).
-/

namespace BealPrimeDescentHigher

open scoped NumberField
open Finset

/-!
## 1. The elementary `(p, p, z)` descent reduction for `p ∈ {7,11,13,17,19}`

Each is a direct specialization of `BealPrimeDescent.prime_sum_descent` at the
given prime, with `Nat.Prime p` by `norm_num` and `Odd p` by `decide`. These are
unconditional and require nothing from class-number / PID theory.
-/

/-- **`(7, 7, z)` prime-sum descent (elementary reduction, case `7 ∤ (A + B)`).**
For coprime naturals `A, B` with `7 ∤ (A + B)` and `z ≠ 0`, a solution
`A⁷ + B⁷ = Cᶻ` forces both factors of `(A + B)·Φ₇ = A⁷ + B⁷` to be perfect
`z`-th powers, with `C` their product:

  `∃ s t, A + B = sᶻ ∧ (Φ₇ A B).toNat = tᶻ ∧ C = s·t`.

This is `BealPrimeDescent.prime_sum_descent` at `p = 7`. Unconditional. -/
theorem prime_sum_descent_seven {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h7 : ¬ (7 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 7 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h7 hz h

/-- **`(11, 11, z)` prime-sum descent (elementary reduction, case `11 ∤ (A + B)`).**
`BealPrimeDescent.prime_sum_descent` at `p = 11`. Unconditional. -/
theorem prime_sum_descent_eleven {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h11 : ¬ (11 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 11 + B ^ 11 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 11 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h11 hz h

/-- **`(13, 13, z)` prime-sum descent (elementary reduction, case `13 ∤ (A + B)`).**
`BealPrimeDescent.prime_sum_descent` at `p = 13`. Unconditional. -/
theorem prime_sum_descent_thirteen {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h13 : ¬ (13 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 13 + B ^ 13 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 13 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h13 hz h

/-- **`(17, 17, z)` prime-sum descent (elementary reduction, case `17 ∤ (A + B)`).**
`BealPrimeDescent.prime_sum_descent` at `p = 17`. Unconditional. -/
theorem prime_sum_descent_seventeen {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h17 : ¬ (17 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 17 + B ^ 17 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 17 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h17 hz h

/-- **`(19, 19, z)` prime-sum descent (elementary reduction, case `19 ∤ (A + B)`).**
`BealPrimeDescent.prime_sum_descent` at `p = 19`. Unconditional. `19` is the top of
the range `p ≤ 19` for which `ℤ[ζ_p]` is (mathematically) a PID. -/
theorem prime_sum_descent_nineteen {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h19 : ¬ (19 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 19 + B ^ 19 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 19 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h19 hz h

/-!
## 2. The cyclotomic power-extraction crux — the precise PID gap for `p ≥ 7`

The power-extraction step `(A + ζ·B)·γ = tᶻ ∧ coprime ⟹ (A + ζ·B) ~ dᶻ` is, as for
`p = 3` and `p = 5`, *purely* a Bézout-domain fact: `exists_associated_pow_of_mul_eq_pow'`.
The generic engine below works in any commutative Bézout domain. The **only** thing
that blocks instantiating it at `𝓞 K = ℤ[ζ_p]` for `p ∈ {7,11,13,17,19}` is the
absence of a `seven_pid`-style `IsPrincipalIdealRing (𝓞 K)` instance in this
mathlib (only `three_pid`, `five_pid` exist). We therefore provide the engine — to
pin the gap to exactly the PID input — but deliberately state **no**
`associated_pow_cyclotomic_seven` etc.: there is no PID to discharge it with, so it
would necessarily carry the PID as an undischarged hypothesis, which is the opposite
of what `BealPrimeDescentFive.associated_pow_cyclotomic_five` achieves (PID
discharged by `five_pid`). The honest endpoint for `p ≥ 7` is the elementary
reduction in §1.
-/

/-- **Power extraction (generic Bézout domain).** In any commutative Bézout domain
`R`, if `α, β` are coprime and `α · β = c ^ z`, then `α` is a `z`-th power up to a
unit: `∃ d, Associated (dᶻ) α`. The engine is `exists_associated_pow_of_mul_eq_pow'`
(identical to `BealPrimeDescentFive.five_power_extraction`). It is the *complete*
power-extraction crux: once a `seven_pid` / `eleven_pid` / … instance exists in
mathlib, `𝓞 K = ℤ[ζ_p]` becomes a Bézout domain and this lemma closes the
cyclotomic extraction for that `p` verbatim, exactly as `five_pid` does for `p = 5`.
The fact that *no such instance exists in this mathlib for `p ≥ 7`* is the entire
reason the power-extraction is not available for `7, 11, 13, 17, 19` here. -/
theorem power_extraction_of_bezout {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    {α β c : R} {z : ℕ} (hcop : IsCoprime α β) (h : α * β = c ^ z) :
    ∃ d : R, Associated (d ^ z) α :=
  exists_associated_pow_of_mul_eq_pow' hcop h

end BealPrimeDescentHigher

/-!
## SUMMARY — the boundary, stated precisely

* **Elementary reduction: closed for every prime `p ∈ {7,11,13,17,19}`.**
  `prime_sum_descent_seven`, `…_eleven`, `…_thirteen`, `…_seventeen`,
  `…_nineteen` are all proved, no `sorry`, by specializing
  `BealPrimeDescent.prime_sum_descent`. The reduction
  `Aᵖ + Bᵖ = Cᶻ ⟹ A + B = sᶻ ∧ (Φ_p).toNat = tᶻ ∧ C = s·t` (case `p ∤ (A+B)`) is
  unconditional for *all* odd primes, so nothing about `p ≥ 7` obstructs it.

* **Cyclotomic power-extraction: closed for NONE of `{7,11,13,17,19}`.** mathlib's
  `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean` supplies the PID instance
  `IsPrincipalIdealRing (𝓞 K)` only for `p = 3` (`three_pid`) and `p = 5`
  (`five_pid`). There is **no** general `p ≤ 19` PID lemma and **no** `seven_pid`/
  `eleven_pid`/`thirteen_pid`/`seventeen_pid`/`nineteen_pid`. So the Bézout
  hypothesis that the engine `power_extraction_of_bezout` (= `five_power_extraction`)
  requires cannot be discharged for `p ≥ 7`, and we state no
  `associated_pow_cyclotomic_p` for these primes (it would necessarily carry an
  undischarged PID hypothesis, unlike the `p = 5` lemma, which discharges it).

* **General-lemma question.** Asked: is there a single
  `associated_pow_cyclotomic_of_pid {p} [Fact p.Prime] [the PID instance] …`
  covering `p ≤ 19` at once? **No** — because there is no general PID instance in
  mathlib to feed it. The generic `power_extraction_of_bezout` is exactly that
  "single lemma", but parameterized over an *arbitrary Bézout domain* `R` rather
  than over `𝓞 K` for `p ≤ 19`, precisely because the per-`p` PID instances that
  would let one phrase it over `𝓞 K` do not exist beyond `p = 5`.

The boundary is therefore: **elementary reduction for all of `7,11,13,17,19`;
cyclotomic power-extraction for none of them, blocked solely by the missing
`ℤ[ζ_p]`-PID instance (mathlib's cyclotomic-PID coverage is `{3, 5}`).**
-/
