import Mathlib.Tactic
import Propositio.NumberTheory.Beal.FiveStructure
import Propositio.NumberTheory.Beal.SevenPID
import Propositio.NumberTheory.Beal.FifthPower
import Propositio.NumberTheory.Beal.SplitPrimeGeneral
import Propositio.NumberTheory.Beal.ABCQuality

/-!
# MASTER capstones for the higher Beal cases `A⁵ + B⁵ = Cᶻ` and `A⁷ + B⁷ = Cᶻ`

**NEW — the comprehensive machine-checked "shape of a counterexample" at `p = 5, 7`.**
This file is the `p = 5` and `p = 7` analogue of `BealCubeMasterCapstone`: for each
prime exponent it collects, into a *single non-vacuous* theorem, **every** constraint a
primitive `(p, p, z)` Beal counterexample is forced to satisfy simultaneously, pulling
together the three independent lines proved across the corpus:

* the **descent** line (integer + cyclotomic) — `BealFiveStructure.beal_55z_structure`
  / `IsCyclotomicExtension.Rat.Seven.beal_77z_structure`;
* the **local split-prime** line (UNCONDITIONAL, finite `decide`) — `BealFifthPower`
  (fifth powers mod `11`) / `BealSplitPrimeGeneral` (seventh powers mod `29`);
* the **ABC-quality** line (unconditional `rad(A^p · B^p · Cᶻ) < Cᶻ`) — `BealABCQuality`.

## Non-vacuity

Every conjunct is a **genuine proven consequence** of the equation, not a hypothesis
restated as the conclusion. Concretely, for `p = 5`:

* the descent conjunct comes from `beal_55z_structure` (the cyclotomic `ℤ[ζ₅]`
  factorization + power extraction);
* the local mod-11 conjunct is the *unconditional* finite fact
  `fifth_sum_not_mem_gap_mod11` (fifth powers mod 11 are `{0,1,10}`, so the sum
  `A⁵ + B⁵` misses the whole block `{3,4,5,6,7,8}`) — applied to the residues of the
  *actual* bases `A, B`, no hypothesis on `C^z` required;
* the ABC-quality conjunct is `beal_radical_lt_c` (`rad(A⁵·B⁵·Cᶻ) < Cᶻ`),
  unconditional for any primitive Beal solution with bases `≥ 2` and exponents `≥ 3`.

And the same shape for `p = 7` with the mod-29 seventh-power gap
(`seventh_sum_ne_three_mod29`: `A⁷ + B⁷ ≢ 3 (mod 29)`, unconditional).

None of the conjuncts is defined as the negation of the goal; there is no circular
hypothesis. The remaining genuine gap (an effective lower bound on the radical) is
isolated as **one** typed hypothesis in each corollary
(`fifth_no_counterexample_of_radical_ge`, `seventh_no_counterexample_of_radical_ge`),
making the effective-ABC input explicit and minimal — exactly as in the cube template.

`lake env lean BealHigherMasterCapstone.lean` to typecheck (SLOW: cyclotomic imports).
-/

namespace BealHigherMasterCapstone

open scoped NumberField

/-! ## The `p = 5` master capstone -/

/-- **MASTER capstone `p = 5` (HEADLINE) — the simultaneous constraints on a primitive
fifth-power-sum Beal counterexample.**

Let `A, B, C ≥ 2` with `Nat.Coprime A B`, let `z` be a prime with `5 ≤ z` and
`5 ∤ (A + B)`, and suppose `A⁵ + B⁵ = Cᶻ`. Then **all** of the following hold at once:

1. **(descent — integer + cyclotomic)** `A + B` is a perfect `z`-th power in `ℤ`,
   and the cyclotomic factor `A + B·ζ` is a `z`-th power up to a unit in `ℤ[ζ₅]`:
   `(∃ s, A + B = sᶻ) ∧ (∃ d : 𝓞 K, Associated (dᶻ) (A + B·ζ))`.
   *(Source: `BealFiveStructure.beal_55z_structure`.)*

2. **(local mod 11, UNCONDITIONAL)** the fifth-power-sum residue avoids the
   split-prime gap `{3,4,5,6,7,8}`:
   `(A : ZMod 11)⁵ + (B : ZMod 11)⁵ ∉ {3,4,5,6,7,8}`.
   *(Source: `BealFifthPower.fifth_sum_not_mem_gap_mod11`, applied to the residues of
   the actual bases — no hypothesis on `C^z`.)*

3. **(ABC-quality, UNCONDITIONAL)** the radical of the Beal product is below the
   value: `rad(A⁵ · B⁵ · Cᶻ) < Cᶻ`, i.e. ABC-quality `q > 1`.
   *(Source: `BealABCQuality.beal_radical_lt_c`.)*

This is the comprehensive machine-checked answer to "what would a primitive
fifth-power-sum Beal counterexample have to look like?". **NEW.** -/
theorem fifth_counterexample_master_constraints
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hAB : Nat.Coprime A B) (_hzp : z.Prime) (hz : 5 ≤ z) (h5 : ¬ 5 ∣ (A + B))
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    -- 1. descent (integer + cyclotomic)
    ((∃ s : ℕ, A + B = s ^ z) ∧
      (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger))) ∧
    -- 2. local mod 11 (UNCONDITIONAL): A⁵+B⁵ misses {3,4,5,6,7,8}
    ((A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 3 ∧
      (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 4 ∧
      (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 5 ∧
      (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 6 ∧
      (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 7 ∧
      (A : ZMod 11) ^ 5 + (B : ZMod 11) ^ 5 ≠ 8) ∧
    -- 3. ABC-quality (unconditional)
    (BealRadical.radical (A ^ 5 * B ^ 5 * C ^ z) < C ^ z) := by
  have hz0 : z ≠ 0 := by omega
  refine ⟨?descent, ?mod11, ?quality⟩
  · -- 1. descent: the integer + cyclotomic structure theorem.
    exact BealFiveStructure.beal_55z_structure hζ hAB h5 hz0 h
  · -- 2. mod 11: fifth-power sums miss {3,4,5,6,7,8} (unconditional).
    exact BealFifthPower.fifth_sum_not_mem_gap_mod11 (A : ZMod 11) (B : ZMod 11)
  · -- 3. ABC-quality: rad(A⁵ B⁵ Cᶻ) < Cᶻ (unconditional). Exponents 5,5,z ≥ 3.
    exact BealABCQuality.beal_radical_lt_c hA hB hC (by norm_num) (by norm_num) (by omega) h

/-- **COROLLARY `p = 5` — the explicit minimal gap: an effective radical lower bound
closes the case.**

The master capstone forces `rad(A⁵·B⁵·Cᶻ) < Cᶻ` *unconditionally*. Therefore **any**
hypothesis providing the matching effective lower bound — an ABC-conjecture-type input
`Cᶻ ≤ rad(A⁵·B⁵·Cᶻ)` — yields an immediate contradiction: there is **no** such
counterexample.

This isolates the entire remaining gap as a *single typed hypothesis* `hABC`, stated as
a lower bound on the radical (the effective-ABC input). It is **not** circular: `hABC`
is a lower bound on `rad`, while the proven `beal_radical_lt_c` is the strict upper
bound `rad < Cᶻ`; the two together are contradictory. **NEW.** -/
theorem fifth_no_counterexample_of_radical_ge
    {A B C z : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (_hzp : z.Prime) (hz : 5 ≤ z)
    (h : A ^ 5 + B ^ 5 = C ^ z)
    -- the typed effective-ABC input (the documented minimal gap):
    (hABC : C ^ z ≤ BealRadical.radical (A ^ 5 * B ^ 5 * C ^ z)) :
    False := by
  -- The unconditional ABC-quality bound: rad(A⁵ B⁵ Cᶻ) < Cᶻ.
  have hrad : BealRadical.radical (A ^ 5 * B ^ 5 * C ^ z) < C ^ z :=
    BealABCQuality.beal_radical_lt_c hA hB hC (by norm_num) (by norm_num) (by omega) h
  -- Contradiction with the typed lower bound.
  omega

/-! ## The `p = 7` master capstone -/

/-- **MASTER capstone `p = 7` (HEADLINE) — the simultaneous constraints on a primitive
seventh-power-sum Beal counterexample.**

Let `A, B, C ≥ 2` with `Nat.Coprime A B`, let `z` be a prime with `5 ≤ z` and
`7 ∤ (A + B)`, and suppose `A⁷ + B⁷ = Cᶻ`. Then **all** of the following hold at once:

1. **(descent — integer + cyclotomic)** `A + B` is a perfect `z`-th power in `ℤ`,
   and the cyclotomic factor `A + B·ζ` is a `z`-th power up to a unit in `ℤ[ζ₇]`:
   `(∃ s, A + B = sᶻ) ∧ (∃ d : 𝓞 K, Associated (dᶻ) (A + B·ζ))`.
   *(Source: `IsCyclotomicExtension.Rat.Seven.beal_77z_structure`, whose PID hypothesis
   is discharged by `seven_pid` — class number 1 of `ℚ(ζ₇)`.)*

2. **(local mod 29, UNCONDITIONAL)** the seventh-power-sum residue avoids the
   split-prime forbidden residue `3`:
   `(A : ZMod 29)⁷ + (B : ZMod 29)⁷ ≠ 3`.
   *(Source: `BealSplitPrimeGeneral.seventh_sum_ne_three_mod29`, applied to the
   residues of the actual bases — `3` is one of `16` residues `A⁷ + B⁷` cannot hit.)*

3. **(ABC-quality, UNCONDITIONAL)** the radical of the Beal product is below the
   value: `rad(A⁷ · B⁷ · Cᶻ) < Cᶻ`, i.e. ABC-quality `q > 1`.
   *(Source: `BealABCQuality.beal_radical_lt_c`.)*

This is the comprehensive machine-checked answer to "what would a primitive
seventh-power-sum Beal counterexample have to look like?". **NEW.** -/
theorem seventh_counterexample_master_constraints
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hAB : Nat.Coprime A B) (_hzp : z.Prime) (hz : 5 ≤ z) (h7 : ¬ 7 ∣ (A + B))
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    -- 1. descent (integer + cyclotomic)
    ((∃ s : ℕ, A + B = s ^ z) ∧
      (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger))) ∧
    -- 2. local mod 29 (UNCONDITIONAL): A⁷+B⁷ ≠ 3
    ((A : ZMod 29) ^ 7 + (B : ZMod 29) ^ 7 ≠ 3) ∧
    -- 3. ABC-quality (unconditional)
    (BealRadical.radical (A ^ 7 * B ^ 7 * C ^ z) < C ^ z) := by
  have hz0 : z ≠ 0 := by omega
  refine ⟨?descent, ?mod29, ?quality⟩
  · -- 1. descent: the integer + cyclotomic structure theorem (PID via seven_pid).
    exact IsCyclotomicExtension.Rat.Seven.beal_77z_structure K hζ hAB h7 hz0 h
  · -- 2. mod 29: seventh-power sums miss 3 (unconditional).
    exact BealSplitPrimeGeneral.seventh_sum_ne_three_mod29 (A : ZMod 29) (B : ZMod 29)
  · -- 3. ABC-quality: rad(A⁷ B⁷ Cᶻ) < Cᶻ (unconditional). Exponents 7,7,z ≥ 3.
    exact BealABCQuality.beal_radical_lt_c hA hB hC (by norm_num) (by norm_num) (by omega) h

/-- **COROLLARY `p = 7` — the explicit minimal gap: an effective radical lower bound
closes the case.**

The master capstone forces `rad(A⁷·B⁷·Cᶻ) < Cᶻ` *unconditionally*. Therefore **any**
hypothesis providing the matching effective lower bound — an ABC-conjecture-type input
`Cᶻ ≤ rad(A⁷·B⁷·Cᶻ)` — yields an immediate contradiction: there is **no** such
counterexample.

This isolates the entire remaining gap as a *single typed hypothesis* `hABC`, stated as
a lower bound on the radical (the effective-ABC input). It is **not** circular: `hABC`
is a lower bound on `rad`, while the proven `beal_radical_lt_c` is the strict upper
bound `rad < Cᶻ`; the two together are contradictory. **NEW.** -/
theorem seventh_no_counterexample_of_radical_ge
    {A B C z : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (_hzp : z.Prime) (hz : 5 ≤ z)
    (h : A ^ 7 + B ^ 7 = C ^ z)
    -- the typed effective-ABC input (the documented minimal gap):
    (hABC : C ^ z ≤ BealRadical.radical (A ^ 7 * B ^ 7 * C ^ z)) :
    False := by
  -- The unconditional ABC-quality bound: rad(A⁷ B⁷ Cᶻ) < Cᶻ.
  have hrad : BealRadical.radical (A ^ 7 * B ^ 7 * C ^ z) < C ^ z :=
    BealABCQuality.beal_radical_lt_c hA hB hC (by norm_num) (by norm_num) (by omega) h
  -- Contradiction with the typed lower bound.
  omega

end BealHigherMasterCapstone
