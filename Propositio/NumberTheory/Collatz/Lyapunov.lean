import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.Basic

/-!
# Per-residue (mod 8) Lyapunov descent/ascent theorems — Lean 4 mirror

Block 3, "Bucket 3" port. LaTTe siblings live in
`src/ai_math/collatz/lyapunov_v2.clj` and
`src/ai_math/collatz/lyapunov_v3.clj`.

We reuse the **compressed Collatz step** from `TerrasDensity`:

  `TerrasDensity.cc n = (3*n + 1) / 2 ^ padicValNat 2 (3*n + 1)`

which is exactly the odd part of `3n+1`, matching the LaTTe operator
`ai-math.collatz-compressed/collatz-odd-compressed` (a.k.a. `cc-comp`). The
semantics line up verbatim, so we `import TerrasDensity` rather than
re-defining the operator (per the brief, avoiding divergent definitions).

## The two candidate Lyapunov functions

LaTTe defines

  * `V  n := v₂(n - 1)`     (`lyapunov-v2`, the "candidate V_a")
  * `V3 n := v₂(3n + 1)`    (`lyapunov-v3`, the "candidate V_b"; this is one
    compressed-step's worth of halvings: `v₂(3n+1)`)

with `v₂ = padicValNat 2`. We mirror both. All residue-class statements
quantify over `n = 8k + r`; on `Nat` the subtraction `n - 1` is exact since
`n ≥ 1` throughout, so `V` agrees with the LaTTe `int`-domain definition.

## Mapping LaTTe `=`/`<` and numerals

LaTTe's integer `=` and `ord/<` are mirrored by `Nat` equality and `<`.
The LaTTe statements use the numeral encodings `eight = 4*2`,
`(succ four) = 5`, `(succ (* two three)) = 7`; we use the literals
`8, 5, 7` directly (definitionally equal after δ-reduction in LaTTe).

## Idiomatic adjustments

The LaTTe proofs thread ~24 bespoke arithmetic / oddness / nat-closure helper
lemmas per file (`eight-k-one-minus-one`, `three-times-8k1-plus-one-eq-…`,
`v-two-of-double`, `odd-part-of-double-odd-eq-itself`, …). In Lean these all
collapse into two reusable helpers plus `omega`/`ring`:

  * `v2_pow_mul_odd`  — `v₂(2^a · m) = a` for odd `m`  (replaces the entire
    `v-two-of-double` cascade and `v-two-of-double-odd-eq-one`);
  * `cc_factor`       — if `3n+1 = 2^a · m` with `m` odd then `cc n = m`
    (replaces the `odd-part`-stripping chain `three-times-…-eq-…` +
    `odd-part-of-double-odd-eq-itself`).

The algebraic identities (`3(8k+1)+1 = 4·(6k+1)` etc.) are discharged by
`ring`; oddness side-conditions (`¬ 2 ∣ (6k+1)` etc.) by `omega`.
-/

namespace Lyapunov

open TerrasDensity (cc)

/-! ## Reusable 2-adic / compressed-step helpers -/

/-- `v₂(2^a · m) = a` for odd `m`.

Collapses the LaTTe `v-two-of-double` recurrence cascade (and the special
case `v-two-of-double-odd-eq-one`) into a single product/prime-power lemma. -/
theorem v2_pow_mul_odd (a m : Nat) (hm : ¬ 2 ∣ m) :
    padicValNat 2 (2 ^ a * m) = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm]
  simp

/-- If `3n + 1 = 2^a · m` with `m` odd, then `cc n = m`.

This is the Lean form of the LaTTe `odd-part`-stripping computation
(`cc-comp(n) = odd-part(3n+1)`): factoring out the full power of two and
keeping the odd cofactor. -/
theorem cc_factor (n a m : Nat) (hm : ¬ 2 ∣ m) (h : 3 * n + 1 = 2 ^ a * m) :
    cc n = m := by
  unfold cc
  rw [h, v2_pow_mul_odd a m hm]
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.mul_div_cancel_left m (by positivity)]

/-! ## The candidate Lyapunov functions -/

/-- `V n := v₂(n - 1)`. The Option-C candidate Lyapunov measure.

LaTTe sibling: `ai-math.collatz.lyapunov-v2/V`. -/
def V (n : Nat) : Nat := padicValNat 2 (n - 1)

/-- `V3 n := v₂(3n + 1)`. The "candidate V_b" — one compressed step's halvings.

LaTTe sibling: `ai-math.collatz.lyapunov-v3/V3`. -/
def V3 (n : Nat) : Nat := padicValNat 2 (3 * n + 1)

/-! ## lyapunov-v2 — per-residue mod-8 behaviour of `V` under `cc` -/

/-- **Positive descent at `n ≡ 1 (mod 8)`.** For `k ≥ 1`,
`V(cc(8k+1)) + 2 = V(8k+1)`.

`V(8k+1) = v₂(8k) = 3 + v₂(k)`, and `cc(8k+1) = 6k+1`, so
`V(6k+1) = v₂(6k) = 1 + v₂(k)`; hence `(1 + v₂(k)) + 2 = 3 + v₂(k)`.
The hypothesis `k ≠ 0` is needed (else `v₂(0)` collapses the count).

LaTTe sibling: `src/ai_math/collatz/lyapunov_v2.clj :: v2-descent-mod-8-1`. -/
theorem v2_descent_mod_8_1 (k : Nat) (hk : k ≠ 0) :
    V (cc (8 * k + 1)) + 2 = V (8 * k + 1) := by
  -- cc(8k+1) = 6k+1
  have hcc : cc (8 * k + 1) = 6 * k + 1 := by
    apply cc_factor (8 * k + 1) 2 (6 * k + 1)
    · omega
    · ring
  rw [hcc]
  unfold V
  -- LHS: v₂((6k+1) - 1) = v₂(6k) = v₂(2 · (3k)) = 1 + v₂(k)
  -- RHS: v₂((8k+1) - 1) = v₂(8k) = v₂(2^3 · k) = 3 + v₂(k)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- LHS: v₂(6k) = v₂(2^1 · 3k) = 1 + v₂k ; RHS: v₂(8k) = v₂(2^3 · k) = 3 + v₂k
  have e6 : 6 * k + 1 - 1 = 2 ^ 1 * (3 * k) := by ring_nf; omega
  have e8 : 8 * k + 1 - 1 = 2 ^ 3 * k := by ring_nf; omega
  have hL : padicValNat 2 (6 * k + 1 - 1) = 1 + padicValNat 2 k := by
    rw [e6, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
        padicValNat.mul (by norm_num) (by omega),
        show padicValNat 2 3 = 0 from padicValNat.eq_zero_of_not_dvd (by omega)]
    ring
  have hR : padicValNat 2 (8 * k + 1 - 1) = 3 + padicValNat 2 k := by
    rw [e8, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
  rw [hL, hR]
  omega

/-- **Strict ascent at `n ≡ 3 (mod 8)`.** `V(8k+3) < V(cc(8k+3))`.

`V(8k+3) = v₂(8k+2) = v₂(2·(4k+1)) = 1`; `cc(8k+3) = 12k+5`, and
`V(12k+5) = v₂(12k+4) = v₂(4·(3k+1)) = 2 + v₂(3k+1) ≥ 2 > 1`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v2.clj :: v2-ascent-mod-8-3`. -/
theorem v2_ascent_mod_8_3 (k : Nat) :
    V (8 * k + 3) < V (cc (8 * k + 3)) := by
  -- cc(8k+3) = 12k+5
  have hcc : cc (8 * k + 3) = 12 * k + 5 := by
    apply cc_factor (8 * k + 3) 1 (12 * k + 5)
    · omega
    · ring
  rw [hcc]
  unfold V
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- V(8k+3) = v₂(2·(4k+1)) = 1
  have eL : 8 * k + 3 - 1 = 2 * (4 * k + 1) := by omega
  have hL : padicValNat 2 (8 * k + 3 - 1) = 1 := by
    rw [eL, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by omega)]
  -- V(12k+5) = v₂(4·(3k+1)) = 2 + v₂(3k+1) ≥ 2
  have eR : 12 * k + 5 - 1 = 2 ^ 2 * (3 * k + 1) := by ring_nf; omega
  have hR : padicValNat 2 (12 * k + 5 - 1) = 2 + padicValNat 2 (3 * k + 1) := by
    rw [eR, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
  rw [hL, hR]
  omega

/-- **Uniform value at `n ≡ 5 (mod 8)`.** `V(8k+5) = 2`.

`V(8k+5) = v₂(8k+4) = v₂(4·(2k+1)) = 2`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v2.clj :: v2-value-mod-8-5`. -/
theorem v2_value_mod_8_5 (k : Nat) : V (8 * k + 5) = 2 := by
  unfold V
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : 8 * k + 5 - 1 = 2 ^ 2 * (2 * k + 1) := by ring_nf; omega
  rw [e, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega)]

/-- **Stagnation at `n ≡ 7 (mod 8)`.** `V(cc(8k+7)) = V(8k+7)`.

Both sides equal `1`: `V(8k+7) = v₂(2·(4k+3)) = 1`; `cc(8k+7) = 12k+11`, and
`V(12k+11) = v₂(2·(6k+5)) = 1`. The whole family `n = 8k+7` is a
`V`-stagnation segment — the cleanest exhibit that no global per-step
`v₂`-Lyapunov function exists.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v2.clj :: v2-stagnation-mod-8-7`. -/
theorem v2_stagnation_mod_8_7 (k : Nat) :
    V (cc (8 * k + 7)) = V (8 * k + 7) := by
  -- cc(8k+7) = 12k+11
  have hcc : cc (8 * k + 7) = 12 * k + 11 := by
    apply cc_factor (8 * k + 7) 1 (12 * k + 11)
    · omega
    · ring
  rw [hcc]
  unfold V
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- both = v₂(2·odd) = 1
  have eL : 12 * k + 11 - 1 = 2 * (6 * k + 5) := by omega
  have eR : 8 * k + 7 - 1 = 2 * (4 * k + 3) := by omega
  rw [eL, eR,
      padicValNat.mul (by norm_num) (by omega),
      padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (6 * k + 5) by omega),
      padicValNat.mul (by norm_num) (by omega),
      padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (4 * k + 3) by omega),
      padicValNat.self (by norm_num)]

/-! ## lyapunov-v3 — per-residue mod-8 behaviour of `V3 = v₂(3n+1)` -/

/-- **Uniform `V3 = 1` at `n ≡ 3 (mod 8)`.** `V3(8k+3) = 1`.

`3(8k+3)+1 = 24k+10 = 2·(12k+5)` with `12k+5` odd, so `v₂ = 1`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v3.clj :: v3-value-mod-8-3`. -/
theorem v3_value_mod_8_3 (k : Nat) : V3 (8 * k + 3) = 1 := by
  unfold V3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : 3 * (8 * k + 3) + 1 = 2 * (12 * k + 5) := by ring
  rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]

/-- **Uniform `V3 = 1` at `n ≡ 7 (mod 8)`.** `V3(8k+7) = 1`.

`3(8k+7)+1 = 24k+22 = 2·(12k+11)` with `12k+11` odd, so `v₂ = 1`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v3.clj :: v3-value-mod-8-7`. -/
theorem v3_value_mod_8_7 (k : Nat) : V3 (8 * k + 7) = 1 := by
  unfold V3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : 3 * (8 * k + 7) + 1 = 2 * (12 * k + 11) := by ring
  rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]

/-- **`V3` stagnation at `n ≡ 7 (mod 8)`.** `V3(cc(8k+7)) = V3(8k+7)`.

Both sides equal `1`: `V3(8k+7) = 1` (above) and `cc(8k+7) = 12k+11` with
`V3(12k+11) = v₂(3(12k+11)+1) = v₂(2·(18k+17)) = 1`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v3.clj :: v3-stagnation-mod-8-7`. -/
theorem v3_stagnation_mod_8_7 (k : Nat) :
    V3 (cc (8 * k + 7)) = V3 (8 * k + 7) := by
  have hcc : cc (8 * k + 7) = 12 * k + 11 := by
    apply cc_factor (8 * k + 7) 1 (12 * k + 11)
    · omega
    · ring
  rw [hcc, v3_value_mod_8_7 k]
  -- V3(12k+11) = 1
  unfold V3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : 3 * (12 * k + 11) + 1 = 2 * (18 * k + 17) := by ring
  rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]

/-- **Strict `V3` ascent at `n ≡ 3 (mod 8)`.** `V3(8k+3) < V3(cc(8k+3))`.

`V3(8k+3) = 1`; `cc(8k+3) = 12k+5`, and `V3(12k+5) = v₂(3(12k+5)+1)
= v₂(4·(9k+4)) = 2 + v₂(9k+4) ≥ 2 > 1`.

LaTTe sibling: `src/ai_math/collatz/lyapunov_v3.clj :: v3-ascent-mod-8-3`. -/
theorem v3_ascent_mod_8_3 (k : Nat) :
    V3 (8 * k + 3) < V3 (cc (8 * k + 3)) := by
  have hcc : cc (8 * k + 3) = 12 * k + 5 := by
    apply cc_factor (8 * k + 3) 1 (12 * k + 5)
    · omega
    · ring
  rw [hcc, v3_value_mod_8_3 k]
  -- V3(12k+5) = v₂(4·(9k+4)) = 2 + v₂(9k+4) ≥ 2
  unfold V3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : 3 * (12 * k + 5) + 1 = 2 ^ 2 * (9 * k + 4) := by ring
  rw [e, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
  omega

end Lyapunov
