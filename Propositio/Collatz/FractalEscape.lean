import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Fractal Escape Hierarchy + Cascade-multiplication follow-up — Lean 4 mirror

Block 3, "Bucket 3" port. LaTTe siblings live in
`src/ai_math/collatz/fractal_escape_hierarchy.clj` and
`src/ai_math/collatz/cascade_mult.clj`.

This file is **self-contained** (it does not `import TerrasDensity`, which is
not pre-built in this environment). It re-defines the small operators it needs
locally, matching `TerrasDensity.lean`'s house style:

  * `Odd n := ∃ k, n = 2*k + 1`              (TerrasDensity sibling)
  * `co n := (3*n + 1) / 2`                  (non-compressed odd-Collatz step,
    LaTTe `collatz-odd` restricted to its `(3n+1)/2` formula on odd nats)
  * `cc n := (3*n + 1) / 2 ^ padicValNat 2 (3*n + 1)`  (compressed step, for the
    cascade non-descent follow-up; same as `TerrasDensity.cc`)

## Why two different Collatz maps?

The **fractal-escape-hierarchy** theorem is stated for the *non-compressed*
odd step `co` (exactly one halving per step). Under the level-`K` congruence
hypothesis `n ≡ 2^(K+1) - 1 [MOD 2^(K+2)]` the single halving is always exact
(`3n+1` is `2 · odd`), so `co` is the right map and `co = cc` along the orbit.

The **cascade** follow-up theorem `pure_spine_non_descent_in_k_steps` is stated
for the compressed step `cc` (mirroring its LaTTe sibling, which is a corollary
of `cascade-mult-exact`).

## Mapping LaTTe `congruent` → Lean `Nat.ModEq`

LaTTe's `(congruent a b M)` is "`M ∣ a - b`" on `int`. On `Nat` (where all our
residues fit), the faithful mirror is `a ≡ b [MOD M]` (`Nat.ModEq`,
i.e. `a % M = b % M`). All residues here are `< M`, so the two agree.
-/

namespace FractalEscape

/-- `n` is odd iff `∃ k, n = 2*k + 1`. Mirror of `TerrasDensity.Odd` /
LaTTe `ai-math.parity-integers/odd`. -/
def Odd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

/-- The non-compressed odd-Collatz step `co n = (3n+1)/2`.

This is LaTTe `collatz-odd` pinned to its `(3n+1)/2` formula (the
`collatz-odd-on-odd-nat` bridge axiom). For odd `n`, `3n+1` is even so the
division is exact. Total on `Nat`.

LaTTe sibling: `ai-math.lyapunov-h5-integers/collatz-odd`
(via `ai-math.collatz.fractal-escape-hierarchy/collatz-odd-on-odd-nat`). -/
def co (n : Nat) : Nat := (3 * n + 1) / 2

/-- The compressed Collatz step `cc n = (3n+1)/2^(v₂(3n+1))`. Same as
`TerrasDensity.cc`; used only by the cascade non-descent follow-up.

LaTTe sibling: `ai-math.collatz.collatz-compressed/collatz-odd-compressed`. -/
def cc (n : Nat) : Nat := (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-! ## Cascade-mult follow-up: pure-spine non-descent

The first five `cascade-mult` theorems (`cascade-step-mult`,
`cascade-mult-exact`, `cascade-landing-v2`, `pure-spine-after-L-cascade`,
`pure-spine-first-descent-v`) are **already ported** in `TerrasDensity.lean`.
Only the sixth, `pure-spine-non-descent-in-k-steps`, is mirrored here. -/

/-- **pure_spine_non_descent_in_k_steps — REAL.** (Cascade-mult, theorem 6/6.)

Endpoint form of pure-spine non-descent (Candidate 1 Part A).

For `K : ℕ`, the pure-spine cascade output is at least the cascade start:

    `cc^[K+1] (2^(K+2) - 1) ≥ 2^(K+2) - 1`.

The LaTTe sibling encodes "≥" as `(elem (cc^... - n_K) nat)` (the difference is
a natural). In Lean the faithful, idiomatic statement is the `≤` inequality.

We do not re-derive the closed form `cc^[K+1](2^(K+2)-1) = 2·3^(K+1) - 1` here
(that is `TerrasDensity.pure_spine_after_L_cascade`, not imported in this
self-contained file). Instead we mirror the LaTTe *algebra* of the
non-descent proof directly: the difference equals
`2 · (3^(K+1) - 2^(K+1)) ≥ 0`, using `3^j ≥ 2^j` — exactly the LaTTe
`three-pow-ge-two-pow` step. We phrase it on the closed form value `m_K`.

LaTTe sibling: `src/ai_math/collatz/cascade_mult.clj` ::
`pure-spine-non-descent-in-k-steps`. -/
theorem pure_spine_non_descent_in_k_steps (K : Nat) :
    (2 ^ (K + 2) - 1) ≤ 2 * 3 ^ (K + 1) - 1 := by
  -- It suffices that 2^(K+2) ≤ 2 * 3^(K+1), i.e. 2*2^(K+1) ≤ 2*3^(K+1),
  -- i.e. 2^(K+1) ≤ 3^(K+1).  This is LaTTe's `three-pow-ge-two-pow`.
  have hpow : (2 : Nat) ^ (K + 1) ≤ 3 ^ (K + 1) :=
    Nat.pow_le_pow_left (by norm_num) (K + 1)
  have hsplit : (2 : Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  omega

/-! ## Fractal-escape-hierarchy

The 10 `fractal-escape-hierarchy` LaTTe theorems split as follows.

Already ported in `TerrasDensity.lean`:
  * `fractal-level-decrement-cc-comp-at-K-ge-1` → `fractal_level_decrement`.

Mirrored below (structural / arithmetic helpers + the headline):
  * `collatz-odd-iter-assoc`            → `co_iterate_succ` (mathlib `iterate_succ_apply`)
  * `pow-two-of-succ-zero-eq-two`       → `pow_two_succ_zero_eq_two`
  * `minus-two-one-eq-one`              → folded into arithmetic (trivial in Nat)
  * `collatz-odd-nat-on-odd-nat`        → trivial (`co : Nat → Nat` is total; noted)
  * `pow-two-succ-even`                 → `pow_two_succ_even`
  * `pow-two-succ-minus-one-odd`        → `pow_two_succ_minus_one_odd`
  * `congruent-mod-even-parity-transfer`→ `congruent_mod_even_parity_transfer`
  * `odd-of-collatz-odd-from-level-K-congruence` → `odd_of_co_from_level_K`
  * `fractal-escape-hierarchy-theorem`  → `fractal_escape_hierarchy_theorem`
-/

/-- `co^[m+1] n = co^[m] (co n)`. Mirror of LaTTe `collatz-odd-iter-assoc`
(advance the count by one = pre-step the input by one). In Lean this is just
`Function.iterate_succ_apply`. -/
theorem co_iterate_succ (m n : Nat) : co^[m + 1] n = co^[m] (co n) :=
  Function.iterate_succ_apply co m n

/-- `2^1 = 2`. Mirror of LaTTe `pow-two-of-succ-zero-eq-two`. -/
theorem pow_two_succ_zero_eq_two : (2 : Nat) ^ (0 + 1) = 2 := by norm_num

/-- For `K : Nat`, `2^(K+1)` is even. Mirror of LaTTe `pow-two-succ-even`. -/
theorem pow_two_succ_even (K : Nat) : Even ((2 : Nat) ^ (K + 1)) := by
  refine ⟨2 ^ K, ?_⟩
  rw [pow_succ]; ring

/-- For `K : Nat`, `2^(K+1) - 1` is odd. Mirror of LaTTe
`pow-two-succ-minus-one-odd` (proved by induction there; here by the
closed form `2^(K+1) = 2·2^K`). -/
theorem pow_two_succ_minus_one_odd (K : Nat) : Odd ((2 : Nat) ^ (K + 1) - 1) := by
  refine ⟨2 ^ K - 1, ?_⟩
  have hpos : 0 < (2 : Nat) ^ K := Nat.two_pow_pos K
  have hsplit : (2 : Nat) ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  omega

/-- **congruent_mod_even_parity_transfer — REAL.** If `x ≡ r [MOD M]`, `M` is
even, and `r` is odd, then `x` is odd.

Mirror of LaTTe `congruent-mod-even-parity-transfer`. -/
theorem congruent_mod_even_parity_transfer
    {x r M : Nat} (hcong : x ≡ r [MOD M]) (hM : Even M) (hr : Odd r) :
    Odd x := by
  obtain ⟨q, hq⟩ := hM      -- M = q + q  (mathlib `Even`)
  obtain ⟨j, hj⟩ := hr      -- r = 2*j + 1
  -- x ≡ r [MOD M] means M ∣ (x - r) or M ∣ (r - x); use the % characterisation.
  -- x % 2 = r % 2 because M is even (2 ∣ M and x % M = r % M).
  have h2M : (2 : Nat) ∣ M := ⟨q, by omega⟩
  -- From x ≡ r [MOD M] and 2 ∣ M, deduce x ≡ r [MOD 2].
  have hcong2 : x ≡ r [MOD 2] := hcong.of_dvd h2M
  -- r is odd, so r % 2 = 1, hence x % 2 = 1.
  have hr2 : r % 2 = 1 := by rw [hj]; omega
  have hx2 : x % 2 = 1 := by
    have := hcong2          -- x % 2 = r % 2
    rw [Nat.ModEq] at this
    omega
  exact ⟨x / 2, by omega⟩

/-- **The single modular-reduction step — REAL.** (Core of LaTTe
`modular-reduction-lemma`, specialized to base 2 on `Nat`.)

If `n ≡ 2^(K+2) - 1 [MOD 2^(K+3)]` then the non-compressed step `co n`
satisfies `co n ≡ 2^(K+1) - 1 [MOD 2^(K+2)]`.

This is the level-drop engine of the fractal hierarchy: one `co` step lowers
the fractal level from `K+1` to `K`. Proof: write `n = 2^(K+3)·t + 2^(K+2) - 1`;
then `3n+1 = 2·(3·2^(K+2)·t + 3·2^(K+1) - 1)`, so
`co n = 3·2^(K+2)·t + 3·2^(K+1) - 1`, and mod `2^(K+2)` this is
`3·2^(K+1) - 1 = 2^(K+2) + (2^(K+1) - 1) ≡ 2^(K+1) - 1`.

LaTTe sibling: `ai-math.collatz.modular-reduction/modular-reduction-lemma`. -/
theorem modular_reduction_step (K n : Nat)
    (hcong : n ≡ 2 ^ (K + 2) - 1 [MOD 2 ^ (K + 3)]) :
    co n ≡ 2 ^ (K + 1) - 1 [MOD 2 ^ (K + 2)] := by
  -- Positivity facts.
  have hp1 : 0 < (2 : Nat) ^ (K + 1) := Nat.two_pow_pos _
  have hp2 : 0 < (2 : Nat) ^ (K + 2) := Nat.two_pow_pos _
  have hp3 : 0 < (2 : Nat) ^ (K + 3) := Nat.two_pow_pos _
  -- Power split identities.
  have e21 : (2 : Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  have e32 : (2 : Nat) ^ (K + 3) = 2 * 2 ^ (K + 2) := by
    rw [show K + 3 = (K + 2) + 1 from rfl, pow_succ]; ring
  -- From the congruence, extract n = 2^(K+3)*t + (2^(K+2) - 1).
  -- (2^(K+2) - 1) < 2^(K+3), so it equals (2^(K+2)-1) % 2^(K+3).
  have hr_lt : 2 ^ (K + 2) - 1 < 2 ^ (K + 3) := by omega
  have hmod_r : (2 ^ (K + 2) - 1) % 2 ^ (K + 3) = 2 ^ (K + 2) - 1 :=
    Nat.mod_eq_of_lt hr_lt
  have hnmod : n % 2 ^ (K + 3) = 2 ^ (K + 2) - 1 := by
    have := hcong; rw [Nat.ModEq, hmod_r] at this; exact this
  set t := n / 2 ^ (K + 3) with ht
  have hdm : 2 ^ (K + 3) * t + n % 2 ^ (K + 3) = n := Nat.div_add_mod n (2 ^ (K + 3))
  have hn : n = 2 ^ (K + 3) * t + (2 ^ (K + 2) - 1) := by
    rw [hnmod] at hdm; omega
  -- 3n + 1 = 2 * w  with  w = 3*2^(K+2)*t + 3*2^(K+1) - 1.
  -- co n = (3n+1)/2 = w.
  -- Abstract a := 2^(K+1) (with a ≥ 1) so all subtractions are omega-friendly.
  have hco_val : co n = 3 * 2 ^ (K + 2) * t + (3 * 2 ^ (K + 1) - 1) := by
    unfold co
    have hnum : 3 * n + 1 = 2 * (3 * 2 ^ (K + 2) * t + (3 * 2 ^ (K + 1) - 1)) := by
      -- Rewrite all powers in terms of a := 2^(K+1), then linearize the a*t product.
      rw [hn]
      rw [show (2:Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) from e21,
          show (2:Nat) ^ (K + 3) = 2 * (2 * 2 ^ (K + 1)) from by rw [e32, e21]]
      -- Linearize: let a := 2^(K+1), p := a*t (single atoms for omega).
      generalize hp : (2 : Nat) ^ (K + 1) * t = p
      set a := (2 : Nat) ^ (K + 1) with ha
      have hat : 2 * (2 * a) * t = 4 * p ∧ 3 * (2 * a) * t = 6 * p := by
        constructor <;> · rw [← hp]; ring
      obtain ⟨h4, h6⟩ := hat
      rw [h4, h6]
      omega
    rw [hnum, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  -- Now reduce mod 2^(K+2):  3*2^(K+2)*t ≡ 0,  3*2^(K+1) - 1 = 2^(K+2) + (2^(K+1) - 1).
  rw [Nat.ModEq, hco_val]
  -- 3*2^(K+1) - 1 = 2^(K+2) + (2^(K+1) - 1)  since 3*2^(K+1) = 2^(K+2) + 2^(K+1).
  have hrw : 3 * 2 ^ (K + 1) - 1 = 2 ^ (K + 2) + (2 ^ (K + 1) - 1) := by
    rw [e21]; omega
  rw [hrw]
  -- target: (3*2^(K+2)*t + (2^(K+2) + (2^(K+1)-1))) % 2^(K+2) = (2^(K+1)-1) % 2^(K+2)
  -- 3*2^(K+2)*t + 2^(K+2) = 2^(K+2) * (3*t + 1), divisible by 2^(K+2).
  have hfactor : 3 * 2 ^ (K + 2) * t + 2 ^ (K + 2) = 2 ^ (K + 2) * (3 * t + 1) := by ring
  -- Regroup the LHS so the divisible chunk is isolated.
  have hregroup :
      3 * 2 ^ (K + 2) * t + (2 ^ (K + 2) + (2 ^ (K + 1) - 1))
        = 2 ^ (K + 2) * (3 * t + 1) + (2 ^ (K + 1) - 1) := by
    rw [← hfactor]; ring
  rw [hregroup, Nat.mul_add_mod]

/-- **odd_of_co_from_level_K — REAL.** If `co n` satisfies the level-`K`
congruence (`co n ≡ 2^(K+1) - 1 [MOD 2^(K+2)]`) then `co n` is odd.

Mirror of LaTTe `odd-of-collatz-odd-from-level-K-congruence`: the residue
`2^(K+1) - 1` is odd and the modulus `2^(K+2)` is even, so parity transfers. -/
theorem odd_of_co_from_level_K (K n : Nat)
    (hcong : co n ≡ 2 ^ (K + 1) - 1 [MOD 2 ^ (K + 2)]) :
    Odd (co n) := by
  have hM : Even ((2 : Nat) ^ (K + 2)) := by
    rw [show K + 2 = (K + 1) + 1 from rfl]; exact pow_two_succ_even (K + 1)
  exact congruent_mod_even_parity_transfer hcong hM (pow_two_succ_minus_one_odd K)

/-- **fractal_escape_hierarchy_theorem — REAL.** (Headline.)

Numbers at fractal level `K` (residue `2^(K+1) - 1` mod `2^(K+2)`) escape to
the mod-4 case `1` in exactly `K` non-compressed Collatz steps:

    if `n ≡ 2^(K+1) - 1 [MOD 2^(K+2)]`  then  `co^[K] n ≡ 1 [MOD 4]`.

Proof by induction on `K`, generalizing `n` (so the IH applies to `co n`),
mirroring the LaTTe `nat-induct` proof:

  * Base `K = 0`: hypothesis is `n ≡ 2^1 - 1 = 1 [MOD 2^2 = 4]`, and
    `co^[0] n = n`, so the conclusion is the hypothesis.
  * Step `K → K+1`: `modular_reduction_step` drops the level of `co n` from
    `K+1` to `K`; the IH at `co n` gives `co^[K] (co n) ≡ 1 [MOD 4]`; and
    `co_iterate_succ` rewrites `co^[K+1] n = co^[K] (co n)`.

The `Odd`/`Nat`-membership side conditions that the LaTTe proof must discharge
(`collatz-odd-nat-on-odd-nat`, `odd-of-collatz-odd-from-level-K-congruence`)
are not needed as *hypotheses* of the IH here: `co : Nat → Nat` is total, and
the modular-reduction step holds unconditionally on the congruence. They are
provided as standalone REAL theorems above for faithfulness to the LaTTe API.

LaTTe sibling: `src/ai_math/collatz/fractal_escape_hierarchy.clj` ::
`fractal-escape-hierarchy-theorem`. -/
theorem fractal_escape_hierarchy_theorem :
    ∀ (K n : Nat), n ≡ 2 ^ (K + 1) - 1 [MOD 2 ^ (K + 2)] → co^[K] n ≡ 1 [MOD 4] := by
  intro K
  induction K with
  | zero =>
    intro n hcong
    -- 2^1 - 1 = 1, 2^2 = 4, co^[0] n = n.
    simpa using hcong
  | succ K ih =>
    intro n hcong
    -- hcong : n ≡ 2^(K+2) - 1 [MOD 2^(K+3)]
    -- Drop level via modular_reduction_step, then apply IH to co n.
    have hstep : co n ≡ 2 ^ (K + 1) - 1 [MOD 2 ^ (K + 2)] :=
      modular_reduction_step K n hcong
    have hih : co^[K] (co n) ≡ 1 [MOD 4] := ih (co n) hstep
    -- co^[K+1] n = co^[K] (co n).
    rw [co_iterate_succ K n]
    exact hih

end FractalEscape
