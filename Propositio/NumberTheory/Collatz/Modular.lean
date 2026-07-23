import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.NumberTheory.Collatz.FractalEscape
import Propositio.NumberTheory.Collatz.Basic

/-!
# Collatz modular-reduction ladder, epoch-map, and compressed-orbit-bridge — Lean 4 mirror

Block 3, "Bucket 3" port. This file mirrors three LaTTe theorem families:

  * **modular-reduction** (+ sub-d + sub-e): the level-drop ladder
    `n ≡ 2^(k+1) - 1 [MOD 2^(k+2)]  ⟹  C(n) ≡ 2^k - 1 [MOD 2^(k+1)]`,
    plus its two algebraic sub-lemmas.
    LaTTe siblings: `src/ai_math/collatz/modular_reduction.clj`,
    `modular_reduction_sub_d.clj`, `modular_reduction_sub_e.clj`.

  * **epoch-map**: the `(L, m) → (L_next, m_next)` recurrence closed form
    and the `K = 0` negative result (`v₂(m_next + 1) = 1`).
    LaTTe sibling: `src/ai_math/collatz/epoch_map.clj`.

  * **compressed-orbit-bridge**: `cc-comp(n) = odd-part(collatz-odd(n))` for odd `n`.
    LaTTe sibling: `src/ai_math/collatz/compressed_orbit_bridge.clj`.

## Reuse

`FractalEscape.lean` already ports the **headline** modular-reduction lemma as
`FractalEscape.modular_reduction_step` (base 2, `Nat`, faithful to LaTTe's
`modular-reduction-lemma`). We `import FractalEscape` and reuse it directly, and
reuse `FractalEscape.co` (= `(3n+1)/2`, the non-compressed odd step,
LaTTe `collatz-odd`). The full ladder is already ported as
`FractalEscape.fractal_escape_hierarchy_theorem`. Here we add only what is
*missing* from FractalEscape: the sub-d / sub-e algebraic identities as
standalone theorems, and the `pow_two_nat` / `three_times_pow_two_nat`
nat-closure facts (trivial on `Nat`, where `2^k, 3·2^k : Nat` automatically).

`TerrasDensity.lean` provides `cc` (= compressed step = odd-part of `3n+1`) and
`cascade_mult_exact` (the engine of the epoch-map corollaries). We `import
TerrasDensity` and reuse both.

## Mapping LaTTe → Lean

  * LaTTe `(congruent a b M)` (`M ∣ a - b` on `int`) → `a ≡ b [MOD M]`
    (`Nat.ModEq`). All residues here fit in `Nat`, `< M`, so the two agree.
  * LaTTe `pow two k` → `2 ^ k`, `pow three k` → `3 ^ k`.
  * LaTTe `quotient-by-two w` → `w / 2` (`co` uses this; exact on even args).
  * LaTTe `odd-part w` → `w / 2 ^ padicValNat 2 w` (mathlib `ord_compl`-style;
    we name it `oddPart`).
  * LaTTe `collatz-odd-compressed-iter (succ K) n` → `cc^[K+1] n`.
  * LaTTe `v-two` → `padicValNat 2`.

The LaTTe sources discharge many nat-membership / sign side-conditions
(`int-split`, `half-of-nat-is-nat`, `times-nat-closed`, …) that are automatic on
`Nat`; those are folded away here and noted in the relevant doc-comments.
-/

namespace CollatzModular

open FractalEscape (co)
open TerrasDensity (cc)

/-! ## Part 1 — modular-reduction sub-lemmas (sub-d, sub-e) and nat-closure

The headline `modular-reduction-lemma` is `FractalEscape.modular_reduction_step`
(reused below in `modular_reduction_lemma`). The two sub-lemmas it factors
through, and the nat-closure helpers, are mirrored here. -/

/-- For `k : Nat`, `2^k` is a natural number. Mirror of LaTTe
`modular-reduction/pow-two-nat`. On `Nat` this is definitional (`2^k : Nat`),
so the faithful statement is the positivity `0 < 2^k`.

LaTTe sibling: `ai-math.collatz.modular-reduction :: pow-two-nat`. -/
theorem pow_two_nat (k : Nat) : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k

/-- For `k : Nat`, `3·2^k` is a natural number (positive). Mirror of LaTTe
`modular-reduction/three-times-pow-two-nat`.

LaTTe sibling: `ai-math.collatz.modular-reduction :: three-times-pow-two-nat`. -/
theorem three_times_pow_two_nat (k : Nat) : 0 < 3 * (2 : Nat) ^ k := by
  have := pow_two_nat k; omega

/-- **Sub-lemma D — REAL.** The core algebraic identity exposing `3n+1` as `2w`:

    `3·(2^(k+2)·p + 2^(k+1) - 1) + 1 = 2·(3·2^(k+1)·p + 3·2^k - 1)`.

Mirror of LaTTe `modular-reduction-sub-d/three-n-plus-one-equals-two-w`. The
LaTTe proof factors into 6 theorems to dodge the JVM method-size limit and to
keep every subtraction on `int`; here the identity is over `Nat`, and because
`2^(k+1) ≥ 1` and `3·2^k ≥ 1` every `Nat` subtraction is exact, so `omega`
(after splitting the powers and linearizing the `2^k · p` product) closes it.

LaTTe sibling: `ai-math.collatz.modular-reduction-sub-d ::
three-n-plus-one-equals-two-w`. -/
theorem three_n_plus_one_equals_two_w (k p : Nat) :
    3 * (2 ^ (k + 2) * p + (2 ^ (k + 1) - 1)) + 1
      = 2 * (3 * 2 ^ (k + 1) * p + 3 * 2 ^ k - 1) := by
  have hk : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hk2 : (2 : Nat) ^ (k + 2) = 4 * 2 ^ k := by
    rw [show k + 2 = k + 1 + 1 from rfl, pow_succ, hk]; ring
  rw [hk, hk2]
  -- linearize the 2^k * p product
  generalize hq : (2 : Nat) ^ k * p = q
  have hpos : 0 < (2 : Nat) ^ k := pow_two_nat k
  have e1 : 4 * 2 ^ k * p = 4 * q := by rw [← hq]; ring
  have e2 : 3 * (2 * 2 ^ k) * p = 6 * q := by rw [← hq]; ring
  rw [e1, e2]
  omega

/-- **Sub-lemma E — REAL.** The residue-difference identity providing the
divisibility witness for the conclusion:

    `(3·2^(k+1)·p + 3·2^k - 1) - (2^k - 1) = 2^(k+1)·(3p + 1)`.

Mirror of LaTTe `modular-reduction-sub-e/residue-difference-identity` (35
have-steps on `int`; one `omega` over `Nat` after power-splitting here).

LaTTe sibling: `ai-math.collatz.modular-reduction-sub-e ::
residue-difference-identity`. -/
theorem residue_difference_identity (k p : Nat) :
    (3 * 2 ^ (k + 1) * p + 3 * 2 ^ k - 1) - (2 ^ k - 1)
      = 2 ^ (k + 1) * (3 * p + 1) := by
  have hk : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hk]
  generalize hq : (2 : Nat) ^ k * p = q
  have hpos : 0 < (2 : Nat) ^ k := pow_two_nat k
  have e1 : 3 * (2 * 2 ^ k) * p = 6 * q := by rw [← hq]; ring
  have e2 : 2 * 2 ^ k * (3 * p + 1) = 6 * q + 2 * 2 ^ k := by rw [← hq]; ring
  rw [e1, e2]
  omega

/-- **modular-reduction-lemma — REAL** (reused from `FractalEscape`).

`n ≡ 2^(k+1) - 1 [MOD 2^(k+2)]  ⟹  co n ≡ 2^k - 1 [MOD 2^(k+1)]`, where
`co n = (3n+1)/2` is the non-compressed odd-Collatz step.

This is exactly `FractalEscape.modular_reduction_step` with the index shifted
(`FractalEscape` states it as `K → K+1 ⟹ K+1 → K+2`; reindex `K := k - 1`).
We restate it at index `k` for parity with the LaTTe `modular-reduction-lemma`
signature (`k : nat`, residue level `k+1` dropping to `k`).

LaTTe sibling: `ai-math.collatz.modular-reduction :: modular-reduction-lemma`. -/
theorem modular_reduction_lemma (k n : Nat)
    (hcong : n ≡ 2 ^ (k + 1) - 1 [MOD 2 ^ (k + 2)]) :
    co n ≡ 2 ^ k - 1 [MOD 2 ^ (k + 1)] := by
  -- FractalEscape.modular_reduction_step K n : level (K+2)→(K+1).
  -- Here level (k+1)→k corresponds to K+2 = k+1, K+1 = k, i.e. K = k - 1.
  -- Handle k = 0 separately (residue 2^0 - 1 = 0, modulus 2^1 = 2).
  match k with
  | 0 =>
    -- target: co n ≡ 0 [MOD 2].  hcong : n ≡ 1 [MOD 4].
    -- n ≡ 1 [MOD 4] ⟹ n odd ⟹ 3n+1 ≡ 0 [MOD 2]·... actually co n = (3n+1)/2.
    -- n = 4t+1 ⟹ 3n+1 = 12t+4 = 2(6t+2) ⟹ co n = 6t+2 even.
    have hmod : n % 4 = 1 := by
      have := hcong; rw [Nat.ModEq] at this; simpa using this
    have ht : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
    obtain ⟨t, ht⟩ := ht
    show co n ≡ 2 ^ 0 - 1 [MOD 2 ^ 1]
    rw [Nat.ModEq]
    unfold co
    have : 3 * n + 1 = 2 * (6 * t + 2) := by rw [ht]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    simp; omega
  | k + 1 =>
    -- level (k+2)→(k+1): exactly FractalEscape.modular_reduction_step k n.
    exact FractalEscape.modular_reduction_step k n hcong

/-- **The full modular-reduction ladder — REAL** (reused from `FractalEscape`).

Iterating `modular_reduction_lemma` `K` times: numbers at fractal level `K`
escape to the mod-4 case `1` in `K` `co`-steps. This is *already* ported as
`FractalEscape.fractal_escape_hierarchy_theorem`; restated here as the headline
consequence of the ladder for completeness of the LaTTe family.

LaTTe sibling: `ai-math.collatz.fractal-escape-hierarchy ::
fractal-escape-hierarchy-theorem`. -/
theorem modular_reduction_ladder (K n : Nat)
    (hcong : n ≡ 2 ^ (K + 1) - 1 [MOD 2 ^ (K + 2)]) :
    co^[K] n ≡ 1 [MOD 4] :=
  FractalEscape.fractal_escape_hierarchy_theorem K n hcong

/-! ## Part 2 — epoch-map

Closed forms of the `(L, m) → (L_next, m_next)` epoch recurrence, all corollaries
of `TerrasDensity.cascade_mult_exact`, and the `K = 0` negative result. We reuse
`TerrasDensity.cc` (compressed step) and `cascade_mult_exact` directly. -/

open TerrasDensity (cascade_mult_exact)

/-- **epoch-map-cc-formula — REAL.** For odd `n` with `v₂(n+1) = K+2`, writing
`m = (n+1)/2^(K+2)` (passed as the hypothesis `n + 1 = 2^(K+2)·m`):

    `cc^[K+1] n = 2·m·3^(K+1) - 1`.

Direct corollary of `cascade_mult_exact` + cancellation of `2^(K+1)`. The LaTTe
proof is a ~30-step `times-assoc`/`times-commute` rearrangement; here the
rearrangement is `ring`/`omega` after the cancellation.

LaTTe sibling: `ai-math.collatz.epoch-map :: epoch-map-cc-formula`. -/
theorem epoch_map_cc_formula (n K m : Nat)
    (hodd : FractalEscape.Odd n)
    (hv2 : padicValNat 2 (n + 1) = K + 2)
    (hm : n + 1 = 2 ^ (K + 2) * m) :
    cc^[K + 1] n = 2 * m * 3 ^ (K + 1) - 1 := by
  -- cascade_mult_exact : 2^(K+1) * (cc^[K+1] n + 1) = (n+1) * 3^(K+1).
  have hcme := cascade_mult_exact n K hodd hv2
  -- Substitute n+1 = 2^(K+2)*m and 2^(K+2) = 2 * 2^(K+1).
  have e21 : (2 : Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  rw [hm, e21] at hcme
  -- hcme : 2^(K+1) * (cc^[K+1] n + 1) = (2 * 2^(K+1) * m) * 3^(K+1)
  --      = 2^(K+1) * (2 * m * 3^(K+1)).
  set A := (2 : Nat) ^ (K + 1) with hA
  have hApos : 0 < A := Nat.two_pow_pos _
  have hcme2 : A * (cc^[K + 1] n + 1) = A * (2 * m * 3 ^ (K + 1)) := by
    rw [hcme]; ring
  have hcancel : cc^[K + 1] n + 1 = 2 * m * 3 ^ (K + 1) :=
    Nat.eq_of_mul_eq_mul_left hApos hcme2
  omega

/-- `m ≠ 0` is forced by `n + 1 = 2^(K+2) * m` (since `n + 1 > 0`). Helper for the
descent-numerator and `K=0` corollaries. -/
private theorem epoch_m_ne_zero (n K m : Nat) (hm : n + 1 = 2 ^ (K + 2) * m) :
    m ≠ 0 := by
  rintro rfl; simp at hm

/-- **epoch-map-descent-numerator — REAL.** Same hypotheses; the numerator form

    `3·(cc^[K+1] n) + 1 = 2·(m·3^(K+2) - 1)`.

Algebraic corollary of `epoch_map_cc_formula`: substitute the closed form and
expand `3·(2m·3^(K+1) - 1) + 1 = 2·(m·3^(K+2) - 1)`.

LaTTe sibling: `ai-math.collatz.epoch-map :: epoch-map-descent-numerator`. -/
theorem epoch_map_descent_numerator (n K m : Nat)
    (hodd : FractalEscape.Odd n)
    (hv2 : padicValNat 2 (n + 1) = K + 2)
    (hm : n + 1 = 2 ^ (K + 2) * m) :
    3 * (cc^[K + 1] n) + 1 = 2 * (m * 3 ^ (K + 2) - 1) := by
  have hcc := epoch_map_cc_formula n K m hodd hv2 hm
  have hmpos : 0 < m := Nat.pos_of_ne_zero (epoch_m_ne_zero n K m hm)
  -- positivity facts so Nat subtractions are exact
  have h3pos : 0 < (3 : Nat) ^ (K + 1) := pow_pos (by norm_num) _
  have hp3 : (3 : Nat) ^ (K + 2) = 3 * 3 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  rw [hcc, hp3]
  generalize hr : (3 : Nat) ^ (K + 1) = r at *
  -- need: 3*(2*m*r - 1) + 1 = 2*(m*(3*r) - 1), with r ≥ 1, m ≥ 1.
  have hrpos : 0 < r := by omega
  -- Collapse the two nonlinear products to a single atom x := m*r.
  set x := m * r with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have e1 : 2 * m * r = 2 * x := by rw [hx]; ring
  have e2 : m * (3 * r) = 3 * x := by rw [hx]; ring
  rw [e1, e2]
  omega

/-- **epoch-image-plus-one-eq-two-times-three-m — REAL.** The `K = 0`
specialization: `cc^[1] n + 1 = 2·(3·m)`. Purely algebraic (no parity on `m`).

LaTTe sibling: `ai-math.collatz.epoch-map ::
epoch-image-plus-one-eq-two-times-three-m`. -/
theorem epoch_image_plus_one_eq_two_times_three_m (n m : Nat)
    (hodd : FractalEscape.Odd n)
    (hv2 : padicValNat 2 (n + 1) = 0 + 2)
    (hm : n + 1 = 2 ^ (0 + 2) * m) :
    cc^[0 + 1] n + 1 = 2 * (3 * m) := by
  have hcc := epoch_map_cc_formula n 0 m hodd hv2 hm
  have hmpos : 0 < m := Nat.pos_of_ne_zero (epoch_m_ne_zero n 0 m hm)
  -- cc^[1] n = 2*m*3^1 - 1 = 6m - 1, so cc^[1] n + 1 = 6m = 2*(3*m).
  rw [hcc]
  simp only [zero_add, pow_one]
  -- 2*m*3 - 1 + 1 = 2*(3*m)
  omega

/-- **epoch-image-v2-eq-one-mod-8-3 — REAL.** The `K = 0` cascade image has
`v₂(cc^[1] n + 1) = 1`, hence is never spine-resident (spine needs `v₂ ≥ 2`).

For odd `n`, `v₂(n+1) = 2`, and `m` odd & nonzero with `n+1 = 4m`:
`cc^[1] n + 1 = 2·(3m)` with `3m` odd, so `v₂ = 1`.

LaTTe sibling: `ai-math.collatz.epoch-map :: epoch-image-v2-eq-one-mod-8-3`. -/
theorem epoch_image_v2_eq_one_mod_8_3 (n m : Nat)
    (hodd : FractalEscape.Odd n)
    (hv2 : padicValNat 2 (n + 1) = 0 + 2)
    (hm : n + 1 = 2 ^ (0 + 2) * m)
    (hm_odd : FractalEscape.Odd m) (_hm_nz : m ≠ 0) :
    padicValNat 2 (cc^[0 + 1] n + 1) = 1 := by
  have himg := epoch_image_plus_one_eq_two_times_three_m n m hodd hv2 hm
  rw [himg]
  -- 3*m is odd and nonzero; v₂(2 * odd) = 1.
  obtain ⟨j, hj⟩ := hm_odd
  have h3m_odd : (3 * m) % 2 = 1 := by rw [hj]; omega
  have h3m_nz : 3 * m ≠ 0 := by omega
  -- padicValNat 2 (2 * (3m)) = 1 + padicValNat 2 (3m), and padicValNat 2 (3m) = 0.
  have hv0 : padicValNat 2 (3 * m) = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right
    intro hdvd; omega
  have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
  rw [padicValNat.mul htwo_ne h3m_nz, padicValNat_self, hv0]

/-! ## Part 3 — compressed-orbit-bridge

`cc-comp(n) = odd-part(collatz-odd(n))` for odd `n`. We define `oddPart`
(mathlib `ord_compl`-style strip of 2-factors) and reuse `co` and `cc`. -/

/-- The odd part of `w`: strip every factor of 2. `oddPart w = w / 2^(v₂ w)`.
Mirror of LaTTe `ai-math.two-adic-valuation/odd-part`. -/
def oddPart (w : Nat) : Nat := w / 2 ^ padicValNat 2 w

/-- For `n = 2k+1`: `3n+1 = 2·(3k+2)`. Mirror of LaTTe
`compressed-orbit-bridge/three-n-plus-one-eq-double-of-3k-plus-2`.

LaTTe sibling: `ai-math.collatz.compressed-orbit-bridge ::
three-n-plus-one-eq-double-of-3k-plus-2`. -/
theorem three_n_plus_one_eq_double_of_3k_plus_2 (k n : Nat)
    (hn : n = 2 * k + 1) :
    3 * n + 1 = 2 * (3 * k + 2) := by rw [hn]; ring

/-- For `k : Nat`, `3k+2 > 0` (nat-closure + nonzero). Mirrors LaTTe
`three-k-plus-two-nat` and `three-k-plus-two-nz` together (on `Nat`, membership
is automatic; nonzeroness is the content).

LaTTe siblings: `ai-math.collatz.compressed-orbit-bridge ::
three-k-plus-two-nat` / `three-k-plus-two-nz`. -/
theorem three_k_plus_two_nz (k : Nat) : 3 * k + 2 ≠ 0 := by omega

/-- `oddPart` strips a factor of 2 from a nonzero argument:
`oddPart (2 * w) = oddPart w` for `w ≠ 0`. Mirror of LaTTe
`two-adic-valuation/odd-part-of-double` (the algebraic core of the bridge). -/
theorem oddPart_of_double (w : Nat) (hw : w ≠ 0) :
    oddPart (2 * w) = oddPart w := by
  unfold oddPart
  have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
  have hv : padicValNat 2 (2 * w) = padicValNat 2 w + 1 := by
    rw [padicValNat.mul htwo_ne hw, padicValNat_self]; omega
  rw [hv, pow_succ]
  -- 2*w / (2^(v) * 2) = w / 2^v
  rw [show 2 ^ padicValNat 2 w * 2 = 2 * 2 ^ padicValNat 2 w from by ring]
  rw [Nat.mul_div_mul_left w _ (by norm_num : 0 < 2)]

/-- **compressed-orbit-bridge — REAL.** For odd `n`,

    `cc n = oddPart (co n)`,

i.e. the compressed step equals the odd part of the non-compressed step.

For odd `n = 2k+1`: `3n+1 = 2·(3k+2)`, so `co n = (3n+1)/2 = 3k+2` and
`cc n = oddPart(3n+1) = oddPart(2·(3k+2)) = oddPart(3k+2) = oddPart(co n)`.

LaTTe sibling: `ai-math.collatz.compressed-orbit-bridge ::
cc-comp-eq-odd-part-of-collatz-odd`. -/
theorem cc_eq_oddPart_of_co (n : Nat) (hodd : FractalEscape.Odd n) :
    cc n = oddPart (co n) := by
  obtain ⟨k, hk⟩ := hodd
  -- 3n+1 = 2*(3k+2)
  have halg : 3 * n + 1 = 2 * (3 * k + 2) :=
    three_n_plus_one_eq_double_of_3k_plus_2 k n hk
  have hwnz : 3 * k + 2 ≠ 0 := three_k_plus_two_nz k
  -- co n = 3k+2
  have hco : co n = 3 * k + 2 := by
    unfold FractalEscape.co
    rw [halg, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  -- cc n = oddPart (3n+1) by definition (cc n = (3n+1)/2^(v₂(3n+1)) = oddPart(3n+1))
  have hcc : cc n = oddPart (3 * n + 1) := by unfold TerrasDensity.cc oddPart; rfl
  rw [hcc, halg, oddPart_of_double (3 * k + 2) hwnz, hco]

end CollatzModular
