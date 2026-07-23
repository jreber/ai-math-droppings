import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Basic
import Propositio.Collatz.Basic

/-!
# Lyapunov-H5 compressed: well-ordering / escape-time descent — Lean 4 mirror

Block 3, "Bucket 3" port of the project's *conditional* Collatz termination
results for the **compressed** odd-Collatz iterator.

LaTTe sibling file: `src/ai_math/collatz/lyapunov_h5_compressed.clj`.

## Faithfulness: this is CONDITIONAL work

The headline LaTTe results in `lyapunov_h5_compressed.clj` are deliberately
*conditional*.  The Lyapunov descent `h5-decrease-compressed` and the
termination claim `h5-well-ordering-compressed` are **NO-PROOF stubs** in
LaTTe — discharging either unconditionally is the Collatz conjecture itself.

What is genuinely REAL in LaTTe (8 theorems, 0 fake axioms) are the
*conditional* versions that take the Collatz-bearing content (the
`escape-time` recurrence behaviour under `cc`, and the existence of a
positive escape-time level — "coverage") as **explicit hypothesis
parameters**, never as trusted axioms.  This Lean port mirrors that exactly:
every Collatz-bearing fact is an explicit hypothesis on the theorem, so no
statement here claims unconditional Collatz convergence.

## How LaTTe's abstract operators are modelled here

LaTTe introduces `escape-time : int → int → int` by a bare *signature axiom*
(no definition); its mathematical content is pinned only by separate equation
axioms.  We mirror this by making `escapeTime : ℕ → ℕ → ℕ` an **opaque
section variable** — a port has no more information about it than LaTTe does.

  * `escapeTime n j`            ↔ LaTTe `escape-time`         (opaque variable)
  * `sumWeightedEscape e n K`   ↔ LaTTe `sum-weighted-escape` (REAL recursion;
        the LaTTe recurrence axioms `sum-weighted-escape-zero-K` /
        `-succ-K` become *definitional* lemmas here)
  * `HK e n := fun K => sumWeightedEscape e n K`   ↔ LaTTe `H-K`

The compressed step `cc` and oddness `Odd` are reused from `TerrasDensity`
(`cc n = (3n+1) / 2 ^ v₂(3n+1)` = odd part of `3n+1`, matching LaTTe
`collatz-odd-compressed`).  The LaTTe iterator `collatz-odd-compressed-iter m n`
is `cc^[m] n` (`Function.iterate`); LaTTe's `…-iter-zero`/`-succ`/`-assoc`
axioms are mathlib `Function.iterate_*` lemmas.

## Mapping LaTTe membership / ordering

LaTTe works over `int` with `(elem _ nat)` side-hypotheses; we work over `ℕ`
directly, so those membership hypotheses vanish and the corresponding LaTTe
structural-closure axioms (`escape-time-nat`, `sum-weighted-escape-nat`) are
free (`ℕ`-valued by type).  LaTTe `ord/<`, `ord/<=` are `Nat` `<`, `≤`.
-/

namespace CollatzH5

open TerrasDensity (cc)

/-- Local alias for `TerrasDensity.Odd` (`∃ k, n = 2k+1`), matching the LaTTe
HONEST `odd` predicate.  Aliased to avoid clashing with mathlib's `_root_.Odd`. -/
abbrev Odd (n : ℕ) : Prop := TerrasDensity.Odd n

/-! ## Oddness of one `cc` step

`cc n = (3n+1) / 2 ^ v₂(3n+1)` is the **odd part** of `3n+1`, hence always
odd (for `n` making `3n+1 ≠ 0`, i.e. every `n : ℕ`).  LaTTe carries this as the
REAL lemma `collatz-odd-compressed-is-odd`; the Lean codebase has no
unconditional version (only `cc_odd_of_odd_four_dvd`), so we prove it here via
mathlib's `Nat.not_dvd_ordCompl`. -/

/-- `Odd n ↔ ¬ 2 ∣ n`, bridging `TerrasDensity.Odd` (`∃ k, n = 2k+1`) and
divisibility. -/
theorem odd_iff_not_two_dvd (n : ℕ) : Odd n ↔ ¬ 2 ∣ n := by
  constructor
  · rintro ⟨k, rfl⟩; omega
  · intro h; exact ⟨n / 2, by omega⟩

/-- One `cc` step always yields an odd number: `cc n` is the odd part of
`3n+1`.  LaTTe sibling:
`ai-math.collatz.collatz-compressed/collatz-odd-compressed-is-odd`. -/
theorem cc_odd (n : ℕ) : Odd (cc n) := by
  rw [odd_iff_not_two_dvd]
  -- cc n = (3n+1) / 2^(padicValNat 2 (3n+1)) = ordCompl[2] (3n+1).
  have hne : (3 * n + 1) ≠ 0 := by omega
  have hfac : (3 * n + 1).factorization 2 = padicValNat 2 (3 * n + 1) :=
    Nat.factorization_def _ Nat.prime_two
  have hcc : cc n = ordCompl[2] (3 * n + 1) := by
    show (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) = (3 * n + 1) / 2 ^ (3 * n + 1).factorization 2
    rw [hfac]
  rw [hcc]
  exact Nat.not_dvd_ordCompl Nat.prime_two hne

/-! ## Abstract escape-time and the weighted sum -/

section EscapeTime

/- `escapeTime n j` — the (abstract) number of compressed odd-Collatz steps
for `n` to change residue mod `2^j`.

LaTTe sibling: `ai-math.lyapunov-h5-integers/escape-time` (a bare signature
`defaxiom`).  Kept opaque here as a section variable: a faithful port knows no
more about it than the LaTTe signature axiom does.  Its behaviour under one
`cc` step (the Collatz-bearing content) is supplied to the theorems below as
explicit hypotheses, exactly as LaTTe pins it via separate equation axioms. -/
variable (escapeTime : ℕ → ℕ → ℕ)

/-- `sumWeightedEscape escapeTime n K = Σ_{j=1}^{K} 2^(K-j) · escapeTime n j`.

LaTTe sibling: `ai-math.lyapunov-h5-integers/sum-weighted-escape`.  There it is
a signature axiom with two recurrence axioms (`-zero-K`, `-succ-K`); here it is
a REAL structural recursion on `K`, so those two axioms become the
definitional lemmas `sumWeightedEscape_zero` / `sumWeightedEscape_succ`. -/
def sumWeightedEscape : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, (K + 1) => 2 * sumWeightedEscape n K + escapeTime n (K + 1)

/-- LaTTe sibling: `ai-math.lyapunov-h5-integers/sum-weighted-escape-zero-K`. -/
@[simp] theorem sumWeightedEscape_zero (n : ℕ) :
    sumWeightedEscape escapeTime n 0 = 0 := rfl

/-- LaTTe sibling: `ai-math.lyapunov-h5-integers/sum-weighted-escape-succ-K`. -/
theorem sumWeightedEscape_succ (n K : ℕ) :
    sumWeightedEscape escapeTime n (K + 1)
      = 2 * sumWeightedEscape escapeTime n K + escapeTime n (K + 1) := rfl

/-- `HK escapeTime n K` — the H5 Lyapunov measure at truncation level `K`.

LaTTe sibling: `ai-math.lyapunov-h5-integers/H-K` (`H_K(n) = Σ 2^(K-j)·e(n,j)`,
realized by `sum-weighted-escape`). -/
def HK (n : ℕ) : ℕ → ℕ := fun K => sumWeightedEscape escapeTime n K

end EscapeTime

/-! ## β.3.c — escape-time recurrence under one `cc` step (as hypotheses)

In LaTTe these are the two OPERATOR-DEFINING axioms `escape-time-cc-step` and
`escape-time-cc-step-zero` plus the NO-PROOF coverage `escape-time-coverage`.
Here they are bundled as named `Prop`s so every theorem can carry them as
explicit hypotheses — keeping the Collatz-bearing content out of any axiom. -/

/-- One `cc` step decrements escape-time by exactly 1 when positive.

LaTTe sibling: `ai-math.collatz.lyapunov-h5-compressed/escape-time-cc-step`
(an OPERATOR-DEFINING `defaxiom`).  Carried here as a hypothesis. -/
def EscapeStepDecr (escapeTime : ℕ → ℕ → ℕ) : Prop :=
  ∀ n, Odd n → 1 < n → ∀ j, 0 < escapeTime n j →
    escapeTime (cc n) j = escapeTime n j - 1

/-- Once escaped at level `j`, `cc` leaves escape-time at 0.

LaTTe sibling: `ai-math.collatz.lyapunov-h5-compressed/escape-time-cc-step-zero`
(an OPERATOR-DEFINING `defaxiom`).  Carried here as a hypothesis. -/
def EscapeStepZero (escapeTime : ℕ → ℕ → ℕ) : Prop :=
  ∀ n, Odd n → ∀ j, escapeTime n j = 0 → escapeTime (cc n) j = 0

/-! ## β.3.d Lemma D1 — per-level monotonicity of escape-time -/

/-- Per-level monotonicity: one `cc` step does not increase escape-time.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/escape-time-monotone-under-cc-comp`.

CONDITIONAL: takes the two operator-defining recurrence facts as hypotheses
`hstep`, `hzero` (matching the LaTTe axioms cited in its proof). -/
theorem escapeTime_monotone_under_cc
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) (j : ℕ) :
    escapeTime (cc n) j ≤ escapeTime n j := by
  -- LaTTe: classical case-split on (escape-time n j = 0).
  rcases Nat.eq_zero_or_pos (escapeTime n j) with h0 | hpos
  · -- Case 1: escape-time n j = 0.  escape-time-cc-step-zero ⇒ both sides 0.
    rw [hzero n hodd j h0, h0]
  · -- Case 2: positive.  escape-time-cc-step ⇒ cc value = e - 1 < e.
    rw [hstep n hodd hgt j hpos]
    omega

/-! ## β.3.d Lemma D2 — H_K-monotonicity under one `cc` step -/

/-- `H_K`-monotonicity: one `cc` step does not increase the Lyapunov measure.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/H-K-monotone-under-cc-comp`.

CONDITIONAL on `hstep`, `hzero`.  Proof: `Nat.rec` on `K` (LaTTe `nat-induct`),
using Lemma D1 at each `succ K`. -/
theorem HK_monotone_under_cc
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) (K : ℕ) :
    HK escapeTime (cc n) K ≤ HK escapeTime n K := by
  unfold HK
  induction K with
  | zero => simp
  | succ x ih =>
    rw [sumWeightedEscape_succ, sumWeightedEscape_succ]
    have hlvl : escapeTime (cc n) (x + 1) ≤ escapeTime n (x + 1) :=
      escapeTime_monotone_under_cc escapeTime hstep hzero n hodd hgt (x + 1)
    omega

/-! ## β.3.d step helpers (low-j and high-j) -/

/-- Step helper (low j): if the weighted sum strictly drops at `K'`, it also
strictly drops at `succ K'`.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-decrease-compressed-step-low-j`.

CONDITIONAL on the strict IH `hIH` (mirroring the LaTTe `H-IH` parameter). -/
theorem h5_decrease_step_low_j
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) (Kp : ℕ)
    (hIH : sumWeightedEscape escapeTime (cc n) Kp < sumWeightedEscape escapeTime n Kp) :
    sumWeightedEscape escapeTime (cc n) (Kp + 1)
      < sumWeightedEscape escapeTime n (Kp + 1) := by
  -- LaTTe: unfold succ-K on both sides; lift strict IH by ×2; per-level ≤ from D1.
  rw [sumWeightedEscape_succ, sumWeightedEscape_succ]
  -- Per-level ≤ at the new top level (Kp+1) from D1.
  have htop : escapeTime (cc n) (Kp + 1) ≤ escapeTime n (Kp + 1) :=
    escapeTime_monotone_under_cc escapeTime hstep hzero n hodd hgt (Kp + 1)
  -- Doubling the strict drop dominates the (≤) top-level term.
  omega

/-- Step helper (high j): if `escapeTime n (succ K') > 0`, the weighted sum
strictly drops at level `succ K'`.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-decrease-compressed-step-high-j`.

CONDITIONAL on `hstep`, `hzero` (for `H_K`-monotonicity / the step decrement)
and on `hpostop : 0 < escapeTime n (succ K')`. -/
theorem h5_decrease_step_high_j
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) (Kp : ℕ)
    (hpostop : 0 < escapeTime n (Kp + 1)) :
    sumWeightedEscape escapeTime (cc n) (Kp + 1)
      < sumWeightedEscape escapeTime n (Kp + 1) := by
  rw [sumWeightedEscape_succ, sumWeightedEscape_succ]
  -- H_K-monotone at K' gives (≤) on the doubled prefix.
  have hpref : sumWeightedEscape escapeTime (cc n) Kp ≤ sumWeightedEscape escapeTime n Kp :=
    HK_monotone_under_cc escapeTime hstep hzero n hodd hgt Kp
  -- escape-time-cc-step gives the strict drop at the top level (since e > 0).
  have htop : escapeTime (cc n) (Kp + 1) = escapeTime n (Kp + 1) - 1 :=
    hstep n hodd hgt (Kp + 1) hpostop
  omega

/-! ## β.3.d MAIN — conditional Lyapunov descent

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-decrease-compressed-conditional`.

The unconditional `h5-decrease-compressed` is a NO-PROOF stub in LaTTe (it *is*
Collatz).  This conditional form takes the coverage existential at `(n, K)` as
the explicit hypothesis `hcov` — exactly the LaTTe `H-coverage` parameter. -/

/-- Coverage at `(n, K)`: some level `j ∈ {1..K}` has positive escape-time.

LaTTe sibling: the existential body of `escape-time-coverage` /
`h5-decrease-compressed-conditional`'s `H-coverage` parameter. -/
def Coverage (escapeTime : ℕ → ℕ → ℕ) (n K : ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ K ∧ 0 < escapeTime n j

/-- Conditional Lyapunov descent: assuming coverage at `(n, K)` and the
escape-time recurrence facts, one `cc` step strictly drops `H_K`.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-decrease-compressed-conditional`. -/
theorem h5_decrease_conditional
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) (K : ℕ) (_hKpos : 0 < K)
    (hcov : Coverage escapeTime n K) :
    HK escapeTime (cc n) K < HK escapeTime n K := by
  unfold HK
  -- LaTTe: nat-induct on K with a ∀j-valued predicate; here we strengthen the
  -- induction to "any covering level ≤ K forces the strict drop".
  -- P K' := ∀ j, 1 ≤ j → j ≤ K' → 0 < escapeTime n j →
  --           sumWeightedEscape (cc n) K' < sumWeightedEscape n K'
  suffices H : ∀ K', ∀ j, 1 ≤ j → j ≤ K' → 0 < escapeTime n j →
      sumWeightedEscape escapeTime (cc n) K' < sumWeightedEscape escapeTime n K' by
    obtain ⟨j, hj1, hjK, hjpos⟩ := hcov
    exact H K j hj1 hjK hjpos
  intro K'
  induction K' with
  | zero =>
    -- Base P 0: vacuous — 1 ≤ j and j ≤ 0 contradict.
    intro j hj1 hjK _; omega
  | succ x ih =>
    intro j hj1 hjK hjpos
    -- Case-split on j = succ x vs j ≤ x  (LaTTe: ord/le-lt-split j (succ x)).
    rcases Nat.lt_or_ge j (x + 1) with hjlt | hjge
    · -- j ≤ x: IH gives strict drop at x; step-low-j lifts to succ x.
      have hdrop : sumWeightedEscape escapeTime (cc n) x < sumWeightedEscape escapeTime n x :=
        ih j hj1 (by omega) hjpos
      exact h5_decrease_step_low_j escapeTime hstep hzero n hodd hgt x hdrop
    · -- j = succ x: escape-time n (succ x) > 0; step-high-j gives strict drop.
      have hjeq : j = x + 1 := by omega
      subst hjeq
      exact h5_decrease_step_high_j escapeTime hstep hzero n hodd hgt x hjpos

/-! ## α+11c helper — odd nat ≠ 1 is > 1 -/

/-- A natural number that is odd and not equal to one is greater than one.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/nat-odd-ne-one-implies-gt-one`. -/
theorem nat_odd_ne_one_implies_gt_one (n : ℕ) (hodd : Odd n) (hne : n ≠ 1) :
    1 < n := by
  obtain ⟨k, hk⟩ := hodd
  omega

/-! ## α+11c — conditional well-ordering on the compressed iterator

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-well-ordering-compressed-conditional`.

CONDITIONAL: the descent inequality `h5-decrease-compressed` is the explicit
hypothesis `hdescent` (a ∀-quantified inequality), NOT a citation of the
NO-PROOF stub.  The conclusion is termination of the `cc`-iterator at 1; it does
NOT claim unconditional Collatz convergence. -/

/-- The descent hypothesis: every odd `m > 1` strictly drops `H_K` under `cc`.

LaTTe sibling: the `H-descent` forall-parameter of
`h5-well-ordering-compressed-conditional`. -/
def HDescent (escapeTime : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ m, Odd m → 1 < m → HK escapeTime (cc m) K < HK escapeTime m K

/-- Conditional well-ordering / termination on the compressed iterator.

Assuming the Lyapunov descent inequality `hdescent`, every `cc`-trajectory from
an odd `n > 1` reaches 1 in finitely many steps: `∃ m, cc^[m] n = 1`.

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-well-ordering-compressed-conditional`.

Proof: strong induction on the Lyapunov value `h := HK n K`
(LaTTe `nat-strong-induct`), via mathlib `Nat.strong_induction_on`. -/
theorem h5_well_ordering_conditional
    (escapeTime : ℕ → ℕ → ℕ) (K : ℕ)
    (hdescent : HDescent escapeTime K)
    (n : ℕ) (hodd : Odd n) (_hgt : 1 < n) :
    ∃ m, cc^[m] n = 1 := by
  -- Strengthen to: P h := ∀ p, Odd p → HK p K = h → ∃ m, cc^[m] p = 1,
  -- proven by strong induction on h, then instantiate at h := HK n K, p := n.
  suffices H : ∀ h, ∀ p, Odd p → HK escapeTime p K = h → ∃ m, cc^[m] p = 1 by
    exact H (HK escapeTime n K) n hodd rfl
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro p hp hpeq
    -- Classical case-split on p = 1 (LaTTe: excluded middle on (= p one)).
    by_cases hp1 : p = 1
    · -- Case p = 1: witness m = 0; cc^[0] p = p = 1.
      exact ⟨0, by simp [hp1]⟩
    · -- Case p ≠ 1: p > 1, apply descent then the IH at the smaller value.
      have hpgt : 1 < p := nat_odd_ne_one_implies_gt_one p hp hp1
      -- h' := HK (cc p) K < HK p K = h.
      have hlt : HK escapeTime (cc p) K < HK escapeTime p K := hdescent p hp hpgt
      rw [hpeq] at hlt
      -- cc p is odd (TerrasDensity); apply IH at h' = HK (cc p) K.
      have hccodd : Odd (cc p) := cc_odd p
      obtain ⟨m', hm'⟩ := ih (HK escapeTime (cc p) K) hlt (cc p) hccodd rfl
      -- iterate-assoc: cc^[m'+1] p = cc^[m'] (cc p) = 1.
      exact ⟨m' + 1, by rw [Function.iterate_succ_apply]; exact hm'⟩

/-! ## β.3.d unconditional-body — doubly-conditional well-ordering on coverage

LaTTe sibling:
`ai-math.collatz.lyapunov-h5-compressed/h5-well-ordering-compressed-on-coverage`.

Chains `h5_decrease_conditional` (to build the per-`m` descent from per-`m`
coverage) into `h5_well_ordering_conditional`.  Still CONDITIONAL: a real proof
of the universal coverage hypothesis `hcovU` is the Collatz conjecture (or a
concrete escape-time redefinition). -/
theorem h5_well_ordering_on_coverage
    (escapeTime : ℕ → ℕ → ℕ)
    (hstep : EscapeStepDecr escapeTime) (hzero : EscapeStepZero escapeTime)
    (K : ℕ) (hKpos : 0 < K)
    (hcovU : ∀ m, Odd m → 1 < m → Coverage escapeTime m K)
    (n : ℕ) (hodd : Odd n) (hgt : 1 < n) :
    ∃ m, cc^[m] n = 1 := by
  -- Build the per-m descent hypothesis from per-m coverage (LaTTe: assume-closure).
  have hdescent : HDescent escapeTime K := by
    intro m hm hmgt
    exact h5_decrease_conditional escapeTime hstep hzero m hm hmgt K hKpos
      (hcovU m hm hmgt)
  exact h5_well_ordering_conditional escapeTime K hdescent n hodd hgt

end CollatzH5
