import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.Collatz.Basic.Tactics
import Propositio.Tactics

/-!
Block 3 (Terras density) — Lean 4 mirror of `src/ai_math/terras_density.clj`.

See `lean4/README.md` for build instructions. Toolchain pinned at
`lean4/lean-toolchain` (leanprover/lean4:v4.29.1, darwin_aarch64 native).

Each theorem below is paired with a `-- LaTTe sibling: <path>::<name>`
cross-reference. As new theorems land in the LaTTe file under Block 3
(C.2–C.5), add a mirror here in the same commit (per the
STATUS-block-3 C.6 "commit discipline" instruction). When LaTTe and
Lean 4 proofs diverge in structure (or one passes and the other
fails), file the divergence in the STATUS-block-3 progress log per
C.6's cross-validation policy.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17,
recorded in `feedback_mathlib4_ok.md`). Use `lake env lean TerrasDensity.lean`
to typecheck (or `lake build` to compile). `lakefile.lean` pins mathlib4
at the `v4.29.1` release tag (commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`), matching the pinned Lean 4
toolchain. The migration eliminated three operator-level axioms
(`count_upto`, `countUptoZ`, `countUptoZ_subadditive`) by switching to
`Nat.count` from `Mathlib.Data.Nat.Count`. `lake exe cache get` is
recommended to skip the multi-hour mathlib4 build (downloads the
upstream olean cache).

Cross-prover validation status (2026-05-17 promotion): the full
existential form of D14/D15/D16 (`count_residue_class_upper_bound`,
`count_residue_class_lower_bound`, `density_bounded_residue_class`) and
the C.5 bridge (`density_bounded_by_parity_vector`) are now REAL on the
Lean 4 side, proved via mathlib4's `Nat.count_modEq_card` (from
`Mathlib.Data.Int.CardIntervalMod`). The LaTTe siblings use the
operator-level axiom `count-residue-euclidean`; the Lean 4 mirrors are
axiom-free. The abstract-form `_abstract` theorems remain as
lightweight helpers and are still consumed by no caller; they may
be deleted in a future cleanup if no consumer materializes.
-/

namespace TerrasDensity

/-- `n` is even iff there exists `k : Nat` with `n = 2 * k`.

Matches the LaTTe sibling `ai-math.parity-integers/even`:
`(definition even [[n int]] (q/ex (lambda [k int] (= n (* two k)))))`.
-/
def Even (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

/-- `n` is odd iff there exists `k : Nat` with `n = 2 * k + 1`.

Matches the LaTTe sibling `ai-math.parity-integers/odd`:
`(definition odd [[n int]] (q/ex (lambda [k int] (= n (+ (* two k) one)))))`.
-/
def Odd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

/--
**Terras half-step T descends on positive evens.**

For every positive even natural number `n`, `n / 2 < n`. This is the
"T(n) := n / 2 on evens" fact that contributes the entire 1/2 mass of
F(1) in Terras's stopping-time density argument.

Note: the `Even n` hypothesis is structurally redundant in Lean 4 (where
`n / 2` is total integer division and `n / 2 < n` holds for any positive
`n`), but is kept for correspondence with the LaTTe sibling, whose
`quotient-by-two` operator only computes on doubles (its defining axiom
`quotient-by-two-of-double` requires the `2k` form).

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`quotient-by-two-of-even-lt-self`.
-/
theorem quotient_by_two_of_even_lt_self
    {n : Nat} (hn : n ≠ 0) (_heven : Even n) : n / 2 < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/--
**Terras half-step T strictly ascends on odd.**

For every odd natural number `n` (in particular every `n ≥ 1`),
`n < (3n + 1) / 2`. This is the "T(n) := (3n+1)/2 on odds" fact:
σ(n) ≠ 1 for any odd n, because T(n) > n. Together with the
companion `quotient_by_two_of_even_lt_self`, this formally
closes the F(1) = 1/2 hand-derivation:
σ(n) = 1 ⟺ n is even, for n ≥ 2.

Proof: open the `Odd n` witness `n = 2k+1`; then `3n+1 = 6k+4 = 2(3k+2)`
and `(3n+1)/2 = 3k+2`, and `2k+1 < 3k+2 ⟺ 0 < k+1`. The `omega`
tactic discharges the whole chain after substitution.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`quotient-by-two-of-three-n-plus-one-gt-self`.
The LaTTe proof is ~70 lines (helper `succ-k-plus-twice-k-plus-one-eq-thrice-k-plus-two`
plus the main lemma's algebra) because LaTTe doesn't have an omega
analogue and every arithmetic step is explicit. Lean 4 + omega
collapses the whole thing to two tactics. A clean instance of the
divergence-in-structure phenomenon called out in the
STATUS-block-3 C.6 cross-validation policy: same theorem, very
different proof shapes.
-/
theorem quotient_by_two_of_three_n_plus_one_gt_self
    {n : Nat} (hodd : Odd n) : n < (3 * n + 1) / 2 := by
  obtain ⟨k, hk⟩ := hodd
  subst hk
  omega

/-
F(2) closure — n ≡ 1 (mod 4) residue class.

For k : Nat, the integer 4k+1 satisfies:
  T(4k+1)  = (3*(4k+1)+1)/2  = (12k+4)/2 = 6k+2  = 2*(3k+1)
  T²(4k+1) = (6k+2)/2        = 3k+1
  T²(4k+1) < 4k+1            iff  k ≥ 1  (i.e. k ≠ 0).

Together with the F(1) facts above, this formally closes F(2) = 3/4:
  density{σ ≤ 2} = density{even} + density{≡1 mod 4} = 1/2 + 1/4 = 3/4.

LaTTe siblings: `src/ai_math/terras_density.clj` ::
  T-of-4k-plus-1-eq-two-times-3k-plus-1
  T-squared-of-4k-plus-1-eq-3k-plus-1
  T-squared-of-4k-plus-1-strict-descent

Cross-validation note: the LaTTe proofs are explicit ~30–80 line
have-chains (expansion-identity + four-k-eq-two-times-two-k + double-halving
for the algebra; decompose-rewrite-recombine for the inequality).
Lean 4 + omega trivializes all arithmetic after the witness substitution
n = 4*k+1. Same ~10× proof-size divergence as the F(1) theorems above.
-/

/--
**T(4k+1) = 2*(3k+1).**

For every `k : Nat`, the first Terras half-step maps `4k+1` to `2*(3k+1)`:
  T(4k+1) := (3*(4k+1)+1)/2 = (12k+4)/2 = 6k+2 = 2*(3k+1).

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-of-4k-plus-1-eq-two-times-3k-plus-1`.
-/
theorem t_of_4k_plus_1_eq_two_times_3k_plus_1
    (k : Nat) : (3 * (4 * k + 1) + 1) / 2 = 2 * (3 * k + 1) := by
  omega

/--
**T²(4k+1) = 3k+1.**

For every `k : Nat`, two Terras half-steps map `4k+1` to `3k+1`:
  T(4k+1) = 2*(3k+1), then T(2*(3k+1)) = (3k+1)/1 ... actually
  T(2*(3k+1)) = 2*(3k+1)/2 = 3k+1 (even case).

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-squared-of-4k-plus-1-eq-3k-plus-1`.
-/
theorem t_squared_of_4k_plus_1_eq_3k_plus_1
    (k : Nat) : ((3 * (4 * k + 1) + 1) / 2) / 2 = 3 * k + 1 := by
  omega

/--
**T²(4k+1) < 4k+1** for `k ≥ 1`.

For every `k : Nat` with `k ≠ 0`, two Terras half-steps strictly descend:
  T²(4k+1) = 3k+1 < 4k+1  ⟺  k ≥ 1.

This is the **F(2) closure** for the n ≡ 1 (mod 4) residue class:
every such n > 1 has stopping time σ(n) ≤ 2. Combined with
`quotient_by_two_of_even_lt_self` (even case, σ ≤ 1), it gives
the density bound F(2) = 3/4.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-squared-of-4k-plus-1-strict-descent`.
-/
theorem t_squared_of_4k_plus_1_strict_descent
    (k : Nat) (hk : k ≠ 0) : ((3 * (4 * k + 1) + 1) / 2) / 2 < 4 * k + 1 := by
  omega

/-
F(2) non-descent — n ≡ 3 (mod 4) case.

The following five theorems mirror the LaTTe F(2) non-descent landing
in `src/ai_math/terras_density.clj`.  Together with the F(2) descent
theorems for n ≡ 1 (mod 4) (Agent A), they formally close

  F(2) = 3/4 :  density{ σ ≤ 2 } = density{even} + density{≡1 mod 4}
              = 1/2 + 1/4 = 3/4.

Proof strategy (cascaded ascent):
  4k+3 is odd → 4k+3 < T(4k+3) = 6k+5.
  6k+5 is odd → T(4k+3) < T²(4k+3) = 9k+8.
  Hence 4k+3 < T²(4k+3), so 4k+3 ≤ T²(4k+3).
All of the arithmetic is discharged by `omega` after substitution.
-/

/--
**Algebraic helper: 4k+3 = 2*(2k+1)+1.**

Used to write 4k+3 in the 2m+1 form needed to apply the three-n-plus-one
identity for the first Terras step.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`four-k-plus-three-eq-two-times-two-k-plus-one-plus-one`.
-/
theorem four_k_plus_three_eq_two_times_two_k_plus_one_plus_one
    (k : Nat) : 4 * k + 3 = 2 * (2 * k + 1) + 1 := by
  omega

/--
**First Terras step: T(4k+3) = 3*(2k+1)+2.**

For n = 4k+3 (odd), T(n) = (3n+1)/2 = (12k+10)/2 = 6k+5 = 3*(2k+1)+2.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-of-4k-plus-3-eq-3-times-two-k-plus-one-plus-two`.
-/
theorem T_of_4k_plus_3_eq (k : Nat) :
    (3 * (4 * k + 3) + 1) / 2 = 3 * (2 * k + 1) + 2 := by
  omega

/--
**Algebraic helper: 3*(2k+1)+2 = 2*(3k+2)+1.**

Rewrites T(4k+3) = 6k+5 into the 2m+1 form needed for the second
Terras step, with m = 3k+2.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`six-k-plus-five-eq-two-times-3k-plus-two-plus-one`.
-/
theorem six_k_plus_five_eq_two_times_3k_plus_two_plus_one
    (k : Nat) : 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1 := by
  omega

/--
**T²(4k+3) = 3*(3k+2)+2.**

Second Terras step on the odd result T(4k+3) = 3*(2k+1)+2 = 6k+5:
  T(6k+5) = (3*(6k+5)+1)/2 = (18k+16)/2 = 9k+8 = 3*(3k+2)+2.
Both T-steps use the odd formula (3n+1)/2 since 6k+5 is odd.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-squared-of-4k-plus-3-eq-3-times-3k-plus-two-plus-two`.
-/
theorem T_squared_of_4k_plus_3_eq (k : Nat) :
    (3 * ((3 * (4 * k + 3) + 1) / 2) + 1) / 2 = 3 * (3 * k + 2) + 2 := by
  omega

/--
**F(2) non-descent: 4k+3 ≤ T²(4k+3) for all k.**

For every n ≡ 3 (mod 4), two Terras half-steps do NOT bring n below
itself, i.e., σ(n) > 2 for all such n.

Proof by cascaded ascent: 4k+3 is odd, so T(4k+3) > 4k+3.  The result
T(4k+3) = 6k+5 is also odd, so T²(4k+3) > T(4k+3) > 4k+3.  In
particular 4k+3 ≤ T²(4k+3).

Note: Lean 4 `omega` dispatches the two strict inequalities and the
transitive chain in a single step because all arithmetic is linear.
The LaTTe proof requires ~25 `have`-steps (cascaded
`quotient-by-two-of-three-n-plus-one-gt-self` applications + explicit
`lt-trans`) because LaTTe lacks an omega oracle.  This is a clean
instance of the proof-structure divergence noted in the C.6 policy.

LaTTe sibling: `src/ai_math/terras_density.clj` ::
`T-squared-of-4k-plus-3-non-descent`.
-/
theorem T_squared_of_4k_plus_3_non_descent (k : Nat) :
    4 * k + 3 ≤ (3 * ((3 * (4 * k + 3) + 1) / 2) + 1) / 2 := by
  omega

/-
**Parity-vector residue lemma at k = 1 (T1 base case).**

If `m` and `n` have the same parity (both even or both odd), then
`m % 2 = n % 2`, equivalently `2 ∣ (m - n)` (for `m ≥ n`) or the
signed version for integers.

We state it over `Nat` using `m % 2 = n % 2` as the conclusion,
which is the Lean 4 analogue of `(congruent m n two)` in the LaTTe
sibling.

LaTTe sibling: `src/ai_math/parity_vector.clj` ::
`parity-vector-eq-1`.

Cross-validation note: the LaTTe proof (~100 lines) case-splits on
(both even) / (both odd), opens each existential witness, and builds
the equality `(* two (- j i)) = (- m n)` by chaining
`times-dist-minus`, `minus-succ`, `minus-succ-pred`, and
`int/succ-of-pred`. Every arithmetic step is explicit.

The Lean 4 proof below collapses the entire argument to `omega` after
the parity hypothesis is destructured — the same ~10× divergence in
proof granularity observed for the earlier T-step theorems.
The mathematical content is identical.
-/
theorem parity_vector_eq_1 (m n : Nat) (h : m % 2 = 0 ↔ n % 2 = 0) :
    m % 2 = n % 2 := by
  omega

/-
**pow_two_coprime_three — 2^k is coprime to 3.**

For every `k : Nat` and `d : Int`, if `2^k ∣ 3 * d` then `2^k ∣ d`.

This is the key helper for the odd-case of the parity-vector residue lemma
(T1, Terras 1976): in the inductive step, the odd witnesses give
`2^k ∣ 3 * (a - b)`, and this lemma extracts `2^k ∣ (a - b)`.

The proof mirrors the LaTTe structure exactly:
  • Base k = 0: 1 ∣ d trivially.
  • Step k → k+1: 2^(k+1) ∣ 3d ⟹ 2^k ∣ 3d (divisibility factor).
    Parity case-split on d mod 2:
      d even (d = 2e): 2^(k+1) ∣ 6e = 2·(3e), so 2^k ∣ 3e; IH gives 2^k ∣ e,
                       so 2^(k+1) ∣ 2e = d.
      d odd  (d = 2e+1): 3d = 6e+3 is odd. But 2^(k+1) ∣ 3d means 2 ∣ 3d —
                         contradiction with 3d being odd (k+1 ≥ 1).

LaTTe sibling: `src/ai_math/parity_vector.clj` :: `pow-two-coprime-three`.

Cross-validation note: the LaTTe proof is ~250 lines because every arithmetic
step (cancellation, distribution, negation of witnesses) is explicit. The Lean 4
proof uses `omega` and `Int.dvd_antisymm`-style facts from the core library,
reducing the odd sub-case to a two-line contradiction and the even sub-case to
an `omega` discharge after extracting the witness. Proof-size divergence ~10×,
same pattern as all other Block 3 mirrors.
-/

/-- `2^k ∣ 3 * d → 2^k ∣ d` for any `k : Nat` and `d : Int`. -/
theorem pow_two_coprime_three (k : Nat) (d : Int) :
    (2 : Int) ^ k ∣ 3 * d → (2 : Int) ^ k ∣ d := by
  revert d
  induction k with
  | zero => intro d _; exact ⟨d, by simp⟩
  | succ k ih =>
    intro d ⟨w, hw⟩
    -- hw : 3 * d = 2^(k+1) * w,  where  2^(k+1) = 2^k * 2
    have hpow : (2 : Int) ^ (k + 1) = (2 : Int) ^ k * 2 := Int.pow_succ 2 k
    -- Case-split on parity of d.
    have hmod : d % 2 = 0 ∨ d % 2 = 1 := by omega
    cases hmod with
    | inl heven =>
      -- EVEN CASE: d = 2 * e.
      obtain ⟨e, he⟩ : ∃ e : Int, d = 2 * e := ⟨d / 2, by omega⟩
      -- Rewrite hw to get 3*(2*e) = 2^k * 2 * w.
      have hw2 : 3 * (2 * e) = (2 : Int)^k * 2 * w := by rw [← he, ← hpow]; exact hw
      -- Cancel factor 2: 3 * e = 2^k * w.
      have h3e : 3 * e = (2 : Int)^k * w :=
        Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (by
          calc (2 : Int) * (3 * e) = 3 * (2 * e) := by
                simp only [← Int.mul_assoc, Int.mul_comm 2 3]
            _ = (2 : Int)^k * 2 * w := hw2
            _ = 2 * ((2 : Int)^k * w) := by
                simp only [Int.mul_assoc, Int.mul_comm ((2:Int)^k) 2])
      -- IH gives 2^k | e.
      obtain ⟨u, hu⟩ := ih e ⟨w, h3e⟩
      -- 2^(k+1) | d = 2 * e = 2 * (2^k * u) = 2^(k+1) * u.
      exact ⟨u, by rw [he, hu, hpow]; simp only [Int.mul_assoc, Int.mul_comm ((2:Int)^k) 2]⟩
    | inr hodd =>
      -- ODD CASE: d odd ⟹ 3*d odd ⟹ 2 ∤ 3*d.
      -- But 2^(k+1) | 3*d ⟹ 2 | 3*d.  Contradiction.
      exfalso
      have h3d_odd : (3 * d) % 2 = 1 := by omega
      have h2_dvd : (2 : Int) ∣ 3 * d := by
        rw [hw, hpow]
        exact ⟨(2:Int)^k * w, by simp only [Int.mul_assoc, Int.mul_comm ((2:Int)^k) 2]⟩
      rw [Int.dvd_iff_emod_eq_zero] at h2_dvd
      omega

/-
**Parity-vector residue lemma — nat-restricted version (T1, Terras 1976).**

This is the main Block 3 C.3 result: if two natural numbers `m` and `n`
have the same length-`k` parity vector under the Terras half-step T, then
`m ≡ n (mod 2^k)`.

## Statement

For `m n k : Nat`, define the **parity-vector equality** predicate:
  `PVEq m n k := ∀ j < k, T^j(m) % 2 = T^j(n) % 2`
where `T n := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2`.

Then `PVEq m n k → 2^k ∣ (m - n : Int)`.

## Lean 4 encoding

We define `T` and its iterate directly on `Nat`, and state the divisibility
conclusion over `Int` (where subtraction is signed).

## Proof status

**FULLY PROVEN** (commit `0fad34f`, 2026-05-17). Nat-induction on `k`
generalizing `m` and `n`:
  - Base `k=0`: `2^0 = 1` divides everything (`Int.one_dvd`).
  - Step `k → k+1`: shift lemma extracts `PVEq (T m) (T n) k` from
    `PVEq m n (k+1)` via `T_iter`'s definitional equation. Same-parity
    at index 0 forced by `h 0`. IH applies to `(T m, T n)`.
    Case-split on `m % 2`:
    - Even: `m = 2*(m/2)`, `n = 2*(n/2)`; `(m : Int) - n = 2 * ((T m : Int) - (T n : Int))`,
      so `2^(k+1) ∣ m - n` follows from IH.
    - Odd: `2 * T m = 3*m + 1`, `2 * T n = 3*n + 1`, so
      `2 * ((T m : Int) - (T n : Int)) = 3 * ((m : Int) - n)`.
      Scale IH by 2 to get `2^(k+1) ∣ 3*(m-n)`, then apply
      `pow_two_coprime_three` to conclude.

LaTTe sibling: `src/ai_math/parity_vector.clj` ::
`parity-vector-residue-lemma-nat` (REAL — kernel-verified).

Cross-validation note: the LaTTe proof is ~380 have-steps because every
arithmetic step (T evaluation, divisibility witness construction, succ-cancel
for (2a+1)-(2b+1) = 2a-2b, etc.) is explicit. The Lean 4 proof, once T-iter is
encoded, should reduce to `induction k` + `omega` for the arithmetic and
`pow_two_coprime_three` for the odd coprimality step. The structural divergence
is ~10×, same as all prior Block 3 mirrors.
-/

-- Terras half-step T : Nat → Nat
def T (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

-- T-iterator: T^k(n)
def T_iter (n : Nat) : Nat → Nat
  | 0     => n
  | k + 1 => T_iter (T n) k

-- Parity-vector equality: m and n have the same length-k parity vector
def PVEq (m n : Nat) (k : Nat) : Prop :=
  ∀ j < k, T_iter m j % 2 = T_iter n j % 2

/--
**Parity-vector residue lemma for nat inputs (T1, Terras 1976).**

If `m` and `n` are natural numbers with the same length-`k` parity vector
(i.e., `T^j(m)` and `T^j(n)` have the same parity for all `j < k`),
then `2^k` divides `m - n` as integers.

LaTTe sibling: `src/ai_math/parity_vector.clj` ::
`parity-vector-residue-lemma-nat` — REAL (kernel-verified, 2026-05-17).

The LaTTe proof is ~380 have-steps via explicit nat-induction on k,
parity case-split via `parity-totality-nat`, and arithmetic witness
construction. The Lean 4 proof below (completed 2026-05-17, commit
`0fad34f`) collapses to nat-induction `generalizing m n` plus parity
case-split and `omega`, using `pow_two_coprime_three` for the odd
sub-case. Approximately 10× shorter than the LaTTe original — the
classic Lean 4 vs LaTTe divergence pattern called out in C.6.
-/
theorem parity_vector_residue_lemma_nat
    (m n k : Nat) (h : PVEq m n k) : (2 : Int) ^ k ∣ (m : Int) - (n : Int) := by
  induction k generalizing m n with
  | zero => exact Int.one_dvd _
  | succ k ih =>
    -- (a) Shift lemma: PVEq (T m) (T n) k
    have h_shift : PVEq (T m) (T n) k := by
      intro j hj
      have := h (j + 1) (Nat.succ_lt_succ hj)
      simp only [show T_iter m (j + 1) = T_iter (T m) j from rfl,
                 show T_iter n (j + 1) = T_iter (T n) j from rfl] at this
      exact this
    -- (b) Same parity at step 0
    have h_par : m % 2 = n % 2 := by
      have := h 0 (Nat.zero_lt_succ k)
      simp only [show T_iter m 0 = m from rfl, show T_iter n 0 = n from rfl] at this
      exact this
    -- (c) IH applied to T m, T n
    have ih_div : (2 : Int) ^ k ∣ (T m : Int) - (T n : Int) := ih (T m) (T n) h_shift
    -- (d) Case split on parity of m
    by_cases hm : m % 2 = 0
    · -- Even case: T m = m / 2, T n = n / 2; (m : Int) − n = 2 * (T m − T n)
      have hn : n % 2 = 0 := by omega
      have hTm : T m = m / 2 := by simp [T, hm]
      have hTn : T n = n / 2 := by simp [T, hn]
      have hid : (m : Int) - (n : Int) = 2 * (((T m : Nat) : Int) - ((T n : Nat) : Int)) := by
        rw [hTm, hTn]
        have hm2 : m = 2 * (m / 2) := by omega
        have hn2 : n = 2 * (n / 2) := by omega
        have : (m : Int) = 2 * ((m / 2 : Nat) : Int) := by exact_mod_cast hm2
        have : (n : Int) = 2 * ((n / 2 : Nat) : Int) := by exact_mod_cast hn2
        omega
      obtain ⟨w, hw⟩ := ih_div
      refine ⟨w, ?_⟩
      have : (2 : Int) ^ (k + 1) * w = 2 * ((2 : Int) ^ k * w) := by
        change (2 : Int) ^ k * 2 * w = 2 * ((2 : Int) ^ k * w)
        rw [Int.mul_comm ((2 : Int) ^ k) 2, Int.mul_assoc]
      rw [hid, hw]; omega
    · -- Odd case: 2 * (T m − T n) = 3 * (m − n); use pow_two_coprime_three
      have hTm_eq : 2 * T m = 3 * m + 1 := by
        simp [T, show m % 2 ≠ 0 from by omega]; omega
      have hTn_eq : 2 * T n = 3 * n + 1 := by
        simp [T, show n % 2 ≠ 0 from by omega]; omega
      have hid : 2 * (((T m : Nat) : Int) - ((T n : Nat) : Int)) =
          3 * ((m : Int) - (n : Int)) := by
        have : 2 * ((T m : Nat) : Int) = 3 * (m : Int) + 1 := by exact_mod_cast hTm_eq
        have : 2 * ((T n : Nat) : Int) = 3 * (n : Int) + 1 := by exact_mod_cast hTn_eq
        omega
      obtain ⟨w, hw⟩ := ih_div
      have h_3 : (2 : Int) ^ (k + 1) ∣ 3 * ((m : Int) - (n : Int)) := by
        refine ⟨w, ?_⟩
        have hmul : (2 : Int) ^ (k + 1) * w = 2 * ((2 : Int) ^ k * w) := by
          change (2 : Int) ^ k * 2 * w = 2 * ((2 : Int) ^ k * w)
          rw [Int.mul_comm ((2 : Int) ^ k) 2, Int.mul_assoc]
        rw [← hid, hw]; omega
      exact pow_two_coprime_three (k + 1) _ h_3

/-
C.4 Natural density infrastructure — D10 numerator scaling.

The density-bounded predicate (epsilon-bound formulation, no reals):
  density_bounded A p q  :=  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → q * count_upto A N ≤ p * N

where count_upto A N = |{k : 0 ≤ k ≤ N | A k}|.

count_upto is defined as a thin wrapper over `Nat.count` from
`Mathlib.Data.Nat.Count` (`Nat.count P n` counts k < n satisfying P, so
`count_upto A N := Nat.count A (N + 1)` counts k ≤ N). We use
`Classical.dec` to make the definition apply to arbitrary `Prop`-valued
predicates without a `DecidablePred` constraint on the API surface,
matching the LaTTe sibling's untyped operator.

Note: `density_bounded` here uses `A : Nat → Prop` (deliberately restricted
to the Nat domain) whereas the LaTTe sibling uses predicates over `int`.
The C.4 application is density of natural-number subsets, so the restriction
is benign — but per C.6 cross-validation policy this divergence is documented.
-/

attribute [local instance] Classical.propDecidable

/-- Counting operator: number of k ≤ N satisfying A. Defined via
    `Nat.count` from mathlib (Migration 2026-05-17: previously an axiom).
    Uses the local `Classical.propDecidable` instance so the definition
    applies to arbitrary `Prop`-valued predicates without surfacing a
    `DecidablePred` constraint on the API. -/
noncomputable def count_upto (A : Nat → Prop) (N : Nat) : Nat :=
  Nat.count A (N + 1)

/-- density_bounded A p q: density of A is bounded above by p/q for all large N. -/
def density_bounded (A : Nat → Prop) (p q : Nat) : Prop :=
  ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → q * count_upto A N ≤ p * N

/-- density_bounded_below A p q: density of A is bounded below by p/q for all large N.
Dual of `density_bounded`. Together they sandwich the density at exactly p/q.

LaTTe sibling: `ai-math.natural-density/density-bounded-below` (definition). -/
def density_bounded_below (A : Nat → Prop) (p q : Nat) : Prop :=
  ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → p * N ≤ q * count_upto A N

/--
**D10 (REAL): Same-denominator numerator scaling.**

If `p ≤ p'` and `density_bounded A p q` then `density_bounded A p' q`.

Proof: take the same witness `N₀` from `density_bounded A p q`.
For each `N ≥ N₀`:
  - the hypothesis gives `q * count_upto A N ≤ p * N`;
  - `Nat.mul_le_mul_right N hle` (or `omega`) gives `p * N ≤ p' * N`;
  - `Nat.le_trans` chains the two inequalities.

LaTTe sibling: `src/ai_math/natural_density.clj` ::
`density-bounded-scale-num`.
-/
theorem density_bounded_scale_num
    {A : Nat → Prop} {p p' q : Nat}
    (hle : p ≤ p')
    (hbnd : density_bounded A p q) : density_bounded A p' q := by
  obtain ⟨N₀, hinner⟩ := hbnd
  exact ⟨N₀, fun N hN => Nat.le_trans (hinner N hN) (Nat.mul_le_mul_right N hle)⟩

-- ============================================================
-- D10-cross (density_bounded_scale) -- cross-multiplication scaling (Project 2)
--
-- LaTTe siblings:
--   src/ai_math/natural_density.clj :: density-bounded-scale  (REAL theorem)
--
-- Formulation: density_bounded A p q and p*q' ≤ p'*q (with q > 0, q' : Nat)
-- implies density_bounded A p' q'.
-- Proof sketch:
--   - Unpack N₀ from density_bounded A p q.
--   - Scale bound q*cu ≤ p*N by q' to get q*q'*cu ≤ p*q'*N
--   - Apply cross: p*q'*N ≤ p'*q*N
--   - Rearrange and cancel q (q > 0) to get q'*cu ≤ p'*N.
-- ============================================================

/-- D10-cross: Cross-multiplication density bound scaling (REAL).

If `density_bounded A p q` and `p * q' ≤ p' * q` (with `q > 0`) then
`density_bounded A p' q'`.

This generalises `density_bounded_scale_num` (fixed denominator) to arbitrary
rational comparisons p/q ≤ p'/q'. (Uses Nat-indexed density_bounded.)

LaTTe sibling: `src/ai_math/natural_density.clj` ::
`density-bounded-scale`.
-/
theorem density_bounded_scale
    {A : Nat → Prop} {p p' q q' : Nat}
    (hq_pos : 0 < q)
    (hcross : p * q' ≤ p' * q)
    (hbnd : density_bounded A p q) : density_bounded A p' q' := by
  obtain ⟨N₀, hinner⟩ := hbnd
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : q * count_upto A N ≤ p * N := hinner N hN
  have h2 : q * q' * count_upto A N ≤ p * q' * N := by
    calc q * q' * count_upto A N
        = q' * (q * count_upto A N) := by ring
      _ ≤ q' * (p * N)               := Nat.mul_le_mul_left q' h1
      _ = p * q' * N                 := by ring
  have h3 : p * q' * N ≤ p' * q * N := Nat.mul_le_mul_right N hcross
  have h4 : q * q' * count_upto A N ≤ p' * q * N := Nat.le_trans h2 h3
  have h7 : q * (q' * count_upto A N) ≤ q * (p' * N) := by linarith [h4]
  exact Nat.le_of_mul_le_mul_left h7 hq_pos

-- (density_zero_monotone_subset + density_zero_inter moved below — they
-- depend on DensityZeroZ / countUptoZ defined in Session 4.)

-- ============================================================
-- D12 -- DensityZero and density_zero_union (Session 4)
--
-- LaTTe siblings:
--   src/ai_math/natural_density.clj :: density-zero        (definition)
--   src/ai_math/natural_density.clj :: density-zero-union  (REAL theorem)
--   src/ai_math/natural_density.clj :: half-nat            (REAL helper)
--   src/ai_math/natural_density.clj :: times-succ-one-le-cancel (REAL helper)
--
-- Formulation: countUptoZ is defined as a thin wrapper over `Nat.count`
-- from mathlib4; subadditivity (D9) is proven by induction on N using
-- `Nat.count_succ`. (Migration 2026-05-17: previously countUptoZ and
-- countUptoZ_subadditive were both axioms; user authorization to use
-- mathlib4 enabled converting them to a real definition + real theorem.)
-- density_zero_union then follows without sorry via explicit arithmetic.
-- The proof mirrors the LaTTe argument: instantiate at (p, q+q),
-- apply D9+monotonicity to get (q+q)*cuAB ≤ 2*(p*N), factor 2*(q*cuAB)
-- = (q+q)*cuAB, cancel 2 via omega.
-- ============================================================

/-- Counting operator over Int: number of integers `0 ≤ k ≤ N` satisfying A.
For `N < 0` we return 0 (vacuous lower bound). Defined via `Nat.count` after
casting through `Int.toNat`; the local `Classical.propDecidable` attribute
above supplies `DecidablePred` for arbitrary `Prop` predicates so the
API surface stays untyped. (Migration 2026-05-17: previously an axiom.) -/
noncomputable def countUptoZ (A : Int → Prop) (N : Int) : Int :=
  (Nat.count (fun n : Nat => A (n : Int)) (N.toNat + 1) : Int)

/-- Helper: subadditivity of `Nat.count` for the disjunction of two predicates.
For any A, B : Nat → Prop and any m : Nat,
`count (A ∨ B) m ≤ count A m + count B m`.
Proven by induction on m, peeling one element at a time via `count_succ`. -/
theorem nat_count_or_le
    (A B : Nat → Prop) [DecidablePred A] [DecidablePred B]
    [DecidablePred (fun n => A n ∨ B n)] (m : Nat) :
    Nat.count (fun n => A n ∨ B n) m ≤ Nat.count A m + Nat.count B m := by
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    have hAB := Nat.count_succ (fun n => A n ∨ B n) k
    have hA  := Nat.count_succ A k
    have hB  := Nat.count_succ B k
    have hstep :
        (if A k ∨ B k then 1 else 0)
          ≤ (if A k then 1 else 0) + (if B k then 1 else 0) := by
      by_cases hA' : A k <;> by_cases hB' : B k <;> simp [hA', hB']
    rw [hAB, hA, hB]
    omega

/-- D9 (subadditivity, REAL — was an axiom prior to mathlib4 migration).
For any predicates A, B over Int and any N ≥ 0,
`countUptoZ (A ∨ B) N ≤ countUptoZ A N + countUptoZ B N`.

Proof: invoke `nat_count_or_le` for the underlying `Nat.count` bound,
then cast to `Int`. The decidability-instance discrepancy between the
goal's `Classical.propDecidable` and `nat_count_or_le`'s
`instDecidableOr` is resolved by `Nat.count`-invariance under swapping
propositionally-equal `DecidablePred` instances, formalized via
`Subsingleton.elim` on the decidability subsingleton. -/
theorem countUptoZ_subadditive (A B : Int → Prop) (N : Int) (_hN : 0 ≤ N) :
    countUptoZ (fun n => A n ∨ B n) N ≤ countUptoZ A N + countUptoZ B N := by
  -- The underlying Nat.count bound (with `nat_count_or_le`'s own instances).
  have hcore :
      Nat.count (fun n : Nat => A (n : Int) ∨ B (n : Int)) (N.toNat + 1)
        ≤ Nat.count (fun n : Nat => A (n : Int)) (N.toNat + 1)
          + Nat.count (fun n : Nat => B (n : Int)) (N.toNat + 1) :=
    nat_count_or_le _ _ _
  -- Rewrite the LHS Nat.count instance to whatever instance the goal expects.
  -- `Nat.count` doesn't actually use the DecidablePred proof in its value,
  -- so `Subsingleton.elim` of the two instances suffices.
  have hinst :
      @Nat.count (fun n : Nat => A (n : Int) ∨ B (n : Int)) _ (N.toNat + 1)
        = @Nat.count (fun n : Nat => A (n : Int) ∨ B (n : Int))
            (Classical.decPred _) (N.toNat + 1) :=
    congrArg (fun (inst : DecidablePred (fun n : Nat => A (n : Int) ∨ B (n : Int))) =>
              @Nat.count _ inst (N.toNat + 1)) (Subsingleton.elim _ _)
  rw [hinst] at hcore
  unfold countUptoZ
  exact_mod_cast hcore

/-- Density-bounded: A is bounded by ratio p/q.
    ∃ N₀ : Int, ∀ N ≥ N₀ with N ≥ 0: q * countUptoZ(A,N) ≤ p * N. -/
def DensityBoundedZ (A : Int → Prop) (p q : Int) : Prop :=
  ∃ N₀ : Int, ∀ N : Int, 0 ≤ N → N₀ ≤ N →
    q * countUptoZ A N ≤ p * N

/-- Density zero: for every positive rational p/q, A is density-bounded by p/q. -/
def DensityZeroZ (A : Int → Prop) : Prop :=
  ∀ (p q : Int), 0 < p → 0 < q → DensityBoundedZ A p q

/-- Factor-of-2 cancellation: 2*a ≤ 2*b → a ≤ b.  Proved by omega. -/
private theorem two_mul_le_cancel {a b : Int} (h : 2 * a ≤ 2 * b) : a ≤ b := by
  omega

/--
**D12 (REAL): density_zero_union** — no sorry.

If A and B both have density zero, so does their pointwise union A∪B.

LaTTe sibling: `src/ai_math/natural_density.clj` :: `density-zero-union` (REAL).

Proof (mirrors LaTTe argument exactly):
1. For goal DensityBoundedZ (A∪B) p q, instantiate hzA, hzB at (p, q+q).
2. Get N₀A, N₀B; witness max(N₀A, N₀B).
3. For N ≥ max(N₀A,N₀B): (q+q)*cuAB ≤ (q+q)*(cuA+cuB) [D9+monotone]
                         = (q+q)*cuA + (q+q)*cuB ≤ p*N + p*N.
4. Rewrite: (q+q)*cuAB = 2*(q*cuAB) and p*N+p*N = 2*(p*N).
5. Cancel 2 via two_mul_le_cancel.
-/
theorem density_zero_union (A B : Int → Prop)
    (hzA : DensityZeroZ A) (hzB : DensityZeroZ B) :
    DensityZeroZ (fun n => A n ∨ B n) := by
  intro p q hpp hqp
  obtain ⟨N₀A, hbA⟩ := hzA p (q + q) hpp (by omega)
  obtain ⟨N₀B, hbB⟩ := hzB p (q + q) hpp (by omega)
  exact ⟨max N₀A N₀B, fun N hnn hge => by
    have hgeA : N₀A ≤ N := Int.le_trans (Int.le_max_left N₀A N₀B) hge
    have hgeB : N₀B ≤ N := Int.le_trans (Int.le_max_right N₀A N₀B) hge
    have hbAN : (q + q) * countUptoZ A N ≤ p * N := hbA N hnn hgeA
    have hbBN : (q + q) * countUptoZ B N ≤ p * N := hbB N hnn hgeB
    have hsub : countUptoZ (fun n => A n ∨ B n) N ≤ countUptoZ A N + countUptoZ B N :=
      countUptoZ_subadditive A B N hnn
    have hqq_nn : (0 : Int) ≤ q + q := by omega
    have hmul : (q + q) * countUptoZ (fun n => A n ∨ B n) N ≤
                (q + q) * (countUptoZ A N + countUptoZ B N) :=
      Int.mul_le_mul_of_nonneg_left hsub hqq_nn
    have hchain : (q + q) * countUptoZ (fun n => A n ∨ B n) N ≤ p * N + p * N :=
      Int.le_trans hmul (by rw [Int.mul_add]; exact Int.add_le_add hbAN hbBN)
    apply two_mul_le_cancel
    calc 2 * (q * countUptoZ (fun n => A n ∨ B n) N)
        = (q + q) * countUptoZ (fun n => A n ∨ B n) N := by
            rw [show q + q = 2 * q from by omega, Int.mul_assoc]
      _ ≤ p * N + p * N := hchain
      _ = 2 * (p * N) := by omega⟩

-- ============================================================
-- density_zero_monotone_subset (helper for D13) (Project 2)
--
-- LaTTe siblings:
--   src/ai_math/natural_density.clj :: density-zero-monotone-subset  (REAL)
-- Note: Uses Int-based DensityZeroZ to match the LaTTe source (density-zero on int).
-- Moved here from earlier in the file (2026-05-18 Bob session) to satisfy
-- forward-reference requirements: depends on DensityZeroZ + countUptoZ.
-- ============================================================

/-- Density-zero is monotone under subset (Int-indexed): if C ⊆ A and
DensityZeroZ A then DensityZeroZ C.

Proof: for each (p, q) with p,q > 0, extract DensityBoundedZ A p q from
hzero, then note countUptoZ C N ≤ countUptoZ A N by the inclusion C ⊆ A,
and apply monotonicity of the bound.

LaTTe sibling: `src/ai_math/natural_density.clj` ::
`density-zero-monotone-subset`.
-/
theorem density_zero_monotone_subset
    {A C : Int → Prop}
    (hsub : ∀ n, C n → A n)
    (hzero : DensityZeroZ A) : DensityZeroZ C := by
  intro p q hp hq
  obtain ⟨N₀, hinner⟩ := hzero p q hp hq
  refine ⟨N₀, fun N hNn hN => ?_⟩
  have hbnd : q * countUptoZ A N ≤ p * N := hinner N hNn hN
  have hle : countUptoZ C N ≤ countUptoZ A N := by
    unfold countUptoZ
    apply Int.ofNat_le.mpr
    exact Nat.count_mono_left (fun k _ => hsub k)
  linarith [Int.mul_le_mul_of_nonneg_left hle (Int.le_of_lt hq)]

-- ============================================================
-- D13 (density_zero_inter) -- Project 2
--
-- LaTTe siblings:
--   src/ai_math/natural_density.clj :: density-zero-inter  (REAL theorem)
-- Note: Uses Int-based DensityZeroZ.
-- ============================================================

/-- D13: Intersection of two density-zero sets is density-zero (REAL).

If `DensityZeroZ A` and `DensityZeroZ B` then `DensityZeroZ (A ∩ B)`.

Proof: A ∩ B ⊆ A (projection), so by `density_zero_monotone_subset`.

LaTTe sibling: `src/ai_math/natural_density.clj` ::
`density-zero-inter`.
-/
theorem density_zero_inter
    {A B : Int → Prop}
    (hzA : DensityZeroZ A)
    (_hzB : DensityZeroZ B) : DensityZeroZ (fun n => A n ∧ B n) :=
  density_zero_monotone_subset (fun _ h => h.1) hzA

/-!
## D14 + D15 — Residue class count bounds (C.4 Session 4b)

LaTTe siblings:
  `ai-math.natural-density/count-residue-class-lower`  (D14)
  `ai-math.natural-density/count-residue-class-upper`  (D15)

The two `_abstract` theorems below are stated at the abstract arithmetic
level (taking `cu` as a parameter satisfying the Euclidean floor bound
`q ≤ cu ≤ q + 1` where `q = N / m`). They remain as helper lemmas. The
**full existential-form promotions**, citing mathlib4's
`Nat.count_modEq_card` directly, appear lower in the file as
`count_residue_class_upper_bound`, `count_residue_class_lower_bound`,
and the headline theorem `density_bounded_residue_class`.

No Finset imports are needed for the abstract form — the proof is purely
arithmetic.
-/

/--
**D15 — upper bound**: `m * cu ≤ N + m`.

Abstract form: given `m > 0`, `m * q ≤ N`, `cu ≤ q + 1`,
we have `m * cu ≤ N + m`.

LaTTe sibling: `ai-math.natural-density/count-residue-class-upper`.
-/
theorem count_residue_class_upper_abstract
    (m N q cu : Nat)
    (_hm : 0 < m)
    (hmq : m * q ≤ N)
    (hcu : cu ≤ q + 1) :
    m * cu ≤ N + m := by
  have h1 : m * cu ≤ m * (q + 1) := Nat.mul_le_mul_left m hcu
  have h2 : m * (q + 1) = m * q + m := Nat.mul_succ m q
  have _h3 : m * q + m ≤ N + m := Nat.add_le_add_right hmq m
  omega

/--
**D14 — lower bound**: `N - m ≤ m * cu` (Nat subtraction).

Abstract form: given `m > 0`, `N < m * q + m`, `q ≤ cu`,
we have `N - m ≤ m * cu`.

LaTTe sibling: `ai-math.natural-density/count-residue-class-lower`.
-/
theorem count_residue_class_lower_abstract
    (m N q cu : Nat)
    (_hm : 0 < m)
    (hNlt : N < m * q + m)
    (hq : q ≤ cu) :
    N - m ≤ m * cu := by
  calc N - m ≤ m * q := by omega
    _ ≤ m * cu := Nat.mul_le_mul_left m hq

/-!
## D16 — density-bounded-residue-class (C.4 Session 5)

LaTTe sibling:
  `ai-math.natural-density/density-bounded-residue-class`

Supporting helpers (also REAL in LaTTe):
  `ai-math.natural-density/lt-impl-succ-le`
  `ai-math.natural-density/times-le-cancel-nat-pos`

The residue class {n : n ≡ r (mod m)} is density-bounded above by
p/q for any p/q > 1/m (encoded as p*m > q).

Proof approach (matching the LaTTe proof):
  Witness N₀ = q*m.  For N ≥ q*m:
    (1) D15: m*cu ≤ N + m
    (2) q*m*cu ≤ q*(N+m) = q*N + q*m       [scale by q]
    (3) q*N + q*m ≤ q*N + N               [q*m ≤ N]
    (4) q*N + N = (q+1)*N                   [factor]
    (5) (q+1)*N ≤ p*m*N                    [q+1 ≤ p*m since q < p*m]
    (6) q*m*cu ≤ p*m*N                     [chain]
    (7) cancel m: q*cu ≤ p*N               [m > 0]

In Lean 4 (core stdlib, omega), this reduces to pure arithmetic
given the abstract cu satisfying D15's bound.
-/

/--
**lt-impl-succ-le**: `q < b → q + 1 ≤ b` (core arithmetic helper).
-/
theorem lt_impl_succ_le (q b : Nat) (h : q < b) : q + 1 ≤ b := h

/--
**times-le-cancel-nat-pos**: For k > 0, `k * x ≤ k * y → x ≤ y`.
-/
theorem times_le_cancel_nat_pos (k x y : Nat) (hk : 0 < k) (h : k * x ≤ k * y) : x ≤ y :=
  Nat.le_of_mul_le_mul_left h hk

/--
**D16 — density-bounded-residue-class** (abstract arithmetic form, helper).

Given m > 0, q < p*m, and `cu` satisfying the D15 upper bound
`m * cu ≤ N + m`, with N ≥ q*m, this proves `q * cu ≤ p * N`.

This abstract form remains as a lightweight helper. The **full
`density_bounded` existential** is now also proved in this file as
`density_bounded_residue_class` (see below), which cites mathlib4's
`Nat.count_modEq_card` directly — eliminating the need for the
abstract `cu` parameter and matching the LaTTe sibling's full
existential statement axiom-free on the Lean 4 side.

LaTTe sibling: `ai-math.natural-density/density-bounded-residue-class`
(proves the full existential form, kernel-verified, depends on the
operator axiom `count-residue-euclidean`).
-/
theorem density_bounded_residue_class_abstract
    (m p q N cu : Nat)
    (hm : 0 < m)
    (hfrac : q < p * m)
    (hD15 : m * cu ≤ N + m)
    (hN0 : q * m ≤ N) :
    q * cu ≤ p * N := by
  -- From D15: m*cu ≤ N+m; scale left by q: q*(m*cu) ≤ q*(N+m)
  have hD15q : q * (m * cu) ≤ q * (N + m) :=
    Nat.mul_le_mul_left q hD15
  -- q*(N+m) = q*N + q*m
  have hexp : q * (N + m) = q * N + q * m := Nat.left_distrib q N m
  -- q*(m*cu) = (q*m)*cu = m*(q*cu)  [reassociate]
  have hassoc : q * (m * cu) = m * (q * cu) := by
    rw [← Nat.mul_assoc q m cu, Nat.mul_comm q m, Nat.mul_assoc m q cu]
  -- So m*(q*cu) ≤ q*N + q*m
  have hstep1 : m * (q * cu) ≤ q * N + q * m := by
    rw [← hassoc]; rw [hexp] at hD15q; exact hD15q
  -- q*N + q*m ≤ q*N + N  (since q*m ≤ N)
  have hstep2 : q * N + q * m ≤ q * N + N :=
    Nat.add_le_add_left hN0 (q * N)
  -- q*N + N = (q+1)*N = N*(q+1) = N*q + N = q*N + N  [already that form]
  -- So m*(q*cu) ≤ q*N + N
  have hstep3 : m * (q * cu) ≤ q * N + N :=
    Nat.le_trans hstep1 hstep2
  -- q*N + N = (q+1)*N
  have hfactor : q * N + N = (q + 1) * N := by
    rw [Nat.add_mul, Nat.one_mul]
  -- So m*(q*cu) ≤ (q+1)*N
  have hstep4 : m * (q * cu) ≤ (q + 1) * N := by
    rw [← hfactor]; exact hstep3
  -- q+1 ≤ p*m  (since q < p*m means q+1 ≤ p*m in Nat)
  have h3 : q + 1 ≤ p * m := hfrac
  -- (q+1)*N ≤ (p*m)*N
  have h4 : (q + 1) * N ≤ p * m * N :=
    Nat.mul_le_mul_right N h3
  -- m*(q*cu) ≤ p*m*N
  have hstep5 : m * (q * cu) ≤ p * m * N :=
    Nat.le_trans hstep4 h4
  -- p*m*N = m*(p*N)
  have hrhs : p * m * N = m * (p * N) := by
    simp only [Nat.mul_assoc, Nat.mul_comm p m, Nat.mul_comm p N]
  -- So m*(q*cu) ≤ m*(p*N)
  have hstep6 : m * (q * cu) ≤ m * (p * N) := by
    rw [← hrhs]; exact hstep5
  -- cancel m > 0
  exact Nat.le_of_mul_le_mul_left hstep6 hm

/-!
## C.5 Bridge — density-bounded-by-parity-vector (abstract helpers + full existential)

LaTTe siblings:
  `ai-math.natural-density/count-upto-mono-pred-nat`  (D5-nat helper)
  `ai-math.natural-density/density-bounded-monotone-nat`  (D8-nat helper)
  `ai-math.parity-vector/density-bounded-by-parity-vector`  (C.5 bridge)

The C.5 bridge states: for any residue r < 2^k, the set of naturals n
whose length-k parity vector equals that of r is density-bounded above
by p/q for any p/q > 1/2^k.

**Proof structure** (matching the LaTTe proof):
  1. D16: the residue class {n : n ≡ r (mod 2^k)} has density ≤ p/q.
  2. T1-nat: for n:nat, same length-k parity vector as r implies n ≡ r (mod 2^k).
  3. D8-nat (nat-restricted monotone): inclusion on nat transfers the bound
     from the residue class to the parity-vector class.

The three `_abstract` theorems below remain as helper lemmas. The
**full `density_bounded` existential** is proved lower in the file as
`density_bounded_by_parity_vector` using the actual `PVEq`/`T_iter`
definitions plus mathlib4's `Nat.count_mono_left` and
`Nat.count_modEq_card` — eliminating the abstract `count_A`/`count_B`
parameters and matching the LaTTe sibling's full existential statement.
-/

/--
**D5-nat** (abstract form): if A ⊆ B on naturals (the predicate inclusion
holds for all n : Nat), then count_A ≤ count_B.

LaTTe sibling: `ai-math.natural-density/count-upto-mono-pred-nat`.

In the LaTTe proof this is proved by nat-induction, using `nat-succ` to
show `(succ k) : nat` at each inductive step so the nat-restricted
hypothesis applies.
-/
theorem count_upto_mono_pred_nat_abstract
    (count_A count_B : Nat)
    (h : count_A ≤ count_B) :
    count_A ≤ count_B := h

/--
**D8-nat** (abstract form): if A ⊆ B on naturals and `q * count_B ≤ p * N`,
then `q * count_A ≤ p * N`.

LaTTe sibling: `ai-math.natural-density/density-bounded-monotone-nat`.
-/
theorem density_bounded_monotone_nat_abstract
    (count_A count_B p q N : Nat)
    (hinc : count_A ≤ count_B)
    (hB : q * count_B ≤ p * N) :
    q * count_A ≤ p * N :=
  Nat.le_trans (Nat.mul_le_mul_left q hinc) hB

/--
**C.5 bridge — density-bounded-by-parity-vector** (abstract arithmetic form, helper).

For any r < 2^k, with 2^k > 0 and q < p * 2^k, given:
  - `cu_res`  : count of {n ≤ N : n ≡ r (mod 2^k)}, satisfying D15's bound
    `2^k * cu_res ≤ N + 2^k`
  - `cu_pv`   : count of {n ≤ N : parity-vector(n) = parity-vector(r)},
    satisfying the nat-restricted inclusion `cu_pv ≤ cu_res`
  - `N₀_bound`: N ≥ q * 2^k (the D16 threshold)

This proves `q * cu_pv ≤ p * N`.

**Proof**: apply D16_abstract (the residue-class bound: `q * cu_res ≤ p * N`)
followed by D8-nat (monotone transfer: `q * cu_pv ≤ q * cu_res`).

This abstract form remains as a lightweight helper. The **full
`density_bounded` existential** is proved in this file as
`density_bounded_by_parity_vector` (see below).

LaTTe sibling: `ai-math.parity-vector/density-bounded-by-parity-vector`.
-/
theorem density_bounded_by_parity_vector_abstract
    (pow2k p q N cu_res cu_pv : Nat)
    (hm : 0 < pow2k)
    (hfrac : q < p * pow2k)
    (hD15 : pow2k * cu_res ≤ N + pow2k)
    (hN0 : q * pow2k ≤ N)
    (hinc : cu_pv ≤ cu_res) :
    q * cu_pv ≤ p * N :=
  -- Step 1: D16_abstract — q * cu_res ≤ p * N
  have hres : q * cu_res ≤ p * N :=
    density_bounded_residue_class_abstract pow2k p q N cu_res hm hfrac hD15 hN0
  -- Step 2: q * cu_pv ≤ q * cu_res  (monotone under inclusion)
  have hmono : q * cu_pv ≤ q * cu_res :=
    Nat.mul_le_mul_left q hinc
  -- Step 3: chain
  Nat.le_trans hmono hres

/-!
## D14 / D15 / D16 / C.5 — REAL existential-form promotions via mathlib4

The abstract-form theorems above (`*_abstract`) provide the arithmetic core
of the residue-class density argument as helper lemmas. The full existential
form of D16 (`density_bounded_residue_class`) and the C.5 bridge
(`density_bounded_by_parity_vector`) connect those arithmetic cores to the
top-level `density_bounded` predicate, citing mathlib4's
`Nat.count_modEq_card` (from `Mathlib.Data.Int.CardIntervalMod`).

**Cross-prover validation note.** The LaTTe sibling
`ai-math.natural-density/density-bounded-residue-class` is REAL but depends
on the operator-level axiom `count-residue-euclidean` (the Euclidean
floor-division decomposition of the count). The Lean 4 mirror here proves
the equivalent fact directly via `Nat.count_modEq_card`, eliminating the
need for any operator-level axiom on the Lean 4 side. This gives genuine
**axiom-free cross-validation** (modulo the mathlib4 trust base, which is
itself axiom-free for these specific lemmas — `count_modEq_card` is proved
from `Ico_filter_modEq_card`, which is proved from `Int.ceil`/`Int.floor`
identities in `Int.CardIntervalMod.lean`).

Promoted (2026-05-17, mathlib4-migration follow-up):
  - `count_residue_class_upper_bound` — explicit `Nat.count_modEq_card` upper bound
    (replaces the abstract `cu` parameter of `count_residue_class_upper_abstract`).
  - `density_bounded_residue_class` — full existential form of D16 (replaces
    `density_bounded_residue_class_abstract`).
  - `density_bounded_by_parity_vector` — full existential form of the C.5 bridge.
-/

/-- Helper: `Nat.count` is invariant under different `DecidablePred` instances
(they form a subsingleton). Used to bridge the gap between `Classical.propDecidable`
and canonical decidability instances when chaining mathlib lemmas with our
`count_upto` (which uses the local classical attribute). -/
private theorem nat_count_inst_eq
    {P : Nat → Prop} (inst₁ inst₂ : DecidablePred P) (n : Nat) :
    @Nat.count P inst₁ n = @Nat.count P inst₂ n := by
  cases Subsingleton.elim inst₁ inst₂; rfl

/--
**Helper: residue-class count upper bound (REAL via `Nat.count_modEq_card`).**

For `m > 0` and `r < m`:
  `m * count_upto (fun n => n % m = r) N ≤ N + 1 + m`.

Proof:
  - `count (fun n => n % m = r) (N+1) ≤ count (· ≡ r [MOD m]) (N+1)` by
    `Nat.count_mono_left` (predicate inclusion `n % m = r → n ≡ r [MOD m]`
    holds whenever `r % m = r`, which is implied by `r < m`).
  - `count (· ≡ r [MOD m]) (N+1) = (N+1)/m + [r%m < (N+1)%m]` by
    `Nat.count_modEq_card`, so `≤ (N+1)/m + 1`.
  - Multiply by `m`: `m * count ≤ m*((N+1)/m + 1) = m*((N+1)/m) + m ≤ (N+1) + m`.

LaTTe sibling: indirectly `ai-math.natural-density/count-residue-class-upper`
(which uses the abstract `cu` parameter satisfying `cu ≤ q + 1`).
-/
theorem count_residue_class_upper_bound
    (m r N : Nat) (hm : 0 < m) (hrm : r < m) :
    m * count_upto (fun n => n % m = r) N ≤ N + 1 + m := by
  -- Predicate inclusion: (n % m = r) → (n ≡ r [MOD m])  (uses r < m)
  have hAB : ∀ k, k < (N + 1) → (k % m = r) → (k ≡ r [MOD m]) := by
    intro k _ hk
    unfold Nat.ModEq
    rw [hk, Nat.mod_eq_of_lt hrm]
  have hle :
      Nat.count (fun n : Nat => n % m = r) (N + 1)
        ≤ Nat.count (fun n : Nat => n ≡ r [MOD m]) (N + 1) :=
    Nat.count_mono_left hAB
  have hcm : Nat.count (· ≡ r [MOD m]) (N + 1) =
              (N + 1) / m + if r % m < (N + 1) % m then 1 else 0 :=
    Nat.count_modEq_card (N + 1) hm r
  have hcm_le :
      Nat.count (fun n : Nat => n ≡ r [MOD m]) (N + 1) ≤ (N + 1) / m + 1 := by
    rw [hcm]; split_ifs <;> omega
  have hbound :
      Nat.count (fun n : Nat => n % m = r) (N + 1) ≤ (N + 1) / m + 1 :=
    Nat.le_trans hle hcm_le
  have hmul :
      m * Nat.count (fun n : Nat => n % m = r) (N + 1) ≤ m * ((N + 1) / m + 1) :=
    Nat.mul_le_mul_left m hbound
  -- Compute m * ((N+1)/m + 1) ≤ N + 1 + m and chain.
  have hdm : m * ((N + 1) / m) + (N + 1) % m = N + 1 := Nat.div_add_mod (N+1) m
  have hmodlt : (N + 1) % m < m := Nat.mod_lt _ hm
  have hbnd_eq : m * ((N + 1) / m + 1) = m * ((N + 1) / m) + m := by ring
  have hbnd_le : m * ((N + 1) / m + 1) ≤ N + 1 + m := by
    rw [hbnd_eq]; omega
  -- Bridge potential DecidablePred-instance mismatch between hmul's count and goal's.
  show m * count_upto (fun n => n % m = r) N ≤ N + 1 + m
  unfold count_upto
  have hbridge :
      @Nat.count (fun n : Nat => n % m = r)
          (fun a => Classical.propDecidable _) (N + 1)
        = Nat.count (fun n : Nat => n % m = r) (N + 1) :=
    nat_count_inst_eq _ _ _
  rw [hbridge]
  exact Nat.le_trans hmul hbnd_le

/--
**Helper: residue-class count lower bound (REAL via `Nat.count_modEq_card`).**

For `m > 0` and `r < m`:
  `(N + 1) / m ≤ count_upto (fun n => n % m = r) N`.

Proof: the reverse-inclusion `(n ≡ r [MOD m]) → (n % m = r)` holds when
`r % m = r`, so `count (· ≡ r [MOD m]) (N+1) ≤ count (fun n => n % m = r) (N+1)`.
The mathlib4 equality `Nat.count_modEq_card` then gives
`(N+1)/m + [r%m < (N+1)%m] ≤ count`, so in particular `(N+1)/m ≤ count`.

LaTTe sibling: indirectly `ai-math.natural-density/count-residue-class-lower`
(which uses the abstract `cu` parameter satisfying `q ≤ cu`).
-/
theorem count_residue_class_lower_bound
    (m r N : Nat) (hm : 0 < m) (hrm : r < m) :
    (N + 1) / m ≤ count_upto (fun n => n % m = r) N := by
  unfold count_upto
  -- Reverse-inclusion: (n ≡ r [MOD m]) → (n % m = r)  (uses r < m)
  have hAB : ∀ k, k < (N + 1) → (k ≡ r [MOD m]) → (k % m = r) := by
    intro k _ hk
    unfold Nat.ModEq at hk
    rw [Nat.mod_eq_of_lt hrm] at hk
    exact hk
  have hle :
      Nat.count (fun n : Nat => n ≡ r [MOD m]) (N + 1)
        ≤ Nat.count (fun n : Nat => n % m = r) (N + 1) :=
    Nat.count_mono_left hAB
  have hcm : Nat.count (· ≡ r [MOD m]) (N + 1) =
              (N + 1) / m + if r % m < (N + 1) % m then 1 else 0 :=
    Nat.count_modEq_card (N + 1) hm r
  have hcm_ge :
      (N + 1) / m ≤ Nat.count (fun n : Nat => n ≡ r [MOD m]) (N + 1) := by
    rw [hcm]; split_ifs <;> omega
  -- Bridge potential DecidablePred-instance discrepancy via nat_count_inst_eq.
  -- The goal's Nat.count comes from `count_upto`'s definition (uses local Classical
  -- attribute), while `hle` from `Nat.count_mono_left` may use the canonical instance.
  have hcombined :
      (N + 1) / m ≤ Nat.count (fun n : Nat => n % m = r) (N + 1) :=
    Nat.le_trans hcm_ge hle
  have hbridge :
      @Nat.count (fun n : Nat => n % m = r)
          (fun a => Classical.propDecidable _) (N + 1)
        = Nat.count (fun n : Nat => n % m = r) (N + 1) :=
    nat_count_inst_eq _ _ _
  rw [hbridge]
  exact hcombined

/--
**D16 — density-bounded-residue-class** (FULL existential form, REAL).

For `m > 0`, `r < m`, and `q < p * m`, the residue class
`{n : n % m = r}` is density-bounded above by `p / q`:
  `∃ N₀, ∀ N ≥ N₀, q * count_upto (fun n => n % m = r) N ≤ p * N`.

This is the full Lean 4 mirror of the LaTTe theorem
`ai-math.natural-density/density-bounded-residue-class` (REAL,
kernel-verified). The LaTTe version uses the operator-level axiom
`count-residue-euclidean`; this Lean 4 version is **axiom-free**
(modulo mathlib4's `Nat.count_modEq_card`, itself proved without
operator axioms in `Mathlib.Data.Int.CardIntervalMod`).

**Proof structure**:
  - Witness `N₀ := q * (m + 1)`.
  - For `N ≥ N₀`, the helper `count_residue_class_upper_bound`
    gives `m * cu ≤ N + 1 + m`.
  - Scale by `q`: `q * (m * cu) = m * (q * cu) ≤ q * (N + 1 + m)`.
  - Algebra: `q * (N + 1 + m) ≤ q*N + N + N = (q+1)*N - N + N = (q+1)*N`...
    actually `q * (m + 1) = q*m + q ≤ N`, so
    `q*N + q*(m+1) ≤ q*N + N = (q+1)*N ≤ (p*m)*N`.
  - Cancel the leading `m` via `Nat.le_of_mul_le_mul_left`.

LaTTe sibling: `ai-math.natural-density/density-bounded-residue-class` (REAL).
-/
theorem density_bounded_residue_class
    (m r p q : Nat) (hm : 0 < m) (hrm : r < m) (hfrac : q < p * m) :
    density_bounded (fun n => n % m = r) p q := by
  refine ⟨q * (m + 1), fun N hN => ?_⟩
  set cu := count_upto (fun n => n % m = r) N with _hcu_def
  have hub : m * cu ≤ N + 1 + m := count_residue_class_upper_bound m r N hm hrm
  apply Nat.le_of_mul_le_mul_left _ hm
  calc m * (q * cu)
      = q * (m * cu) := by ring
    _ ≤ q * (N + 1 + m) := Nat.mul_le_mul_left q hub
    _ = q * N + q * (m + 1) := by ring
    _ ≤ q * N + N := by omega
    _ = (q + 1) * N := by ring
    _ ≤ (p * m) * N := Nat.mul_le_mul_right N hfrac
    _ = m * (p * N) := by ring

/--
**Dual D16 — density_bounded_below_residue_class** (FULL existential form, REAL).

For `m > 0`, `r < m`, and `p * m < q`, the residue class
`{n : n % m = r}` is density-bounded **below** by `p / q`:
  `∃ N₀, ∀ N ≥ N₀, p * N ≤ q * count_upto (fun n => n % m = r) N`.

Companion to `density_bounded_residue_class` (D16). Together they sandwich the
residue class density at exactly 1/m in the ε-bound sense.

**Proof structure**:
  - Witness `N₀ := q * m`.
  - For `N ≥ N₀`, `count_residue_class_lower_bound` gives `(N+1)/m ≤ cu`.
  - Euclidean division: `m * ((N+1)/m) + (N+1)%m = N+1` and `(N+1)%m < m`
    give `N + 1 ≤ m * cu + m`.
  - With `p * m + 1 ≤ q` and `q * m ≤ N`, `nlinarith` closes `p * N ≤ q * cu`.

LaTTe sibling: `ai-math.natural-density/density-bounded-below-residue-class` (REAL).
-/
theorem density_bounded_below_residue_class
    (m r p q : Nat) (hm : 0 < m) (hrm : r < m) (hfrac : p * m < q) :
    density_bounded_below (fun n => n % m = r) p q := by
  refine ⟨q * m, fun N hN => ?_⟩
  set cu := count_upto (fun n => n % m = r) N with _hcu_def
  have hlb : (N + 1) / m ≤ cu := count_residue_class_lower_bound m r N hm hrm
  have hdm : m * ((N + 1) / m) + (N + 1) % m = N + 1 := Nat.div_add_mod (N + 1) m
  have hmod : (N + 1) % m < m := Nat.mod_lt _ hm
  have h_mcu : m * ((N + 1) / m) ≤ m * cu := Nat.mul_le_mul_left m hlb
  -- N + 1 ≤ m * cu + m  (from Euclidean lower bound on m*cu)
  have h_Nbound : N + 1 ≤ m * cu + m := by omega
  -- Goal: p * N ≤ q * cu
  -- Key: p*m*N ≤ q*m*cu, then cancel m.
  apply Nat.le_of_mul_le_mul_left _ hm
  -- Suffices: m * (p * N) ≤ m * (q * cu), i.e., p*m*N ≤ q*m*cu.
  -- From p*m+1 ≤ q and N+1 ≤ m*cu+m and q*m ≤ N:
  --   p*m*N + N ≤ q*N  (mult hfrac by N)
  --   q*N + q ≤ q*m*cu + q*m  (mult h_Nbound by q)
  --   q*m ≤ N  (= hN)
  -- So: p*m*N ≤ q*m*cu.
  nlinarith [Nat.mul_le_mul_right N hfrac, Nat.mul_le_mul_left q h_Nbound, hN]

/-!
## C.5 bridge — density-bounded-by-parity-vector (FULL existential form, REAL)

LaTTe sibling:
  `ai-math.parity-vector/density-bounded-by-parity-vector` (REAL).

The C.5 bridge says: for any residue `r < 2^k`, the set of naturals `n`
whose length-`k` parity vector equals that of `r` is density-bounded
above by `p / q` for any `q < p * 2^k`.

**Proof structure**:
  1. `parity_vector_residue_lemma_nat` (T1-nat, REAL): for `n m : Nat`,
     `PVEq n m k → 2^k ∣ (n - m : Int)`.
  2. Convert to Nat mod: `2^k ∣ ((n : Int) - m) → n % 2^k = m % 2^k`
     via `Int.modEq_iff_dvd` and `Int.natCast_modEq_iff`.
  3. With `r < 2^k`, this gives `PVEq n r k → n % 2^k = r`.
  4. Apply `Nat.count_mono_left` to lift `count (PVEq · r k) ≤ count (· % 2^k = r)`.
  5. Apply `density_bounded_residue_class` for the residue-class bound.
-/

/-- Helper: convert `2^k ∣ (m - n : Int)` to `m % 2^k = n % 2^k` for `m n : Nat`. -/
theorem pow_two_dvd_int_imp_mod_eq
    (k m n : Nat) (h : (2 : Int) ^ k ∣ (m : Int) - (n : Int)) :
    m % 2^k = n % 2^k := by
  have hmod : (m : Int) ≡ (n : Int) [ZMOD (2 : Int) ^ k] := by
    rw [Int.modEq_iff_dvd]
    have h' := dvd_neg.mpr h
    have hneg : (-((m : Int) - n)) = (n : Int) - m := by ring
    rw [hneg] at h'
    exact h'
  have hpow : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  rw [hpow] at hmod
  exact_mod_cast (Int.natCast_modEq_iff.mp hmod)

/--
**C.5 bridge (REAL): density_bounded_by_parity_vector** — FULL existential form.

For any `r < 2^k` (where `r k : Nat`, `2^k > 0` automatically holds), and
any `p q : Nat` with `q < p * 2^k`, the set `{n : Nat | PVEq n r k}` is
density-bounded above by `p / q`:
  `∃ N₀, ∀ N ≥ N₀, q * count_upto (fun n => PVEq n r k) N ≤ p * N`.

**Proof**:
  1. Apply `density_bounded_residue_class` with `m := 2^k`, witness for residue class.
  2. Transfer via `Nat.count_mono_left`: `PVEq n r k → n % 2^k = r`
     follows from `parity_vector_residue_lemma_nat` (T1-nat) and
     `pow_two_dvd_int_imp_mod_eq`.

LaTTe sibling: `ai-math.parity-vector/density-bounded-by-parity-vector` (REAL).
The LaTTe proof composes D16 + T1-nat + D8-nat (monotone) over `int`-valued
predicates; the Lean 4 proof composes the same three pieces over `Nat`-valued
predicates (the C.4 mirrors are `Nat`-only by design, see the comment block
in front of `density_bounded`).
-/
theorem density_bounded_by_parity_vector
    (r k p q : Nat) (hr : r < 2 ^ k) (hfrac : q < p * 2 ^ k) :
    density_bounded (fun n => PVEq n r k) p q := by
  -- Apply the residue-class bound with m := 2^k.
  have hm : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨N₀, hres⟩ := density_bounded_residue_class (2 ^ k) r p q hm hr hfrac
  refine ⟨N₀, fun N hN => ?_⟩
  -- Inclusion at the Nat level: PVEq n r k → n % 2^k = r.
  have hinc : ∀ n, n < (N + 1) → PVEq n r k → (n % 2 ^ k = r) := by
    intro n _ hpv
    have hdvd : (2 : Int) ^ k ∣ (n : Int) - (r : Int) :=
      parity_vector_residue_lemma_nat n r k hpv
    have hmod : n % 2 ^ k = r % 2 ^ k := pow_two_dvd_int_imp_mod_eq k n r hdvd
    rwa [Nat.mod_eq_of_lt hr] at hmod
  -- Count monotonicity transfer.
  have hcount_le :
      Nat.count (fun n : Nat => PVEq n r k) (N + 1)
        ≤ Nat.count (fun n : Nat => n % 2 ^ k = r) (N + 1) :=
    Nat.count_mono_left hinc
  -- Multiply by q
  have hq_mul :
      q * Nat.count (fun n : Nat => PVEq n r k) (N + 1)
        ≤ q * Nat.count (fun n : Nat => n % 2 ^ k = r) (N + 1) :=
    Nat.mul_le_mul_left q hcount_le
  -- Conclude via the residue-class bound.
  have hres_N : q * count_upto (fun n => n % 2 ^ k = r) N ≤ p * N := hres N hN
  unfold count_upto at hres_N
  -- The two Nat.count instances (Classical vs canonical) coincide; bridge.
  have hbridge :
      @Nat.count (fun n : Nat => n % 2 ^ k = r)
                  (fun a => Classical.propDecidable _) (N + 1)
        = Nat.count (fun n : Nat => n % 2 ^ k = r) (N + 1) :=
    nat_count_inst_eq _ _ _
  rw [hbridge] at hres_N
  exact Nat.le_trans hq_mul hres_N

/-!
## C.6 Disjointness of parity-vector classes

The three theorems below formalise the disjointness claim that is the
combinatorial engine of the Terras density argument: distinct residues
in `[0, 2^k)` pick out disjoint subsets of `ℕ`.

LaTTe siblings in `src/ai_math/parity_vector.clj`:
- `divides-lt-nat-zero`          (REAL, C.6 helper)
- `diff-le-left`                 (REAL, C.6 helper)
- `parity-vector-classes-disjoint` (REAL, C.6 main)
-/

/--
**C.6 arithmetic helper: divides_lt_nat_zero.**

If `0 < m`, `n : Nat`, `n < m`, and `m ∣ (n : Int)`, then `n = 0`.

This is the key fact: the only non-negative integer strictly less than
`m` that `m` divides is zero.

LaTTe sibling: `ai-math.parity-vector/divides-lt-nat-zero` (REAL).
-/
theorem divides_lt_nat_zero
    (m n : Nat) (_hm : 0 < m) (hn : n < m)
    (hdvd : (m : Int) ∣ (n : Int)) : n = 0 := by
  have hnn : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
  have hnm : (n : Int) < (m : Int) := by exact_mod_cast hn
  -- Int.eq_zero_of_dvd_of_nonneg_of_lt: 0 ≤ n → n < m → m ∣ n → n = 0
  have hn_zero : (n : Int) = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hnm hdvd
  exact_mod_cast hn_zero

/--
**C.6 helper: diff_le_left.**

For any `r1 r2 : Nat`, `r1 - r2 ≤ r1` (as integers and as naturals
when `r2 ≤ r1`).  The integer form is used in `parity_vector_classes_disjoint`.

LaTTe sibling: `ai-math.parity-vector/diff-le-left` (REAL).
-/
theorem diff_le_left_int (r1 r2 : Nat) : (r1 : Int) - r2 ≤ r1 := by
  have : (0 : Int) ≤ r2 := Int.natCast_nonneg r2
  linarith

/--
**C.6 main: parity_vector_classes_disjoint (REAL).**

If `r1, r2 < 2^k` are distinct naturals, then no natural `n` can have
both `PVEq n r1 k` and `PVEq n r2 k`.

**Proof**:
1. Apply `parity_vector_residue_lemma_nat` twice:
   `2^k ∣ (n : Int) - r1` and `2^k ∣ (n : Int) - r2`.
2. By subtraction: `2^k ∣ (r2 : Int) - r1`.
3. Bound: `|(r2 : Int) - r1| < 2^k` (since `0 ≤ r1, r2 < 2^k`).
4. Case-split: `r2 - r1 ≥ 0` or `r2 - r1 < 0`.
   In the non-negative case, cast to Nat and use `divides_lt_nat_zero`.
   In the negative case, `r1 - r2 > 0`, use `divides_lt_nat_zero` on `r1 - r2`.
   Both cases give contradiction with `r1 ≠ r2`.

LaTTe sibling: `ai-math.parity-vector/parity-vector-classes-disjoint` (REAL).
-/
theorem parity_vector_classes_disjoint
    (r1 r2 k n : Nat) (hr1 : r1 < 2 ^ k) (hr2 : r2 < 2 ^ k) (hne : r1 ≠ r2)
    (h1 : PVEq n r1 k) (h2 : PVEq n r2 k) : False := by
  -- Step 1: divisibility from T1-nat applied twice
  have hd1 : (2 : Int) ^ k ∣ (n : Int) - (r1 : Int) :=
    parity_vector_residue_lemma_nat n r1 k h1
  have hd2 : (2 : Int) ^ k ∣ (n : Int) - (r2 : Int) :=
    parity_vector_residue_lemma_nat n r2 k h2
  -- Step 2: 2^k ∣ (r2 : Int) - r1
  have hdiff : (2 : Int) ^ k ∣ ((r2 : Int) - (r1 : Int)) := by
    have : (2 : Int) ^ k ∣ ((n : Int) - r1 - ((n : Int) - r2)) := Int.dvd_sub hd1 hd2
    simpa using this
  -- Step 3: integer bounds
  have hpow_pos : (0 : Int) < 2 ^ k := by positivity
  have hr1_int : (r1 : Int) < 2 ^ k := by exact_mod_cast hr1
  have hr2_int : (r2 : Int) < 2 ^ k := by exact_mod_cast hr2
  have hr1_nn : (0 : Int) ≤ r1 := Int.natCast_nonneg r1
  have hr2_nn : (0 : Int) ≤ r2 := Int.natCast_nonneg r2
  -- Step 4: case-split r2 ≥ r1 or r2 < r1
  by_cases hle : r2 ≤ r1
  · -- Case r1 ≥ r2: 2^k ∣ (r1 : Int) - r2 (from negating diff)
    have hdvd_r1r2 : (2 : Int) ^ k ∣ (r1 : Int) - r2 := by
      have := Int.dvd_neg.mpr hdiff
      rwa [neg_sub] at this
    -- (r1 - r2) as Nat, bounded
    have hr1r2_lt : r1 - r2 < 2 ^ k := by omega
    -- cast: (r1 - r2 : Nat) = (r1 : Int) - r2 when r2 ≤ r1
    have hdvd_nat : (2 ^ k : Int) ∣ ((r1 - r2 : Nat) : Int) := by
      rwa [Nat.cast_sub hle]
    -- divides_lt_nat_zero: r1 - r2 = 0
    have hz : r1 - r2 = 0 :=
      divides_lt_nat_zero (2 ^ k) (r1 - r2) (Nat.two_pow_pos k) hr1r2_lt hdvd_nat
    -- r1 = r2, contradicts hne
    omega
  · -- Case r2 > r1: 2^k ∣ (r2 : Int) - r1
    simp only [not_le] at hle
    have hr2r1_lt : r2 - r1 < 2 ^ k := by omega
    -- cast: (r2 - r1 : Nat) = (r2 : Int) - r1 when r1 ≤ r2
    have hdvd_nat : (2 ^ k : Int) ∣ ((r2 - r1 : Nat) : Int) := by
      rwa [Nat.cast_sub (Nat.le_of_lt hle)]
    -- divides_lt_nat_zero: r2 - r1 = 0
    have hz : r2 - r1 = 0 :=
      divides_lt_nat_zero (2 ^ k) (r2 - r1) (Nat.two_pow_pos k) hr2r1_lt hdvd_nat
    -- r1 = r2, contradicts hne
    omega

/-!
## Project 1 — Cascade Multiplication Theorem

LaTTe sibling file: `src/ai_math/cascade_mult.clj`.

The two theorems mirrored here are:

  1. `cascade_step_mult`: per-step formula. For odd `n` with `v₂(n+1) ≥ 2`,
     `2 * (cc n + 1) = 3 * (n + 1)`.

  2. `cascade_mult_exact`: iterated form. For odd `n` with `v₂(n+1) = L + 2`,
     `2^(L+1) * (cc^[L+1] n + 1) = (n+1) * 3^(L+1)`.

Here `cc n = (3n+1) / 2^(v₂(3n+1))` is the compressed Collatz step
(strip all factors of 2 from `3n+1`). When `n` is odd and `v₂(n+1) ≥ 2`
(equivalently `4 ∣ n+1`), `v₂(3n+1) = 1` and so `cc n = (3n+1)/2`.

Cross-validation note: the LaTTe proofs are ~200+ have-steps because every
arithmetic step (distribute, commute, two-adic valuation manipulation) is
explicit. The Lean 4 proofs collapse most arithmetic to `omega` and use
mathlib4's `padicValNat` machinery (`padicValNat_dvd_iff_le`,
`padicValNat.mul`, `pow_padicValNat_dvd`) for the 2-adic facts.
-/

/-- The compressed Collatz step: `cc n = (3n+1) / 2^(v₂(3n+1))`.

Strips all factors of 2 from `3n+1`. When `n` is odd, this is the standard
Collatz "odd-to-odd" jump (the result is odd). For even `n`, this is not the
quantity usually called "cc", but the definition is total on `Nat`.

LaTTe sibling: `ai-math.collatz-compressed/collatz-odd-compressed`. -/
def cc (n : Nat) : Nat := (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-- **Key 2-adic lemma**: for odd `n` with `4 ∣ n+1`, `v₂(3n+1) = 1`.

Proof: `4 ∣ n+1` ⟹ `n = 4q - 1 = 4q + 3` (mod 4) form. Then
`3n+1 = 12q + 10 = 2*(6q+5)` with `6q+5` odd, so the 2-adic valuation
of `3n+1` is exactly 1. -/
theorem padicValNat_three_n_plus_one_eq_one
    {n : Nat} (h4 : 4 ∣ n + 1) (hpos : 0 < n) :
    padicValNat 2 (3 * n + 1) = 1 := by
  -- Step 1: 2 ∣ 3n+1.
  have h2_dvd : (2 : Nat) ∣ 3 * n + 1 := by
    obtain ⟨q, hq⟩ := h4
    refine ⟨6 * q - 1, ?_⟩
    have hq_pos : 0 < q := by omega
    -- n + 1 = 4q, so 3n+1 = 3*(4q - 1) + 1 = 12q - 2 = 2*(6q - 1)
    omega
  -- Step 2: ¬ 4 ∣ 3n+1.
  have h4_not_dvd : ¬ (2 ^ 2 ∣ 3 * n + 1) := by
    rintro ⟨k, hk⟩
    obtain ⟨q, hq⟩ := h4
    -- 4 | 3n+1 and 4 | n+1 would give 4 | (3n+1) - 3*(n+1) = -2; contradiction.
    -- Phrased via omega on the witness expansion.
    have hpow : (2 : Nat) ^ 2 = 4 := by norm_num
    rw [hpow] at hk
    omega
  -- Step 3: nonzero.
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  -- Step 4: 2 ∣ 3n+1 gives padicValNat ≥ 1; ¬ 4 ∣ 3n+1 gives padicValNat < 2.
  have h_ge : 1 ≤ padicValNat 2 (3 * n + 1) := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl] at h2_dvd
    exact (padicValNat_dvd_iff_le h3n1_ne).mp h2_dvd
  have h_lt : padicValNat 2 (3 * n + 1) < 2 := by
    rw [← Nat.not_le]
    intro hge2
    exact h4_not_dvd ((padicValNat_dvd_iff_le h3n1_ne).mpr hge2)
  omega

/-- For odd `n` with `4 ∣ n+1`, `cc n = (3n+1) / 2`. Equational form. -/
theorem cc_eq_of_four_dvd
    {n : Nat} (h4 : 4 ∣ n + 1) (hpos : 0 < n) :
    cc n = (3 * n + 1) / 2 := by
  unfold cc
  rw [padicValNat_three_n_plus_one_eq_one h4 hpos]
  norm_num

/-- **cascade_step_mult — REAL.**

Per-step cascade formula. For `n : Nat`, `n` odd, with `4 ∣ n+1`
(equivalently `v₂(n+1) ≥ 2`), `2 * (cc n + 1) = 3 * (n + 1)`.

This is the integer-arithmetic form (avoiding division). The condition
`4 ∣ n+1` ensures `cc n = (3n+1)/2` (one step of halving suffices).

LaTTe sibling: `src/ai_math/cascade_mult.clj` :: `cascade-step-mult`. -/
theorem cascade_step_mult
    {n : Nat} (hodd : Odd n) (h4 : 4 ∣ n + 1) :
    2 * (cc n + 1) = 3 * (n + 1) := by
  have hpos : 0 < n := by
    obtain ⟨k, hk⟩ := hodd; omega
  rw [cc_eq_of_four_dvd h4 hpos]
  -- (3n+1) is even, so 2 * ((3n+1)/2 + 1) = (3n+1) + 2 = 3*(n+1).
  have h2_dvd : (2 : Nat) ∣ 3 * n + 1 := by
    obtain ⟨q, hq⟩ := h4
    refine ⟨6 * q - 1, ?_⟩
    have hq_pos : 0 < q := by omega
    omega
  obtain ⟨m, hm⟩ := h2_dvd
  rw [hm]
  rw [Nat.mul_div_cancel_left m (by norm_num : (0 : Nat) < 2)]
  -- 2*(m+1) = 3*(n+1), and we know 3*n+1 = 2*m, so 3*(n+1) = 2*m + 2 = 2*(m+1). ✓
  omega

/-- **Fractal level decrement**: if `n` is odd and `v₂(n+1) = K + 1` with
`K ≥ 1` (i.e. `4 ∣ n+1`), then `v₂(cc n + 1) = K`.

Equivalently: after one cascade step, the 2-adic valuation of `n+1`
drops by exactly 1.

Proof. From `cc_eq_of_four_dvd`, `cc n = (3n+1)/2`. Write `n+1 = 2^(K+1) * q`
with `q` odd (so `v₂(n+1) = K+1`). Then `3*(n+1) = 2 * (cc n + 1)`, i.e.
`cc n + 1 = 3*(n+1)/2 = 3 * 2^K * q`. Since `q` is odd and `3` is odd,
`v₂(cc n + 1) = K`.

LaTTe sibling: `ai-math.fractal-escape-hierarchy/fractal-level-decrement-cc-comp-at-K-ge-1`. -/
theorem fractal_level_decrement
    {n K : Nat} (hodd : Odd n) (hK : 1 ≤ K)
    (hv2 : padicValNat 2 (n + 1) = K + 1) :
    padicValNat 2 (cc n + 1) = K := by
  -- From `cascade_step_mult` we get 2 * (cc n + 1) = 3 * (n + 1).
  have h4 : 4 ∣ n + 1 := by
    have h_ge : 2 ≤ padicValNat 2 (n + 1) := by omega
    have hn1_ne : n + 1 ≠ 0 := by omega
    have := (padicValNat_dvd_iff_le hn1_ne).mpr h_ge
    simpa [show (2 : Nat) ^ 2 = 4 from rfl] using this
  have hstep : 2 * (cc n + 1) = 3 * (n + 1) := cascade_step_mult hodd h4
  -- padicValNat 2 (2 * (cc n + 1)) = 1 + padicValNat 2 (cc n + 1)
  have hcc_pos : 0 < cc n + 1 := Nat.succ_pos _
  have hcc_ne : cc n + 1 ≠ 0 := Nat.succ_ne_zero _
  have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
  have h_left : padicValNat 2 (2 * (cc n + 1)) = padicValNat 2 (cc n + 1) + 1 := by
    rw [padicValNat.mul htwo_ne hcc_ne, padicValNat_self]
    omega
  -- padicValNat 2 (3 * (n + 1)) = padicValNat 2 (n + 1) since gcd(3, 2) = 1
  -- (3 is odd, so it contributes 0 to the 2-adic valuation)
  have hn1_ne : n + 1 ≠ 0 := by omega
  have hthree_ne : (3 : Nat) ≠ 0 := by norm_num
  have h_three : padicValNat 2 3 = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right
    decide
  have h_right : padicValNat 2 (3 * (n + 1)) = padicValNat 2 (n + 1) := by
    rw [padicValNat.mul hthree_ne hn1_ne, h_three, Nat.zero_add]
  -- Combine: padicValNat 2 (cc n + 1) + 1 = K + 1
  have hcong : padicValNat 2 (2 * (cc n + 1)) = padicValNat 2 (3 * (n + 1)) :=
    congrArg (padicValNat 2) hstep
  rw [h_left, h_right, hv2] at hcong
  omega

/-- Helper: `cc n` is odd when `n` is odd and `4 ∣ n + 1`.

After one cascade step, the result is still odd. This is needed so that the
inductive hypothesis in `cascade_mult_exact` can be applied to `cc n`.

Proof: `cc n = (3n+1) / 2`, and `(3n+1)/2 = (3 * (4q - 1) + 1) / 2 = (12q - 2)/2 = 6q - 1`
for `q := (n+1)/4`. `6q - 1` is odd. -/
theorem cc_odd_of_odd_four_dvd
    {n : Nat} (hodd : Odd n) (h4 : 4 ∣ n + 1) : Odd (cc n) := by
  have hpos : 0 < n := by obtain ⟨k, hk⟩ := hodd; omega
  rw [cc_eq_of_four_dvd h4 hpos]
  obtain ⟨q, hq⟩ := h4
  have hq_pos : 0 < q := by omega
  -- (3n+1)/2 = 6q - 1 = 2*(3q - 1) + 1
  refine ⟨3 * q - 1, ?_⟩
  -- Need (3*n + 1)/2 = 2*(3q - 1) + 1
  have h3n1 : 3 * n + 1 = 2 * (6 * q - 1) := by omega
  rw [h3n1, Nat.mul_div_cancel_left _ (by norm_num : (0 : Nat) < 2)]
  omega

/-- **cascade_mult_exact — REAL.**

The iterated cascade multiplication theorem. For `n : Nat`, `n` odd, `L : Nat`,
with `padicValNat 2 (n + 1) = L + 2` (= `succ (succ L)`), after `L + 1` cascade
steps the exact integer identity holds:

  `2^(L+1) * (cc^[L+1] n + 1) = (n + 1) * 3^(L+1)`.

This is the exact integer form of the cascade landing formula
(spec at top of `docs/archive/STATUS-snapshot-2026-05-19.md` Project 1).

REAL — no new axioms; composed from `cascade_step_mult`,
`fractal_level_decrement`, `cc_odd_of_odd_four_dvd`, `Function.iterate_succ_apply'`,
`Nat.pow_succ`.

LaTTe sibling: `src/ai_math/cascade_mult.clj` :: `cascade-mult-exact`. -/
theorem cascade_mult_exact
    (n L : Nat) (hodd : Odd n)
    (hv2 : padicValNat 2 (n + 1) = L + 2) :
    2 ^ (L + 1) * ((cc^[L + 1] n) + 1) = (n + 1) * 3 ^ (L + 1) := by
  -- Induction on L generalizing n (so the IH can be applied to cc n).
  induction L generalizing n with
  | zero =>
    -- L = 0: need 2 * (cc n + 1) = (n+1) * 3 = 3*(n+1).
    -- cascade_step_mult applies since v₂(n+1) = 2 means 4 ∣ n+1.
    have h4 : 4 ∣ n + 1 := by
      have h_ge : 2 ≤ padicValNat 2 (n + 1) := by omega
      have hn1_ne : n + 1 ≠ 0 := by omega
      have := (padicValNat_dvd_iff_le hn1_ne).mpr h_ge
      simpa [show (2 : Nat) ^ 2 = 4 from rfl] using this
    have hstep : 2 * (cc n + 1) = 3 * (n + 1) := cascade_step_mult hodd h4
    -- Simplify the goal.
    simp only [zero_add, pow_one, Function.iterate_one]
    linarith [hstep]
  | succ L ih =>
    -- L → L+1: hypothesis padicValNat 2 (n+1) = L + 3, want
    -- 2^(L+2) * (cc^[L+2] n + 1) = (n+1) * 3^(L+2).
    -- Strategy: apply step once to get to cc n with padicValNat 2 (cc n + 1) = L + 2,
    -- apply IH on cc n, then combine.
    have h4 : 4 ∣ n + 1 := by
      have h_ge : 2 ≤ padicValNat 2 (n + 1) := by omega
      have hn1_ne : n + 1 ≠ 0 := by omega
      have := (padicValNat_dvd_iff_le hn1_ne).mpr h_ge
      simpa [show (2 : Nat) ^ 2 = 4 from rfl] using this
    have hcc_odd : Odd (cc n) := cc_odd_of_odd_four_dvd hodd h4
    have hcc_v2 : padicValNat 2 (cc n + 1) = L + 2 := by
      -- fractal_level_decrement with K := L+2, K+1 = L+3 matches hypothesis (succ L) + 2 = L + 3.
      have := fractal_level_decrement (n := n) (K := L + 2) hodd
        (by omega : 1 ≤ L + 2)
        (by omega : padicValNat 2 (n + 1) = (L + 2) + 1)
      exact this
    -- Apply IH on (cc n) with same L (NOT L+1).
    -- IH (specialized): 2^(L+1) * (cc^[L+1] (cc n) + 1) = (cc n + 1) * 3^(L+1).
    have ih_cc := ih (cc n) hcc_odd hcc_v2
    -- cc^[L+2] n = cc^[L+1] (cc n)  [iterate_succ_apply for f^[k+1] x = f^[k] (f x)]
    have hiter : cc^[L + 2] n = cc^[L + 1] (cc n) := by
      rw [show L + 2 = (L + 1) + 1 from rfl, Function.iterate_succ_apply]
    -- Per-step cascade for n itself: 2 * (cc n + 1) = 3 * (n + 1).
    have hstep : 2 * (cc n + 1) = 3 * (n + 1) := cascade_step_mult hodd h4
    -- Combine: 2^(L+2) * (cc^[L+2] n + 1) = 2 * (2^(L+1) * (cc^[L+1] (cc n) + 1))
    --                                     = 2 * ((cc n + 1) * 3^(L+1))         [IH]
    --                                     = (2 * (cc n + 1)) * 3^(L+1)
    --                                     = (3 * (n+1)) * 3^(L+1)               [step]
    --                                     = (n+1) * 3^(L+2)
    calc 2 ^ (L + 1 + 1) * ((cc^[L + 1 + 1] n) + 1)
        = 2 * (2 ^ (L + 1) * ((cc^[L + 1] (cc n)) + 1)) := by
              rw [hiter, show L + 1 + 1 = (L + 1) + 1 from rfl, pow_succ]
              ring
      _ = 2 * ((cc n + 1) * 3 ^ (L + 1)) := by rw [ih_cc]
      _ = (2 * (cc n + 1)) * 3 ^ (L + 1) := by ring
      _ = (3 * (n + 1)) * 3 ^ (L + 1) := by rw [hstep]
      _ = (n + 1) * 3 ^ (L + 1 + 1) := by
              rw [show L + 1 + 1 = (L + 1) + 1 from rfl, pow_succ]
              ring

/-- **cascade_landing_v2 — REAL.** (Project 1 optional corollary.)

For `n : Nat`, `n` odd, `L : Nat`, with `padicValNat 2 (n + 1) = L + 2`
(= `succ (succ L)`), after `L + 1` cascade-compressed-Collatz steps the
two-adic valuation of `m + 1` (where `m = cc^[L+1] n`) is exactly `1`:

    `padicValNat 2 (cc^[L+1] n + 1) = 1`.

Interpretation: after exactly `L + 1` cascade steps the ν₂ has dropped
to its minimum (just `1`); the next cascade step would leave the
"fractal hierarchy" — i.e. `m + 1` is `2 * odd`.

REAL — no `sorry`, no new axioms. Proved by approach (A) from the task:
apply `padicValNat 2` to both sides of `cascade_mult_exact`'s identity
`2^(L+1) * (cc^[L+1] n + 1) = (n+1) * 3^(L+1)`. The LHS contributes
`(L+1) + padicValNat 2 (cc^[L+1] n + 1)` (via `padicValNat.mul` and
the `padicValNat` of a power of `2`); the RHS contributes
`padicValNat 2 (n+1) + 0 = (L+2)` (since `3` is odd, `padicValNat 2 (3^k) = 0`).
The conclusion drops out by `omega`.

LaTTe sibling: `src/ai_math/cascade_mult.clj` :: `cascade-landing-v2`. -/
theorem cascade_landing_v2
    (n : Nat) (hn_odd : Odd n) (L : Nat)
    (hv : padicValNat 2 (n + 1) = L + 2) :
    padicValNat 2 (cc^[L + 1] n + 1) = 1 := by
  -- Step 1: get the exact integer identity from cascade_mult_exact.
  have hmul : 2 ^ (L + 1) * ((cc^[L + 1] n) + 1) = (n + 1) * 3 ^ (L + 1) :=
    cascade_mult_exact n L hn_odd hv
  -- Step 2: apply padicValNat 2 to both sides.
  have hcong : padicValNat 2 (2 ^ (L + 1) * ((cc^[L + 1] n) + 1))
             = padicValNat 2 ((n + 1) * 3 ^ (L + 1)) :=
    congrArg (padicValNat 2) hmul
  -- Non-zero side conditions.
  have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
  have hthree_ne : (3 : Nat) ≠ 0 := by norm_num
  have hpow2_ne : (2 : Nat) ^ (L + 1) ≠ 0 := pow_ne_zero _ htwo_ne
  have hpow3_ne : (3 : Nat) ^ (L + 1) ≠ 0 := pow_ne_zero _ hthree_ne
  have hcc_ne : cc^[L + 1] n + 1 ≠ 0 := Nat.succ_ne_zero _
  have hn1_ne : n + 1 ≠ 0 := Nat.succ_ne_zero _
  -- LHS expansion.
  -- padicValNat 2 (2^(L+1) * (cc^[L+1] n + 1))
  --   = padicValNat 2 (2^(L+1)) + padicValNat 2 (cc^[L+1] n + 1)
  --   = (L+1) + padicValNat 2 (cc^[L+1] n + 1)
  -- `padicValNat 2 (2^(L+1)) = L+1` by `padicValNat.prime_pow` (2 is prime).
  have h_pow2_val : padicValNat 2 ((2 : Nat) ^ (L + 1)) = L + 1 :=
    padicValNat.prime_pow (L + 1)
  -- `padicValNat 2 (3^(L+1)) = 0` since 3 is odd (its 2-adic valuation is 0).
  have h_three_val : padicValNat 2 3 = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right; decide
  have h_pow3_val : padicValNat 2 ((3 : Nat) ^ (L + 1)) = 0 := by
    rw [padicValNat.pow _ hthree_ne, h_three_val, Nat.mul_zero]
  -- Now expand the multiplicative congruence.
  have h_lhs : padicValNat 2 (2 ^ (L + 1) * ((cc^[L + 1] n) + 1))
             = (L + 1) + padicValNat 2 (cc^[L + 1] n + 1) := by
    rw [padicValNat.mul hpow2_ne hcc_ne, h_pow2_val]
  have h_rhs : padicValNat 2 ((n + 1) * 3 ^ (L + 1))
             = padicValNat 2 (n + 1) := by
    rw [padicValNat.mul hn1_ne hpow3_ne, h_pow3_val, Nat.add_zero]
  rw [h_lhs, h_rhs, hv] at hcong
  omega

/-!
## Project 1 follow-up — Pure-spine cascade specialization

Two corollaries of `cascade_mult_exact` specialized to the unique
"pure-spine" cascade start `n_L = 2^(L+1) - 1` (with `L = K + 1`).
The pure-spine entry has the maximal possible `padicValNat 2 (n+1)`
for a given length-`L` cascade (every step keeps `v_2 = L+1` initially,
decrementing by one each cascade step until landing at `v_2 = 1` after
`L+1` steps).

LaTTe siblings (both REAL in `src/ai_math/cascade_mult.clj`):

  1. `pure-spine-after-L-cascade` — closed form for the cascade output:
     `cc^[K+1] (2^(K+2) - 1) = 2 * 3^(K+1) - 1`.

  2. `pure-spine-first-descent-v` — `v_2` of the very first descent
     step that exits the cascade, expressed in terms of `v_2(3^(K+2) - 1)`.
     The LaTTe proof uses only `v_two_of_double` (i.e.
     `v_2(2*x) = succ(v_2(x))` for `x ≠ 0`); it does NOT compute
     `v_2(3^j - 1)` directly (that's the LTE identity, which is left as
     an external input to the formula). Same here: we mirror exactly
     that statement, no LTE axiom required.

Mathlib lemmas used here: `padicValNat.prime_pow` (for
`padicValNat 2 (2^k) = k`), `padicValNat.mul`, `padicValNat_self`,
`Nat.eq_of_mul_eq_mul_left`, `pow_pos`, `Nat.pow_le_pow_right`.
-/

/-- **pure_spine_after_L_cascade — REAL.** (Project 1 follow-up.)

For `K : ℕ`, the pure-spine cascade start `n_K = 2^(K+2) - 1` satisfies

    `cc^[K+1] (2^(K+2) - 1) = 2 * 3^(K+1) - 1`.

Direct corollary of `cascade_mult_exact` at `n = 2^(K+2) - 1`, followed by
cancellation of `2^(K+1)` and a `-1` on both sides.

REAL — sorry-free, no new axioms.

LaTTe sibling: `src/ai_math/cascade_mult.clj` :: `pure-spine-after-L-cascade`. -/
theorem pure_spine_after_L_cascade (K : Nat) :
    cc^[K + 1] (2 ^ (K + 2) - 1) = 2 * 3 ^ (K + 1) - 1 := by
  -- Let n = 2^(K+2) - 1.
  set n := 2 ^ (K + 2) - 1 with hn_def
  -- pow positivity / nonzero.
  have hpow_pos : 0 < (2 : Nat) ^ (K + 2) := pow_pos (by norm_num : (0 : Nat) < 2) (K + 2)
  have hpow_ge_two : 2 ≤ (2 : Nat) ^ (K + 2) := by
    calc 2 = 2 ^ 1     := (pow_one 2).symm
      _ ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- n + 1 = 2^(K+2).
  have hn1 : n + 1 = 2 ^ (K + 2) := by
    show (2 ^ (K + 2) - 1) + 1 = 2 ^ (K + 2)
    omega
  -- n is odd. Write 2^(K+2) = 2 * 2^(K+1), so n = 2 * 2^(K+1) - 1 = 2*(2^(K+1)-1) + 1.
  have hn_odd : Odd n := by
    refine ⟨2 ^ (K + 1) - 1, ?_⟩
    have hpow_split : (2 : Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) := by
      rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
    have hpow1_pos : 0 < (2 : Nat) ^ (K + 1) :=
      pow_pos (by norm_num : (0 : Nat) < 2) (K + 1)
    show n = 2 * (2 ^ (K + 1) - 1) + 1
    rw [hn_def, hpow_split]
    omega
  -- v_2(n+1) = K+2. padicValNat 2 (2^(K+2)) = K+2 via padicValNat.prime_pow.
  have hv2_pow : padicValNat 2 ((2 : Nat) ^ (K + 2)) = K + 2 :=
    padicValNat.prime_pow (K + 2)
  have hv2 : padicValNat 2 (n + 1) = K + 2 := by
    rw [hn1]; exact hv2_pow
  -- Apply cascade_mult_exact: 2^(K+1) * (cc^[K+1] n + 1) = (n+1) * 3^(K+1).
  have hcme : 2 ^ (K + 1) * ((cc^[K + 1] n) + 1) = (n + 1) * 3 ^ (K + 1) :=
    cascade_mult_exact n K hn_odd hv2
  -- Rewrite (n+1) on RHS as 2^(K+2) = 2 * 2^(K+1).
  have hpow_split : (2 : Nat) ^ (K + 2) = 2 * 2 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  have hrhs : (n + 1) * 3 ^ (K + 1) = 2 ^ (K + 1) * (2 * 3 ^ (K + 1)) := by
    rw [hn1, hpow_split]; ring
  -- So 2^(K+1) * (cc^[K+1] n + 1) = 2^(K+1) * (2 * 3^(K+1)).
  have hmul_eq : 2 ^ (K + 1) * ((cc^[K + 1] n) + 1) =
                 2 ^ (K + 1) * (2 * 3 ^ (K + 1)) := by
    rw [hcme, hrhs]
  -- Cancel 2^(K+1) > 0.
  have hpow1_pos : 0 < (2 : Nat) ^ (K + 1) :=
    pow_pos (by norm_num : (0 : Nat) < 2) (K + 1)
  have hcancel : (cc^[K + 1] n) + 1 = 2 * 3 ^ (K + 1) :=
    Nat.eq_of_mul_eq_mul_left hpow1_pos hmul_eq
  -- 3^(K+1) > 0 so 2*3^(K+1) ≥ 2; conclude by omega.
  have hpow3_pos : 0 < (3 : Nat) ^ (K + 1) :=
    pow_pos (by norm_num : (0 : Nat) < 3) (K + 1)
  -- Conclude: cc^[K+1] n = (cc^[K+1] n + 1) - 1 = 2*3^(K+1) - 1.
  omega

/-- **pure_spine_first_descent_v — REAL.** (Project 1 follow-up.)

After the `L = K+1` pure-spine cascade, the post-cascade value is
`m_K = 2 * 3^(K+1) - 1` (see `pure_spine_after_L_cascade`). The next
Collatz step computes `3 m_K + 1`. Pure algebra shows

    `3 * (2 * 3^(K+1) - 1) + 1 = 2 * (3^(K+2) - 1)`,

so taking `padicValNat 2` of both sides (using `padicValNat 2 (2*x)
= padicValNat 2 x + 1` when `x ≠ 0`) gives

    `padicValNat 2 (3 * m_K + 1) = padicValNat 2 (3^(K+2) - 1) + 1`.

Note: the LaTTe sibling does NOT compute `v_2(3^j - 1)` explicitly
(that's the LTE identity); the mirror here matches LaTTe exactly,
leaving `padicValNat 2 (3^(K+2) - 1)` as an opaque term on the RHS.
No LTE axiom is required for this statement.

REAL — sorry-free, no new axioms.

LaTTe sibling: `src/ai_math/cascade_mult.clj` :: `pure-spine-first-descent-v`. -/
theorem pure_spine_first_descent_v (K : Nat) :
    padicValNat 2 (3 * (2 * 3 ^ (K + 1) - 1) + 1)
      = padicValNat 2 ((3 : Nat) ^ (K + 2) - 1) + 1 := by
  -- 3^(K+1) ≥ 3 > 0, so 2 * 3^(K+1) ≥ 6 ≥ 1.
  have h3pow_pos : 0 < (3 : Nat) ^ (K + 1) := pow_pos (by norm_num : (0 : Nat) < 3) (K + 1)
  have h3pow_ge : (3 : Nat) ^ (K + 1) ≥ 3 := by
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- 3^(K+2) = 3 * 3^(K+1).
  have hpow_split : (3 : Nat) ^ (K + 2) = 3 * 3 ^ (K + 1) := by
    rw [show K + 2 = (K + 1) + 1 from rfl, pow_succ]; ring
  -- Algebraic identity: 3*(2*3^(K+1) - 1) + 1 = 2 * (3^(K+2) - 1).
  -- Both subtractions are well-behaved (2*3^(K+1) ≥ 2 and 3^(K+2) ≥ 3 ≥ 1).
  have halg : 3 * (2 * 3 ^ (K + 1) - 1) + 1 = 2 * ((3 : Nat) ^ (K + 2) - 1) := by
    rw [hpow_split]
    omega
  -- 3^(K+2) - 1 ≠ 0 since 3^(K+2) ≥ 3 > 1.
  have h3pow2_ge : (3 : Nat) ^ (K + 2) ≥ 3 := by
    rw [hpow_split]; nlinarith [h3pow_ge]
  have hm_ne : (3 : Nat) ^ (K + 2) - 1 ≠ 0 := by omega
  -- padicValNat 2 (2 * x) = padicValNat 2 x + 1 when x ≠ 0.
  have htwo_ne : (2 : Nat) ≠ 0 := by norm_num
  have hmul : padicValNat 2 (2 * ((3 : Nat) ^ (K + 2) - 1))
            = padicValNat 2 ((3 : Nat) ^ (K + 2) - 1) + 1 := by
    rw [padicValNat.mul htwo_ne hm_ne, padicValNat_self]
    omega
  rw [halg, hmul]

/-! ### v_2 multiplicativity (LaTTe `v-two-mul-distrib` mirror)

Cross-reference: the LaTTe theorem `v-two-mul-distrib` in
`src/ai_math/two_adic_valuation.clj` states

    `v_2(a * b) = v_2(a) + v_2(b)`  for positive `a, b`.

In Lean 4 + Mathlib this is already a library lemma:
`padicValNat.mul` (in `Mathlib.NumberTheory.Padics.PadicVal.Basic`),
applicable for any prime `p` (via `[Fact p.Prime]`) and non-zero
naturals. The wrapper `v_two_mul_distrib` below specializes it to
`p = 2`. Mathlib auto-provides `Fact (Nat.Prime 2)`, so no explicit
instance plumbing is needed (this lemma is already used inside the
cascade theorems above — see `cascade_landing_v2` and
`pure_spine_first_descent_v`).

Helper-level mirrors (also direct Mathlib facts):

  * `v-two-of-mul-odd-left` (K-thread): in Lean, `v_2(odd * b) = v_2(b)`
    follows from `padicValNat.mul` + the fact that `padicValNat 2 (2k+1) = 0`
    (an odd natural has 2-adic valuation 0, i.e. `Nat.Odd.padicValNat_eq_zero`
    / `Odd.padicValNat_two_eq_zero` in Mathlib).
  * `odd-times-odd-is-odd` (K-thread): `Odd.mul` in Mathlib core.

LaTTe sibling: `src/ai_math/two_adic_valuation.clj` :: `v-two-mul-distrib`. -/
theorem v_two_mul_distrib (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat 2 (a * b) = padicValNat 2 a + padicValNat 2 b :=
  padicValNat.mul ha hb

/-- Odd times odd is odd. Direct mirror of LaTTe `odd-times-odd-is-odd`.

Note: the local `TerrasDensity.Odd` is defined as `∃ k, n = 2k + 1`
(see line 57 above), so we cannot reuse Mathlib's `Odd.mul` projection
directly. Instead we open the witnesses and exhibit the new witness
`2*j*k + j + k` via `ring`. -/
theorem odd_times_odd_is_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  obtain ⟨j, hj⟩ := ha
  obtain ⟨k, hk⟩ := hb
  refine ⟨2 * j * k + j + k, ?_⟩
  rw [hj, hk]; ring


/-!
## C.5/C.6 endgame — Terras (1976) headline (Bob session 2026-05-18)

LaTTe siblings in `src/ai_math/terras_density.clj`:
- `pow-two-exceeds-nat`               (REAL, helper)
- `admissible-parity-vector-density`  (REAL, C.5 wrapper)
- `terras-stopping-time-density`      (REAL, C.6 ε-bound)
-/

/-- **C.6 helper: pow_two_exceeds_nat.** For any n : Nat, there exists k : Nat
with n < 2^k. Direct from Mathlib's `Nat.lt_two_pow_self`. -/
theorem pow_two_exceeds_nat (n : Nat) : ∃ k : Nat, n < 2 ^ k :=
  ⟨n, Nat.lt_two_pow_self⟩

/-- **C.5: admissible_parity_vector_density.** For r, k, p, q : Nat with
`r < 2^k` and `q < p * 2^k`, the parity-vector class `{n : PVEq n r k}`
has density bounded above by p/q.

Direct wrapper of `density_bounded_by_parity_vector`; matches the LaTTe
sibling `admissible-parity-vector-density`. -/
theorem admissible_parity_vector_density
    (r k p q : Nat) (hr : r < 2 ^ k) (hfrac : q < p * 2 ^ k) :
    density_bounded (fun n => PVEq n r k) p q :=
  density_bounded_by_parity_vector r k p q hr hfrac

/-- **C.6: terras_stopping_time_density.** ε-bound formulation of Terras (1976):
for any rational ε = p/q > 0 (with `p > 0`, `q > 0`) and any residue r : Nat,
there exists k : Nat such that `r < 2^k` and the parity-vector class
`{n : PVEq n r k}` has density bounded above by p/q.

Mirrors LaTTe `terras-stopping-time-density`. Proof: take k from
`pow_two_exceeds_nat (r + q)`; then r < r + q < 2^k and q ≤ r + q < 2^k,
and q < 2^k ≤ p * 2^k since p ≥ 1. Apply admissible_parity_vector_density. -/
theorem terras_stopping_time_density
    (r p q : Nat) (_hp : 0 < p) (hq : 0 < q) :
    ∃ k : Nat, r < 2 ^ k ∧ density_bounded (fun n => PVEq n r k) p q := by
  obtain ⟨k, hk⟩ := pow_two_exceeds_nat (r + q)
  have hr_lt : r < 2 ^ k := by omega
  have hq_lt : q < 2 ^ k := by omega
  have hpw_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h_le : 2 ^ k ≤ p * 2 ^ k := Nat.le_mul_of_pos_left (2 ^ k) _hp
  have hfrac : q < p * 2 ^ k := lt_of_lt_of_le hq_lt h_le
  exact ⟨k, hr_lt, admissible_parity_vector_density r k p q hr_lt hfrac⟩

end TerrasDensity
