import Propositio.NumberTheory.Collatz.ValuationDensity

/-!
# The second-moment identity for the `v₂(3n+1)` valuation distribution

`CollatzValuationDensity.expected_valuation_sum` proves the exact first-moment
identity `Σ_{a=1}^{M-1} a · 2^(M-a-1) = 2^M - M - 1`, i.e. the expected 2-adic
valuation `v₂(3r+1)` over residues `r < 2^M` converges to `2` (the "Collatz
contracts on average" arithmetic backbone).

This file proves the matching **second-moment** identity

`Σ_{a=1}^{M-1} a² · 2^(M-a-1) = 3·2^M - (M² + 2M + 3)`

for `M ≥ 1`. Combined with the geometric count law
`CollatzValuationDensity.v2_count`, this gives `E[a²] → 6` as `M → ∞`, hence
`Var[a] = E[a²] - E[a]² → 6 - 4 = 2` — a genuinely new quantitative refinement
of the concentration behaviour of the valuation distribution (relevant to the
Chernoff/geometric-tail machinery in `CollatzBinomialTail`).

The proof is a direct mirror of `expected_valuation_sum`'s own induction:
peel the top index `a = M-1` from `Finset.Ico 1 M`, reindex the tail sum via
the doubling relation `2^(M-a-1) = 2 · 2^((M-1)-a-1)`, apply the induction
hypothesis, and close with `omega` (treating `2^n` and `n^2` as opaque atoms,
exactly as the template does for `2^n`). The only new ingredient (absent from
the first-moment proof) is the auxiliary growth bound `n² + 2n + 3 ≤ 3·2^n`
(for `n ≥ 1`), needed to keep the `Nat`-subtraction well-defined across the
induction step; it is proved by a small self-contained induction below.

Axiom-clean: no `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzValuationSecondMoment

open CollatzValuationDensity

/-! ## Auxiliary growth bound

`n² + 2n + 3 ≤ 3 · 2^n` for `n ≥ 1` (with equality at `n = 1`). This is exactly
the fact needed to keep `3·2^n - (n²+2n+3)` (and its successor-index cousin)
well-behaved under `Nat` subtraction in the main induction. -/

theorem sq_add_bound (n : Nat) (hn : 1 ≤ n) : n ^ 2 + 2 * n + 3 ≤ 3 * 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; decide
    · have hk := ih h0
      have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      nlinarith [hk, hpow]

/-! ## The second-moment partial sum -/

/-- **Second-moment valuation partial sum — REAL.**
`Σ_{a=1}^{M-1} a² · 2^(M-a-1) = 3·2^M - (M²+2M+3)` for `M ≥ 1`. Each summand
`a² · 2^(M-a-1)` is `a² ·` the count of residues `r < 2^M` with `v₂(3r+1) = a`
(`CollatzValuationDensity.v2_count`), so this is the second moment of the
2-adic valuation over `r < 2^M`. Combined with `expected_valuation_sum`
(`E[a] → 2`), gives `E[a²] → 6`, hence `Var[a] → 2` as `M → ∞`. -/
theorem second_moment_sum (M : Nat) (hM : 1 ≤ M) :
    (Finset.Ico 1 M).sum (fun a => a ^ 2 * 2 ^ (M - a - 1)) = 3 * 2 ^ M - (M ^ 2 + 2 * M + 3) := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h1 | h1
    · -- M = 1 (n = 0): empty sum = 0 = 3*2 - (1+2+3) = 0.
      subst h1; decide
    · -- M = n+1 with n ≥ 1. Split off the top index a = n.
      have hn1 : 1 ≤ n := h1
      have hico : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn1]
      rw [hico, Finset.sum_insert (by simp)]
      -- term a = n contributes n^2 * 2^(n+1-n-1) = n^2 * 2^0 = n^2.
      have hterm : n ^ 2 * 2 ^ (n + 1 - n - 1) = n ^ 2 := by
        rw [show n + 1 - n - 1 = 0 from by omega]; ring
      -- the inner sum re-indexes: 2^(n+1-a-1) = 2 * 2^(n-a-1) for a < n.
      have hshift : (Finset.Ico 1 n).sum (fun a => a ^ 2 * 2 ^ (n + 1 - a - 1))
          = 2 * (Finset.Ico 1 n).sum (fun a => a ^ 2 * 2 ^ (n - a - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_Ico] at ha
        have : n + 1 - a - 1 = (n - a - 1) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [hterm, hshift, ih hn1]
      -- need the growth bound so the IH's Nat subtraction behaves under doubling.
      have hbound : n ^ 2 + 2 * n + 3 ≤ 3 * 2 ^ n := sq_add_bound n hn1
      have hpow : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [hpow, hsq]
      omega

end CollatzValuationSecondMoment
