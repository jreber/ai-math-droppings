import Propositio.NumberTheory.Collatz.SyracuseThreeAdicBias
import Mathlib.Logic.Function.Iterate
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# The Syracuse maximal-growth family on Mersenne-like numbers `2^k - 1`

The Syracuse map `Syr` (the odd part of `3N+1`, defined in `SyracuseThreeAdicBias`) sends a
Mersenne-like number `2^k - 1` through the longest possible run of "pure tripling" steps.

Concretely, starting from `2^k - 1`, the `j`-th Syracuse iterate (for `0 ≤ j ≤ k-1`) is

    Syr^[j] (2^k - 1) = 3^j * 2^(k-j) - 1.

Each step strips exactly one factor of `2` from `3N+1` while multiplying the "`3^j`" part by `3`:
this is the family of trajectories on which the Syracuse map grows the fastest.

## Main results

  * `Syr_step`              — one-step identity `Syr (4*M - 1) = 6*M - 1` for `M ≥ 1`.
  * `Syr_iterate_mersenne`  — the closed form `Syr^[j] (2^k - 1) = 3^j * 2^(k-j) - 1`, `j < k`.

All sorry-free / axiom-clean (no `native_decide`).
-/

namespace SyracuseThreeAdicBias

/-- `padicValNat 2 (2 * w) = 1` when `w` is odd: the single factor of `2` is the only one. -/
private theorem padicValNat_two_two_mul_odd {w : ℕ} (hw : Odd w) :
    padicValNat 2 (2 * w) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := hw
  have h1 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have h2 : padicValNat 2 (2 * m + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  rw [padicValNat.mul (by norm_num) (by omega), h1, h2]

/-- **One Syracuse step on a maximal-growth value.**  For `M ≥ 1`,

    Syr (4*M - 1) = 6*M - 1.

Reason: `3*(4M-1)+1 = 12M-2 = 2*(6M-1)` and `6M-1` is odd, so `v₂(3·x+1) = 1` and the Syracuse
map divides off exactly one `2`.  Applied with `M = 3^j * 2^(e-2)` this is the tripling step
`3^j * 2^e - 1 ↦ 3^(j+1) * 2^(e-1) - 1` (valid for `e ≥ 2`). -/
theorem Syr_step (M : ℕ) (hM : 1 ≤ M) : Syr (4 * M - 1) = 6 * M - 1 := by
  have hw : Odd (6 * M - 1) := Nat.odd_iff.mpr (by omega)
  have heq : 3 * (4 * M - 1) + 1 = 2 * (6 * M - 1) := by omega
  have hv : padicValNat 2 (3 * (4 * M - 1) + 1) = 1 := by
    rw [heq]; exact padicValNat_two_two_mul_odd hw
  unfold Syr
  rw [hv, pow_one, heq, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **The Syracuse maximal-growth family.**  For `0 ≤ j ≤ k-1` (i.e. `j < k`),

    Syr^[j] (2^k - 1) = 3^j * 2^(k-j) - 1.

Each step trades one power of `2` for one power of `3`; the run lasts exactly `k` steps before
the exponent of `2` would drop below `1`. -/
theorem Syr_iterate_mersenne (k j : ℕ) (hj : j < k) :
    (Syr^[j]) (2 ^ k - 1) = 3 ^ j * 2 ^ (k - j) - 1 := by
  revert hj
  induction j with
  | zero => intro _; simp
  | succ n ih =>
    intro hj
    have hn : n < k := by omega
    rw [Function.iterate_succ_apply', ih hn]
    -- Goal: Syr (3^n * 2^(k-n) - 1) = 3^(n+1) * 2^(k-(n+1)) - 1
    have p1 : (2 : ℕ) ^ (k - n) = 2 ^ 2 * 2 ^ (k - n - 2) := by
      conv_lhs => rw [show k - n = 2 + (k - n - 2) from by omega]
      rw [pow_add]
    have p2 : (2 : ℕ) ^ (k - (n + 1)) = 2 ^ 1 * 2 ^ (k - n - 2) := by
      conv_lhs => rw [show k - (n + 1) = 1 + (k - n - 2) from by omega]
      rw [pow_add]
    have key1 : 3 ^ n * 2 ^ (k - n) = 4 * (3 ^ n * 2 ^ (k - n - 2)) := by
      rw [p1]; ring
    have key2 : 3 ^ (n + 1) * 2 ^ (k - (n + 1)) = 6 * (3 ^ n * 2 ^ (k - n - 2)) := by
      rw [p2]; ring
    have hMpos : 0 < 3 ^ n * 2 ^ (k - n - 2) := by positivity
    rw [key1, key2]
    exact Syr_step _ hMpos

end SyracuseThreeAdicBias
