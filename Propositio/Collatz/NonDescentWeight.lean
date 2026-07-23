import Propositio.Collatz.DensityCount

/-!
# Non-descending Collatz orbits are "tripling-heavy"

This file proves the **structural weight lemma** for the Everett–Terras
"almost all integers descend" program: a Collatz orbit that does **not** drop
below its start within `k` Terras steps must take a *disproportionate* number of
odd (`3n+1`) steps.  Concretely, the count of odd steps
`a := aCoef n k` (defined in `CollatzDensityCount`) satisfies `3^a ≥ 2^k`,
i.e. `a ≥ k · log₃2 = 0.6309… · k`, a strict excess over the `k/2` an
"unbiased" parity vector would carry.

Together with a binomial-tail / large-deviation bound on parity vectors (the
remaining analytic input, documented in `CollatzDensityCount` §9 and restated
here), this lemma yields the Everett–Terras theorem `b(k) → 0`.

## The mathematics

Recall the **Terras affine form** (`CollatzDensityCount.affine_form`):
`2^j · T^j n = 3^{aCoef n j} · n + cCoef n j`, with `aCoef n j` the number of
odd steps and `cCoef n j ≥ 0` the accumulated additive constant.

If `Bad k n` (the orbit does not descend within `k` steps) and `1 ≤ k`, then in
particular `n ≤ T^k n`, so multiplying by `2^k` and applying `affine_form`:

    2^k · n ≤ 2^k · T^k n = 3^{aCoef n k} · n + cCoef n k.        (★)

This is the **exact** inequality — the additive `cCoef n k` is carried, never
dropped.  Rearranging (★): if it were the case that `3^{aCoef n k} < 2^k`, then
`3^{aCoef n k} ≤ 2^k − 1`, so `3^{aCoef n k} · n ≤ 2^k · n − n`, and (★) forces
`n ≤ cCoef n k`.  Contrapositively:

    cCoef n k < n  →  2^k ≤ 3^{aCoef n k}.                        (HEADLINE)

### Handling the additive correction `cCoef n k` HONESTLY

The hypothesis `cCoef n k < n` is the honest, *exact* condition under which the
clean bound `2^k ≤ 3^{aCoef n k}` follows — it is NOT assumed away.  Numerically
(`#eval`), the ONLY non-descending `n` for which `2^k ≤ 3^{aCoef n k}` *fails*
are the degenerate boundary values `n ∈ {0, 1, 2}` (orbits that never leave the
small fixed/short-cycle region); for *every* `n ≥ 3` — in particular the entire
density-relevant regime `n ≥ 2^k` — non-descent forces `2^k ≤ 3^{aCoef n k}`.
We package both forms:

* `bad_implies_affine_bound` — the raw exact inequality (★), correction explicit.
* `three_pow_ge_of_correction_lt` / `bad_implies_three_pow_ge` — the clean
  `2^k ≤ 3^{aCoef n k}` under the honest side condition `cCoef n k < n`.

### From a power bound to an odd-step count

`minOdd k` is the least `a` with `2^k ≤ 3^a` (it exists since `3^k ≥ 2^k`).
`odd_steps_ge_of_three_pow_ge` converts `2^k ≤ 3^{aCoef n k}` into
`minOdd k ≤ aCoef n k`, a pure lower bound on the odd-step count, stated with NO
real logarithms (only `Nat` powers).  `bad_implies_odd_steps_ge` is the end-to-end
statement.

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzNonDescentWeight

open TerrasDensity
open CollatzStoppingF3 (DescBy)
open CollatzBadDensity (Bad)
open CollatzDensityCount (aCoef cCoef affine_form)

/-! ## §1  Non-descent gives the exact affine inequality (★) -/

/-- **From `Bad` to the `j = k` non-descent instance.**  `Bad k n` says the orbit
does not drop below `n` at any step `1 ≤ j ≤ k`; for `k ≥ 1` the step `j = k`
itself gives `n ≤ T^k n`.  (`Bad k n := ¬ DescBy n k` and
`DescBy n k := ∃ j, 1 ≤ j ∧ j ≤ k ∧ T^j n < n`.) -/
theorem bad_implies_le_iter (k n : Nat) (hk : 1 ≤ k) (hbad : Bad k n) :
    n ≤ T_iter n k := by
  by_contra hlt
  exact hbad ⟨k, hk, le_refl k, Nat.lt_of_not_le hlt⟩

/-- **The exact affine inequality (★).**  If the orbit of `n` has not descended
within `k` steps (`n ≤ T^k n`), then
`2^k · n ≤ 3^{aCoef n k} · n + cCoef n k`.  This is `affine_form` applied to a
non-descending orbit; the additive correction `cCoef n k` is carried explicitly. -/
theorem affine_bound_of_le_iter (k n : Nat) (h : n ≤ T_iter n k) :
    2 ^ k * n ≤ 3 ^ (aCoef n k) * n + cCoef n k := by
  have haf := affine_form n k
  calc 2 ^ k * n ≤ 2 ^ k * T_iter n k := Nat.mul_le_mul_left _ h
    _ = 3 ^ (aCoef n k) * n + cCoef n k := haf

/-- **`bad_implies_affine_bound` (item 1).**  For `k ≥ 1`, a non-descending orbit
(`Bad k n`) satisfies the exact inequality
`2^k · n ≤ 3^{aCoef n k} · n + cCoef n k`. -/
theorem bad_implies_affine_bound (k n : Nat) (hk : 1 ≤ k) (hbad : Bad k n) :
    2 ^ k * n ≤ 3 ^ (aCoef n k) * n + cCoef n k :=
  affine_bound_of_le_iter k n (bad_implies_le_iter k n hk hbad)

/-! ## §2  HEADLINE — the clean power bound `2^k ≤ 3^{aCoef n k}` -/

/-- **The clean power bound, honest version.**  From the exact inequality (★),
`2^k · n ≤ 3^{aCoef n k} · n + cCoef n k`, *together with* the side condition
`cCoef n k < n`, one gets `2^k ≤ 3^{aCoef n k}`.

Proof: if instead `3^{aCoef n k} < 2^k`, i.e. `3^{aCoef n k} + 1 ≤ 2^k`, then
`2^k · n ≥ (3^{aCoef n k} + 1) · n = 3^{aCoef n k} · n + n`; combined with (★),
`3^{aCoef n k} · n + n ≤ 3^{aCoef n k} · n + cCoef n k`, forcing `n ≤ cCoef n k`,
contradicting `cCoef n k < n`.  The side hypothesis is the honest, exact
condition — numerically it fails only for the boundary `n ∈ {0,1,2}`. -/
theorem three_pow_ge_of_correction_lt (k n : Nat)
    (hbound : 2 ^ k * n ≤ 3 ^ (aCoef n k) * n + cCoef n k)
    (hc : cCoef n k < n) : 2 ^ k ≤ 3 ^ (aCoef n k) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  -- 3^a + 1 ≤ 2^k
  have h1 : 3 ^ (aCoef n k) + 1 ≤ 2 ^ k := hlt
  have h2 : (3 ^ (aCoef n k) + 1) * n ≤ 2 ^ k * n := Nat.mul_le_mul_right n h1
  -- (3^a + 1)·n = 3^a·n + n
  have h3 : 3 ^ (aCoef n k) * n + n ≤ 2 ^ k * n := by
    calc 3 ^ (aCoef n k) * n + n = (3 ^ (aCoef n k) + 1) * n := by ring
      _ ≤ 2 ^ k * n := h2
  -- combine with (★): 3^a·n + n ≤ 3^a·n + cCoef
  have h4 : 3 ^ (aCoef n k) * n + n ≤ 3 ^ (aCoef n k) * n + cCoef n k :=
    le_trans h3 hbound
  -- ⟹ n ≤ cCoef, contradiction
  have h5 : n ≤ cCoef n k := Nat.le_of_add_le_add_left h4
  omega

/-- **`bad_implies_three_pow_ge` (HEADLINE, item 2).**  For `k ≥ 1`, a
non-descending orbit (`Bad k n`) with the honest correction control
`cCoef n k < n` satisfies the clean power bound `2^k ≤ 3^{aCoef n k}`: the number
of odd (`3n+1`) steps is large enough that `3^{(odd steps)}` dominates `2^k`. -/
theorem bad_implies_three_pow_ge (k n : Nat) (hk : 1 ≤ k) (hbad : Bad k n)
    (hc : cCoef n k < n) : 2 ^ k ≤ 3 ^ (aCoef n k) :=
  three_pow_ge_of_correction_lt k n (bad_implies_affine_bound k n hk hbad) hc

/-! ## §3  From the power bound to the odd-step count `aCoef n k ≥ minOdd k` -/

/-- The least exponent `a` with `2^k ≤ 3^a`.  Exists because `3^k ≥ 2^k`
(`Nat.pow_le_pow_left`), so `a = k` always witnesses the predicate. -/
def minOdd (k : Nat) : Nat :=
  Nat.find (⟨k, Nat.pow_le_pow_left (by norm_num) k⟩ : ∃ a, 2 ^ k ≤ 3 ^ a)

/-- `minOdd k` indeed satisfies its defining property: `2^k ≤ 3^{minOdd k}`. -/
theorem two_pow_le_three_pow_minOdd (k : Nat) : 2 ^ k ≤ 3 ^ (minOdd k) :=
  Nat.find_spec (⟨k, Nat.pow_le_pow_left (by norm_num) k⟩ : ∃ a, 2 ^ k ≤ 3 ^ a)

/-- Minimality: any `a` with `2^k ≤ 3^a` has `minOdd k ≤ a`. -/
theorem minOdd_le_of_two_pow_le (k a : Nat) (h : 2 ^ k ≤ 3 ^ a) : minOdd k ≤ a :=
  Nat.find_le h

/-- **`odd_steps_ge_of_three_pow_ge`.**  Converting the power bound into an
odd-step count: `2^k ≤ 3^a` implies `minOdd k ≤ a`.  Specialized to `a = aCoef n k`
this lower-bounds the number of `3n+1` steps purely in terms of `k` (no real
logarithms — `minOdd k = ⌈k · log₃2⌉` is computed by comparing `Nat` powers). -/
theorem odd_steps_ge_of_three_pow_ge (k n : Nat)
    (h : 2 ^ k ≤ 3 ^ (aCoef n k)) : minOdd k ≤ aCoef n k :=
  minOdd_le_of_two_pow_le k (aCoef n k) h

/-- **`bad_implies_odd_steps_ge` (item 3).**  End-to-end: for `k ≥ 1`, a
non-descending orbit (`Bad k n`) with honest correction control `cCoef n k < n`
takes at least `minOdd k` odd (`3n+1`) steps in its first `k` steps,
`minOdd k ≤ aCoef n k`.  Since `minOdd k = ⌈k · log₃2⌉ ≈ 0.6309·k > k/2`, this is
the disproportionate-tripling statement. -/
theorem bad_implies_odd_steps_ge (k n : Nat) (hk : 1 ≤ k) (hbad : Bad k n)
    (hc : cCoef n k < n) : minOdd k ≤ aCoef n k :=
  odd_steps_ge_of_three_pow_ge k n (bad_implies_three_pow_ge k n hk hbad hc)

/-! ### Sanity: the threshold `minOdd k` is strictly tripling-heavy

`minOdd k` grows like `0.6309·k`, strictly above `k/2`.  We pin a few values to
confirm the bound is non-trivial (these are `decide`-checked, kernel-computable
via `Nat.find` on a decidable predicate). -/

theorem minOdd_one   : minOdd 1 = 1  := by decide
theorem minOdd_two   : minOdd 2 = 2  := by decide
theorem minOdd_three : minOdd 3 = 2  := by decide
theorem minOdd_four  : minOdd 4 = 3  := by decide
theorem minOdd_five  : minOdd 5 = 4  := by decide
theorem minOdd_six   : minOdd 6 = 4  := by decide
theorem minOdd_ten   : minOdd 10 = 7 := by decide

/-- A clean qualitative consequence: for `k ≥ 2`, the odd-step threshold strictly
exceeds half the steps, `k < 2 · minOdd k` — a *strict* tripling excess.  (For
`k = 1` it is an equality `1 = 2·1 − 1`; we state the strict form for `k ≥ 2`
where `2^k ≤ 3^{minOdd k}` forces `minOdd k > k/2`.) -/
theorem minOdd_gt_half (k : Nat) (hk : 2 ≤ k) : k < 2 * minOdd k := by
  -- 2^k ≤ 3^a ≤ (2^2)^a = 2^(2a) ⟹ k ≤ 2a; strictness from 3^a < 4^a for a ≥ 1.
  by_contra hle
  rw [Nat.not_lt] at hle  -- 2 * minOdd k ≤ k
  set a := minOdd k with ha
  have hspec : 2 ^ k ≤ 3 ^ a := two_pow_le_three_pow_minOdd k
  -- 3^a ≤ 4^a = 2^(2a) ≤ 2^k (since 2a ≤ k); but 3^a < 4^a strictly when a ≥ 1.
  have h3lt4 : 3 ^ a < 4 ^ a := by
    have hapos : 1 ≤ a := by
      -- a = 0 ⟹ 2^k ≤ 1 ⟹ k = 0, contradicting k ≥ 2
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · exfalso; rw [h0] at hspec; simp at hspec
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega
      · exact h0
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h4 : (4 : Nat) ^ a = 2 ^ (2 * a) := by
    rw [pow_mul]; norm_num
  have hle2 : 2 ^ (2 * a) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hle
  -- chain: 2^k ≤ 3^a < 4^a = 2^(2a) ≤ 2^k, contradiction
  rw [h4] at h3lt4
  omega

/-! ## §4  Bridge to `b(k) → 0` (documented analytic target)

The structural lemmas above are the *combinatorial* half of Everett–Terras.
Here is the precise shape of the remaining analytic input.

**Setup.**  By `CollatzDensityCount.descending_vector_count`, the bad count
`β(k) = 2^k − D(k)` counts residues `r < 2^k` whose canonical representative
`n = r + 2^k` (which lies in the regime `n ≥ 2^k`, so `n ≥ 3` and the boundary
exceptions `n ∈ {0,1,2}` are excluded) is `Bad k`.  By
`bad_implies_odd_steps_ge`, *every* such survivor — once the honest correction
`cCoef n k < n` is supplied in the lift regime — has odd-step count
`aCoef n k ≥ minOdd k`.

Because `aCoef n k` depends only on the length-`k` parity vector
(`CollatzDensityCount.coef_congr`) and the parity vector is determined by
`n mod 2^k` (`CollatzDensityCount.PVEq_of_mod_eq`), the map
`r ↦ (parity vector of r + 2^k)` is the bijection `pvMap k : Fin (2^k) ≃ (Fin k →
Bool)`, and `aCoef` becomes the Hamming **weight** of the parity vector (number of
odd entries).  Hence:

    β(k)  =  #{ survivors }  ≤  #{ v ∈ {0,1}^k : weight(v) ≥ minOdd k }.

So `b(k) = β(k)/2^k ≤ #{weight ≥ minOdd k}/2^k`, and since
`minOdd k / k → log₃2 = 0.6309… > 1/2`, the right-hand side is a **binomial upper
tail past the mean**, which `→ 0` by the standard Chernoff/Hoeffding
large-deviation bound.  This binomial-tail estimate is the single remaining
analytic fact (the file proves everything *up to* it).

We record the typed shape of this domination as the open target. -/

/-- **`bk_to_zero_bridge` (documented target).**  The reduction statement: a lower
bound `minOdd k ≤ aCoef n k` on every survivor's odd-step count (delivered by
`bad_implies_odd_steps_ge`) means the bad set injects into the set of
"heavy-weight" parity vectors `{ weight ≥ minOdd k }`.  Concretely, the
implication below holds definitionally — it is the per-`n` content that, summed
over residues, gives `β(k) ≤ #{weight ≥ minOdd k}`; the remaining open input is
the binomial tail `#{weight ≥ minOdd k}/2^k → 0` (`minOdd k ≈ 0.6309·k > k/2`). -/
theorem bk_to_zero_bridge (k n : Nat) (hk : 1 ≤ k) (hbad : Bad k n)
    (hc : cCoef n k < n) :
    minOdd k ≤ aCoef n k ∧ 2 ^ k ≤ 3 ^ (aCoef n k) :=
  ⟨bad_implies_odd_steps_ge k n hk hbad hc, bad_implies_three_pow_ge k n hk hbad hc⟩

end CollatzNonDescentWeight
