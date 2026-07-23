import Propositio.Collatz.BinomialTail
import Propositio.Collatz.NonDescentWeight
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Unconditional decay of the Collatz non-descent binomial tail

This file upgrades the binomial-tail decay used by the Everett–Terras
"almost all Collatz orbits descend" capstone from a *conditional* statement
(`CollatzBinomialTail.binom_tail_decay`, which assumes an entropy-style
`C(k, t k) ≤ 2^k·ρ^k` bound and a geometric-constant bound `K k ≤ B`) to an
**unconditional** one, for the specific threshold `t k = minOdd k`.

## Strategy

`upperTail k (minOdd k) / 2^k → 0` follows from three facts.

1. **Geometric tail bound** (already proved, `binom_tail_geometric`):
   `upperTail k t ≤ C(k,t)·(1−r)⁻¹` with `r = (k−t)/(t+1)` for `k < 2t+1`.

2. **The geometric constant is bounded by a CONSTANT** (`geom_const_le_three`):
   `minOdd k ≥ (3/5)·k` (elementary, from `27 < 32`, i.e. `3^(3k) < 2^(5k)`),
   so `r ≤ 2/3` and `(1−r)⁻¹ ≤ 3` — no hypothesis.

3. **Central-binomial decay** (`central_decay`):
   `C(k, k/2)/2^k → 0`.  This is the genuinely analytic step.  Mathlib has
   **no** off-the-shelf upper bound `centralBinom n ≤ 4^n/√n`; the only direct
   `centralBinom`-vs-`4^n` facts are *lower* bounds.  We therefore derive the
   decay from **Stirling's formula** (`Stirling.tendsto_stirlingSeq_sqrt_pi`):
   writing `s n = n!/(√(2n)·(n/e)^n)`, an exact rearrangement gives, for `n ≥ 1`,
     `centralBinom n / 4^n = s(2n) / (s n)^2 · (1/√n)`,
   and `s(2n)/(s n)^2 → √π/π = 1/√π` while `1/√n → 0`, so the product `→ 0`.
   `C(k, k/2)/2^k → 0` then follows by comparing with the central coefficient
   (even/odd `k` handled by `Nat.choose_le_middle` and `centralBinom`).

Assembling 1+2+3 via `binom_tail_geometric` + `squeeze_zero` gives the headline
`upperTail_minOdd_decay` **unconditionally**, removing `hcoef`/`hK` from the
capstone and leaving only the descent dichotomy as a hypothesis downstream.

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.
-/

open Filter Topology
open CollatzBinomialTail
open CollatzNonDescentWeight

namespace CollatzTailDecayUncond

/-! ## §1  The geometric constant is bounded — `minOdd k ≥ (3/5) k` -/

/-- **`minOdd_ge_three_fifths`.**  `3·k ≤ 5·minOdd k`, i.e. `minOdd k ≥ (3/5)k`.

Elementary: set `a = minOdd k`, so `2^k ≤ 3^a`.  If we had `5a < 3k`, then
`5a ≤ 3k − 1 < 3k`, and `3^(5a) ≤ 3^(3k) = 27^k < 32^k = 2^(5k) = (2^k)^5 ≤ (3^a)^5
= 3^(5a)`, a contradiction.  Hence `3k ≤ 5a`. -/
theorem minOdd_ge_three_fifths (k : ℕ) : 3 * k ≤ 5 * minOdd k := by
  set a := minOdd k with ha
  have hspec : 2 ^ k ≤ 3 ^ a := two_pow_le_three_pow_minOdd k
  by_contra hlt
  rw [Nat.not_le] at hlt          -- 5 * a < 3 * k
  -- 3^(5a) ≤ 3^(3k) since 5a ≤ 3k
  have h1 : 3 ^ (5 * a) ≤ 3 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- 3^(3k) = 27^k < 32^k = 2^(5k)
  have h27 : (3 : ℕ) ^ (3 * k) = 27 ^ k := by rw [pow_mul]; norm_num
  have h32 : (2 : ℕ) ^ (5 * k) = 32 ^ k := by rw [pow_mul]; norm_num
  have h2 : (27 : ℕ) ^ k < 32 ^ k ∨ (27 : ℕ) ^ k = 32 ^ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · right; rw [hk0]; simp
    · left; exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  -- 2^(5k) = (2^k)^5 ≤ (3^a)^5 = 3^(5a)
  have h3 : (2 ^ k) ^ 5 ≤ (3 ^ a) ^ 5 := Nat.pow_le_pow_left hspec 5
  have h4 : (2 ^ k) ^ 5 = 2 ^ (5 * k) := by rw [← pow_mul]; ring_nf
  have h5 : (3 ^ a) ^ 5 = 3 ^ (5 * a) := by rw [← pow_mul]; ring_nf
  -- Chain: 3^(5a) ≤ 3^(3k) = 27^k ≤ 32^k = 2^(5k) = (2^k)^5 ≤ (3^a)^5 = 3^(5a).
  -- With strictness when k ≥ 1; handle k = 0 separately.
  rcases h2 with hstrict | heq
  · -- strict: 27^k < 32^k gives 3^(5a) < 3^(5a), contradiction
    rw [h27] at h1
    rw [h32] at h4
    -- h1 : 3^(5a) ≤ 27^k ; hstrict : 27^k < 32^k ; h4 : (2^k)^5 = 32^k
    -- h3 : (2^k)^5 ≤ (3^a)^5 ; h5 : (3^a)^5 = 3^(5a)
    omega
  · -- k = 0 case forces equality; then hlt : 5a < 0 impossible
    -- 27^k = 32^k over ℕ only if k = 0
    have hk0 : k = 0 := by
      by_contra hk
      have : (27 : ℕ) ^ k < 32 ^ k := Nat.pow_lt_pow_left (by norm_num) hk
      omega
    omega

/-- **`geom_const_le_three`.**  Over ℝ, for `k ≥ 1` the geometric constant
`(1 − (k − minOdd k)/(minOdd k + 1))⁻¹ ≤ 3`.

From `minOdd k ≥ (3/5)k` (and `minOdd k > k/2`, so the ratio is `< 1`): with
`a = minOdd k`, `r = (k−a)/(a+1) ≤ (2k/5)/(3k/5) = 2/3`, hence `1−r ≥ 1/3` and
`(1−r)⁻¹ ≤ 3`. -/
theorem geom_const_le_three (k : ℕ) (hk : 1 ≤ k) :
    (1 - ((k - minOdd k : ℕ) : ℝ) / ((minOdd k + 1 : ℕ) : ℝ))⁻¹ ≤ 3 := by
  set a := minOdd k with ha
  have h35 : 3 * k ≤ 5 * a := minOdd_ge_three_fifths k
  -- minOdd k > k/2 (strict), giving k - a < a + 1, so r < 1
  have hhalf : k < 2 * a := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- k = 1: minOdd 1 = 1, 1 < 2
      interval_cases k
      · simp [ha, minOdd_one]
    · exact minOdd_gt_half k hk2
  have ha1pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos a
  -- r = (k - a)/(a + 1)
  set r : ℝ := ((k - a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) with hr
  have hrnonneg : 0 ≤ r := by rw [hr]; positivity
  -- 1 - r ≥ 1/3:  need r ≤ 2/3, i.e. 3(k-a) ≤ 2(a+1).
  -- From 3k ≤ 5a:  3(k-a) = 3k - 3a ≤ 5a - 3a = 2a ≤ 2a + 2 = 2(a+1)  (over ℕ, k ≥ a since k < 2a needs a ≥ 1)
  have hka : (k : ℕ) - a < a + 1 := by omega
  -- numerator bound: 3*(k - a) ≤ 2*(a+1)
  have hnum : 3 * ((k - a : ℕ)) ≤ 2 * ((a + 1 : ℕ)) := by omega
  have hr23 : r ≤ 2 / 3 := by
    rw [hr, div_le_div_iff₀ ha1pos (by norm_num : (0:ℝ) < 3)]
    have : (3 : ℝ) * ((k - a : ℕ) : ℝ) ≤ 2 * ((a + 1 : ℕ) : ℝ) := by exact_mod_cast hnum
    nlinarith [this]
  have h1mr : (1 : ℝ) / 3 ≤ 1 - r := by linarith
  have hpos : (0 : ℝ) < 1 - r := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-! ## §2  The boundary coefficient is sub-central: `C(k, minOdd k) ≤ C(k, k/2)` -/

/-- **`choose_minOdd_le_central`.**  `C(k, minOdd k) ≤ C(k, k/2)`.

This is `Nat.choose_le_middle r n : choose n r ≤ choose n (n/2)`, specialized to
`r = minOdd k`.  (The middle coefficient `C(k, k/2)` is the largest; `minOdd k`
lies past the middle, but the inequality holds for *every* `r`.) -/
theorem choose_minOdd_le_central (k : ℕ) : k.choose (minOdd k) ≤ k.choose (k / 2) :=
  Nat.choose_le_middle (minOdd k) k

/-! ## §3  Central-binomial decay via Stirling -/

open Real Stirling

/-- Factorial expanded through the Stirling sequence: for `n ≥ 1`,
`(n! : ℝ) = stirlingSeq n · (√(2n) · (n/e)^n)`.  (Just unfolding `stirlingSeq`
and clearing the nonzero denominator.) -/
theorem factorial_eq_stirlingSeq_mul {n : ℕ} (hn : n ≠ 0) :
    (Nat.factorial n : ℝ) = stirlingSeq n * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * n) := Real.sqrt_pos.mpr (by positivity)
  have hden : (0 : ℝ) < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by positivity
  rw [stirlingSeq]
  field_simp

/-- The defining factorial identity for the central binomial coefficient over ℝ:
`centralBinom n · n! · n! = (2n)!`. -/
theorem centralBinom_factorial_identity (n : ℕ) :
    (Nat.centralBinom n : ℝ) * Nat.factorial n * Nat.factorial n
      = Nat.factorial (2 * n) := by
  have h : Nat.centralBinom n * Nat.factorial n * Nat.factorial n = Nat.factorial (2 * n) := by
    have hle : n ≤ 2 * n := by omega
    have hkey := Nat.choose_mul_factorial_mul_factorial hle
    -- choose (2n) n * n! * (2n - n)! = (2n)!, and 2n - n = n
    rw [Nat.centralBinom]
    rwa [show 2 * n - n = n by omega] at hkey
  exact_mod_cast h

/-- **The Stirling ratio identity (√n-cleared form).**  For `n ≥ 1`,
`(centralBinom n / 4^n) · √n = stirlingSeq (2n) / (stirlingSeq n)^2`.

Substituting the Stirling expansions of `(2n)!` and `(n!)^2` into the factorial
identity `centralBinom n · (n!)^2 = (2n)!` and cancelling `(2n/e)^{2n}/(n/e)^{2n}
= 4^n` and `√(4n)·√n/(2n) = 1`. -/
theorem centralBinom_div_four_pow_mul_sqrt {n : ℕ} (hn : n ≠ 0) :
    (Nat.centralBinom n : ℝ) / 4 ^ n * Real.sqrt n
      = stirlingSeq (2 * n) / (stirlingSeq n) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2n : (2 * n : ℕ) ≠ 0 := by omega
  -- Expansions
  have hfn : (Nat.factorial n : ℝ) = stirlingSeq n * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) :=
    factorial_eq_stirlingSeq_mul hn
  have hf2n : (Nat.factorial (2 * n) : ℝ)
      = stirlingSeq (2 * n) * (Real.sqrt (2 * (2 * n)) * ((2 * n) / Real.exp 1) ^ (2 * n)) := by
    have := factorial_eq_stirlingSeq_mul h2n
    push_cast at this ⊢
    convert this using 4
  -- key identity centralBinom * (n!)^2 = (2n)!
  have hid := centralBinom_factorial_identity n
  -- positivity facts
  have hsn : (0 : ℝ) < stirlingSeq n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact stirlingSeq'_pos m
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsqrt2n : Real.sqrt (2 * (2 * n)) = 2 * Real.sqrt n := by
    rw [show (2 * (2 * n) : ℝ) = 2 ^ 2 * n by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hsqrtn_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- (n)! cast nonzero
  have hfn_ne : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  -- Rewrite centralBinom = (2n)! / (n! * n!)
  have hcb : (Nat.centralBinom n : ℝ) = (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    rw [show ((Nat.factorial n : ℝ) ^ 2) = (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) by ring]
    rw [← mul_assoc]; exact hid
  rw [hcb, hfn, hf2n, hsqrt2n]
  -- (2n/e)^{2n} = 4^n · ((n/e)^n)^2
  have hpow : ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) = (4 : ℝ) ^ n * ((n / Real.exp 1) ^ n) ^ 2 := by
    rw [show ((2 * n : ℝ) / Real.exp 1) = 2 * (n / Real.exp 1) by ring, mul_pow]
    have hA : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
      rw [pow_mul]; norm_num
    have hB : ((n : ℝ) / Real.exp 1) ^ (2 * n) = ((n / Real.exp 1) ^ n) ^ 2 := by
      rw [mul_comm, pow_mul]
    rw [hA, hB]
  rw [hpow]
  -- abbreviations
  set S2 := stirlingSeq (2 * n) with hS2
  set Sn := stirlingSeq n with hSn
  set q := ((n : ℝ) / Real.exp 1) ^ n with hq
  have hq_ne : q ≠ 0 := by rw [hq]; positivity
  have hSn_ne : Sn ≠ 0 := hsn.ne'
  have h4_ne : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hsqn2 : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have hsqnn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := Real.mul_self_sqrt (by positivity)
  -- LHS denominator: (Sn * (√(2n) * q))^2 = Sn^2 * (2n) * q^2
  have e1 : (Sn * (Real.sqrt (2 * (n:ℝ)) * q)) ^ 2 = Sn ^ 2 * (2 * n) * q ^ 2 := by
    rw [mul_pow, mul_pow, hsqn2]; ring
  -- Clear all denominators and reduce.  Both sides multiplied through.
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity), e1]
  -- Goal now polynomial in S2,Sn,q,√n,n; replace √n*√n by n then ring.
  have hn_ne : (n : ℝ) ≠ 0 := hnpos.ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hnpos)]

/-- **`centralBinom_div_four_pow_tendsto`.**  `centralBinom n / 4^n → 0`.

`centralBinom n / 4^n = (stirlingSeq (2n)/(stirlingSeq n)^2)·(1/√n)`; the first
factor tends to `√π/π` (Stirling) and `1/√n → 0`, so the product → 0. -/
theorem centralBinom_div_four_pow_tendsto :
    Tendsto (fun n : ℕ => (Nat.centralBinom n : ℝ) / 4 ^ n) atTop (𝓝 0) := by
  -- stirlingSeq (2n) → √π
  have h2 : Tendsto (fun n : ℕ => stirlingSeq (2 * n)) atTop (𝓝 (Real.sqrt π)) := by
    have hmul : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num)) Filter.tendsto_id
    exact tendsto_stirlingSeq_sqrt_pi.comp hmul
  -- (stirlingSeq n)^2 → π
  have hsq : Tendsto (fun n : ℕ => (stirlingSeq n) ^ 2) atTop (𝓝 π) := by
    have := (tendsto_stirlingSeq_sqrt_pi.pow 2)
    rwa [Real.sq_sqrt Real.pi_pos.le] at this
  -- ratio → √π / π
  have hπ_ne : π ≠ 0 := Real.pi_ne_zero
  have hratio : Tendsto (fun n : ℕ => stirlingSeq (2 * n) / (stirlingSeq n) ^ 2) atTop
      (𝓝 (Real.sqrt π / π)) := h2.div hsq hπ_ne
  -- 1/√n → 0
  have hinv : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
    have hsqrt_top : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa using hsqrt_top.inv_tendsto_atTop
  -- product → (√π/π)·0 = 0
  have hprod : Tendsto
      (fun n : ℕ => stirlingSeq (2 * n) / (stirlingSeq n) ^ 2 * (1 / Real.sqrt n)) atTop
      (𝓝 (Real.sqrt π / π * 0)) := hratio.mul hinv
  rw [mul_zero] at hprod
  -- agree with centralBinom/4^n eventually (n ≥ 1)
  apply hprod.congr'
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{n | 1 ≤ n}, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩, ?_⟩
  intro n hn
  have hn1 : n ≠ 0 := by have : 1 ≤ n := hn; omega
  -- centralBinom/4^n = (ratio)·(1/√n) from the √n-cleared identity (√n > 0)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn1)
  show stirlingSeq (2 * n) / (stirlingSeq n) ^ 2 * (1 / Real.sqrt n)
      = (Nat.centralBinom n : ℝ) / 4 ^ n
  rw [← centralBinom_div_four_pow_mul_sqrt hn1]
  field_simp

/-- The central coefficient is dominated by a slightly larger central binomial:
`C(k, k/2) ≤ centralBinom (k/2 + 1)`.  Monotonicity of `choose` in the top
argument (`Nat.choose_le_choose`, since `k ≤ 2(k/2)+2`) lands us in
`choose (2(k/2)+2) (k/2)`, which is `≤` its middle `choose (2(k/2)+2) (k/2+1) =
centralBinom (k/2+1)` (`Nat.choose_le_middle`). -/
theorem choose_half_le_centralBinom (k : ℕ) :
    k.choose (k / 2) ≤ Nat.centralBinom (k / 2 + 1) := by
  set m := k / 2 with hm
  have hkle : k ≤ 2 * m + 2 := by omega
  -- C(k, m) ≤ C(2m+2, m)
  have h1 : k.choose m ≤ (2 * m + 2).choose m := Nat.choose_le_choose m hkle
  -- C(2m+2, m) ≤ C(2m+2, (2m+2)/2) = C(2m+2, m+1)
  have h2 : (2 * m + 2).choose m ≤ (2 * m + 2).choose ((2 * m + 2) / 2) :=
    Nat.choose_le_middle m (2 * m + 2)
  have hmid : (2 * m + 2) / 2 = m + 1 := by omega
  have h2n : (2 * m + 2) = 2 * (m + 1) := by ring
  rw [hmid] at h2
  -- C(2m+2, m+1) = centralBinom (m+1)
  have h3 : (2 * m + 2).choose (m + 1) = Nat.centralBinom (m + 1) := by
    rw [Nat.centralBinom, h2n]
  calc k.choose m ≤ (2 * m + 2).choose m := h1
    _ ≤ (2 * m + 2).choose (m + 1) := h2
    _ = Nat.centralBinom (m + 1) := h3

/-- **`central_decay` (item 3).**  `C(k, k/2) / 2^k → 0`.

Squeeze: `0 ≤ C(k,k/2)/2^k ≤ 4 · (centralBinom (k/2+1) / 4^(k/2+1))`, using
`C(k,k/2) ≤ centralBinom (k/2+1)` and `4^(k/2) ≤ 2^k`; the right side tends to
`4·0 = 0` because `centralBinom·/4^· → 0` and `k/2+1 → atTop`. -/
theorem central_decay :
    Tendsto (fun k : ℕ => (k.choose (k / 2) : ℝ) / 2 ^ k) atTop (𝓝 0) := by
  -- upper bound g k = 4 * (centralBinom (k/2+1) / 4^(k/2+1))
  have hg : Tendsto
      (fun k : ℕ => 4 * ((Nat.centralBinom (k / 2 + 1) : ℝ) / 4 ^ (k / 2 + 1))) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun k : ℕ => k / 2 + 1) atTop atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b; exact ⟨2 * b, fun n hn => by omega⟩
    have h0 : Tendsto
        (fun k : ℕ => (Nat.centralBinom (k / 2 + 1) : ℝ) / 4 ^ (k / 2 + 1)) atTop (𝓝 0) :=
      centralBinom_div_four_pow_tendsto.comp hcomp
    have := h0.const_mul (4 : ℝ)
    simpa using this
  apply squeeze_zero (fun k => by positivity) _ hg
  intro k
  have h2pos : (0 : ℝ) < 2 ^ k := by positivity
  -- C(k,k/2) ≤ centralBinom (k/2+1)  (nat, cast)
  have hnat : (k.choose (k / 2) : ℝ) ≤ (Nat.centralBinom (k / 2 + 1) : ℝ) := by
    exact_mod_cast choose_half_le_centralBinom k
  -- 4^(k/2) ≤ 2^k  (nat, cast):  4^(k/2) = 2^(2*(k/2)) ≤ 2^k
  have hpow_le : (4 : ℝ) ^ (k / 2) ≤ 2 ^ k := by
    have : (4 : ℝ) ^ (k / 2) = 2 ^ (2 * (k / 2)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [this]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h4pos : (0 : ℝ) < 4 ^ (k / 2) := by positivity
  -- C(k,k/2)/2^k ≤ centralBinom(k/2+1)/4^(k/2) = 4·centralBinom(k/2+1)/4^(k/2+1)
  rw [div_le_iff₀ h2pos]
  have hrhs : (4 : ℝ) * ((Nat.centralBinom (k / 2 + 1) : ℝ) / 4 ^ (k / 2 + 1)) * 2 ^ k
      = (Nat.centralBinom (k / 2 + 1) : ℝ) / 4 ^ (k / 2) * 2 ^ k := by
    rw [pow_succ]
    field_simp
  rw [hrhs]
  -- now: C(k,k/2) ≤ centralBinom(k/2+1)/4^(k/2) · 2^k
  rw [div_mul_eq_mul_div, le_div_iff₀ h4pos]
  exact mul_le_mul hnat hpow_le (by positivity) (by positivity)

/-! ## §4  HEADLINE — unconditional tail decay at `t = minOdd k` -/

/-- `k < 2·minOdd k + 1` for **every** `k` (including `k = 0, 1`).  If `k ≥ 2a+1`
with `a = minOdd k`, then `2^k ≥ 2^(2a+1) = 2·4^a > 3^a ≥ 2^k`, a contradiction.
(For `k ≥ 2` this is the strict `minOdd_gt_half`; the lemma covers all `k`.) -/
theorem minOdd_lt_half_add_one (k : ℕ) : k < 2 * minOdd k + 1 := by
  set a := minOdd k with ha
  have hspec : 2 ^ k ≤ 3 ^ a := two_pow_le_three_pow_minOdd k
  by_contra hle
  rw [Nat.not_lt] at hle          -- 2a + 1 ≤ k
  -- 2^(2a+1) ≤ 2^k
  have h1 : 2 ^ (2 * a + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hle
  -- 3^a < 2^(2a+1):  2^(2a+1) = 2·4^a and 3^a < 4^a ≤ 2·4^a (a≥1), or a=0: 3^0=1<2.
  have h2 : 3 ^ a < 2 ^ (2 * a + 1) := by
    have hpow : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
      rw [pow_succ, mul_comm, pow_mul]; norm_num
    rw [hpow]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0]; norm_num
    · have h34 : 3 ^ a < 4 ^ a := Nat.pow_lt_pow_left (by norm_num) (by omega)
      have h4 : 4 ^ a ≤ 2 * 4 ^ a := by omega
      omega
  omega

/-- **`upperTail_minOdd_decay` (HEADLINE).**  Unconditionally,
`upperTail k (minOdd k) / 2^k → 0`.

Assembles the three ingredients with `squeeze_zero`:
* `binom_tail_geometric` (`k < 2·minOdd k + 1` from `minOdd_lt_half_add_one`):
  `upperTail k (minOdd k) ≤ C(k, minOdd k)·(1−r)⁻¹`;
* `geom_const_le_three`: `(1−r)⁻¹ ≤ 3` — a constant, no hypothesis;
* `choose_minOdd_le_central` + `central_decay`: `C(k, minOdd k) ≤ C(k, k/2)` and
  `C(k, k/2)/2^k → 0`.
Hence `0 ≤ upperTail/2^k ≤ 3·C(k,k/2)/2^k → 0`.

This removes the `hcoef`/`hK` hypotheses of `CollatzBinomialTail.binom_tail_decay`
at the Collatz threshold `t k = minOdd k`: the only remaining input to the
Everett–Terras capstone is the descent dichotomy (`bad_implies_odd_steps_ge`). -/
theorem upperTail_minOdd_decay :
    Tendsto (fun k : ℕ => (upperTail k (minOdd k) : ℝ) / 2 ^ k) atTop (𝓝 0) := by
  -- upper bound g k = 3 * (C(k,k/2)/2^k) → 0
  have hg : Tendsto (fun k : ℕ => 3 * ((k.choose (k / 2) : ℝ) / 2 ^ k)) atTop (𝓝 0) := by
    have := central_decay.const_mul (3 : ℝ)
    simpa using this
  apply squeeze_zero (fun k => by positivity) _ hg
  intro k
  have h2pos : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ h2pos]
  -- handle k = 0 trivially; else use the geometric machinery.
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    -- upperTail 0 (minOdd 0): minOdd 0 = 0, upperTail 0 0 = ∑_{Icc 0 0} C(0,i) = 1 ≤ 3·1·1
    have hm0 : minOdd 0 = 0 := by decide
    simp only [hm0, upperTail, CollatzBinomialTail.upperTail]
    norm_num
  · -- k ≥ 1
    have hk1 : 1 ≤ k := hk0
    have hgeom : (upperTail k (minOdd k) : ℝ)
        ≤ (k.choose (minOdd k) : ℝ)
          * (1 - ((k - minOdd k : ℕ) : ℝ) / ((minOdd k + 1 : ℕ) : ℝ))⁻¹ :=
      binom_tail_geometric (minOdd_lt_half_add_one k)
    have hconst : (1 - ((k - minOdd k : ℕ) : ℝ) / ((minOdd k + 1 : ℕ) : ℝ))⁻¹ ≤ 3 :=
      geom_const_le_three k hk1
    have hchoose : (k.choose (minOdd k) : ℝ) ≤ (k.choose (k / 2) : ℝ) := by
      exact_mod_cast choose_minOdd_le_central k
    -- chain
    calc (upperTail k (minOdd k) : ℝ)
        ≤ (k.choose (minOdd k) : ℝ)
            * (1 - ((k - minOdd k : ℕ) : ℝ) / ((minOdd k + 1 : ℕ) : ℝ))⁻¹ := hgeom
      _ ≤ (k.choose (k / 2) : ℝ) * 3 := by
          apply mul_le_mul hchoose hconst _ (by positivity)
          -- inverse is nonneg
          have hrlt : ((k - minOdd k : ℕ) : ℝ) / ((minOdd k + 1 : ℕ) : ℝ) < 1 := by
            rw [div_lt_one (by exact_mod_cast Nat.succ_pos (minOdd k))]
            have : k - minOdd k < minOdd k + 1 := by
              have := minOdd_lt_half_add_one k; omega
            exact_mod_cast this
          exact inv_nonneg.mpr (by linarith)
      _ = 3 * ((k.choose (k / 2) : ℝ) / 2 ^ k) * 2 ^ k := by
          field_simp

end CollatzTailDecayUncond

