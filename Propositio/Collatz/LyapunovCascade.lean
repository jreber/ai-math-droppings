import Propositio.Collatz.Basic

/-!
# V-cascade Lyapunov descent family (Collatz)

Port of the project's novel V-cascade Lyapunov-function descent results from
LaTTe to Lean 4 + mathlib (Bucket 3).

The cascade-aware Lyapunov candidate is
  `V_cascade(n) := n * 2 ^ (v₂(n+1) - 1)`,
weighted by the "spine level" `v₂(n+1)`.  The headline results show
deterministic descent (`V_cascade(cc n) < V_cascade n`) on the spine
(`v₂(n+1) ≥ 2`) and a descent/ascent *dichotomy* parameterised by the
2-adic valuation triple `(α, β, γ) = (v₂(n+1), v₂(3n+1), v₂(cc n + 1))`:
descent ⟺ `α + β − γ ≥ 2`.

We reuse `TerrasDensity.cc`, `TerrasDensity.Odd`, `cascade_step_mult`, etc.

## House-style note on idiomatic adjustments

The LaTTe development works over `Int` with explicit `(elem _ nat)` membership
hypotheses and a hand-rolled `collatz-odd-compressed`.  Here we work over `Nat`
directly, reusing `TerrasDensity.cc` / `TerrasDensity.Odd`.  Consequently the
LaTTe "membership / naturality" helpers (`lc-one-nat`, `odd-nat-not-zero`,
`two-n-minus-cc-nat`, …) collapse to `Nat`-level facts that `omega` discharges
once the load-bearing multiplicative identity (`2^β · cc n = 3n+1`) is in hand.
Each ported theorem records its `LaTTe sibling`.

LaTTe sibling files:
  `src/ai_math/collatz/lyapunov_cascade.clj`
  `src/ai_math/collatz/lyapunov_cascade_L0.clj`
  `src/ai_math/collatz/lyapunov_cascade_generic.clj`
-/

namespace LyapunovCascade

open TerrasDensity

/-- `V_cascade(n) := n * 2 ^ (v₂(n+1) - 1)`.

The cascade-aware Lyapunov candidate, weighted by spine level.

LaTTe sibling: `lyapunov_cascade.clj :: V-cascade`. -/
def Vcascade (n : Nat) : Nat := n * 2 ^ (padicValNat 2 (n + 1) - 1)

/-! ## Shared factorization bridge

The single load-bearing fact behind the whole family: `2^(v₂(3n+1)) · cc n = 3n+1`.
Everything else is `Nat` arithmetic. -/

/-- **Factorization bridge — REAL.**
`2 ^ v₂(3n+1) * cc n = 3n + 1`.  Immediate from the definition of `cc` and
`pow_padicValNat_dvd`.  This subsumes LaTTe's `two-cc-eq` (β = 1) and
`l0-four-cc-eq-3n-plus-1` (β = 2).

LaTTe siblings: `lyapunov_cascade.clj :: two-cc-eq`,
`lyapunov_cascade_L0.clj :: l0-four-cc-eq-3n-plus-1`. -/
theorem pow_v2_mul_cc (n : Nat) :
    2 ^ padicValNat 2 (3 * n + 1) * cc n = 3 * n + 1 := by
  unfold cc
  exact Nat.mul_div_cancel' (pow_padicValNat_dvd)

/-! ## File 1: `lyapunov_cascade` — spine case (v₂(n+1) ≥ 2)

The 9 REAL theorems from `lyapunov-cascade-theorems-real`.  The LaTTe helpers
that exist purely to track `Int`-`nat` membership are noted as folded into
`omega`. -/

/-- LaTTe sibling: `lyapunov_cascade.clj :: lc-one-nat` (`one ∈ nat`).
Trivial over `Nat`. -/
theorem lc_one_nat : (1 : Nat) = 1 := rfl

/-- LaTTe sibling: `lyapunov_cascade.clj :: odd-nat-not-zero`.
For odd `n`, `n ≠ 0`. -/
theorem odd_nat_not_zero {n : Nat} (h : TerrasDensity.Odd n) : n ≠ 0 := by
  obtain ⟨k, hk⟩ := h; omega

/-- LaTTe sibling: `lyapunov_cascade.clj :: odd-nat-minus-one-nat`.
For odd `n`, `n - 1` is a genuine `Nat` (`n ≥ 1`). -/
theorem odd_nat_minus_one_nat {n : Nat} (h : TerrasDensity.Odd n) : 1 ≤ n := by
  obtain ⟨k, hk⟩ := h; omega

/-- LaTTe sibling: `lyapunov_cascade.clj :: two-times-two-eq-four`. -/
theorem two_times_two_eq_four : (2 : Nat) * 2 = 4 := rfl

/-- LaTTe sibling: `lyapunov_cascade.clj :: n-not-one-from-v2-ge-2`.
If `v₂(n+1) = J + 2` then `n ≠ 1` (else `v₂(2) = 1 ≠ J+2`). -/
theorem n_not_one_from_v2_ge_2 {n J : Nat}
    (hv2 : padicValNat 2 (n + 1) = J + 2) : n ≠ 1 := by
  intro hn
  subst hn
  -- v₂(2) = 1, contradicting J + 2.
  have : padicValNat 2 (1 + 1) = 1 := by norm_num [padicValNat.self]
  omega

/-- **`2 * cc n = 3n + 1`** for the spine case `4 ∣ n+1` (`v₂(n+1) ≥ 2`).

LaTTe sibling: `lyapunov_cascade.clj :: two-cc-eq`. -/
theorem two_cc_eq {n : Nat} (hodd : TerrasDensity.Odd n) (h4 : 4 ∣ n + 1) :
    2 * cc n = 3 * n + 1 := by
  have h := cascade_step_mult hodd h4
  omega

/-- **`2 * (2n - cc n) = n - 1`** in the spine case.

LaTTe sibling: `lyapunov_cascade.clj :: two-times-two-n-minus-cc`. -/
theorem two_times_two_n_minus_cc {n : Nat} (hodd : TerrasDensity.Odd n) (h4 : 4 ∣ n + 1) :
    2 * (2 * n - cc n) = n - 1 := by
  have h := two_cc_eq hodd h4
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **`2n - cc n ≥ 0` (i.e. `cc n ≤ 2n`)** in the spine case.
Over `Nat` this is `cc n ≤ 2 * n`.

LaTTe sibling: `lyapunov_cascade.clj :: two-n-minus-cc-nat`. -/
theorem two_n_minus_cc_nat {n : Nat} (hodd : TerrasDensity.Odd n) (h4 : 4 ∣ n + 1) :
    cc n ≤ 2 * n := by
  have h := two_cc_eq hodd h4
  omega

/-- **MAIN — `V-cascade-descent-spine-positive`.**

For odd `n` with `v₂(n+1) = J + 2` (the spine case),
`cc n * 2 ^ J < n * 2 ^ (J + 1)`, i.e. `V_cascade(cc n) < V_cascade n`.

LaTTe sibling: `lyapunov_cascade.clj :: V-cascade-descent-spine-positive`. -/
theorem V_cascade_descent_spine_positive {n J : Nat} (hodd : TerrasDensity.Odd n)
    (hv2 : padicValNat 2 (n + 1) = J + 2) :
    cc n * 2 ^ J < n * 2 ^ (J + 1) := by
  -- 4 ∣ n + 1 from v₂(n+1) ≥ 2.
  have h4 : 4 ∣ n + 1 := by
    have h_ge : 2 ≤ padicValNat 2 (n + 1) := by omega
    have hn1_ne : n + 1 ≠ 0 := by omega
    have := (padicValNat_dvd_iff_le hn1_ne).mpr h_ge
    simpa [show (2 : Nat) ^ 2 = 4 from rfl] using this
  have hcc : 2 * cc n = 3 * n + 1 := two_cc_eq hodd h4
  have hne : n ≠ 1 := n_not_one_from_v2_ge_2 hv2
  obtain ⟨k, hk⟩ := hodd
  -- n is odd and n ≠ 1, so n ≥ 3; hence cc n < 2 n strictly.
  -- 2^(J+1) = 2 * 2^J.
  have hpow : (2 : Nat) ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
  have hPpos : 0 < (2 : Nat) ^ J := Nat.two_pow_pos J
  -- From 2 cc = 3n+1 and n ≥ 3 (k ≥ 1): cc < 2n.
  have hcc_lt : cc n < 2 * n := by omega
  calc cc n * 2 ^ J < (2 * n) * 2 ^ J := by
        exact (Nat.mul_lt_mul_right hPpos).mpr hcc_lt
    _ = n * 2 ^ (J + 1) := by rw [hpow]; ring

/-! ## File 2: `lyapunov_cascade_L0` — spine level L = 0 (v₂(n+1) = 1)

The 9 REAL theorems from `lyapunov-cascade-L0-theorems-real`.  Hypotheses are
v₂-conditioned (`v₂(n+1)=1`, `v₂(3n+1)=2`, …) to mirror the LaTTe design that
sidesteps mod-16 arithmetic. -/

/-- LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-succ-succ-zero-nat`. Trivial. -/
theorem l0_succ_succ_zero_nat : (0 : Nat) + 2 = 2 := rfl

/-- LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-even-of-v2-succ`.
If `v₂(X) = K + 1` (with `X ≠ 0`) then `X` is even. -/
theorem l0_even_of_v2_succ {X K : Nat} (hX : X ≠ 0)
    (hv2 : padicValNat 2 X = K + 1) : 2 ∣ X := by
  have h_ge : 1 ≤ padicValNat 2 X := by omega
  have := (padicValNat_dvd_iff_le hX).mpr h_ge
  simpa using this

/-- LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-X-eq-four-times-odd-part`.
If `v₂(X) = 2` then `X = 4 * (X / 4)` and `X / 4` is odd, i.e. `X` is exactly
`4 · odd-part(X)`.  Over `Nat` the "odd-part" is `X / 2^(v₂ X) = X / 4`. -/
theorem l0_X_eq_four_times_odd_part {X : Nat} (_hX : X ≠ 0)
    (hv2 : padicValNat 2 X = 2) :
    X = 4 * (X / 2 ^ padicValNat 2 X) := by
  have hdvd : 2 ^ padicValNat 2 X ∣ X := pow_padicValNat_dvd
  rw [hv2] at hdvd ⊢
  have h4 : (2 : Nat) ^ 2 = 4 := rfl
  rw [h4] at hdvd ⊢
  exact (Nat.mul_div_cancel' hdvd).symm

/-- **`4 * cc n = 3n + 1`** when `v₂(3n+1) = 2`.

LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-four-cc-eq-3n-plus-1`. -/
theorem l0_four_cc_eq_3n_plus_1 {n : Nat}
    (hv2 : padicValNat 2 (3 * n + 1) = 2) :
    4 * cc n = 3 * n + 1 := by
  have h := pow_v2_mul_cc n
  rw [hv2] at h
  simpa [show (2 : Nat) ^ 2 = 4 from rfl] using h

/-- **`4 * (n - cc n) = n - 1`** when `v₂(3n+1) = 2` (and `n` odd).

LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-four-n-minus-cc-eq-n-minus-1`. -/
theorem l0_four_n_minus_cc_eq_n_minus_1 {n : Nat} (hodd : TerrasDensity.Odd n)
    (hv2 : padicValNat 2 (3 * n + 1) = 2) :
    4 * (n - cc n) = n - 1 := by
  have h := l0_four_cc_eq_3n_plus_1 hv2
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **`cc n ≤ n`** when `v₂(3n+1) = 2` (and `n` odd).
Over `Nat`, the LaTTe `(n - cc n) ∈ nat`.

LaTTe sibling: `lyapunov_cascade_L0.clj :: l0-n-minus-cc-nat`. -/
theorem l0_n_minus_cc_nat {n : Nat} (hodd : TerrasDensity.Odd n)
    (hv2 : padicValNat 2 (3 * n + 1) = 2) :
    cc n ≤ n := by
  have h := l0_four_cc_eq_3n_plus_1 hv2
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Theorem A — `V-cascade-descent-L0`.**

For odd `n` with `v₂(n+1) = 1`, `v₂(3n+1) = 2`, `v₂(cc n + 1) = 1`, and `n > 1`:
`cc n * 2^0 < n * 2^0`, i.e. `cc n < n`.

LaTTe sibling: `lyapunov_cascade_L0.clj :: V-cascade-descent-L0`. -/
theorem V_cascade_descent_L0 {n : Nat} (_hodd : TerrasDensity.Odd n)
    (_hv2n1 : padicValNat 2 (n + 1) = 1)
    (hv2_3n1 : padicValNat 2 (3 * n + 1) = 2)
    (_hv2cc1 : padicValNat 2 (cc n + 1) = 1)
    (hn_gt_1 : 1 < n) :
    cc n * 2 ^ 0 < n * 2 ^ 0 := by
  simp only [pow_zero, Nat.mul_one]
  -- 4 cc = 3n+1 and n > 1 ⟹ cc < n.
  have h := l0_four_cc_eq_3n_plus_1 hv2_3n1
  omega

/-- **Theorem B — `V-cascade-ascent-L0-Lnew-pos`.**

For odd `n` with `v₂(n+1) = 1`, `v₂(3n+1) = 2`, `v₂(cc n + 1) = J + 2` (≥ 2):
`n * 2^0 < cc n * 2^(J+1)`, i.e. an *ascent* of `V_cascade`.

LaTTe sibling: `lyapunov_cascade_L0.clj :: V-cascade-ascent-L0-Lnew-pos`. -/
theorem V_cascade_ascent_L0_Lnew_pos {n J : Nat} (hodd : TerrasDensity.Odd n)
    (_hv2n1 : padicValNat 2 (n + 1) = 1)
    (hv2_3n1 : padicValNat 2 (3 * n + 1) = 2)
    (_hv2cc1 : padicValNat 2 (cc n + 1) = J + 2) :
    n * 2 ^ 0 < cc n * 2 ^ (J + 1) := by
  simp only [pow_zero, Nat.mul_one]
  have h := l0_four_cc_eq_3n_plus_1 hv2_3n1
  obtain ⟨k, hk⟩ := hodd
  -- 4 cc = 3n+1 ⟹ cc*2 > n  (since 2 cc = (3n+1)/2 > n for n ≥ 1).
  -- Then cc * 2^(J+1) ≥ cc * 2 > n.
  have hPpos : 0 < (2 : Nat) ^ (J + 1) := Nat.two_pow_pos (J + 1)
  have hge : (2 : Nat) ≤ 2 ^ (J + 1) := by
    calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- n < cc * 2  from 4 cc = 3n+1 and n odd (k arbitrary ≥ 0, n = 2k+1 ≥ 1).
  have hccpos : 0 < cc n := by omega
  have h1 : n < cc n * 2 := by omega
  calc n < cc n * 2 := h1
    _ ≤ cc n * 2 ^ (J + 1) := Nat.mul_le_mul_left (cc n) hge

/-! ## File 3: `lyapunov_cascade_generic` — the dichotomy parameterised by (α,β,γ)

The 5 REAL theorems from `lyapunov-cascade-generic-theorems-real`: the descent
half of the dichotomy plus its four power-of-two helpers.  (The ascent half is
a NO-PROOF stub in LaTTe and is *not* in the deftest, so it is not ported.) -/

/-- LaTTe sibling: `lyapunov_cascade_generic.clj :: pow-two-add`. -/
theorem pow_two_add (a b : Nat) : (2 : Nat) ^ (a + b) = 2 ^ a * 2 ^ b :=
  pow_add 2 a b

/-- LaTTe sibling: `lyapunov_cascade_generic.clj :: pow-two-halving`.
`2^β * X` being a `Nat` forces `X` to be a `Nat`.  Over `Nat` the LaTTe content
is the cancellation `2^β * X = 2^β * Y → X = Y`; we state the divisibility form
`2^β ∣ 2^β * X` reduced, i.e. the round-trip `(2^β * X) / 2^β = X`. -/
theorem pow_two_halving (β X : Nat) : (2 ^ β * X) / 2 ^ β = X :=
  Nat.mul_div_cancel_left X (Nat.two_pow_pos β)

/-- LaTTe sibling: `lyapunov_cascade_generic.clj :: pow-two-ssK-ge-four`.
`4 ≤ 2 ^ (K + 2)`. -/
theorem pow_two_ssK_ge_four (K : Nat) : 4 ≤ (2 : Nat) ^ (K + 2) := by
  calc (4 : Nat) = 2 ^ 2 := rfl
    _ ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- LaTTe sibling: `lyapunov_cascade_generic.clj :: pow-two-scaled-factorization`.
If `2^β * cc = 3n+1` then `2^A * (3n+1) = 2^(A+β) * cc`. -/
theorem pow_two_scaled_factorization {A β cc n : Nat}
    (hfact : 2 ^ β * cc = 3 * n + 1) :
    2 ^ A * (3 * n + 1) = 2 ^ (A + β) * cc := by
  rw [← hfact, pow_two_add]; ring

/-- **MAIN — `V-cascade-descent-generic`.**

The descent half of the V-cascade dichotomy, parameterised by the 2-adic
valuation triple via `α = A + 1`, `γ = C + 1`, `β`, with descent condition
`A + β = C + (K + 2)` (i.e. `α + β − γ = K + 2 ≥ 2`).  Given the factorization
`2^β * cc n = 3n + 1` and `n > 1` odd:
  `cc n * 2 ^ C < n * 2 ^ A`,  i.e. `V_cascade(cc n) < V_cascade n`.

Subsumes the two specific descent theorems (spine: `A=J+1,β=1,C=J,K=0`;
L0: `A=0,β=2,C=0,K=0`).

LaTTe sibling: `lyapunov_cascade_generic.clj :: V-cascade-descent-generic`. -/
theorem V_cascade_descent_generic {n A β C K : Nat} (_hodd : TerrasDensity.Odd n)
    (hn_gt_1 : 1 < n)
    (hfact : 2 ^ β * cc n = 3 * n + 1)
    (hdesc : A + β = C + (K + 2)) :
    cc n * 2 ^ C < n * 2 ^ A := by
  -- Scale the goal by the strictly-positive 2^β and reduce to an identity.
  have hβpos : 0 < (2 : Nat) ^ β := Nat.two_pow_pos β
  refine (Nat.mul_lt_mul_left hβpos).mp ?_
  -- 2^β * (cc * 2^C) = (2^β * cc) * 2^C = (3n+1) * 2^C
  have hL : 2 ^ β * (cc n * 2 ^ C) = (3 * n + 1) * 2 ^ C := by
    rw [← hfact]; ring
  -- 2^β * (n * 2^A) = n * 2^(A+β) = n * 2^(C+K+2) = n * 2^C * 2^(K+2)
  have hR : 2 ^ β * (n * 2 ^ A) = n * 2 ^ (K + 2) * 2 ^ C := by
    have : β + A = C + (K + 2) := by omega
    calc 2 ^ β * (n * 2 ^ A)
        = n * (2 ^ β * 2 ^ A) := by ring
      _ = n * 2 ^ (β + A) := by rw [pow_add]
      _ = n * 2 ^ (C + (K + 2)) := by rw [this]
      _ = n * 2 ^ (K + 2) * 2 ^ C := by rw [pow_add]; ring
  rw [hL, hR]
  -- Now: (3n+1) * 2^C < n * 2^(K+2) * 2^C.  Cancel 2^C; reduce to 3n+1 < n * 2^(K+2).
  have hCpos : 0 < (2 : Nat) ^ C := Nat.two_pow_pos C
  rw [mul_comm (3 * n + 1) (2 ^ C), mul_comm (n * 2 ^ (K + 2)) (2 ^ C)]
  refine (Nat.mul_lt_mul_left hCpos).mpr ?_
  -- 3n+1 < n * 2^(K+2) since 2^(K+2) ≥ 4 and n ≥ 2.
  have hpow4 : 4 ≤ (2 : Nat) ^ (K + 2) := pow_two_ssK_ge_four K
  have : 4 * n ≤ n * 2 ^ (K + 2) := by
    rw [mul_comm 4 n]; exact Nat.mul_le_mul_left n hpow4
  omega

end LyapunovCascade
