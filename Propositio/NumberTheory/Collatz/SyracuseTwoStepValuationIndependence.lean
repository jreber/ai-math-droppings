import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Count
import Propositio.NumberTheory.Collatz.SyracuseValuationDistribution
import Propositio.NumberTheory.Collatz.SyracuseThreeAdicBias

/-!
# Two-step Syracuse valuation independence — Lean 4 (NEW)

This file extends the one-step geometric law proved in `SyracuseValuationDistribution.lean`
(`v N := padicValNat 2 (3N+1)` satisfies `P(v=j) = 2^{-j}`, over the odd population) to
**two consecutive Syracuse steps**. Writing `Syr N` for the (odd) next iterate
(`SyracuseThreeAdicBias.Syr`), we show the joint event `{v N = i ∧ v (Syr N) = j}` has
*exactly* the density `2^{-i}·2^{-j}` among odd `N < 2^K` — i.e. the 2-adic valuation at
one Syracuse step carries **no correlation** with the valuation at the next step. This is
the exact-density backbone of the standard negative-drift heuristic underlying the whole
Collatz density program (Tao 2019/2022): the valuations behave as i.i.d. Geometric(1/2)
random variables.

## Strategy

The one-step law shows `v N = i` picks out a single residue class of `N` modulo `2^{i+1}`
(`SyracuseValuationDistribution.exists_residue`). Within that residue class, writing
`N = 2^{i+1}·m + N₀`, we show algebraically that `Syr N = q₀ + 6m` for a FIXED odd `q₀`
(depending only on `i`, not on `m`) — i.e. `Syr N` is an *affine* function of the free
parameter `m`, with slope `6 = 2·3` (one factor of 2, matching that `Syr N` is always odd).
Consequently `v (Syr N) = j` becomes (after peeling off that one guaranteed factor of `2`) a
linear valuation condition `padicValNat 2 (9m + r₀) = j - 1` in `m`, which by the *same*
unit-coefficient argument as the one-step law (generalized here to an arbitrary odd
coefficient: `exists_residue_linear`) picks out a single residue class of `m` modulo `2^j`.

Combining "`N` fixed mod `2^{i+1}`" with "`m = N/2^{i+1}` fixed mod `2^j`" is a
**digit-decomposition** fact (`digit_decomp`, base-`2` positional independence — NOT CRT,
since the two moduli share the prime 2): it collapses to a single congruence class of `N`
modulo `2^{i+1}·2^j = 2^{i+1+j}`. Counting residue classes over `[0, 2^K)` then gives the
exact card `2^{K-i-1-j}`, i.e. density `2^{-(i+1+j)}` among ALL `N < 2^K` — which, relative
to the `2^{K-1}` odd naturals below `2^K`, is exactly `2^{-i}·2^{-j}`
(`density_joint_valuation_eq_over_odds`, the HEADLINE).

## What is proved (all sorry-free, axiom-clean)

  * `exists_residue_linear`  — generalization of `SyracuseValuationDistribution.exists_residue`
    to an arbitrary odd coefficient and offset: `{N : padicValNat 2 (a·N+c) = t}` is a single
    residue class mod `2^{t+1}`, for `a` odd and `c ≠ 0`.
  * `digit_decomp`           — base-2 digit-decomposition: fixing `N mod e₁` and
    `(N/e₁) mod e₂` is the same as fixing `N mod (e₁·e₂)`.
  * `joint_residue`          — the joint event `{v N = i ∧ v (Syr N) = j}` is a single
    residue class of `N` modulo `2^{i+1+j}`                                    (PRIMARY).
  * `card_joint_valuation_eq`— exact count over `[0,2^K)`: `2^{K-i-1-j}`.
  * `count_odds_range`       — `[0,2^K)` contains exactly `2^{K-1}` odd naturals (`K ≥ 1`).
  * `density_joint_valuation_eq_over_odds` — the proportion, among ODD `N < 2^K`, of
    `N` with `v N = i` and `v (Syr N) = j`, is exactly `2^{-i}·2^{-j}`         (HEADLINE).
-/

namespace SyracuseTwoStepValuationIndependence

open Finset

/-- Elementary divisibility lemma (mirrors the private lemma of the same name in
`SyracuseValuationDistribution.lean`, restated here since that one is private):
for `p > 0`, an integer is divisible by `p` but not `2p` exactly when it is
`≡ p (mod 2p)`. -/
private theorem dvd_not_dvd_iff_modEq_gen {a p : ℕ} (hp : 0 < p) :
    (p ∣ a ∧ ¬ 2 * p ∣ a) ↔ a ≡ p [MOD 2 * p] := by
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt (show p < 2 * p by omega)]
  constructor
  · rintro ⟨⟨q, rfl⟩, h2⟩
    have hodd : ¬ 2 ∣ q := fun ⟨k, hk⟩ => h2 ⟨k, by rw [hk]; ring⟩
    obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    have hexp : p * (2 * k + 1) = p + 2 * p * k := by ring
    rw [hexp, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · intro h
    have hdm := Nat.div_add_mod a (2 * p)
    rw [h] at hdm
    set Q := a / (2 * p) with hQ
    refine ⟨⟨2 * Q + 1, ?_⟩, ?_⟩
    · rw [← hdm]; ring
    · rintro ⟨t, ht⟩
      have hcancel : 2 * Q + 1 = 2 * t := by
        apply Nat.eq_of_mul_eq_mul_left hp
        have e1 : p * (2 * Q + 1) = a := by rw [← hdm]; ring
        have e2 : p * (2 * t) = a := by rw [ht]; ring
        rw [e1, e2]
      omega

/-- **General linear residue lemma.** For odd `a` and any nonzero `c`, the set
`{N : padicValNat 2 (a·N+c) = t}` is a single residue class mod `2^{t+1}` — the same
unit-coefficient argument that isolates `SyracuseValuationDistribution.exists_residue`
(which is the special case `a=3, c=1`), generalized to an arbitrary odd coefficient. -/
theorem exists_residue_linear (a c t : ℕ) (ha : Odd a) (hc : c ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, padicValNat 2 (a * N + c) = t ↔ N ≡ N₀ [MOD 2 ^ (t + 1)] := by
  set m := 2 ^ (t + 1) with hm
  haveI : NeZero m := ⟨by rw [hm]; exact (pow_pos (by norm_num) (t + 1)).ne'⟩
  have hcop : Nat.Coprime a m := by
    rw [hm]; exact (Nat.coprime_two_right.mpr ha).pow_right (t + 1)
  have hcopgcd : Nat.gcd m a = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hunita : IsUnit (a : ZMod m) := by
    simpa using (ZMod.isUnit_iff_coprime a m).mpr hcop
  set s : ZMod m := (a : ZMod m)⁻¹ * ((2 : ZMod m) ^ t - (c : ZMod m)) with hs
  have hsol : (a : ZMod m) * s + (c : ZMod m) = (2 : ZMod m) ^ t := by
    rw [hs, ← mul_assoc, ZMod.mul_inv_of_unit (a : ZMod m) hunita]
    ring
  have hN0 : a * s.val + c ≡ 2 ^ t [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val s]
    exact hsol
  refine ⟨s.val, fun N => ?_⟩
  have ha0 : a * N + c ≠ 0 := by omega
  have hiff1 : padicValNat 2 (a * N + c) = t ↔
      (2 ^ t ∣ a * N + c ∧ ¬ 2 ^ (t + 1) ∣ a * N + c) := by
    rw [padicValNat_dvd_iff_le ha0, padicValNat_dvd_iff_le ha0]; omega
  have hiff2 : (2 ^ t ∣ a * N + c ∧ ¬ 2 ^ (t + 1) ∣ a * N + c) ↔
      a * N + c ≡ 2 ^ t [MOD m] := by
    have := dvd_not_dvd_iff_modEq_gen (a := a * N + c) (pow_pos (show 0 < 2 by norm_num) t)
    rw [show (2 : ℕ) * 2 ^ t = 2 ^ (t + 1) from by rw [pow_succ]; ring] at this
    rw [hm]; exact this
  rw [hiff1, hiff2]
  constructor
  · intro h
    have h2 : a * N + c ≡ a * s.val + c [MOD m] := h.trans hN0.symm
    have h3 : a * N ≡ a * s.val [MOD m] := Nat.ModEq.add_right_cancel' c h2
    exact Nat.ModEq.cancel_left_of_coprime hcopgcd h3
  · intro h
    exact ((h.mul_left a).add_right c).trans hN0

/-- **Digit-decomposition.** Fixing `N mod e₁` to `N₀` and `(N/e₁) mod e₂` to `m₀` is the
same as fixing `N mod (e₁·e₂)` to the single combined residue `e₁·m₀+N₀`. Base-2 positional
independence (used here with `e₁,e₂` both powers of 2) — distinct from CRT, which requires
coprime moduli; here the moduli instead *nest* (`e₁ ∣ e₁e₂`). -/
theorem digit_decomp (e1 e2 N0 m0 : ℕ) (he1 : 0 < e1) (he2 : 0 < e2) (hN0 : N0 < e1) (N : ℕ) :
    (N ≡ N0 [MOD e1] ∧ N / e1 ≡ m0 [MOD e2]) ↔ N ≡ e1 * m0 + N0 [MOD e1 * e2] := by
  constructor
  · rintro ⟨h1, h2⟩
    have hmod : N % e1 = N0 := Nat.mod_eq_of_modEq h1 hN0
    have hdec : e1 * (N / e1) + N0 = N := by
      have := Nat.div_add_mod N e1
      rw [hmod] at this; exact this
    have hstep : e1 * (N / e1) ≡ e1 * m0 [MOD e1 * e2] := h2.mul_left' e1
    have hstep2 : e1 * (N / e1) + N0 ≡ e1 * m0 + N0 [MOD e1 * e2] := hstep.add_right N0
    rwa [hdec] at hstep2
  · intro h
    have hdvd : e1 ∣ e1 * e2 := ⟨e2, rfl⟩
    have h1' : N ≡ e1 * m0 + N0 [MOD e1] := Nat.ModEq.of_dvd hdvd h
    have h1'' : e1 * m0 + N0 ≡ N0 [MOD e1] := by
      have : e1 * m0 ≡ 0 [MOD e1] := (Nat.modEq_zero_iff_dvd).mpr ⟨m0, rfl⟩
      simpa using this.add_right N0
    have h1 : N ≡ N0 [MOD e1] := h1'.trans h1''
    have hmod : N % e1 = N0 := Nat.mod_eq_of_modEq h1 hN0
    have hdec : e1 * (N / e1) + N0 = N := by
      have := Nat.div_add_mod N e1
      rw [hmod] at this; exact this
    have h2' : e1 * (N / e1) + N0 ≡ e1 * m0 + N0 [MOD e1 * e2] := by
      rw [hdec]; exact h
    have h2'' : e1 * (N / e1) ≡ e1 * m0 [MOD e1 * e2] :=
      Nat.ModEq.add_right_cancel' N0 h2'
    have hgcd : (e1 * e2).gcd e1 = e1 := by
      rw [Nat.gcd_comm]; exact Nat.gcd_eq_left ⟨e2, rfl⟩
    have h2 := Nat.ModEq.cancel_left_div_gcd (m := e1 * e2) (c := e1)
      (a := N / e1) (b := m0) (Nat.mul_pos he1 he2) h2''
    rw [hgcd, Nat.mul_div_cancel_left e2 he1] at h2
    exact ⟨h1, h2⟩

/-- **PRIMARY headline.** For `i,j ≥ 1`, the joint event `{v N = i ∧ v (Syr N) = j}` is a
single residue class of `N` modulo `2^{i+1+j}`. This is the residue-class fact that the
whole two-step independence law rests on: knowing `v N = i` and `v (Syr N) = j` together
pins `N` down to *one* class mod `2^{i+1+j}`, exactly the product of the moduli of the two
individual one-step laws (`2^{i+1}` and `2^j`; the `j` — not `j+1` — reflects that, once
`v N = i` is already fixed, `Syr N` ranges only over odds as `N` varies, so its own
valuation-`j` law needs one fewer bit of information than the unconditional one-step law). -/
theorem joint_residue (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∃ Nstar : ℕ, ∀ N : ℕ,
      (SyracuseValuationDistribution.v N = i ∧
       padicValNat 2 (3 * SyracuseThreeAdicBias.Syr N + 1) = j)
      ↔ N ≡ Nstar [MOD 2 ^ (i + 1 + j)] := by
  obtain ⟨N0raw, hN0raw⟩ := SyracuseValuationDistribution.exists_residue i
  set N0 := N0raw % 2 ^ (i + 1) with hN0def
  have hN0lt : N0 < 2 ^ (i + 1) := Nat.mod_lt _ (pow_pos (by norm_num) (i + 1))
  have hN0 : ∀ N, SyracuseValuationDistribution.v N = i ↔ N ≡ N0 [MOD 2 ^ (i + 1)] := by
    intro N
    rw [hN0raw N]
    constructor
    · intro h; exact h.trans (Nat.mod_modEq N0raw _).symm
    · intro h; exact h.trans (Nat.mod_modEq N0raw _)
  have hvN0 : SyracuseValuationDistribution.v N0 = i := (hN0 N0).mpr Nat.ModEq.rfl
  obtain ⟨hdvd0, hndvd0⟩ := (SyracuseValuationDistribution.v_eq_iff N0 i).mp hvN0
  obtain ⟨q0, hq0⟩ := hdvd0
  -- `q0` is the odd quotient `(3N₀+1)/2^i`.
  have hq0odd : Odd q0 := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    rintro ⟨q0', hq0'⟩
    exact hndvd0 ⟨q0', by rw [hq0, hq0', pow_succ]; ring⟩
  obtain ⟨k, hk⟩ := hq0odd
  set r0 := 3 * k + 2 with hr0def
  -- `3q0+1 = 2r0` since `q0` is odd.
  have hr0 : 3 * q0 + 1 = 2 * r0 := by rw [hk, hr0def]; ring
  have hr0ne : r0 ≠ 0 := by omega
  -- Within the residue class `N = 2^{i+1}m+N₀`, `v N = i` always (unconditionally on `m`).
  have hvNm : ∀ m, padicValNat 2 (3 * (2 ^ (i + 1) * m + N0) + 1) = i := by
    intro m
    have h := (hN0 (2 ^ (i + 1) * m + N0)).mpr (by
      have h1 : (2 ^ (i + 1) * m) ≡ 0 [MOD 2 ^ (i + 1)] := (Nat.modEq_zero_iff_dvd).mpr ⟨m, rfl⟩
      simpa using h1.add_right N0)
    simpa [SyracuseValuationDistribution.v] using h
  -- Algebraic identity: `3N+1 = 2^i(q0+6m)` inside this residue class.
  have h3Nm : ∀ m, 3 * (2 ^ (i + 1) * m + N0) + 1 = 2 ^ i * (q0 + 6 * m) := by
    intro m
    have hpow : (2 : ℕ) ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
    calc 3 * (2 ^ (i + 1) * m + N0) + 1 = (3 * N0 + 1) + 6 * (2 ^ i * m) := by rw [hpow]; ring
      _ = 2 ^ i * q0 + 6 * (2 ^ i * m) := by rw [hq0]
      _ = 2 ^ i * (q0 + 6 * m) := by ring
  -- Hence `Syr N = q0 + 6m` — affine in the free parameter `m`.
  have hSyrNm : ∀ m, SyracuseThreeAdicBias.Syr (2 ^ (i + 1) * m + N0) = q0 + 6 * m := by
    intro m
    simp only [SyracuseThreeAdicBias.Syr]
    rw [hvNm m, h3Nm m]
    exact Nat.mul_div_cancel_left _ (pow_pos (by norm_num) i)
  -- The second-step valuation condition, as a linear condition on `m`.
  obtain ⟨m0, hm0⟩ := exists_residue_linear 9 r0 (j - 1) (by decide) hr0ne
  have hwNm : ∀ m, padicValNat 2 (3 * (q0 + 6 * m) + 1) = j ↔ m ≡ m0 [MOD 2 ^ j] := by
    intro m
    have heq : 3 * (q0 + 6 * m) + 1 = 2 * (r0 + 9 * m) := by
      calc 3 * (q0 + 6 * m) + 1 = (3 * q0 + 1) + 18 * m := by ring
        _ = 2 * r0 + 18 * m := by rw [hr0]
        _ = 2 * (r0 + 9 * m) := by ring
    have hne : r0 + 9 * m ≠ 0 := by omega
    rw [heq, padicValNat.mul (by norm_num) hne, padicValNat_self]
    rw [show (1 + padicValNat 2 (r0 + 9 * m) = j) ↔ (padicValNat 2 (r0 + 9 * m) = j - 1) from
      by omega]
    rw [show r0 + 9 * m = 9 * m + r0 from by ring]
    rw [hm0 m]
    rw [show (j - 1) + 1 = j from by omega]
  -- Combine the two residue-class facts (on `N mod 2^{i+1}` and `m mod 2^j`) via
  -- digit-decomposition into one residue class of `N` mod `2^{i+1+j}`.
  refine ⟨2 ^ (i + 1) * m0 + N0, fun N => ?_⟩
  have hexp : (2 : ℕ) ^ (i + 1 + j) = 2 ^ (i + 1) * 2 ^ j := by rw [pow_add]
  rw [hexp, ← digit_decomp (2 ^ (i + 1)) (2 ^ j) N0 m0
    (pow_pos (by norm_num) (i + 1)) (pow_pos (by norm_num) j) hN0lt N]
  constructor
  · rintro ⟨hvN, hwN⟩
    refine ⟨(hN0 N).mp hvN, ?_⟩
    have hmodN : N % 2 ^ (i + 1) = N0 := Nat.mod_eq_of_modEq ((hN0 N).mp hvN) hN0lt
    have hdecN : 2 ^ (i + 1) * (N / 2 ^ (i + 1)) + N0 = N := by
      have hh := Nat.div_add_mod N (2 ^ (i + 1)); rw [hmodN] at hh; exact hh
    have hSyrN : SyracuseThreeAdicBias.Syr N = q0 + 6 * (N / 2 ^ (i + 1)) := by
      conv_lhs => rw [← hdecN]
      exact hSyrNm (N / 2 ^ (i + 1))
    rw [hSyrN] at hwN
    exact (hwNm (N / 2 ^ (i + 1))).mp hwN
  · rintro ⟨hmodN, hmN⟩
    have hvN : SyracuseValuationDistribution.v N = i := (hN0 N).mpr hmodN
    refine ⟨hvN, ?_⟩
    have hmodN' : N % 2 ^ (i + 1) = N0 := Nat.mod_eq_of_modEq hmodN hN0lt
    have hdecN : 2 ^ (i + 1) * (N / 2 ^ (i + 1)) + N0 = N := by
      have hh := Nat.div_add_mod N (2 ^ (i + 1)); rw [hmodN'] at hh; exact hh
    have hSyrN : SyracuseThreeAdicBias.Syr N = q0 + 6 * (N / 2 ^ (i + 1)) := by
      conv_lhs => rw [← hdecN]
      exact hSyrNm (N / 2 ^ (i + 1))
    rw [hSyrN]
    exact (hwNm (N / 2 ^ (i + 1))).mpr hmN

/-- **Exact count.** For `1 ≤ i, 1 ≤ j, i+1+j ≤ K`, the number of `N < 2^K` with
`v N = i` and `v (Syr N) = j` is exactly `2^{K-i-1-j}`. -/
theorem card_joint_valuation_eq (K i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hK : i + 1 + j ≤ K) :
    ((Finset.range (2 ^ K)).filter (fun N =>
        SyracuseValuationDistribution.v N = i ∧
        padicValNat 2 (3 * SyracuseThreeAdicBias.Syr N + 1) = j)).card
      = 2 ^ (K - i - 1 - j) := by
  obtain ⟨Nstar, hNstar⟩ := joint_residue i j hi hj
  have hfilter : (Finset.range (2 ^ K)).filter (fun N =>
        SyracuseValuationDistribution.v N = i ∧
        padicValNat 2 (3 * SyracuseThreeAdicBias.Syr N + 1) = j)
      = (Finset.range (2 ^ K)).filter (fun N => N ≡ Nstar [MOD 2 ^ (i + 1 + j)]) :=
    Finset.filter_congr (fun N _ => hNstar N)
  rw [hfilter, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (2 ^ K) (pow_pos (by norm_num) (i + 1 + j)) Nstar]
  have hsplit : 2 ^ K = 2 ^ (i + 1 + j) * 2 ^ (K - i - 1 - j) := by
    rw [← pow_add]; congr 1; omega
  have hmod : 2 ^ K % 2 ^ (i + 1 + j) = 0 := by rw [hsplit, Nat.mul_mod_right]
  have hdiv : 2 ^ K / 2 ^ (i + 1 + j) = 2 ^ (K - i - 1 - j) := by
    rw [hsplit, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) (i + 1 + j))]
  rw [hmod, hdiv, if_neg (Nat.not_lt_zero (Nstar % 2 ^ (i + 1 + j))), add_zero]

/-- The number of odd naturals below `2^K` (for `K ≥ 1`) is `2^{K-1}` — the size of the
"population" the conjecture's density is measured against. -/
theorem count_odds_range (K : ℕ) (hK : 1 ≤ K) :
    ((Finset.range (2 ^ K)).filter (fun N => Odd N)).card = 2 ^ (K - 1) := by
  have hfilter : (Finset.range (2 ^ K)).filter (fun N => Odd N)
      = (Finset.range (2 ^ K)).filter (fun N => N ≡ 1 [MOD 2]) := by
    apply Finset.filter_congr
    intro N _
    rw [Nat.odd_iff]
    simp [Nat.ModEq]
  rw [hfilter, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card (2 ^ K) (by norm_num) 1]
  have hsplit : 2 ^ K = 2 * 2 ^ (K - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hmod : 2 ^ K % 2 = 0 := by rw [hsplit, Nat.mul_mod_right]
  have hdiv : 2 ^ K / 2 = 2 ^ (K - 1) := by
    rw [hsplit, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hmod, hdiv, if_neg (Nat.not_lt_zero (1 % 2)), add_zero]

/-- **HEADLINE — two-step density (over the odd population).** Fixing `i,j ≥ 1`, the
proportion, among the *odd* naturals below `2^K`, of `N` with `v₂(3N+1)=i` and
`v₂(3·Syr N+1)=j` is EXACTLY `2^{-i}·2^{-j}` — the one-step geometric law extends
*multiplicatively* across one Syracuse step: no correlation between consecutive 2-adic
valuations. This is `conj-2026-07-18-015`'s statement made precise and proved: the
2-adic valuations along a Syracuse orbit behave as (exactly, not just asymptotically)
independent Geometric(1/2) draws at consecutive steps. -/
theorem density_joint_valuation_eq_over_odds (K i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hK : i + 1 + j ≤ K) :
    (((Finset.range (2 ^ K)).filter (fun N =>
        SyracuseValuationDistribution.v N = i ∧
        padicValNat 2 (3 * SyracuseThreeAdicBias.Syr N + 1) = j)).card : ℝ) /
      (((Finset.range (2 ^ K)).filter (fun N => Odd N)).card : ℝ)
      = 1 / (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ j) := by
  rw [card_joint_valuation_eq K i j hi hj hK, count_odds_range K (by omega)]
  have hK1 : K - 1 = i + j + (K - i - 1 - j) := by omega
  push_cast
  rw [hK1, pow_add, pow_add]
  field_simp

end SyracuseTwoStepValuationIndependence
