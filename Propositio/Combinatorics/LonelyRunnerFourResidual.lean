/-
# Lonely Runner Conjecture, `k = 4`: closing the equal-magnitude case and reducing the
  residual **exactly** to pairwise-coprime triples

This file continues the honest `k = 4` Lonely Runner attack (3 distinct nonzero integer
relative speeds `v1, v2, v3`, target bound `1/4`, tracked as
`conj-2026-07-09-lonelyrunner-k4-true`). It builds on:

* `LonelyRunnerSmallK.lonely_runner_three` — the `k = 3` base case (bound `1/3`), and
* `LonelyRunnerFourFull.lonely_runner_four_gcd_pair` — the gcd-pair construction, which
  handles a pair of unequal-magnitude speeds whose gcd does not divide the third.

## What is new here

### 1. The equal-magnitude case (UNCONDITIONAL)

`lonely_runner_four_equal_mag`: whenever two of the three speeds have **equal magnitude**
(`|vᵢ| = |vⱼ|`, i.e. `vᵢ = -vⱼ` since they are distinct), the `k = 4` statement holds
outright. Reason: two equal-magnitude runners impose the *same* nid-constraint, so the
problem collapses to two distinct-magnitude speeds — handled by the `k = 3` base case
with slack (`1/3 ≥ 1/4`). This closes an infinite family left open by the gcd-pair file,
including its own cited counterexample `(4, -4, 6)`. Distinctness of the three speeds forces
the third magnitude to differ from the repeated one (three distinct integers cannot share a
single magnitude, since only `±a` realise magnitude `a`), which is exactly what the `k = 3`
base case needs.

### 2. The residual is EXACTLY the pairwise-coprime case (reduction theorem)

`lonely_runner_four_reduce`: assuming the `k = 4` statement for all **pairwise-coprime,
pairwise-distinct positive** triples (hypothesis `H`), the statement holds for *every*
distinct nonzero integer triple. Combined with the two unconditional tools above, this
pins the open residual precisely:

* equal magnitudes  → handled unconditionally (§1);
* all magnitudes distinct → divide out the overall gcd `d = gcd(gcd(a,b),c)`, giving
  `(a',b',c')` with `gcd(a',b',c') = 1`; then either the reduced triple is pairwise coprime
  (apply `H`) or some pair shares a factor `g > 1` which — because the overall gcd is `1` —
  cannot divide the third, so the gcd-pair construction applies. Rescaling time by `1/d`
  transports the witness back.

So the earlier file's vague residual ("*at least* the pairwise-coprime triples plus
`(4,-4,6)`-like ones") is sharpened: up to sign, scaling and relabelling, the **only** open
case is pairwise-coprime pairwise-distinct positive triples. That kernel is where the genuine
Betke–Wills / Barajas–Serra content lives — its extremal instance `(1,2,3)` is tight at
`1/4` (only `t = 1/4, 3/4` work on the natural lattice), so no slack-based pigeonhole closes
it; it is left as the explicit hypothesis `H`, honestly unproved.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Propositio.Combinatorics.LonelyRunnerSmallK
import Propositio.Combinatorics.LonelyRunnerFourFull

namespace LonelyRunnerFourResidual

open LonelyRunnerSmallK LonelyRunnerFourFull

/-- The pairwise-coprime kernel of `k = 4`, packaged as a reusable hypothesis shape:
for pairwise-distinct pairwise-coprime positive speeds, there is a lonely time at bound
`1/4`. This is the (still open) heart of the conjecture. -/
def CoprimeKernel : Prop :=
  ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → 1 ≤ z → x ≠ y → x ≠ z → y ≠ z →
    Nat.Coprime x y → Nat.Coprime x z → Nat.Coprime y z →
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t)

/-- Two equal-magnitude runners share a nid-value: if `|p| = |q|` then `nid (q·t) = nid (p·t)`. -/
lemma nid_eq_of_natAbs_eq (p q : ℤ) (t : ℝ) (h : p.natAbs = q.natAbs) :
    nid ((q : ℝ) * t) = nid ((p : ℝ) * t) := by
  rw [nid_natAbs_mul q t, nid_natAbs_mul p t, h]

/-- If three integers are pairwise distinct and two of them (`x, y`) have equal magnitude,
the third (`z`) has a *different* magnitude. Three distinct integers cannot share a
magnitude, since magnitude `a` is realised only by `±a`. -/
lemma third_natAbs_ne (x y z : ℤ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : x.natAbs = y.natAbs) : x.natAbs ≠ z.natAbs := by
  intro hxz'
  -- `|x| = |y|` with `x ≠ y` forces `x = -y`.
  have hxeq : x = -y := (Int.natAbs_eq_natAbs_iff.mp h).resolve_left hxy
  -- `|x| = |z|` with `x ≠ z` forces `x = -z`.
  have hxeq2 : x = -z := (Int.natAbs_eq_natAbs_iff.mp hxz').resolve_left hxz
  -- then `-y = -z`, i.e. `y = z`, contradiction.
  apply hyz
  have : (-y : ℤ) = -z := by rw [← hxeq, hxeq2]
  linarith [this]

/-- **Equal-magnitude core.** Given `p, q, r` nonzero with `|p| = |q|` and `|p| ≠ |r|`,
there is a lonely time at bound `1/4`. -/
lemma emag_core (p q r : ℤ) (hp : p ≠ 0) (_hq : q ≠ 0) (hr : r ≠ 0)
    (heq : p.natAbs = q.natAbs) (hne : p.natAbs ≠ r.natAbs) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((p : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((q : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((r : ℝ) * t) := by
  have hpr : p ≠ r := by
    intro h; exact hne (by rw [h])
  obtain ⟨t, htp, htr⟩ := lonely_runner_three p r hp hr hpr
  refine ⟨t, by linarith [htp], ?_, by linarith [htr]⟩
  rw [nid_eq_of_natAbs_eq p q t heq]; linarith [htp]

/-- **The equal-magnitude case (unconditional).** Three distinct nonzero integer speeds,
two of which share a magnitude: there is a lonely time at bound `1/4`. -/
theorem lonely_runner_four_equal_mag (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hm : v1.natAbs = v2.natAbs ∨ v1.natAbs = v3.natAbs ∨ v2.natAbs = v3.natAbs) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * t) := by
  rcases hm with hm | hm | hm
  · -- |v1| = |v2|, third is v3
    have hne : v1.natAbs ≠ v3.natAbs := third_natAbs_ne v1 v2 v3 h12 h13 h23 hm
    obtain ⟨t, ha, hb, hc⟩ := emag_core v1 v2 v3 h1 h2 h3 hm hne
    exact ⟨t, ha, hb, hc⟩
  · -- |v1| = |v3|, third is v2
    have hne : v1.natAbs ≠ v2.natAbs := third_natAbs_ne v1 v3 v2 h13 h12 (Ne.symm h23) hm
    obtain ⟨t, ha, hc, hb⟩ := emag_core v1 v3 v2 h1 h3 h2 hm hne
    exact ⟨t, ha, hb, hc⟩
  · -- |v2| = |v3|, third is v1
    have hne : v2.natAbs ≠ v1.natAbs := third_natAbs_ne v2 v3 v1 h23 (Ne.symm h12) (Ne.symm h13) hm
    obtain ⟨t, hb, hc, ha⟩ := emag_core v2 v3 v1 h2 h3 h1 hm hne
    exact ⟨t, ha, hb, hc⟩

/-- **Time rescaling.** If `(a', b', c')` admit a lonely time `s` and `a = d·a'`, `b = d·b'`,
`c = d·c'` with `d > 0`, then `(a, b, c)` admit the lonely time `t = s/d`. -/
lemma scale_down (a b c d a' b' c' : ℕ) (hd : 0 < d)
    (ha : a = d * a') (hb : b = d * b') (hc : c = d * c') (s : ℝ)
    (h1 : (1 : ℝ) / 4 ≤ nid ((a' : ℝ) * s)) (h2 : (1 : ℝ) / 4 ≤ nid ((b' : ℝ) * s))
    (h3 : (1 : ℝ) / 4 ≤ nid ((c' : ℝ) * s)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((a : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((b : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((c : ℝ) * t) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨s / (d : ℝ), ?_, ?_, ?_⟩
  · have e : (a : ℝ) * (s / (d : ℝ)) = (a' : ℝ) * s := by
      rw [ha]; push_cast; field_simp
    rw [e]; exact h1
  · have e : (b : ℝ) * (s / (d : ℝ)) = (b' : ℝ) * s := by
      rw [hb]; push_cast; field_simp
    rw [e]; exact h2
  · have e : (c : ℝ) * (s / (d : ℝ)) = (c' : ℝ) * s := by
      rw [hc]; push_cast; field_simp
    rw [e]; exact h3

/-- **Positive-magnitude master lemma (all magnitudes distinct).** Given the pairwise-coprime
kernel `H`, three pairwise-distinct positive speeds admit a lonely time at bound `1/4`. The
proof divides out the overall gcd and splits on pairwise coprimality of the reduced triple. -/
lemma lr4_nat (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (H : CoprimeKernel) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((a : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((b : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((c : ℝ) * t) := by
  set d : ℕ := Nat.gcd (Nat.gcd a b) c with hddef
  have hgabpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left c hgabpos
  have hd_ab : d ∣ Nat.gcd a b := Nat.gcd_dvd_left _ _
  have hda : d ∣ a := hd_ab.trans (Nat.gcd_dvd_left a b)
  have hdb : d ∣ b := hd_ab.trans (Nat.gcd_dvd_right a b)
  have hdc : d ∣ c := Nat.gcd_dvd_right _ _
  set a' : ℕ := a / d with ha'def
  set b' : ℕ := b / d with hb'def
  set c' : ℕ := c / d with hc'def
  have hae : a = d * a' := (Nat.mul_div_cancel' hda).symm
  have hbe : b = d * b' := (Nat.mul_div_cancel' hdb).symm
  have hce : c = d * c' := (Nat.mul_div_cancel' hdc).symm
  have ha' : 1 ≤ a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h, Nat.mul_zero] at hae; omega
    · exact h
  have hb' : 1 ≤ b' := by
    rcases Nat.eq_zero_or_pos b' with h | h
    · rw [h, Nat.mul_zero] at hbe; omega
    · exact h
  have hc' : 1 ≤ c' := by
    rcases Nat.eq_zero_or_pos c' with h | h
    · rw [h, Nat.mul_zero] at hce; omega
    · exact h
  have hab' : a' ≠ b' := by
    intro h; apply hab; rw [hae, hbe, h]
  have hac' : a' ≠ c' := by
    intro h; apply hac; rw [hae, hce, h]
  have hbc' : b' ≠ c' := by
    intro h; apply hbc; rw [hbe, hce, h]
  -- the reduced triple has overall gcd one
  have hgcd1 : Nat.gcd (Nat.gcd a' b') c' = 1 := by
    set e : ℕ := Nat.gcd (Nat.gcd a' b') c' with hedef
    have hea' : e ∣ a' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a' b')
    have heb' : e ∣ b' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a' b')
    have hec' : e ∣ c' := Nat.gcd_dvd_right _ _
    have hepos : 0 < e := Nat.gcd_pos_of_pos_left c' (Nat.gcd_pos_of_pos_left b' (by omega))
    have hdea : d * e ∣ a := by rw [hae]; exact mul_dvd_mul_left d hea'
    have hdeb : d * e ∣ b := by rw [hbe]; exact mul_dvd_mul_left d heb'
    have hdec : d * e ∣ c := by rw [hce]; exact mul_dvd_mul_left d hec'
    have hded : d * e ∣ d := by
      rw [hddef]; exact Nat.dvd_gcd (Nat.dvd_gcd hdea hdeb) hdec
    have hle : d * e ≤ d := Nat.le_of_dvd hdpos hded
    have hge : d ≤ d * e := Nat.le_mul_of_pos_right d hepos
    have hdede : d * e = d := le_antisymm hle hge
    have : d * e = d * 1 := by rw [hdede, Nat.mul_one]
    exact Nat.eq_of_mul_eq_mul_left hdpos this
  -- case split on pairwise coprimality of the reduced triple
  by_cases hcab : Nat.Coprime a' b'
  · by_cases hcac : Nat.Coprime a' c'
    · by_cases hcbc : Nat.Coprime b' c'
      · -- all pairwise coprime: apply the kernel
        obtain ⟨s, hs1, hs2, hs3⟩ := H a' b' c' ha' hb' hc' hab' hac' hbc' hcab hcac hcbc
        exact scale_down a b c d a' b' c' hdpos hae hbe hce s hs1 hs2 hs3
      · -- b', c' not coprime: gcd(b',c') > 1 and does not divide a'
        have hg1 : Nat.gcd b' c' ≠ 1 := hcbc
        have hnd : ¬ (Nat.gcd b' c' ∣ a') := by
          intro hdvd
          apply hg1
          have : Nat.gcd b' c' ∣ Nat.gcd (Nat.gcd a' b') c' :=
            Nat.dvd_gcd (Nat.dvd_gcd hdvd (Nat.gcd_dvd_left b' c')) (Nat.gcd_dvd_right b' c')
          rw [hgcd1] at this
          exact Nat.eq_one_of_dvd_one this
        obtain ⟨s, hsb, hsc, hsa⟩ :=
          lonely_runner_four_gcd_pair b' c' a' hb' hc' ha' hbc' hnd
        exact scale_down a b c d a' b' c' hdpos hae hbe hce s hsa hsb hsc
    · -- a', c' not coprime
      have hg1 : Nat.gcd a' c' ≠ 1 := hcac
      have hnd : ¬ (Nat.gcd a' c' ∣ b') := by
        intro hdvd
        apply hg1
        have : Nat.gcd a' c' ∣ Nat.gcd (Nat.gcd a' b') c' :=
          Nat.dvd_gcd (Nat.dvd_gcd (Nat.gcd_dvd_left a' c') hdvd) (Nat.gcd_dvd_right a' c')
        rw [hgcd1] at this
        exact Nat.eq_one_of_dvd_one this
      obtain ⟨s, hsa, hsc, hsb⟩ :=
        lonely_runner_four_gcd_pair a' c' b' ha' hc' hb' hac' hnd
      exact scale_down a b c d a' b' c' hdpos hae hbe hce s hsa hsb hsc
  · -- a', b' not coprime
    have hg1 : Nat.gcd a' b' ≠ 1 := hcab
    have hnd : ¬ (Nat.gcd a' b' ∣ c') := by
      intro hdvd
      apply hg1
      have : Nat.gcd a' b' ∣ Nat.gcd (Nat.gcd a' b') c' :=
        Nat.dvd_gcd (dvd_refl (Nat.gcd a' b')) hdvd
      rw [hgcd1] at this
      exact Nat.eq_one_of_dvd_one this
    obtain ⟨s, hsa, hsb, hsc⟩ :=
      lonely_runner_four_gcd_pair a' b' c' ha' hb' hc' hab' hnd
    exact scale_down a b c d a' b' c' hdpos hae hbe hce s hsa hsb hsc

/-- **The reduction theorem: `k = 4` reduces exactly to the pairwise-coprime kernel.**
Assuming the pairwise-coprime kernel `H`, the honest `k = 4` Lonely Runner statement holds
for every triple of pairwise-distinct nonzero integer speeds. Together with the unconditional
`lonely_runner_four_equal_mag`, this shows the only genuinely open case is the pairwise-coprime
one. -/
theorem lonely_runner_four_reduce (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) (H : CoprimeKernel) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * t) := by
  by_cases hm : v1.natAbs = v2.natAbs ∨ v1.natAbs = v3.natAbs ∨ v2.natAbs = v3.natAbs
  · exact lonely_runner_four_equal_mag v1 v2 v3 h1 h2 h3 h12 h13 h23 hm
  · rw [not_or, not_or] at hm
    obtain ⟨hm12, hm13, hm23⟩ := hm
    have ha : 1 ≤ v1.natAbs := by
      have : v1.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h1
      omega
    have hb : 1 ≤ v2.natAbs := by
      have : v2.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h2
      omega
    have hc : 1 ≤ v3.natAbs := by
      have : v3.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h3
      omega
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      lr4_nat v1.natAbs v2.natAbs v3.natAbs ha hb hc hm12 hm13 hm23 H
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [nid_natAbs_mul]; exact ht1
    · rw [nid_natAbs_mul]; exact ht2
    · rw [nid_natAbs_mul]; exact ht3

end LonelyRunnerFourResidual
