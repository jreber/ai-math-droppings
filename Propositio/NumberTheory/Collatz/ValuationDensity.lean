import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.LyapunovCascade
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The exact `v₂(3n+1)` residue-density law and the one-step descent characterization

This file formalizes the rigorous backbone of the **"Collatz contracts on average"**
heuristic for the compressed odd map
`cc n = (3n+1) / 2^(v₂(3n+1))` (defined in `TerrasDensity.lean`).

Two exact, axiom-clean facts:

## 1. One-step descent characterization (`cc_lt_iff_one_mod_four`)

For odd `n ≥ 1`, write `a := v₂(3n+1) ≥ 1`. Then
`cc n < n  ⟺  a ≥ 2  ⟺  n % 4 = 1`,
and dually `cc n > n ⟺ n % 4 = 3`. So among odd `n`, **exactly half**
(those `≡ 1 (mod 4)`) strictly descend in one compressed step; those
`≡ 3 (mod 4)` ascend. (The `< vs >` dichotomy is sharp: `cc n = n` never
happens for odd `n > 1`.)

The proof rests on the factorization bridge `2^a · cc n = 3n+1`
(`LyapunovCascade.pow_v2_mul_cc`): `cc n < n ⟺ 3n+1 < n·2^a ⟺ 2^a ≥ 4`,
and `4 ∣ 3n+1 ⟺ n ≡ 1 (mod 4)`.

## 2. The geometric `2^{-a}` valuation distribution (`v2_count`)

For `1 ≤ a < M`, the residues `r < 2^M` with `v₂(3r+1) = a` number exactly
`2^(M-a-1)`, i.e. density `2^{-(a+1)}` over all integers. Restricted to ODD
residues the density is `2^{-a}` — and in fact `v₂(3r+1) = a ≥ 1` already
*forces* `r` odd, so the odd-restricted count equals the full count.

This `2^{-a}` geometric law is exactly what makes the expected
log-contraction per step `Σ a·2^{-a} = 2 > log₂ 3`, the rigorous backbone of
the heuristic that compressed Collatz steps shrink on average.

The single residue condition behind the count is
`v₂(3r+1) = a  ⟺  (3r+1) % 2^(a+1) = 2^a`  (for `a ≥ 1`)
(`v2_eq_iff_residue`), so the count reduces to a residue-class enumeration mod
`2^(a+1)` (`v2_count_aux`, by the same `Finset` induction style as
`CollatzDescentDensity.spine_count_eq`).

## HONESTY — this is NOT a proof of Collatz

The exact distribution of the *division counts* `v₂(3n+1)` is an unconditional
statement about residues; it gives the expected value `2` of the per-step
2-adic valuation. It says nothing about whether individual trajectories
terminate: the residue of `cc n` is not pinned by the residue of `n`, so the
favorable expectation does not chain into a global potential. What is rigorous
here is purely the exact one-step descent split and the exact geometric
distribution of the valuation.

All theorems are axiom-clean (`propext, Classical.choice, Quot.sound` only);
no `native_decide`, no `sorry`, no new axioms.
-/

namespace CollatzValuationDensity

open TerrasDensity LyapunovCascade

/-! ## 0. Preliminaries: `v₂(3n+1) ≥ 1` for odd `n`, and the 2-adic value at a residue -/

/-- For odd `n`, `3n+1` is even, so `1 ≤ v₂(3n+1)`. -/
theorem one_le_v2_three_n_plus_one {n : Nat} (hodd : TerrasDensity.Odd n) :
    1 ≤ padicValNat 2 (3 * n + 1) := by
  obtain ⟨k, hk⟩ := hodd
  have hne : 3 * n + 1 ≠ 0 := by omega
  have hdvd : (2 : Nat) ^ 1 ∣ 3 * n + 1 := by
    refine ⟨3 * k + 2, ?_⟩; omega
  exact (padicValNat_dvd_iff_le hne).mp hdvd

/-! ## 1. The one-step descent characterization

`cc n < n ⟺ v₂(3n+1) ≥ 2 ⟺ n % 4 = 1`, with the dual ascent statement. -/

/-- `4 ∣ 3n+1 ⟺ n % 4 = 1`. (`3n+1 ≡ 0 (mod 4) ⟺ 3n ≡ 3 ⟺ n ≡ 1`.) -/
theorem four_dvd_three_n_plus_one_iff (n : Nat) :
    4 ∣ (3 * n + 1) ↔ n % 4 = 1 := by
  omega

/-- `v₂(3n+1) ≥ 2 ⟺ n % 4 = 1` for any `n`. -/
theorem two_le_v2_iff_one_mod_four {n : Nat} (hodd : TerrasDensity.Odd n) :
    2 ≤ padicValNat 2 (3 * n + 1) ↔ n % 4 = 1 := by
  have hne : 3 * n + 1 ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  rw [← four_dvd_three_n_plus_one_iff,
      show (4 : Nat) = 2 ^ 2 from rfl,
      padicValNat_dvd_iff_le hne]

/-- **One-step descent characterization — REAL.**

For odd `n > 1`, `cc n < n ⟺ n % 4 = 1` (equivalently `v₂(3n+1) ≥ 2`).

The hypothesis `n > 1` is necessary: `cc 1 = 1` (not `< 1`) while `1 % 4 = 1`,
so `n = 1` is the unique odd exception.

Proof via the factorization bridge `2^a · cc n = 3n+1`: with `a := v₂(3n+1)`,
`cc n < n ⟺ 2^a · cc n < 2^a · n ⟺ 3n+1 < n·2^a`. For `a ≥ 1`, `n > 1`,
this holds iff `2^a ≥ 4` iff `a ≥ 2`, and `a ≥ 2 ⟺ n % 4 = 1`. -/
theorem cc_lt_iff_one_mod_four {n : Nat} (hodd : TerrasDensity.Odd n) (hn : 1 < n) :
    cc n < n ↔ n % 4 = 1 := by
  set a := padicValNat 2 (3 * n + 1) with ha
  have hbridge : 2 ^ a * cc n = 3 * n + 1 := pow_v2_mul_cc n
  have ha1 : 1 ≤ a := one_le_v2_three_n_plus_one hodd
  rw [← two_le_v2_iff_one_mod_four hodd, ← ha]
  constructor
  · intro hlt
    -- cc n < n ⟹ 3n+1 = 2^a cc n < 2^a n; if a = 1, 2 cc n = 3n+1 with cc n < n ⟹ 3n+1 < 2n.
    by_contra hlt2
    have ha_eq : a = 1 := by omega
    rw [ha_eq] at hbridge
    -- 2 * cc n = 3n+1, and cc n < n ⟹ 2 cc n ≤ 2n - 2 ⟹ 3n+1 ≤ 2n-2, impossible
    omega
  · intro hge2
    -- a ≥ 2 ⟹ 2^a ≥ 4 ⟹ 4·cc n ≤ 3n+1; if n ≤ cc n then 4n ≤ 3n+1 ⟹ n ≤ 1, contra n > 1.
    have hpow : 4 ≤ 2 ^ a := by
      calc (4 : Nat) = 2 ^ 2 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hge2
    by_contra hge
    have hge' : n ≤ cc n := by omega
    have h1 : 4 * cc n ≤ 2 ^ a * cc n := Nat.mul_le_mul_right _ hpow
    have hn_cc : 4 * n ≤ 4 * cc n := Nat.mul_le_mul_left _ hge'
    omega

/-- `cc n = n` is impossible for odd `n`: `2^a cc n = 3n+1` is odd-ish; concretely
`cc n = n ⟹ 2^a n = 3n+1 ⟹ (2^a - 3)n = 1`, forcing `n = 1` and `2^a = 4`, but
`v₂(3·1+1) = v₂(4) = 2` gives `2^a = 4`, yet then `cc 1 = (3+1)/4 = 1 = n` — so in
fact `cc 1 = 1`. The dichotomy is therefore stated for `n > 1`. -/
theorem cc_ne_self_of_odd_gt_one {n : Nat} (hodd : TerrasDensity.Odd n) (hn : 1 < n) : cc n ≠ n := by
  intro hcc
  have hbridge : 2 ^ padicValNat 2 (3 * n + 1) * cc n = 3 * n + 1 := pow_v2_mul_cc n
  rw [hcc] at hbridge
  set a := padicValNat 2 (3 * n + 1)
  have ha1 : 1 ≤ a := one_le_v2_three_n_plus_one hodd
  -- 2^a * n = 3n + 1.  a=1: 2n=3n+1 impossible.  a≥2: 2^a n ≥ 4n > 3n+1 for n>1.
  rcases Nat.lt_or_ge a 2 with h | h
  · have : a = 1 := by omega
    rw [this] at hbridge; omega
  · have hpow : 4 ≤ 2 ^ a := by
      calc (4 : Nat) = 2 ^ 2 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
    have : 4 * n ≤ 2 ^ a * n := Nat.mul_le_mul_right _ hpow
    omega

/-- **One-step ascent characterization — REAL.**
For odd `n > 1`, `cc n > n ⟺ n % 4 = 3`. The complement of the descent class
(`n % 4 = 1`) among odd `n`. -/
theorem cc_gt_iff_three_mod_four {n : Nat} (hodd : TerrasDensity.Odd n) (hn : 1 < n) :
    n < cc n ↔ n % 4 = 3 := by
  have hodd4 : n % 4 = 1 ∨ n % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  have hne : cc n ≠ n := cc_ne_self_of_odd_gt_one hodd hn
  have hiff := cc_lt_iff_one_mod_four hodd hn
  constructor
  · intro h; rcases hodd4 with h1 | h3
    · exact absurd (hiff.mpr h1) (by omega)
    · exact h3
  · intro h3
    have hnot1 : ¬ cc n < n := fun hlt => by have := hiff.mp hlt; omega
    omega

/-- **The exact odd-`n` descent dichotomy — REAL.**
For odd `n > 1`, exactly one of `cc n < n` (when `n ≡ 1 mod 4`) or `cc n > n`
(when `n ≡ 3 mod 4`) holds; equality is impossible. Among odd residues this is
the clean "half descend / half ascend" split. -/
theorem cc_descent_dichotomy {n : Nat} (hodd : TerrasDensity.Odd n) (hn : 1 < n) :
    (cc n < n ∧ n % 4 = 1) ∨ (n < cc n ∧ n % 4 = 3) := by
  have hodd4 : n % 4 = 1 ∨ n % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  rcases hodd4 with h1 | h3
  · exact Or.inl ⟨(cc_lt_iff_one_mod_four hodd hn).mpr h1, h1⟩
  · exact Or.inr ⟨(cc_gt_iff_three_mod_four hodd hn).mpr h3, h3⟩

/-! ## 2. The single residue condition `v₂(3r+1) = a ⟺ (3r+1) % 2^(a+1) = 2^a`

For `a ≥ 1`, having `v₂(3r+1)` exactly `a` is a single congruence condition mod
`2^(a+1)`: `3r+1 ≡ 2^a (mod 2^(a+1))` (i.e. divisible by `2^a` but not `2^(a+1)`). -/

/-- **Valuation = single residue condition — REAL.**
For `a ≥ 1` and any `r`, `v₂(3r+1) = a ⟺ (3r+1) % 2^(a+1) = 2^a`. -/
theorem v2_eq_iff_residue (r a : Nat) (_ha : 1 ≤ a) :
    padicValNat 2 (3 * r + 1) = a ↔ (3 * r + 1) % 2 ^ (a + 1) = 2 ^ a := by
  have hne : 3 * r + 1 ≠ 0 := by omega
  constructor
  · intro hv
    -- v₂ = a ⟹ 2^a ∣ 3r+1 but ¬ 2^(a+1) ∣ 3r+1.
    have hdvd : (2 : Nat) ^ a ∣ 3 * r + 1 := by
      have := pow_padicValNat_dvd (n := 3 * r + 1) (p := 2)
      rwa [hv] at this
    have hnotdvd : ¬ (2 : Nat) ^ (a + 1) ∣ 3 * r + 1 := by
      intro hd
      have := (padicValNat_dvd_iff_le hne).mp hd
      omega
    -- 2^a ∣ 3r+1 ⟹ (3r+1) % 2^a = 0; combine with the mod 2^(a+1) split.
    obtain ⟨q, hq⟩ := hdvd
    -- (3r+1) % 2^(a+1) = 2^a * (q % 2); q is odd since ¬ 2^(a+1) ∣ 3r+1.
    have hpow : (2 : Nat) ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
    have hqodd : q % 2 = 1 := by
      rcases Nat.even_or_odd q with ⟨t, ht⟩ | ⟨t, ht⟩
      · exfalso; apply hnotdvd; exact ⟨t, by rw [hq, ht, hpow]; ring⟩
      · omega
    rw [hq, hpow]
    -- (2^a * q) % (2^a * 2) = 2^a * (q % 2) = 2^a
    rw [Nat.mul_mod_mul_left, hqodd, Nat.mul_one]
  · intro hmod
    -- (3r+1) % 2^(a+1) = 2^a ⟹ 2^a ∣ 3r+1 (since 2^a ∣ 2^(a+1) and ∣ remainder)
    -- and ¬ 2^(a+1) ∣ 3r+1 (else remainder = 0 ≠ 2^a).
    have hpos : 0 < (2 : Nat) ^ a := Nat.two_pow_pos a
    have h1 : (2 : Nat) ^ a ∣ 2 ^ (a + 1) := ⟨2, by rw [pow_succ]⟩
    have hdvd : (2 : Nat) ^ a ∣ 3 * r + 1 := by
      -- 3r+1 = 2^(a+1)*((3r+1)/2^(a+1)) + remainder; 2^a divides both summands.
      have hsplit : 3 * r + 1
          = 2 ^ (a + 1) * ((3 * r + 1) / 2 ^ (a + 1)) + (3 * r + 1) % 2 ^ (a + 1) :=
        (Nat.div_add_mod _ _).symm
      rw [hsplit]
      exact Nat.dvd_add (Dvd.dvd.mul_right h1 _) (by rw [hmod])
    have hge : a ≤ padicValNat 2 (3 * r + 1) := (padicValNat_dvd_iff_le hne).mp hdvd
    have hnotdvd : ¬ (2 : Nat) ^ (a + 1) ∣ 3 * r + 1 := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      rw [hd] at hmod
      omega
    have hlt : padicValNat 2 (3 * r + 1) < a + 1 := by
      rw [← Nat.not_le]; intro hle
      exact hnotdvd ((padicValNat_dvd_iff_le hne).mpr hle)
    omega

/-! ## 3. The geometric `2^{-a}` valuation count

`v2_count_aux`: among `r < 2^(a+1) * m`, exactly `m` satisfy `v₂(3r+1) = a`
(for `a ≥ 1`).  Proved by the residue-class `Finset` induction on `m` (mirroring
`CollatzDescentDensity.spine_count_eq`), using `v2_eq_iff_residue` to turn the
valuation condition into the single congruence `(3r+1) % 2^(a+1) = 2^a`.

`v2_count`: specialising `m = 2^(M-a-1)` gives the headline closed form
`card = 2^(M-a-1)` for `1 ≤ a < M`. -/

/-- The condition `(3r+1) % P = w` depends only on `r mod P`: shifting `r` down
by a multiple `P*k` leaves the residue `(3r+1) % P` unchanged. -/
theorem mod_shift (P k r : Nat) (h : P * k ≤ r) :
    (3 * r + 1) % P = (3 * (r - P * k) + 1) % P := by
  have hr : r = (r - P * k) + P * k := by omega
  conv_lhs => rw [hr]
  have he : 3 * ((r - P * k) + P * k) + 1 = (3 * (r - P * k) + 1) + (3 * k) * P := by ring
  rw [he, Nat.add_mul_mod_self_right]

/-- **Linear-congruence fiber is a singleton — REAL.**
When `gcd(P,3) = 1` and `w < P`, exactly one `s < P` satisfies `(3s+1) % P = w`.
(The map `s ↦ (3s+1) % P` is a bijection of `range P`, so each fiber is a point.) -/
theorem linear_congr_card_one (P : Nat) (hP : 0 < P) (hcop : Nat.gcd P 3 = 1)
    (w : Nat) (hw : w < P) :
    ((Finset.range P).filter (fun r => (3 * r + 1) % P = w)).card = 1 := by
  rw [Finset.card_eq_one]
  -- injectivity of s ↦ (3s+1) % P on range P, via cancellation of the unit 3 mod P.
  have hinj : ∀ x ∈ Finset.range P, ∀ y ∈ Finset.range P,
      (3 * x + 1) % P = (3 * y + 1) % P → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_range] at hx hy
    have hme : (3 * x + 1) ≡ (3 * y + 1) [MOD P] := hxy
    have h3 : 3 * x ≡ 3 * y [MOD P] := by
      have := Nat.ModEq.add_right_cancel' 1 hme; simpa using this
    have hxy2 : x ≡ y [MOD P] := Nat.ModEq.cancel_left_of_coprime hcop h3
    have : x % P = y % P := hxy2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  -- the map is therefore a bijection range P → range P, so it is surjective.
  have himg : ((Finset.range P).image (fun r => (3 * r + 1) % P)) = Finset.range P := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
      obtain ⟨r, _, hr⟩ := hy; rw [← hr]; exact Nat.mod_lt _ hP
    · rw [Finset.card_range, Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h),
        Finset.card_range]
  have hwimg : w ∈ (Finset.range P).image (fun r => (3 * r + 1) % P) := by
    rw [himg]; exact Finset.mem_range.mpr hw
  obtain ⟨s, hs, hsw⟩ := Finset.mem_image.mp hwimg
  refine ⟨s, ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzw⟩; exact hinj z hz s hs (by rw [hzw, hsw])
  · rintro rfl; exact ⟨hs, hsw⟩

/-- Each block `[P*k, P*k+P)` carries the same number of solutions of the
congruence `(3r+1) % P = w` as the base block `range P` (residue-shift bijection
`r ↦ r - P*k`). -/
theorem block_eq_range (P k w : Nat) :
    ((Finset.Ico (P * k) (P * k + P)).filter (fun r => (3 * r + 1) % P = w)).card
      = ((Finset.range P).filter (fun s => (3 * s + 1) % P = w)).card := by
  apply Finset.card_bij (fun r _ => r - P * k)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Ico] at hr
    simp only [Finset.mem_filter, Finset.mem_range]
    obtain ⟨⟨h1, _⟩, h3⟩ := hr
    exact ⟨by omega, by rw [← mod_shift P k r h1]; exact h3⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
    omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    refine ⟨P * k + s, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [mod_shift P k (P * k + s) (by omega)]
    simpa using hs.2

/-- **Residue-class count over `m` blocks — REAL.**
For `P > 0`, `gcd(P,3) = 1` and `w < P`: among `r < P*m`, exactly `m` solve the
congruence `(3r+1) % P = w`. (One solution per length-`P` block, by induction.) -/
theorem residue_block_count (P : Nat) (hPpos : 0 < P) (hcop : Nat.gcd P 3 = 1)
    (w : Nat) (hw : w < P) (m : Nat) :
    ((Finset.range (P * m)).filter (fun r => (3 * r + 1) % P = w)).card = m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.range (P * (k + 1)) =
        Finset.range (P * k) ∪ (Finset.Ico (P * k) (P * k + P)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      constructor
      · intro h; rcases Nat.lt_or_ge x (P * k) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h', by ring_nf; ring_nf at h; omega⟩
      · rintro (h | ⟨_, h2⟩) <;> [nlinarith [hPpos]; nlinarith [hPpos]]
    rw [hsplit, Finset.filter_union]
    have hdisj : Disjoint
        ((Finset.range (P * k)).filter (fun r => (3 * r + 1) % P = w))
        ((Finset.Ico (P * k) (P * k + P)).filter (fun r => (3 * r + 1) % P = w)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
      omega
    rw [Finset.card_union_of_disjoint hdisj, ih]
    -- The block [P*k, P*k+P) contains exactly one solution of the congruence.
    have hblock : ((Finset.Ico (P * k) (P * k + P)).filter
        (fun r => (3 * r + 1) % P = w)).card = 1 := by
      rw [block_eq_range P k w]
      exact linear_congr_card_one P hPpos hcop w hw
    rw [hblock]

/-- **Auxiliary residue count — REAL.**
For `a ≥ 1`, among `r < 2^(a+1) · m` exactly `m` have `v₂(3r+1) = a`.

Within each block of `2^(a+1)` consecutive `r`, exactly one residue solves the
congruence `3r+1 ≡ 2^a (mod 2^(a+1))` (since `3` is invertible mod `2^(a+1)`).
The induction adds one solution per block. -/
theorem v2_count_aux (a : Nat) (ha : 1 ≤ a) (m : Nat) :
    ((Finset.range (2 ^ (a + 1) * m)).filter
      (fun r => padicValNat 2 (3 * r + 1) = a)).card = m := by
  -- Replace the valuation predicate by the residue predicate (extensionally equal).
  have hrw : ((Finset.range (2 ^ (a + 1) * m)).filter
        (fun r => padicValNat 2 (3 * r + 1) = a)) =
      ((Finset.range (2 ^ (a + 1) * m)).filter
        (fun r => (3 * r + 1) % 2 ^ (a + 1) = 2 ^ a)) :=
    Finset.filter_congr (fun r _ => v2_eq_iff_residue r a ha)
  rw [hrw]
  have hPpos : 0 < (2 : Nat) ^ (a + 1) := Nat.two_pow_pos _
  have hcop : Nat.gcd (2 ^ (a + 1)) 3 = 1 := Nat.Coprime.pow_left _ (by decide)
  have h2a_lt : (2 : Nat) ^ a < 2 ^ (a + 1) := by
    rw [pow_succ]; have := Nat.two_pow_pos a; omega
  exact residue_block_count (2 ^ (a + 1)) hPpos hcop (2 ^ a) h2a_lt m

/-- **Geometric valuation law — REAL.**
For `1 ≤ a < M`, the residues `r < 2^M` with `v₂(3r+1) = a` number exactly
`2^(M-a-1)`. Density `2^{-(a+1)}` over all integers, `2^{-a}` over odds. -/
theorem v2_count (M a : Nat) (ha : 1 ≤ a) (haM : a < M) :
    ((Finset.range (2 ^ M)).filter (fun r => padicValNat 2 (3 * r + 1) = a)).card
      = 2 ^ (M - a - 1) := by
  have hsplit : (2 : Nat) ^ M = 2 ^ (a + 1) * 2 ^ (M - a - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, v2_count_aux a ha]

/-! ### Odd-restricted count: density `2^{-a}`

A residue `r` with `v₂(3r+1) = a ≥ 1` is automatically odd (if `r` were even,
`3r+1` would be odd, forcing `v₂ = 0`). So the odd-restricted count equals the
full count, and against the `2^(M-1)` odd residues `< 2^M` the density is
`2^(M-a-1) / 2^(M-1) = 2^{-a}` — the clean geometric law for the odd map. -/

/-- `v₂(3r+1) = a` with `a ≥ 1` forces `r` odd. -/
theorem odd_of_v2_eq {r a : Nat} (ha : 1 ≤ a) (hv : padicValNat 2 (3 * r + 1) = a) :
    r % 2 = 1 := by
  by_contra h
  have hreven : r % 2 = 0 := by omega
  -- r even ⟹ 3r+1 odd ⟹ v₂ = 0, contradicting a ≥ 1.
  have hodd31 : (3 * r + 1) % 2 = 1 := by omega
  have hne : 3 * r + 1 ≠ 0 := by omega
  have : ¬ (2 : Nat) ∣ 3 * r + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hv0 : padicValNat 2 (3 * r + 1) = 0 := by
    rw [padicValNat.eq_zero_iff]; right; right; exact this
  omega

/-- **Odd-restricted geometric count — REAL.**
For `1 ≤ a < M`, restricting to ODD residues does not change the count: still
`2^(M-a-1)`. Over the `2^(M-1)` odd residues below `2^M` this is the density
`2^{-a}`. -/
theorem v2_count_odd (M a : Nat) (ha : 1 ≤ a) (haM : a < M) :
    ((Finset.range (2 ^ M)).filter
        (fun r => r % 2 = 1 ∧ padicValNat 2 (3 * r + 1) = a)).card = 2 ^ (M - a - 1) := by
  -- The odd condition is implied by v₂ = a ≥ 1, so the filter is unchanged.
  have hcongr : ((Finset.range (2 ^ M)).filter
        (fun r => r % 2 = 1 ∧ padicValNat 2 (3 * r + 1) = a)) =
      ((Finset.range (2 ^ M)).filter (fun r => padicValNat 2 (3 * r + 1) = a)) := by
    apply Finset.filter_congr
    intro r _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨odd_of_v2_eq ha h, h⟩
  rw [hcongr, v2_count M a ha haM]

/-! ### STRETCH: the expected-valuation partial sum (`Σ a · 2^(M-a-1) = 2^M - M - 1`)

Summing the valuation counts weighted by `a` gives the total number of `2`-adic
division steps among `r < 2^M` (over `1 ≤ a < M`).  The closed form
`Σ_{a=1}^{M-1} a · 2^(M-a-1) = 2^M - M - 1` makes the **expected** per-step
2-adic valuation `(2^M - M - 1) / 2^(M-1) → 2` as `M → ∞`.  Since `2 > log₂ 3`,
this is the rigorous arithmetic backbone of "Collatz contracts on average". -/

/-- **Expected-valuation partial sum — REAL.**
`Σ_{a=1}^{M-1} a · 2^(M-a-1) = 2^M - M - 1` for `M ≥ 1`. Each summand `a · 2^(M-a-1)`
is `a · (v2_count M a)`, so the left side is the total count of 2-adic division
steps performed across all `r < 2^M`. The mean `≈ 2` (dividing by `2^(M-1)` odd
residues) is the `Σ a·2^{-a} = 2 > log₂3` heuristic, made exact. -/
theorem expected_valuation_sum (M : Nat) (hM : 1 ≤ M) :
    (Finset.Ico 1 M).sum (fun a => a * 2 ^ (M - a - 1)) = 2 ^ M - M - 1 := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h1 | h1
    · -- M = 1 (n = 0): empty sum = 0 = 2^1 - 1 - 1.
      subst h1; decide
    · -- M = n+1 with n ≥ 1. Split off the top index a = n.
      have hn1 : 1 ≤ n := h1
      have hico : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn1]
      rw [hico, Finset.sum_insert (by simp)]
      -- term a = n contributes n * 2^(n+1-n-1) = n * 2^0 = n.
      have hterm : n * 2 ^ (n + 1 - n - 1) = n := by
        rw [show n + 1 - n - 1 = 0 from by omega]; ring
      -- the inner sum re-indexes: 2^(n+1-a-1) = 2 * 2^(n-a-1) for a < n.
      have hshift : (Finset.Ico 1 n).sum (fun a => a * 2 ^ (n + 1 - a - 1))
          = 2 * (Finset.Ico 1 n).sum (fun a => a * 2 ^ (n - a - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_Ico] at ha
        have : n + 1 - a - 1 = (n - a - 1) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [hterm, hshift, ih hn1]
      -- need n + 1 ≤ 2^n so the Nat subtraction behaves.
      have hbound : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
      have hpow : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      rw [hpow]; omega

end CollatzValuationDensity
