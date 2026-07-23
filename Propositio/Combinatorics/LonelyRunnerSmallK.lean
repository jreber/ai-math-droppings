/-
# The Lonely Runner Conjecture: the elementary small-`k` cases

The Lonely Runner Conjecture concerns `k` runners on a unit-circumference circular
track, all starting at the origin at time `0` and running forever at distinct
constant speeds.  A runner is *lonely* at time `t` if every other runner is at
circular distance `≥ 1/k` from it.  The conjecture asserts that each runner is
lonely at some time.

By the standard reduction (subtract the speed of the runner we focus on, fixing it
at the origin), the statement for `k` runners becomes: given `k - 1` distinct nonzero
speeds `v₁, …, v_{k-1}`, there is a time `t` with `‖vᵢ · t‖ ≥ 1/k` for all `i`, where
`‖·‖` is the distance to the nearest integer.

This file proves the two elementary base cases for **integer speeds** (the standard
hardest formalization), with the genuine bound `1/k`:

* `lonely_runner_two`  — `k = 2` (one nonzero speed), bound `1/2`.  Warm-up.
* `lonely_runner_three` — `k = 3` (two nonzero speeds), bound `1/3`.  The first
  *nontrivial* case.

The `k = 3` proof is the real content.  After reducing to two **coprime positive**
speeds `a₀, b₀` (handling signs via `‖-x‖ = ‖x‖` and a common factor by rescaling
time), set `s = a₀ + b₀ ≥ 3` and pick `t = m / s` on the lattice `(1/s)ℤ`.  Because
`b₀ ≡ -a₀ (mod s)`, both runners sit at the *same* nearest-integer distance
`‖a₀ m / s‖`.  As `a₀` is invertible mod `s`, choosing `m` with `a₀ m ≡ k (mod s)`
for any `k ∈ [s/3, 2s/3]` (such an integer exists since the interval has length
`s/3 ≥ 1`) gives both distances `≥ 1/3`.

The nearest-integer distance is the genuine `nid x = |x - round x|`, reusing
mathlib's `round` and `abs_sub_round_eq_min`.
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

namespace LonelyRunnerSmallK

/-- Distance from `x` to the nearest integer: `‖x‖ = |x - round x|`.
This is the genuine nearest-integer distance (`round` rounds to the nearest integer),
and equals `min (fract x) (1 - fract x)` by `abs_sub_round_eq_min`. -/
noncomputable def nid (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- `nid` as a minimum of fractional-part data. -/
lemma nid_eq (x : ℝ) : nid x = min (Int.fract x) (1 - Int.fract x) := by
  unfold nid
  exact abs_sub_round_eq_min x

/-- The nearest-integer distance is even. -/
lemma nid_neg (x : ℝ) : nid (-x) = nid x := by
  rw [nid_eq, nid_eq]
  by_cases h : Int.fract x = 0
  · simp [Int.fract_neg_eq_zero.mpr h, h]
  · rw [Int.fract_neg h, sub_sub_cancel]
    exact min_comm _ _

/-- `nid (v · t)` depends only on `|v|`. -/
lemma nid_natAbs_mul (v : ℤ) (t : ℝ) : nid ((v : ℝ) * t) = nid ((v.natAbs : ℝ) * t) := by
  have h := Int.natAbs_eq v
  set N := v.natAbs with hN
  rcases h with h | h
  · -- v = N
    have e : (v : ℝ) = (N : ℝ) := by rw [h]; push_cast; ring
    rw [e]
  · -- v = -N
    have e : (v : ℝ) = -(N : ℝ) := by rw [h]; push_cast; ring
    rw [e, neg_mul, nid_neg]

/-- Nearest-integer distance of a rational `m / n` is `≥ 1/3` whenever its residue
`r = m mod n` lies in `[n/3, 2n/3]`. -/
lemma nid_ge_of_residue (m : ℤ) (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : m % (n : ℤ) = r) (h1 : (n : ℝ) ≤ 3 * (r : ℝ)) (h2 : 3 * (r : ℝ) ≤ 2 * (n : ℝ)) :
    (1 : ℝ) / 3 ≤ nid ((m : ℝ) / (n : ℝ)) := by
  rw [nid_eq, Int.fract_div_intCast_eq_div_intCast_mod, hr]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (1 : ℝ) / 3 ≤ (r : ℝ) / n := by
    rw [le_div_iff₀ hn']; linarith
  have e2 : (r : ℝ) / n ≤ 2 / 3 := by
    rw [div_le_iff₀ hn']; linarith
  exact le_min e1 (by linarith)

/-- `nid (1/3) ≥ 1/3`. -/
lemma nid_one_third : (1 : ℝ) / 3 ≤ nid (1 / 3) := by
  have e : ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ) = (1 : ℝ) / 3 := by norm_num
  have h := nid_ge_of_residue 1 3 (by norm_num) 1 (by norm_num) (by norm_num) (by norm_num)
  rw [e] at h
  exact h

/-- **Core construction (coprime case).** For coprime positive distinct integers
`a₀, b₀`, there is a time `t` making both runners at distance `≥ 1/3`. -/
lemma core (a₀ b₀ : ℕ) (ha : 1 ≤ a₀) (hb : 1 ≤ b₀) (hne : a₀ ≠ b₀)
    (hcop : Nat.Coprime a₀ b₀) :
    ∃ t : ℝ, (1 : ℝ) / 3 ≤ nid ((a₀ : ℝ) * t) ∧ (1 : ℝ) / 3 ≤ nid ((b₀ : ℝ) * t) := by
  have hs3 : 3 ≤ a₀ + b₀ := by omega
  set s : ℕ := a₀ + b₀ with hsdef
  set k : ℕ := (s + 2) / 3 with hkdef
  have hk1 : s ≤ 3 * k := by rw [hkdef]; omega
  have hk2 : 3 * k ≤ 2 * s := by rw [hkdef]; omega
  have hks : k < s := by rw [hkdef]; omega
  have hkpos : 1 ≤ k := by rw [hkdef]; omega
  -- `a₀` is coprime to `s = a₀ + b₀`.
  have hcopAS : Nat.Coprime a₀ s := by
    rw [hsdef]
    have h := (Nat.coprime_add_self_right (m := a₀) (n := b₀)).mpr hcop
    rwa [Nat.add_comm b₀ a₀] at h
  have hgcd : Int.gcd (a₀ : ℤ) (s : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hcopAS
  -- Bézout: `1 = a₀ · x + s · y`.
  have hbez : (1 : ℤ) = (a₀ : ℤ) * Int.gcdA (a₀ : ℤ) (s : ℤ)
      + (s : ℤ) * Int.gcdB (a₀ : ℤ) (s : ℤ) := by
    have h := Int.gcd_eq_gcd_ab (a₀ : ℤ) (s : ℤ)
    rw [hgcd] at h
    exact_mod_cast h
  set x : ℤ := Int.gcdA (a₀ : ℤ) (s : ℤ) with hxdef
  set y : ℤ := Int.gcdB (a₀ : ℤ) (s : ℤ) with hydef
  have hax : (a₀ : ℤ) * x = 1 - (s : ℤ) * y := by linarith [hbez]
  set m : ℤ := (k : ℤ) * x with hmdef
  have hk0Z : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hksZ : (k : ℤ) < (s : ℤ) := by exact_mod_cast hks
  -- Residue of runner `a₀`: `a₀ · m ≡ k (mod s)`.
  have hresa : (a₀ : ℤ) * m % (s : ℤ) = (k : ℤ) := by
    have e : (a₀ : ℤ) * m = (k : ℤ) + (s : ℤ) * (-((k : ℤ) * y)) := by
      rw [hmdef]
      have hcomm : (a₀ : ℤ) * ((k : ℤ) * x) = (k : ℤ) * ((a₀ : ℤ) * x) := by ring
      rw [hcomm, hax]; ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hk0Z hksZ]
  -- Residue of runner `b₀`: `b₀ · m ≡ s - k (mod s)`.
  have hresb : (b₀ : ℤ) * m % (s : ℤ) = (s : ℤ) - (k : ℤ) := by
    have hbZ : (b₀ : ℤ) = (s : ℤ) - (a₀ : ℤ) := by rw [hsdef]; push_cast; ring
    have e : (b₀ : ℤ) * m = (-(k : ℤ)) + (s : ℤ) * ((k : ℤ) * x + (k : ℤ) * y) := by
      rw [hbZ, hmdef]; linear_combination (-(k : ℤ)) * hax
    rw [e, Int.add_mul_emod_self_left]
    have e2 : (-(k : ℤ)) = ((s : ℤ) - (k : ℤ)) + (s : ℤ) * (-1) := by ring
    rw [e2, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  have hk1r : (s : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hk1
  have hk2r : 3 * (k : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hk2
  refine ⟨(m : ℝ) / (s : ℝ), ?_, ?_⟩
  · have hcast : (a₀ : ℝ) * ((m : ℝ) / (s : ℝ)) = (((a₀ : ℤ) * m : ℤ) : ℝ) / (s : ℝ) := by
      push_cast; ring
    rw [hcast]
    exact nid_ge_of_residue ((a₀ : ℤ) * m) s (by omega) (k : ℤ) hresa
      (by exact_mod_cast hk1) (by exact_mod_cast hk2)
  · have hcast : (b₀ : ℝ) * ((m : ℝ) / (s : ℝ)) = (((b₀ : ℤ) * m : ℤ) : ℝ) / (s : ℝ) := by
      push_cast; ring
    rw [hcast]
    refine nid_ge_of_residue ((b₀ : ℤ) * m) s (by omega) ((s : ℤ) - (k : ℤ)) hresb ?_ ?_
    · push_cast; linarith [hk2r]
    · push_cast; linarith [hk1r]

/-- **Two distinct positive speeds.** Reduce by the gcd to the coprime `core`. -/
lemma core' (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hne : a ≠ b) :
    ∃ t : ℝ, (1 : ℝ) / 3 ≤ nid ((a : ℝ) * t) ∧ (1 : ℝ) / 3 ≤ nid ((b : ℝ) * t) := by
  obtain ⟨d, a₀, b₀, hd, hda, hdb, hcop⟩ :
      ∃ d a₀ b₀, 0 < d ∧ a = d * a₀ ∧ b = d * b₀ ∧ Nat.Coprime a₀ b₀ := by
    have hd0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
    exact ⟨Nat.gcd a b, a / Nat.gcd a b, b / Nat.gcd a b, hd0,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm,
      Nat.coprime_div_gcd_div_gcd hd0⟩
  have ha0 : 1 ≤ a₀ := by
    rcases Nat.eq_zero_or_pos a₀ with h | h
    · rw [h, Nat.mul_zero] at hda; omega
    · exact h
  have hb0 : 1 ≤ b₀ := by
    rcases Nat.eq_zero_or_pos b₀ with h | h
    · rw [h, Nat.mul_zero] at hdb; omega
    · exact h
  have hne0 : a₀ ≠ b₀ := by
    intro h; apply hne; rw [hda, hdb, h]
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨t₀, h1c, h2c⟩ := core a₀ b₀ ha0 hb0 hne0 hcop
  refine ⟨t₀ / (d : ℝ), ?_, ?_⟩
  · have e : (a : ℝ) * (t₀ / (d : ℝ)) = (a₀ : ℝ) * t₀ := by
      rw [hda]; push_cast; field_simp
    rw [e]; exact h1c
  · have e : (b : ℝ) * (t₀ / (d : ℝ)) = (b₀ : ℝ) * t₀ := by
      rw [hdb]; push_cast; field_simp
    rw [e]; exact h2c

/-- **Lonely Runner, `k = 2` (warm-up).** One nonzero integer speed `v`: there is a
time `t` with nearest-integer distance `‖v · t‖ ≥ 1/2`.  Witness `t = 1 / (2v)`. -/
theorem lonely_runner_two (v : ℤ) (hv : v ≠ 0) :
    ∃ t : ℝ, (1 : ℝ) / 2 ≤ nid ((v : ℝ) * t) := by
  have hvR : (v : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hv
  refine ⟨1 / (2 * (v : ℝ)), ?_⟩
  have hval : (v : ℝ) * (1 / (2 * (v : ℝ))) = 1 / 2 := by field_simp
  rw [hval]
  have hnid : nid ((1 : ℝ) / 2) = 1 / 2 := by
    unfold nid
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, round_two_inv]
    norm_num
  rw [hnid]

/-- **Lonely Runner, `k = 3` (first nontrivial case).** Two distinct nonzero integer
speeds `v₁, v₂`: there is a time `t` with `‖v₁ · t‖ ≥ 1/3` and `‖v₂ · t‖ ≥ 1/3`. -/
theorem lonely_runner_three (v1 v2 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h12 : v1 ≠ v2) :
    ∃ t : ℝ, (1 : ℝ) / 3 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 3 ≤ nid ((v2 : ℝ) * t) := by
  have ha1 : 1 ≤ v1.natAbs := by
    have : v1.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h1
    omega
  have hb1 : 1 ≤ v2.natAbs := by
    have : v2.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using h2
    omega
  suffices key : ∃ t : ℝ, (1 : ℝ) / 3 ≤ nid ((v1.natAbs : ℝ) * t)
      ∧ (1 : ℝ) / 3 ≤ nid ((v2.natAbs : ℝ) * t) by
    obtain ⟨t, hta, htb⟩ := key
    refine ⟨t, ?_, ?_⟩
    · rw [nid_natAbs_mul]; exact hta
    · rw [nid_natAbs_mul]; exact htb
  by_cases hab : v1.natAbs = v2.natAbs
  · -- Equal magnitudes: both runner conditions coincide; use `t = 1/(3·|v₁|)`.
    have hAR : (v1.natAbs : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨1 / (3 * (v1.natAbs : ℝ)), ?_, ?_⟩
    · have hval : (v1.natAbs : ℝ) * (1 / (3 * (v1.natAbs : ℝ))) = 1 / 3 := by field_simp
      rw [hval]; exact nid_one_third
    · have hval : (v2.natAbs : ℝ) * (1 / (3 * (v1.natAbs : ℝ))) = 1 / 3 := by
        rw [← hab]; field_simp
      rw [hval]; exact nid_one_third
  · -- Distinct magnitudes: the genuine `core'` construction.
    exact core' v1.natAbs v2.natAbs ha1 hb1 hab

end LonelyRunnerSmallK
