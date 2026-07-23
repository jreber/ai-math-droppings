/-
# `seven_pid`: the ring of integers of ℚ(ζ₇) is a principal ideal ring.

This file proves that `𝓞 ℚ(ζ₇)` is a PID (equivalently, class number 1), the
key missing input that unlocks the general `(p, p, z)` cyclotomic descent at
`p = 7` (`BealCyclotomicDescent.beal_ppz_structure_gen`).

## Why this is harder than `p = 3, 5`
Mathlib's `three_pid` / `five_pid` use
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, which needs the Minkowski
bound to be `< ~2`. For ℚ(ζ₇) the Minkowski bound is

  `M = (4/π)³ · (6! / 6⁶) · √|disc| ≈ 4.13`,

so that crude criterion does NOT apply. Instead we use the finer Galois criterion
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`:
to show `𝓞 K` is a PID it suffices that for every prime `p ≤ ⌊M K⌋₊` there is a
prime ideal `P` above `p` with `⌊M K⌋₊ < p ^ (inertiaDeg P)` (or `P` principal).

## The arithmetic that makes it work
- `|disc ℚ(ζ₇)| = 7⁵ = 16807`, `finrank = 6`, `nrComplexPlaces = 3`.
- `⌊M K⌋₊ = 4`.
- The only primes `p ≤ 4` are `p = 2, 3`. Since `7 ∤ 2, 3`, the inertia degree of
  any prime above `p` equals `orderOf (p : ZMod 7)`
  (`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`):
    * `orderOf (2 : ZMod 7) = 3`  ⟹  `2³ = 8 > 4`;
    * `orderOf (3 : ZMod 7) = 6`  ⟹  `3⁶ = 729 > 4`.
  So the left disjunct `⌊M K⌋₊ < p ^ inertiaDeg P` holds for both primes.

All kept theorems are axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Propositio.Beal.CyclotomicDescent

universe u

namespace IsCyclotomicExtension.Rat.Seven

open NumberField Polynomial InfinitePlace Ideal Nat Real cyclotomic Module

variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]

/-- `Fact (Nat.Prime 7)`, needed by the cyclotomic API. -/
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ## Numerical invariants of ℚ(ζ₇) -/

/-- The discriminant of `ℚ(ζ₇)` is `-7⁵ = -16807`. -/
theorem discr_seven : NumberField.discr K = -16807 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 7 K]; norm_num

/-- `finrank ℚ ℚ(ζ₇) = 6`. -/
theorem finrank_seven : Module.finrank ℚ K = 6 := by
  rw [IsCyclotomicExtension.finrank (n := 7) K (irreducible_rat (by decide))]; decide

/-- `nrComplexPlaces ℚ(ζ₇) = 3` (`ℚ(ζ₇)` is totally complex of degree 6). -/
theorem nrComplexPlaces_seven : nrComplexPlaces K = 3 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 7]; decide

/-! ## The Minkowski bound floor -/

/-- The floor of the Minkowski bound of `ℚ(ζ₇)` is `4`:
`⌊(4/π)³ · (6!/6⁶) · √16807⌋ = 4` (the bound itself is `≈ 4.13`). This is the
exact `M K` expression appearing in mathlib's Galois class-number-1 criterion
`isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`. -/
theorem minkowski_floor :
    ⌊((4 / π) ^ nrComplexPlaces K *
      ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        √|(NumberField.discr K : ℝ)|))⌋₊ = 4 := by
  rw [nrComplexPlaces_seven K, finrank_seven K, discr_seven K]
  have h6 : ((6 : ℕ)! : ℝ) = 720 := by norm_num [Nat.factorial]
  have habs : |((-16807 : ℤ) : ℝ)| = 16807 := by norm_num
  rw [h6, habs]
  -- `129.64 < √16807 < 129.65`
  have hsL : (129.64 : ℝ) < √16807 := by
    rw [show (129.64 : ℝ) = √(129.64 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hsU : √16807 < (129.65 : ℝ) := by
    rw [show (129.65 : ℝ) = √(129.65 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hs : (0 : ℝ) < √16807 := by positivity
  -- `3.1415 < π < 3.1416`
  have hpiL : (3.1415 : ℝ) < π := pi_gt_d4
  have hpiU : π < (3.1416 : ℝ) := pi_lt_d4
  have hpi : (0 : ℝ) < π := pi_pos
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨?_, ?_⟩
  · show (4 : ℝ) ≤ _
    rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hpi 3, mul_pos (mul_pos hpi hpi) hpi, hpiU, hpiL, hsL, hsU,
      mul_pos hpi hpi]
  · show _ < ((4 : ℕ) + 1 : ℝ)
    rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [pow_pos hpi 3, mul_pos (mul_pos hpi hpi) hpi, hpiU, hpiL, hsL, hsU,
      mul_pos hpi hpi]

/-! ## Residue degrees of the small primes -/

/-- `orderOf (2 : ZMod 7) = 3` (the residue degree of any prime above `2` in
`ℚ(ζ₇)`). -/
theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m hm hpos => by interval_cases m <;> decide⟩

/-- `orderOf (3 : ZMod 7) = 6` (`3` is a primitive root mod `7`; the residue degree
of any prime above `3` in `ℚ(ζ₇)`). -/
theorem orderOf_three_zmod_seven : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m hm hpos => by interval_cases m <;> decide⟩

/-! ## The main result -/

/-- **`seven_pid`.** The ring of integers of `ℚ(ζ₇)` is a principal ideal ring
(class number 1).

Proof via the Galois Minkowski criterion: `⌊M K⌋₊ = 4`, the only primes `≤ 4` are
`2` and `3`, both coprime to `7`, and the residue degree of any prime above `p`
equals `orderOf (p : ZMod 7)` — giving `2³ = 8 > 4` and `3⁶ = 729 > 4`, so the left
disjunct of the criterion holds for every relevant prime. -/
theorem seven_pid : IsPrincipalIdealRing (𝓞 K) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  rw [minkowski_floor K]
  intro p hp hpp
  -- `p ∈ Finset.Icc 1 4` and `p.Prime`, so `p = 2` or `p = 3`.
  rw [Finset.mem_Icc] at hp
  obtain ⟨hp1, hp4⟩ := hp
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  -- `span {p}` is a prime ideal of `ℤ` (since `p` is prime), so it has a prime above it.
  haveI hpr : (span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hpp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hpp
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, ⟨hP1, hP2⟩, Or.inl ?_⟩
  -- Reduce to the concrete primes `2` and `3` (cases `1, 4` are not prime).
  interval_cases p
  · exact absurd hpp (by decide)
  · -- `p = 2`: residue degree is `orderOf (2 : ZMod 7) = 3`, so `2³ = 8 > 4`.
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by decide)]
    norm_num [orderOf_two_zmod_seven]
  · -- `p = 3`: residue degree is `orderOf (3 : ZMod 7) = 6`, so `3⁶ = 729 > 4`.
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by decide)]
    norm_num [orderOf_three_zmod_seven]
  · exact absurd hpp (by decide)

/-! ## The unlock: the `(7, 7, z)` structure theorem

With `seven_pid` in hand, the general cyclotomic descent engine
`BealCyclotomicDescent.beal_ppz_structure_gen` applies at `p = 7`, recovering the
`(7, 7, z)` per-prime structure theorem as a one-line corollary — exactly mirroring
the `p = 3` / `p = 5` instances `beal_33z_structure_inst` / `beal_55z_structure_inst`. -/

/-- **The `p = 7` instance.** If `A ^ 7 + B ^ 7 = C ^ z` with `A, B` coprime,
`7 ∤ (A + B)`, and `z ≠ 0`, then `A + B` is a perfect `z`-th power and the
cyclotomic factor `A + B·ζ₇` is associated to a `z`-th power in `𝓞 ℚ(ζ₇)`.
The PID hypothesis of the general engine `beal_ppz_structure_gen` is discharged by
`seven_pid` (class number 1 of `ℚ(ζ₇)`). One line. -/
theorem beal_77z_structure
    {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h7 : ¬ 7 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := seven_pid K
  exact BealCyclotomicDescent.beal_ppz_structure_gen (by decide) hζ hAB h7 hz h

end IsCyclotomicExtension.Rat.Seven
