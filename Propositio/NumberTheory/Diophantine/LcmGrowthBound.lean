import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# An explicit exponential upper bound on `lcm(1, …, n)`

The single arithmetic brick missing from mathlib for effective-irrationality-measure
(Padé / Legendre-integral) constructions: an explicit `lcm(1..n) ≤ Cⁿ`.

`log(lcm(1..n)) = ψ(n)` (the Chebyshev `ψ` function `∑_{m ≤ n} Λ(m)`), and mathlib's
`Chebyshev.psi_le_const_mul_self` gives `ψ(n) ≤ (log 4 + 4)·n`.  Exponentiating yields

  `lcm(1..n) ≤ exp((log 4 + 4)·n) = (4·e⁴)ⁿ`.

The constant `4e⁴ ≈ 218` is far from the truth `(lcm(1..n))^{1/n} → e`, but it is **finite
and explicit**, which is all the downstream construction needs (any finite denominator
growth rate yields a finite irrationality measure).
-/

open Finset ArithmeticFunction

namespace LcmGrowthBound

/-- `lcm(1, …, n)` as a natural number: the `Finset.lcm` of `Icc 1 n` under the identity. -/
noncomputable def lcmUpto (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm _root_.id

theorem lcmUpto_ne_zero (n : ℕ) : lcmUpto n ≠ 0 := by
  rw [lcmUpto, Finset.lcm_ne_zero_iff]
  intro x hx
  simp only [_root_.id, Finset.mem_Icc] at *
  omega

/-- `p`-adic valuation of `Finset.lcm` is the sup of the valuations of the members. -/
theorem factorization_finsetLcm_apply (p : ℕ) {s : Finset ℕ} (hs : ∀ m ∈ s, m ≠ 0) :
    ((s.lcm _root_.id).factorization) p = s.sup (fun m => m.factorization p) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hane : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ m ∈ s, m ≠ 0 := fun m hm => hs m (Finset.mem_insert_of_mem hm)
    have hslcm : s.lcm _root_.id ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]; exact hs'
    rw [Finset.lcm_insert, Finset.sup_insert, ← ih hs']
    -- `Finset.lcm_insert` gives `GCDMonoid.lcm (id a) (s.lcm id)`; reduce to `Nat.lcm`.
    show ((Nat.lcm a (s.lcm _root_.id)).factorization) p = _
    rw [Nat.factorization_lcm hane hslcm]
    simp [Finsupp.sup_apply]

/-- **The bridge.**  For a prime power `q`, `q ∣ lcm(1..n) ↔ q ≤ n`. -/
theorem primePow_dvd_lcmUpto_iff {q n : ℕ} (hq : IsPrimePow q) :
    q ∣ lcmUpto n ↔ q ≤ n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have hpprime : p.Prime := hp
  have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow k p hpprime.pos
  constructor
  · intro hdvd
    -- p^k ∣ lcm ⟹ factorization at p ≥ k ⟹ some member m has p^k ∣ m ⟹ p^k ≤ m ≤ n
    have hkle : k ≤ (lcmUpto n).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpprime (lcmUpto_ne_zero n)).mp hdvd
    rw [lcmUpto, factorization_finsetLcm_apply p (s := Finset.Icc 1 n)
        (by intro m hm; simp only [Finset.mem_Icc] at hm; omega)] at hkle
    have hk0 : (⊥ : ℕ) < k := by simp only [Nat.bot_eq_zero]; omega
    obtain ⟨m, hm, hmf⟩ := (Finset.le_sup_iff hk0).mp hkle
    simp only [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have hdvdm : p ^ k ∣ m := (Nat.Prime.pow_dvd_iff_le_factorization hpprime hm0).mpr hmf
    have : p ^ k ≤ m := Nat.le_of_dvd (by omega) hdvdm
    omega
  · intro hle
    have hmem : p ^ k ∈ Finset.Icc 1 n := by
      rw [Finset.mem_Icc]; exact ⟨hpk1, hle⟩
    have := Finset.dvd_lcm (f := _root_.id) hmem
    simpa [_root_.id] using this

/-- **lcm-clearing divisibility.**  Every `1 ≤ m ≤ n` divides `lcm(1..n)` — so it clears a
denominator `m` (used for the `(k−n) ∣ lcm(1..n)` step of the Legendre linear form, `|k−n| ≤ n`). -/
theorem dvd_lcmUpto {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : m ∣ lcmUpto n := by
  have hmem : m ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hm, hmn⟩
  simpa using Finset.dvd_lcm (f := _root_.id) hmem

/-- **The keystone identity.** `log(lcm(1..n)) = ψ(n)`, the Chebyshev function. -/
theorem log_lcmUpto_eq_psi (n : ℕ) :
    Real.log (lcmUpto n) = Chebyshev.psi n := by
  classical
  have hv : Real.log (lcmUpto n) = ∑ d ∈ (lcmUpto n).divisors, Λ d := vonMangoldt_sum.symm
  rw [hv, Chebyshev.psi, Nat.floor_natCast]
  -- Both sums collapse onto prime powers; the prime-power index sets coincide by the bridge.
  have hset : (lcmUpto n).divisors.filter IsPrimePow = (Finset.Ioc 0 n).filter IsPrimePow := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hpp⟩
      exact ⟨⟨hpp.pos, (primePow_dvd_lcmUpto_iff hpp).mp hdvd⟩, hpp⟩
    · rintro ⟨⟨hpos, hle⟩, hpp⟩
      exact ⟨⟨(primePow_dvd_lcmUpto_iff hpp).mpr hle, lcmUpto_ne_zero n⟩, hpp⟩
  have hL : ∑ d ∈ (lcmUpto n).divisors with IsPrimePow d, Λ d
      = ∑ d ∈ (lcmUpto n).divisors, Λ d :=
    Finset.sum_filter_of_ne (fun x _ hx => vonMangoldt_ne_zero_iff.mp hx)
  have hR : ∑ d ∈ Finset.Ioc 0 n with IsPrimePow d, Λ d = ∑ d ∈ Finset.Ioc 0 n, Λ d :=
    Finset.sum_filter_of_ne (fun x _ hx => vonMangoldt_ne_zero_iff.mp hx)
  rw [← hL, ← hR, hset]

/-- **The explicit exponential bound.** `lcm(1..n) ≤ exp((log 4 + 4)·n) = (4e⁴)ⁿ`. -/
theorem lcmUpto_le (n : ℕ) :
    (lcmUpto n : ℝ) ≤ Real.exp ((Real.log 4 + 4) * n) := by
  have h1 : Real.log (lcmUpto n) ≤ (Real.log 4 + 4) * n := by
    rw [log_lcmUpto_eq_psi]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  have h2 : (0 : ℝ) < lcmUpto n := by
    exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero n)
  calc (lcmUpto n : ℝ) = Real.exp (Real.log (lcmUpto n)) := (Real.exp_log h2).symm
    _ ≤ Real.exp ((Real.log 4 + 4) * n) := Real.exp_le_exp.mpr h1

/-- **The sharp (fit-for-purpose) bound.**  `log(lcm(1..n)) ≤ log 4 · n + 2·√n·log n`, i.e.
`lcm(1..n) ≤ 4ⁿ · exp(2√n·log n)`.  The leading constant is `4` (`= exp(log 4)`), the genuine
Chebyshev main term, with only a sub-exponential `exp(2√n log n)` correction.

This is the version the Padé/Legendre-integral construction actually needs: with the diagonal
integral `Iₙ ≤ (√2−1)^{2n}`, the linear forms `dₙ·Iₙ` decay like `(4·(√2−1)²)ⁿ·exp(2√n log n)`
and `4·(√2−1)² ≈ 0.686 < 1`, so they tend to `0` — whereas the cruder `(4e⁴)ⁿ` bound
(`lcmUpto_le`) gives `218·0.172 ≈ 37 > 1` and is *too weak to drive the construction*.  (For
the application one feeds `Q = 4 + ε` to the combination criterion, absorbing the
sub-exponential factor.) -/
theorem log_lcmUpto_le_sharp (n : ℕ) (hn : 1 ≤ n) :
    Real.log (lcmUpto n) ≤ Real.log 4 * n + 2 * Real.sqrt n * Real.log n := by
  rw [log_lcmUpto_eq_psi]
  exact Chebyshev.psi_le (by exact_mod_cast hn)

end LcmGrowthBound
