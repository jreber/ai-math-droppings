import Propositio.Beal.GoldenIntEuclidean
import Propositio.Beal.GoldenIntUnits
import Propositio.Beal.GoldenIntRamification
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# `√5`-adic valuation theory and fifth-power extraction in `ℤ[φ]`

This is the **valuation / bounded-extraction module** that both prior FLT-5 Case II attempts
(`docs/kb/failed/2026-07-12__…`, `docs/kb/failed/2026-07-18__…`) identified as the genuinely
missing infrastructure: it turns "the norm is divisible by `5ᵏ`" into concrete
`√5`-power / unit-times-fifth-power factorizations of the *element* in `ℤ[φ] = GoldenInt`.

It builds directly on the three existing landed layers and adds nothing that redefines their
types (everything below is about `BealGoldenIntEuclidean.GoldenInt`, the real ring):

* `BealGoldenIntEuclidean` — `GoldenInt`, its `EuclideanDomain` structure (⟹ PID ⟹ UFD ⟹ Bézout).
* `BealGoldenIntUnits` — `phiZpow`, `unit_eq_pm_phiZpow` (every unit is `±φⁿ`),
  `isUnit_iff_norm_eq_one`.
* `BealGoldenIntRamification` — `sqrt5 = 2φ-1`, `prime_sqrt5`, `norm_sqrt5 = -5`,
  `sqrt5_dvd_iff_five_dvd_norm`.

## Main results (proved, axiom-clean, no `sorry`)

### Fifth-power extraction (item (b) of the descent programme)

* `norm_pow` — `norm (z ^ m) = (norm z) ^ m` (the custom `GoldenInt.norm` is multiplicative on
  powers; needed everywhere below).
* `ofInt_pow` — `ofInt (n ^ k) = (ofInt n) ^ k`.
* `unit_mul_pow_of_isCoprime_mul_eq_pow` — **the general coprime-power extraction**: if
  `IsCoprime a b` and `a * b = c ^ k`, then `a = u · dᵏ` for a *unit* `u` and some `d`. This is
  mathlib's `exists_associated_pow_of_mul_eq_pow'` (available because `GoldenInt` is Bézout)
  repackaged into explicit `unit × k-th power` form.
* `pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow` — **item (b) headline, unit pinned**: same
  hypotheses give `a = ±φⁿ · dᵏ` (the unit is pinned to `±φⁿ` via `unit_eq_pm_phiZpow`). This is
  exactly the "pull the residual back to a fifth power up to a unit, then pin the unit" brick
  that `BealGoldenIntCoprime`/`FermatLastTheoremFiveCaseTwoCofactors`' scope notes flagged as
  the open item (b).
* `pm_phiZpow_mul_pow_of_mul_conj_eq_pow` — the specialization the descent actually consumes:
  if `IsCoprime β (conj β)` and `norm β = ± eᵏ` (`k` odd), then `β = ±φⁿ · dᵏ`. (Here
  `β · conj β = ofInt (norm β) = (±ofInt e)ᵏ` is a `k`-th power *because* `β, conj β` are coprime.)

### `√5`-adic valuation (the ramification-lifting / bounded-extraction core)

* `norm_sqrt5_pow_mul` — `norm (√5ᵐ · β) = (-5)ᵐ · norm β` (each `√5` divides the norm by `-5`).
* `exists_sqrt5_adic_decomp` — every `α ≠ 0` factors as `α = √5ᵐ · β` with `√5 ∤ β`
  (equivalently `5 ∤ N(β)`), `m = v_{√5}(α)` the exact `√5`-adic valuation. This is the
  existence half of `√5`-adic valuation theory.
* `five_pow_natAbs_eq` — the `p`-adic injectivity fact over `ℤ` (`p = 5`): `5ᵐ·A = 5ᵏ·B` with
  `5 ∤ A`, `5 ∤ B` forces `m = k`. The engine that pins the valuation to the norm's `5`-power.
* `exists_sqrt5_pow_decomp_of_norm_natAbs` — **the exact-valuation lift**: if
  `(norm α).natAbs = 5ᵏ · t` with `5 ∤ t`, then `α = √5ᵏ · β` with `5 ∤ N(β)` and
  `(norm β).natAbs = t`. Turns a `5`-power in the (integer) norm into the *exact* `√5`-power of
  the element — the "`5ᵏ ∣ N(x) ⟹ v_{√5}(x) = k`" miracle for the ramified prime.

## What this does NOT do (honest scope note)

This is the **reusable valuation + extraction machinery**, built standalone. It does not itself
close the FLT-5 Case II descent: to feed the extraction into the descent one additionally needs
`IsCoprime β (conj β)` for the `√5`-peeled factor `β` (so that `β · conj β` is a genuine fifth
power and `pm_phiZpow_mul_pow_of_mul_conj_eq_pow` applies), which is a coprimality-of-conjugates
statement not established here. `pm_phiZpow_mul_pow_of_mul_conj_eq_pow` isolates exactly that
remaining hypothesis.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

/-! ## `norm` and `ofInt` on powers -/

/-- **`norm (z ^ m) = (norm z) ^ m`.** The custom field norm is multiplicative on powers
(by induction from `norm_mul` / `norm_one`). -/
theorem norm_pow (z : GoldenInt) (m : ℕ) : norm (z ^ m) = (norm z) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, norm_mul, ih]

/-- **`ofInt (n ^ k) = (ofInt n) ^ k`.** The `ℤ`-embedding respects powers. -/
theorem ofInt_pow (n : ℤ) (k : ℕ) : ofInt (n ^ k) = (ofInt n) ^ k := by
  induction k with
  | zero => ext <;> simp [ofInt]
  | succ k ih => rw [pow_succ, pow_succ, ofInt_mul, ih]

/-! ## Fifth-power (general `k`-th power) extraction — item (b) -/

/-- **General coprime-power extraction.** If `a, b` are coprime in `ℤ[φ]` and `a·b = cᵏ`, then
`a = u · dᵏ` for a *unit* `u` and some `d`. Uses mathlib's `exists_associated_pow_of_mul_eq_pow'`
(applicable since `GoldenInt` is a Bézout domain via its `EuclideanDomain`/PID structure) and
unfolds the resulting `Associated` into explicit `unit × power` form. -/
theorem unit_mul_pow_of_isCoprime_mul_eq_pow {a b c : GoldenInt} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ k) : ∃ (u d : GoldenInt), IsUnit u ∧ a = u * d ^ k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  obtain ⟨u, hu⟩ := hd
  exact ⟨(u : GoldenInt), d, u.isUnit, by rw [← hu]; ring⟩

/-- **Item (b) headline — coprime-power extraction with the unit pinned to `±φⁿ`.** If `a, b`
are coprime and `a·b = cᵏ`, then `a = ±φⁿ · dᵏ`. Combines `unit_mul_pow_of_isCoprime_mul_eq_pow`
with `unit_eq_pm_phiZpow` (every unit of `ℤ[φ]` is `±φⁿ`). This is the concrete "unit × fifth
power" extraction the FLT-5 Case II descent needs. -/
theorem pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow {a b c : GoldenInt} (hab : IsCoprime a b)
    {k : ℕ} (h : a * b = c ^ k) :
    ∃ (n : ℤ) (d : GoldenInt), a = phiZpow n * d ^ k ∨ a = -(phiZpow n * d ^ k) := by
  obtain ⟨u, d, hu, ha⟩ := unit_mul_pow_of_isCoprime_mul_eq_pow hab h
  obtain ⟨n, hn⟩ := unit_eq_pm_phiZpow hu
  rcases hn with hn | hn
  · exact ⟨n, d, Or.inl (by rw [ha, hn])⟩
  · exact ⟨n, d, Or.inr (by rw [ha, hn]; ring)⟩

/-- **Item (b) headline, specialized to a self-conjugate norm equation.** If `β` is coprime to
its conjugate and `norm β = ±eᵏ` (`k` odd, so `-(eᵏ) = (-e)ᵏ`), then `β = ±φⁿ · dᵏ`. The point:
`β · conj β = ofInt (norm β) = (±ofInt e)ᵏ` is a genuine `k`-th power (because `β, conj β` are
coprime), so `pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow` applies with `a = β`, `b = conj β`.
This is the exact shape the descent needs on the `√5`-peeled factor. -/
theorem pm_phiZpow_mul_pow_of_mul_conj_eq_pow {β : GoldenInt} {e : ℤ} {k : ℕ} (hk : Odd k)
    (hcop : IsCoprime β (conj β)) (hnorm : norm β = e ^ k ∨ norm β = -(e ^ k)) :
    ∃ (n : ℤ) (d : GoldenInt), β = phiZpow n * d ^ k ∨ β = -(phiZpow n * d ^ k) := by
  have hbc : β * conj β = ofInt (norm β) := mul_conj_eq_ofInt β
  rcases hnorm with hpos | hneg
  · -- norm β = eᵏ : β · conj β = (ofInt e)ᵏ
    have h : β * conj β = (ofInt e) ^ k := by rw [hbc, hpos, ofInt_pow]
    exact pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow hcop h
  · -- norm β = -(eᵏ) = (-e)ᵏ (k odd) : β · conj β = (ofInt (-e))ᵏ
    have hneg' : (-e) ^ k = -(e ^ k) := Odd.neg_pow hk e
    have h : β * conj β = (ofInt (-e)) ^ k := by
      rw [hbc, hneg, ← hneg', ofInt_pow]
    exact pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow hcop h

/-! ## `√5`-adic valuation -/

/-- **`norm (√5ᵐ · β) = (-5)ᵐ · norm β`.** Each factor of `√5` divides the norm by `-5`
(`N(√5) = -5`). -/
theorem norm_sqrt5_pow_mul (m : ℕ) (β : GoldenInt) :
    norm (sqrt5 ^ m * β) = (-5) ^ m * norm β := by
  rw [norm_mul, norm_pow, norm_sqrt5]

/-- **`√5`-adic decomposition (existence).** Every nonzero `α ∈ ℤ[φ]` factors as `α = √5ᵐ · β`
with `√5 ∤ β`, where `m = v_{√5}(α) = multiplicity √5 α`. This is the existence half of the
`√5`-adic valuation on `ℤ[φ]` (via `FiniteMultiplicity` for the prime `√5`). -/
theorem exists_sqrt5_adic_decomp {α : GoldenInt} (hα : α ≠ 0) :
    ∃ (m : ℕ) (β : GoldenInt), α = sqrt5 ^ m * β ∧ ¬ sqrt5 ∣ β := by
  have hfin : FiniteMultiplicity sqrt5 α := FiniteMultiplicity.of_prime_left prime_sqrt5 hα
  obtain ⟨c, hc, hnc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨multiplicity sqrt5 α, c, hc, hnc⟩

/-- `¬ √5 ∣ β ↔ ¬ 5 ∣ N(β)` — the ramified-prime dictionary, contrapositive form. -/
theorem not_five_dvd_norm_iff_not_sqrt5_dvd (β : GoldenInt) :
    ¬ sqrt5 ∣ β ↔ ¬ (5 : ℤ) ∣ norm β := by
  rw [sqrt5_dvd_iff_five_dvd_norm]

/-! ## The `p = 5` `p`-adic injectivity engine over `ℤ` / `ℕ` -/

/-- **`5`-adic injectivity over `ℕ`.** If `5ᵐ·A = 5ᵏ·B` with `5 ∤ A` and `5 ∤ B`, then `m = k`.
(If say `m < k`, cancelling `5ᵐ` gives `A = 5^{k-m}·B`, so `5 ∣ A`, contradiction.) -/
theorem five_pow_natAbs_eq {m k A B : ℕ} (hA : ¬ 5 ∣ A) (hB : ¬ 5 ∣ B)
    (h : 5 ^ m * A = 5 ^ k * B) : m = k := by
  rcases Nat.lt_trichotomy m k with hlt | heq | hgt
  · exfalso
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hlt   -- k = m + j + 1
    apply hA
    have hcancel : A = 5 ^ (j + 1) * B := by
      have hc : 5 ^ m * A = 5 ^ m * (5 ^ (j + 1) * B) := by
        rw [h, hj]; rw [pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) m) hc
    rw [hcancel, pow_succ]
    exact ⟨5 ^ j * B, by ring⟩
  · exact heq
  · exfalso
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hgt   -- m = k + j + 1
    apply hB
    have hcancel : B = 5 ^ (j + 1) * A := by
      have hc : 5 ^ k * B = 5 ^ k * (5 ^ (j + 1) * A) := by
        rw [← h, hj]; rw [pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) hc
    rw [hcancel, pow_succ]
    exact ⟨5 ^ j * A, by ring⟩

/-- `¬ 5 ∣ (N β).natAbs` from `¬ 5 ∣ N β`. -/
theorem not_five_dvd_natAbs_norm {β : GoldenInt} (h : ¬ (5 : ℤ) ∣ norm β) :
    ¬ 5 ∣ (norm β).natAbs :=
  fun hd => h (Int.natAbs_dvd_natAbs.mp hd)

/-- **The exact-valuation lift.** If the (integer) norm of `α` has `|N(α)| = 5ᵏ · t` with
`5 ∤ t`, then `α = √5ᵏ · β` with `√5 ∤ β` (`5 ∤ N(β)`) and `|N(β)| = t`. That is: a `5ᵏ` in
the norm forces the element's `√5`-adic valuation to be *exactly* `k`. This is the ramified-prime
"norm-divisibility ⟹ exact element-valuation" lift, the concrete descent-metric control. -/
theorem exists_sqrt5_pow_decomp_of_norm_natAbs {α : GoldenInt} (hα : α ≠ 0) {k t : ℕ}
    (ht : ¬ 5 ∣ t) (hnorm : (norm α).natAbs = 5 ^ k * t) :
    ∃ β : GoldenInt, α = sqrt5 ^ k * β ∧ ¬ sqrt5 ∣ β ∧ (norm β).natAbs = t := by
  obtain ⟨m, β, hαβ, hβ⟩ := exists_sqrt5_adic_decomp hα
  -- 5 ∤ N(β) since √5 ∤ β
  have h5Nβ : ¬ (5 : ℤ) ∣ norm β := (not_five_dvd_norm_iff_not_sqrt5_dvd β).mp hβ
  have h5Nβ' : ¬ 5 ∣ (norm β).natAbs := not_five_dvd_natAbs_norm h5Nβ
  -- |N(α)| = 5ᵐ · |N(β)|
  have hnormα : norm α = (-5) ^ m * norm β := by rw [hαβ, norm_sqrt5_pow_mul]
  have hnatAbs : (norm α).natAbs = 5 ^ m * (norm β).natAbs := by
    rw [hnormα, Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  -- 5ᵐ · |N(β)| = 5ᵏ · t, with both cofactors coprime to 5 ⟹ m = k
  have heq : 5 ^ m * (norm β).natAbs = 5 ^ k * t := by rw [← hnatAbs, hnorm]
  have hmk : m = k := five_pow_natAbs_eq h5Nβ' ht heq
  subst hmk
  have htβ : (norm β).natAbs = t :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) m) heq
  exact ⟨β, hαβ, hβ, htβ⟩

end GoldenInt

section AxiomCheck
open GoldenInt
#print axioms norm_pow
#print axioms ofInt_pow
#print axioms unit_mul_pow_of_isCoprime_mul_eq_pow
#print axioms pm_phiZpow_mul_pow_of_isCoprime_mul_eq_pow
#print axioms pm_phiZpow_mul_pow_of_mul_conj_eq_pow
#print axioms norm_sqrt5_pow_mul
#print axioms exists_sqrt5_adic_decomp
#print axioms five_pow_natAbs_eq
#print axioms exists_sqrt5_pow_decomp_of_norm_natAbs
end AxiomCheck
