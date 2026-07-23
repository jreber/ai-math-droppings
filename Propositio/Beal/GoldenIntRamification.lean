import Propositio.Beal.GoldenIntEuclidean
import Propositio.Beal.GoldenIntUnits
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic

/-!
# Ramification of `5` and `√5`-adic divisibility in `ℤ[φ]`

`BealGoldenIntEuclidean.lean` builds the ring of integers `ℤ[φ] = 𝓞(ℚ(√5))` as its own type
`GoldenInt` (`φ² = φ + 1`, norm `N(a+bφ) = a²+ab-b²`) and proves it a full `EuclideanDomain`.
`BealGoldenIntUnits.lean` proves every unit of `GoldenInt` is `±φⁿ` and that
`IsUnit z ↔ N(z) = ±1`.

This file supplies the **divisibility / ramification layer** that the FLT-5 Case II infinite
descent needs and that the two prior Case-II attempts
(`docs/kb/failed/2026-07-12__…`, `docs/kb/failed/2026-07-18__…`) identified as the actual
blocker: the concrete behaviour of the ramified rational prime `5` in `ℤ[φ]`.

Because `GoldenInt` is a Euclidean domain, mathlib's instance chain
(`EuclideanDomain → IsDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid`) gives it
unique factorization *for free*; the content here is the **arithmetic of the specific prime
`√5 = 2φ − 1`**, which no general machinery provides:

## Main results (proved, axiom-clean, no `sorry`)

* `GoldenInt.sqrt5 : GoldenInt` — the element `√5 = 2φ − 1 = ⟨-1, 2⟩`, and the basic identities
  `sqrt5_sq : sqrt5 * sqrt5 = ofInt 5` (so `5 = √5²` **on the nose**, unit `= 1` — the
  ramification `(5) = (√5)²`), `norm_sqrt5 : norm sqrt5 = -5`, `conj_sqrt5 : conj sqrt5 = -sqrt5`
  (`√5` is anti-fixed by the Galois conjugation, as it must be).
* `GoldenInt.irreducible_of_norm_natAbs_prime` / `GoldenInt.prime_of_norm_natAbs_prime` — the
  general "prime norm ⟹ irreducible ⟹ prime" fact for `GoldenInt` (an element whose norm has
  prime absolute value is a prime element), the reusable engine behind everything below.
* `GoldenInt.irreducible_sqrt5`, `GoldenInt.prime_sqrt5` — `√5` is a prime element of `ℤ[φ]`.
* `GoldenInt.five_dvd_norm_of_sqrt5_dvd` and `GoldenInt.sqrt5_dvd_of_five_dvd_norm`, packaged as
  `GoldenInt.sqrt5_dvd_iff_five_dvd_norm : sqrt5 ∣ α ↔ (5 : ℤ) ∣ norm α` — **the key
  norm-divisibility → element-divisibility lift** for the ramified prime. This is item (3) of the
  dispatch: lifting `5 ∣ N(α)` to `√5 ∣ α`. The forward direction is easy; the hard direction
  uses `ofInt (N α) = α · conj α`, `5 = √5²`, primality of `√5`, and `conj √5 = -√5`.
* `GoldenInt.sqrt5_sq_dvd_iff_five_dvd` : `sqrt5^2 ∣ α ↔ ofInt 5 ∣ α` (both say the same thing).
* `GoldenInt.sqrt5_valuation_one_of_five_dvd_norm_not_25` — **the exact-`√5`-valuation lemma**:
  if `5 ∣ N(α)` but `25 ∤ N(α)`, then `√5 ∣ α` while `√5² ∤ α`, i.e. `v_{√5}(α) = 1` exactly.
  This is the concrete `√5`-valuation control the descent uses on the `N(α) = ∓5·e⁵`, `5 ∤ e`
  case of `FermatLastTheoremFiveCaseTwo.case2_norm_eq`.

## What this does NOT do (honest scope note)

This is the ramification + single-prime-valuation layer only. It does **not** yet assemble the
full FLT-5 Case II descent: that additionally needs (a) coprimality of the two concrete factors
`a₁+bφ`, `a₂+bφ` of `case2_norm_eq` away from `√5`, and (b) the "unit × fifth power" extraction
(`N(α) = ±5^k·e⁵` with the `√5`-part peeled ⟹ residual is a fifth power up to a unit, then pin
the unit via `BealGoldenIntUnits.unit_eq_pm_phiZpow`). Those are the remaining bricks.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

/-! ## `ofInt` is multiplicative and respects divisibility -/

/-- `ofInt` is multiplicative: `ofInt (m·n) = ofInt m · ofInt n`. -/
theorem ofInt_mul (m n : ℤ) : ofInt (m * n) = ofInt m * ofInt n := by
  ext <;> simp [ofInt]

/-- The norm of a rational integer `ofInt n` is `n²`. -/
@[simp] theorem norm_ofInt (n : ℤ) : norm (ofInt n) = n ^ 2 := by
  simp [norm, ofInt]

/-- `ofInt` carries `ℤ`-divisibility into `GoldenInt`-divisibility. -/
theorem ofInt_dvd_ofInt {m n : ℤ} (h : m ∣ n) : ofInt m ∣ ofInt n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨ofInt k, by rw [ofInt_mul]⟩

/-! ## Prime-norm ⟹ prime element (the reusable engine) -/

/-- An element whose norm is `±1` is a unit — the easy half of `isUnit_iff_norm_eq_one`
repackaged for the `natAbs` form used below. -/
theorem isUnit_of_norm_natAbs_one {z : GoldenInt} (h : (norm z).natAbs = 1) : IsUnit z := by
  rw [isUnit_iff_norm_eq_one]
  omega

/-- The norm's absolute value is multiplicative on `ℕ`. -/
theorem norm_natAbs_mul (z w : GoldenInt) :
    (norm (z * w)).natAbs = (norm z).natAbs * (norm w).natAbs := by
  rw [norm_mul, Int.natAbs_mul]

/-- **Prime norm ⟹ irreducible element.** If `|N(z)|` is a rational prime `p`, then `z` is
irreducible in `ℤ[φ]`: it is not a unit (`|N| = p ≠ 1`), and in any factorization `z = a·b` the
norms multiply to `±p`, forcing one factor to have norm `±1`, i.e. to be a unit. -/
theorem irreducible_of_norm_natAbs_prime {z : GoldenInt} {p : ℕ} (hp : p.Prime)
    (h : (norm z).natAbs = p) : Irreducible z := by
  refine ⟨?_, ?_⟩
  · intro hu
    rw [isUnit_iff_norm_eq_one] at hu
    have h2 := hp.two_le
    rcases hu with h1 | h1 <;> rw [h1] at h <;> simp at h <;> omega
  · intro a b hab
    have key : (norm a).natAbs * (norm b).natAbs = p := by
      rw [← norm_natAbs_mul, ← hab, h]
    have hda : (norm a).natAbs ∣ p := ⟨(norm b).natAbs, key.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hda with h1 | h1
    · exact Or.inl (isUnit_of_norm_natAbs_one h1)
    · right
      apply isUnit_of_norm_natAbs_one
      rw [h1] at key
      have hp0 : 0 < p := hp.pos
      have key' : p * (norm b).natAbs = p * 1 := by rw [mul_one]; exact key
      exact Nat.eq_of_mul_eq_mul_left hp0 key'

/-- **Prime norm ⟹ prime element.** In a `UniqueFactorizationMonoid` (which `GoldenInt` is, via
the `EuclideanDomain → PID → UFD` instance chain), irreducible ⟺ prime, so `irreducible_of_norm_
natAbs_prime` upgrades to primality. -/
theorem prime_of_norm_natAbs_prime {z : GoldenInt} {p : ℕ} (hp : p.Prime)
    (h : (norm z).natAbs = p) : Prime z :=
  (UniqueFactorizationMonoid.irreducible_iff_prime).mp (irreducible_of_norm_natAbs_prime hp h)

/-! ## The ramified prime `√5 = 2φ − 1` -/

/-- The element `√5 = 2φ − 1 = ⟨-1, 2⟩ ∈ ℤ[φ]`. (Note `√5 ∈ ℤ[φ]` even though `φ ∉ ℤ[√5]`.) -/
def sqrt5 : GoldenInt := ⟨-1, 2⟩

@[simp] theorem a_sqrt5 : sqrt5.a = -1 := rfl
@[simp] theorem b_sqrt5 : sqrt5.b = 2 := rfl

/-- **Ramification `(5) = (√5)²`, on the nose.** `√5 · √5 = 5` in `ℤ[φ]` (the ramification unit
is literally `1`): `(2φ-1)² = 4φ²-4φ+1 = 4(φ+1)-4φ+1 = 5`. -/
theorem sqrt5_sq : sqrt5 * sqrt5 = ofInt 5 := by
  ext <;> simp [sqrt5, ofInt]

/-- The norm of `√5` is `-5`. -/
@[simp] theorem norm_sqrt5 : norm sqrt5 = -5 := by
  simp [norm, sqrt5]

/-- `√5` is anti-fixed by the Galois conjugation: `conj √5 = -√5`. -/
theorem conj_sqrt5 : conj sqrt5 = -sqrt5 := by
  ext <;> simp [conj, sqrt5]

theorem sqrt5_ne_zero : sqrt5 ≠ 0 := by
  intro h
  have : sqrt5.b = (0 : GoldenInt).b := by rw [h]
  simp [sqrt5] at this

/-- **`√5` is irreducible** in `ℤ[φ]` (its norm `-5` has prime absolute value `5`). -/
theorem irreducible_sqrt5 : Irreducible sqrt5 :=
  irreducible_of_norm_natAbs_prime (p := 5) (by norm_num) (by simp)

/-- **`√5` is a prime element** of `ℤ[φ]`. -/
theorem prime_sqrt5 : Prime sqrt5 :=
  prime_of_norm_natAbs_prime (p := 5) (by norm_num) (by simp)

/-! ## The norm-divisibility lift for `√5` -/

/-- Easy half: if `√5 ∣ α` then `5 ∣ N(α)` (since `N(√5) = -5` is multiplicative). -/
theorem five_dvd_norm_of_sqrt5_dvd {α : GoldenInt} (h : sqrt5 ∣ α) : (5 : ℤ) ∣ norm α := by
  obtain ⟨β, rfl⟩ := h
  rw [norm_mul, norm_sqrt5]
  exact ⟨-norm β, by ring⟩

/-- **Hard half — the key lift.** If `5 ∣ N(α)` then `√5 ∣ α`. Proof: `ofInt (N α) = α·conj α`,
so `√5² = ofInt 5 ∣ α·conj α`, hence `√5 ∣ α·conj α`; primality of `√5` gives `√5 ∣ α` or
`√5 ∣ conj α`, and the latter transfers to the former via `conj √5 = -√5` (apply `conj`). -/
theorem sqrt5_dvd_of_five_dvd_norm {α : GoldenInt} (h : (5 : ℤ) ∣ norm α) : sqrt5 ∣ α := by
  have hprod : α * conj α = ofInt (norm α) := mul_conj_eq_ofInt α
  have h5 : ofInt 5 ∣ ofInt (norm α) := ofInt_dvd_ofInt h
  rw [← hprod, ← sqrt5_sq] at h5
  have hsqrt5_dvd : sqrt5 ∣ α * conj α := dvd_trans (dvd_mul_right sqrt5 sqrt5) h5
  rcases prime_sqrt5.2.2 _ _ hsqrt5_dvd with hα | hcα
  · exact hα
  · obtain ⟨γ, hγ⟩ := hcα
    have hback : α = -sqrt5 * conj γ := by
      have := congrArg conj hγ
      rwa [conj_conj, conj_mul, conj_sqrt5] at this
    exact ⟨-conj γ, by rw [hback]; ring⟩

/-- **The lift, packaged as an iff.** `√5 ∣ α ↔ 5 ∣ N(α)`. This is item (3) of the FLT-5 Case II
divisibility programme: for the ramified prime `√5`, element-divisibility and norm-divisibility
are equivalent. -/
theorem sqrt5_dvd_iff_five_dvd_norm (α : GoldenInt) : sqrt5 ∣ α ↔ (5 : ℤ) ∣ norm α :=
  ⟨five_dvd_norm_of_sqrt5_dvd, sqrt5_dvd_of_five_dvd_norm⟩

/-- **Norm of the `√5`-cofactor.** If `α = √5 · β` then `N(α) = -5·N(β)`, i.e. peeling one factor
of `√5` divides the norm by `-5`. This is the arithmetic that makes the norm a strictly
decreasing descent metric each time a `√5` is removed. -/
theorem sqrt5_cofactor_norm {α β : GoldenInt} (h : α = sqrt5 * β) : norm α = -5 * norm β := by
  rw [h, norm_mul, norm_sqrt5]

/-- `√5² ∣ α ↔ 5 ∣ α` (both are `ofInt 5 ∣ α`, since `√5² = ofInt 5`). -/
theorem sqrt5_sq_dvd_iff_five_dvd (α : GoldenInt) : sqrt5 * sqrt5 ∣ α ↔ ofInt 5 ∣ α := by
  rw [sqrt5_sq]

/-! ## Exact `√5`-valuation control -/

/-- **Exact `√5`-valuation `= 1`.** If `5 ∣ N(α)` but `25 ∤ N(α)`, then `√5 ∣ α` but `√5² ∤ α`.
Concretely `v_{√5}(α) = 1`. This is the valuation control the descent uses on the
`N(α) = ∓5·e⁵` (with `5 ∤ e`) branch of `FermatLastTheoremFiveCaseTwo.case2_norm_eq`: there
`5 ∣ N(α)` and `25 ∤ N(α)`, so `α` is divisible by `√5` exactly once. -/
theorem sqrt5_valuation_one_of_five_dvd_norm_not_25 {α : GoldenInt}
    (h5 : (5 : ℤ) ∣ norm α) (h25 : ¬ (25 : ℤ) ∣ norm α) :
    sqrt5 ∣ α ∧ ¬ (sqrt5 * sqrt5 ∣ α) := by
  refine ⟨sqrt5_dvd_of_five_dvd_norm h5, ?_⟩
  intro hsq
  -- `√5² = ofInt 5 ∣ α` ⟹ `α = ofInt 5 · β` ⟹ `N α = 25 · N β` ⟹ `25 ∣ N α`, contradiction.
  rw [sqrt5_sq] at hsq
  obtain ⟨β, hβ⟩ := hsq
  apply h25
  refine ⟨norm β, ?_⟩
  rw [hβ, norm_mul, norm_ofInt]
  ring

end GoldenInt

section AxiomCheck
open GoldenInt
#print axioms ofInt_dvd_ofInt
#print axioms prime_of_norm_natAbs_prime
#print axioms sqrt5_sq
#print axioms conj_sqrt5
#print axioms prime_sqrt5
#print axioms sqrt5_dvd_iff_five_dvd_norm
#print axioms sqrt5_valuation_one_of_five_dvd_norm_not_25
end AxiomCheck
