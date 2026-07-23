/-
  Erdős–Straus residue bricks.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  Here we prove the elementary residue cases via explicit witnesses:

  * even n            : 4/n = 1/(n/2) + 1/n + 1/n
  * n ≡ 3 (mod 4)     : n = 4k+3, 4/n = 1/(k+1) + 1/(2(k+1)n) + 1/(2(k+1)n)
                        (since 4/n − 1/(k+1) = 1/((k+1)n), split in half)
  * 3 ∣ n             : n = 3m,   4/n = 1/m + 1/(6m) + 1/(6m)

  Consequently every n ≥ 2 with n % 4 ≠ 1 has a representation, and the set of
  n ≥ 2 without a representation is contained in
  {n | n % 4 = 1 ∧ ¬ 3 ∣ n}.

  The OPEN content of Erdős–Straus (primes ≡ 1 mod 24) is NOT touched here.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ErdosStrausResidue

/-- `n` has an Erdős–Straus representation: `4/n = 1/a + 1/b + 1/c`
with positive natural numbers `a, b, c` (equation stated over `ℚ`). -/
def HasRep (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / c

/-- **Even case**, explicit witness: for even `n ≥ 2`,
`4/n = 1/(n/2) + 1/n + 1/n`. -/
theorem erdos_straus_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨m, rfl⟩ := he
  have hm : 0 < m := by omega
  refine ⟨m, m + m, m + m, hm, by omega, by omega, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp
  ring

/-- Even case, `HasRep` form. -/
theorem hasRep_of_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) : HasRep n :=
  erdos_straus_even hn he

/-- **`n ≡ 3 (mod 4)` case**, explicit witness: writing `n = 4k + 3`,
`4/n = 1/(k+1) + 1/(2(k+1)n) + 1/(2(k+1)n)`.

(Indeed `4/n − 1/(k+1) = (4(k+1) − n)/(n(k+1)) = 1/(n(k+1))`, split in half.) -/
theorem erdos_straus_three_mod_four {n : ℕ} (h : n % 4 = 3) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (k + 1) * (4 * k + 3), 2 * (k + 1) * (4 * k + 3),
    by omega, by positivity, by positivity, ?_⟩
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn3 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 3 (mod 4)` case, `HasRep` form. -/
theorem hasRep_of_three_mod_four {n : ℕ} (h : n % 4 = 3) : HasRep n :=
  erdos_straus_three_mod_four h

/-- **`3 ∣ n` case**, explicit witness: writing `n = 3m`,
`4/n = 1/m + 1/(6m) + 1/(6m)`. -/
theorem erdos_straus_three_dvd {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨m, rfl⟩ := h3
  have hm : 0 < m := by omega
  refine ⟨m, 6 * m, 6 * m, hm, by omega, by omega, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp
  ring

/-- `3 ∣ n` case, `HasRep` form. -/
theorem hasRep_of_three_dvd {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ n) : HasRep n :=
  erdos_straus_three_dvd hn h3

/-- **Mod-4 coverage**: every `n ≥ 2` with `n % 4 ≠ 1` has an Erdős–Straus
representation (classes `0, 2` mod 4 are even; class `3` is the explicit
`4k+3` identity). -/
theorem hasRep_of_not_one_mod_four {n : ℕ} (hn : 2 ≤ n) (h : n % 4 ≠ 1) :
    HasRep n := by
  rcases Nat.even_or_odd n with he | ho
  · exact hasRep_of_even hn he
  · have h3 : n % 4 = 3 := by
      obtain ⟨j, rfl⟩ := ho
      omega
    exact hasRep_of_three_mod_four h3

/-- **Coverage with the mod-3 refinement**: every `n ≥ 2` that is either
`≢ 1 (mod 4)` or divisible by `3` has an Erdős–Straus representation. -/
theorem hasRep_of_not_one_mod_four_or_three_dvd {n : ℕ} (hn : 2 ≤ n)
    (h : n % 4 ≠ 1 ∨ 3 ∣ n) : HasRep n := by
  rcases h with h | h
  · exact hasRep_of_not_one_mod_four hn h
  · exact hasRep_of_three_dvd hn h

/-- **Wrapper**: the set of `n ≥ 2` without an Erdős–Straus representation is
contained in the residue class `n ≡ 1 (mod 4)`. -/
theorem nonRep_subset_one_mod_four :
    {n : ℕ | 2 ≤ n ∧ ¬HasRep n} ⊆ {n : ℕ | n % 4 = 1} := by
  intro n hn
  obtain ⟨h2, hrep⟩ := hn
  by_contra h
  exact hrep (hasRep_of_not_one_mod_four h2 h)

/-- **Wrapper, refined**: the set of `n ≥ 2` without an Erdős–Straus
representation is contained in `{n | n ≡ 1 (mod 4) and 3 ∤ n}`. -/
theorem nonRep_subset_one_mod_four_not_three_dvd :
    {n : ℕ | 2 ≤ n ∧ ¬HasRep n} ⊆ {n : ℕ | n % 4 = 1 ∧ ¬3 ∣ n} := by
  intro n hn
  obtain ⟨h2, hrep⟩ := hn
  constructor
  · by_contra h
    exact hrep (hasRep_of_not_one_mod_four h2 h)
  · intro h3
    exact hrep (hasRep_of_three_dvd h2 h3)

/-- Sanity: explicit numeric instances of each identity. -/
example : (4 : ℚ) / 6 = 1 / 3 + 1 / 6 + 1 / 6 := by norm_num
example : (4 : ℚ) / 7 = 1 / 2 + 1 / 28 + 1 / 28 := by norm_num
example : (4 : ℚ) / 9 = 1 / 3 + 1 / 18 + 1 / 18 := by norm_num

end ErdosStrausResidue
