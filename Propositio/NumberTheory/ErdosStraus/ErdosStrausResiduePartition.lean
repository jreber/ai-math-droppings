/-
  Erdős–Straus residue partition assembly.

  The main reduction: if the n ≡ 1 (mod 4) case is resolved,
  the full Erdős–Straus conjecture follows, by dispatching
  n % 4 ∈ {0, 1, 2, 3} via the known residue lemmas.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausResidue

/-- **Main assembly theorem**: if the `n ≡ 1 (mod 4)` case is resolved,
the full Erdős–Straus conjecture follows.

This makes explicit that the remaining open content is precisely the
n ≡ 1 (mod 4), 3 ∤ n residue class (uncovered by even and mod-3 cases). -/
theorem erdos_straus_reduces_to_one_mod_four :
    (∀ n : ℕ, 2 ≤ n → n % 4 = 1 → HasRep n) → (∀ n : ℕ, 2 ≤ n → HasRep n) := by
  intro h_one_mod_four n hn
  -- Split by even/odd, then examine the mod-4 value for odd n
  rcases Nat.even_or_odd n with he | ho
  · -- Case: n is even (covers n % 4 = 0 and n % 4 = 2)
    exact hasRep_of_even hn he
  · -- Case: n is odd; determine if n ≡ 1 or 3 (mod 4)
    obtain ⟨j, rfl⟩ := ho
    by_cases h : (2 * j + 1) % 4 = 1
    · exact h_one_mod_four (2 * j + 1) hn h
    · have h3 : (2 * j + 1) % 4 = 3 := by omega
      exact hasRep_of_three_mod_four h3

end ErdosStrausResidue
