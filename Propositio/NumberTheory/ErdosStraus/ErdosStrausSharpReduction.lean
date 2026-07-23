/-
  Erdős–Straus SHARP reduction.

  Combining the residue coverage (`ErdosStrausResidue`) with the divisor
  reduction (`ErdosStrausDivisorReduction`): a *minimal* counterexample to
  Erdős–Straus — an `n ≥ 2` all of whose proper "sub-values" `2 ≤ m < n` have
  a representation, but which itself does not — must be both

  * PRIME (`prime_of_minimal_nonRep`, divisor reduction), and
  * `≡ 1 (mod 4)` (`nonRep_subset_one_mod_four` / `hasRep_of_not_one_mod_four`,
    residue coverage).

  So the Erdős–Straus conjecture reduces exactly to: every prime `p ≡ 1
  (mod 4)` has an Erdős–Straus representation. (The classically known open
  reduction is to primes `≡ 1 (mod 24)`; the mod-4 form here is the coarser,
  but fully elementary, version obtained from the residue file's coverage
  lemmas without the extra `3 ∤ n` refinement.)
-/
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue
import Propositio.NumberTheory.ErdosStraus.ErdosStrausDivisorReduction
import Mathlib.Data.Nat.Prime.Basic

namespace ErdosStrausResidue

/-- **Sharp reduction**: a minimal non-representable `n` (every smaller
`2 ≤ m < n` has a representation, but `n` does not) is a prime `≡ 1 (mod 4)`. -/
theorem minimal_nonRep_prime_one_mod_four {n : ℕ} (hn : 2 ≤ n)
    (hbelow : ∀ m, 2 ≤ m → m < n → HasRep m) (hnonrep : ¬ HasRep n) :
    n.Prime ∧ n % 4 = 1 := by
  refine ⟨prime_of_minimal_nonRep hn hbelow hnonrep, ?_⟩
  by_contra h
  exact hnonrep (hasRep_of_not_one_mod_four hn h)

/-- **Non-representable ⟹ prime and `≡ 1 (mod 4)`**, same statement under the
name matching the "global counterexample" phrasing: if `n ≥ 2` fails to have
a representation but every smaller value `2 ≤ m < n` does (i.e. `n` witnesses
minimality among counterexamples), then `n` is a prime `≡ 1 (mod 4)`.

Consequently: if every prime `p ≡ 1 (mod 4)` has an Erdős–Straus
representation, then EVERY `n ≥ 2` does (strong induction: a minimal
counterexample would have to be such a prime, contradiction). -/
theorem nonRep_imp_prime_one_mod_four {n : ℕ} (hn : 2 ≤ n) (hnonrep : ¬ HasRep n)
    (hstrong : ∀ m, 2 ≤ m → m < n → HasRep m) :
    n.Prime ∧ n % 4 = 1 :=
  minimal_nonRep_prime_one_mod_four hn hstrong hnonrep

/-- **Erdős–Straus reduces to primes `≡ 1 mod 4`**: if every prime `p ≡ 1
(mod 4)` has a representation, then every `n ≥ 2` does. Proof by strong
induction on `n`: at a putative minimal counterexample, the two results above
force `n` to be exactly such a prime, contradicting the hypothesis. -/
theorem hasRep_of_primes_one_mod_four
    (hprimes : ∀ p : ℕ, p.Prime → p % 4 = 1 → HasRep p) :
    ∀ n, 2 ≤ n → HasRep n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_contra hnonrep
    have hbelow : ∀ m, 2 ≤ m → m < n → HasRep m := fun m hm2 hmlt => ih m hmlt hm2
    obtain ⟨hpn, hmod⟩ := minimal_nonRep_prime_one_mod_four hn hbelow hnonrep
    exact hnonrep (hprimes n hpn hmod)

end ErdosStrausResidue
