/-
  Erdős–Straus divisor reduction.

  If a divisor `m ≥ 2` of `n` has an Erdős–Straus representation `HasRep m`,
  then so does `n` (scale the representation for `m` by `k = n / m`, using
  `erdosStraus_scale`). Consequently:

  * a minimal-counterexample argument shows any `n ≥ 2` all of whose proper
    divisors `2 ≤ m < n` have `HasRep m`, but which is itself not `HasRep`,
    must be prime;
  * in particular the Erdős–Straus conjecture reduces to the case of prime `n`.
-/
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue
import Propositio.NumberTheory.ErdosStraus.ErdosStrausMultiplicative
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity

namespace ErdosStrausResidue

/-- **Divisor reduction**: if `m ≥ 2` divides `n` (with `n ≥ 1`) and `m` has an
Erdős–Straus representation, then so does `n`. Proof: write `n = k * m`,
scale the representation of `m` by `k` via `erdosStraus_scale`. -/
theorem hasRep_of_dvd {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (hmn : m ∣ n)
    (hrep : HasRep m) : HasRep n := by
  obtain ⟨k, hk⟩ := hmn
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.mul_zero] at hk; omega
    · exact h0
  obtain ⟨a, b, c, ha, hb, hc, heq⟩ := hrep
  have hscaled := erdosStraus_scale m a b c k hm0 ha hb hc hk0 heq
  have hnkm : n = k * m := by rw [hk, Nat.mul_comm]
  refine ⟨k * a, k * b, k * c, by positivity, by positivity, by positivity, ?_⟩
  rw [hnkm]
  push_cast
  exact hscaled

/-- **Composite witness form**: if `n` has a divisor `m` with `2 ≤ m < n` that
has an Erdős–Straus representation, then so does `n`. -/
theorem hasRep_of_composite_witness {n : ℕ} (hn : 2 ≤ n)
    (hcomp : ∃ m, 2 ≤ m ∧ m ∣ n ∧ m < n ∧ HasRep m) : HasRep n := by
  obtain ⟨m, hm2, hmn, _hlt, hrep⟩ := hcomp
  exact hasRep_of_dvd hm2 (by omega) hmn hrep

/-- **Minimal counterexamples are prime**: if `n ≥ 2` is such that every
`m` with `2 ≤ m < n` has an Erdős–Straus representation, but `n` itself does
not, then `n` is prime. Equivalently: the Erdős–Straus conjecture reduces to
the case of prime `n` (a minimal non-representable `n`, if one exists, must
be prime). -/
theorem prime_of_minimal_nonRep {n : ℕ} (hn : 2 ≤ n)
    (hbelow : ∀ m, 2 ≤ m → m < n → HasRep m) (hnonrep : ¬ HasRep n) :
    n.Prime := by
  by_contra hnp
  obtain ⟨m, hmn, hm2, hmlt⟩ := (Nat.not_prime_iff_exists_dvd_lt hn).mp hnp
  exact hnonrep (hasRep_of_dvd hm2 (by omega) hmn (hbelow m hm2 hmlt))

end ErdosStrausResidue
