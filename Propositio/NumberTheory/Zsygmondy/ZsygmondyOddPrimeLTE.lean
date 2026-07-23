/-
# Lifting-the-Exponent (LTE) lemma for ODD primes `p`

Companion to the `p = 2` engine in `Zsygmondy2adicLTE.lean`.  For an odd prime
`p` and integers `a, b` with `p ∤ a` and `p ∣ (a − b)` (and `a ≠ b`):

  * `v_p(aⁿ − bⁿ) = v_p(a − b) + v_p(n)`   for every `n ≥ 1`,

where `v_p = padicValInt p` on `ℤ` and `padicValNat p` on `ℕ`.  Unlike the
`p = 2` even case there is **no `−1` correction** — the odd-prime arithmetic is
the clean additive identity.

This is a faithful repackaging, in the natural-number-valued `padicVal` form, of
mathlib's `Int.emultiplicity_pow_sub_pow` (the odd-prime LTE engine, living in
`Mathlib.NumberTheory.Multiplicity`), transported across the
`padicVal ↔ emultiplicity` bridge exactly as in the `p = 2` file.
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Multiplicity

open scoped Classical

namespace ZsygmondyOddPrimeLTE

/-- Bridge: for a prime `p` and a nonzero integer `z`, the natural-number-valued
`padicValInt p z` agrees with the `ℕ∞`-valued `emultiplicity (p : ℤ) z`. -/
private theorem padicValInt_cast_eq_emultiplicity {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : z ≠ 0) :
    (padicValInt p z : ℕ∞) = emultiplicity (p : ℤ) z := by
  have hfin : FiniteMultiplicity (p : ℤ) z :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one, hz⟩
  rw [padicValInt.of_ne_one_ne_zero hp.ne_one hz, hfin.emultiplicity_eq_multiplicity]

/-- **Lifting-the-Exponent for odd primes.**  Let `p` be an odd prime and
`a, b : ℤ` with `a ≠ b`, `p ∤ a`, and `p ∣ (a − b)`.  Then for every `n ≥ 1`,

  `v_p(aⁿ − bⁿ) = v_p(a − b) + v_p(n)`.

(`a ≠ b` is needed only to keep the valuations finite; the modular hypotheses
`p ∤ a`, `p ∣ (a − b)` are the genuine LTE hypotheses.  Note `p ∤ b` follows
automatically.) -/
theorem lte_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) {a b : ℤ}
    (hne : a ≠ b) (hpa : ¬ (p : ℤ) ∣ a) (hab : (p : ℤ) ∣ (a - b)) {n : ℕ}
    (hn : 1 ≤ n) :
    padicValInt p (a ^ n - b ^ n) = padicValInt p (a - b) + padicValNat p n := by
  have _hp : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  -- the LTE engine, valued in `ℕ∞`
  have heq :
      emultiplicity (p : ℤ) (a ^ n - b ^ n)
        = emultiplicity (p : ℤ) (a - b) + emultiplicity p n :=
    Int.emultiplicity_pow_sub_pow hp hodd hab hpa n
  -- the right-hand side is finite
  have hfin_sub : emultiplicity (p : ℤ) (a - b) ≠ ⊤ :=
    finiteMultiplicity_iff_emultiplicity_ne_top.1
      (Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one, hsub⟩)
  have hfin_n : emultiplicity (p : ℕ) n ≠ ⊤ :=
    finiteMultiplicity_iff_emultiplicity_ne_top.1
      (Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.pos_of_ne_zero hn0⟩)
  -- hence the left-hand side is finite, so `aⁿ − bⁿ ≠ 0`
  have hpow : a ^ n - b ^ n ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero] at heq
    exact (WithTop.add_ne_top.mpr ⟨hfin_sub, hfin_n⟩) heq.symm
  -- transport the `ℕ∞` identity back to `padicVal`
  rw [← Nat.cast_inj (R := ℕ∞)]
  push_cast
  rw [padicValInt_cast_eq_emultiplicity hp hpow,
      padicValInt_cast_eq_emultiplicity hp hsub,
      padicValNat_eq_emultiplicity hn0]
  exact heq

end ZsygmondyOddPrimeLTE
