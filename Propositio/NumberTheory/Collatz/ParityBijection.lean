import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ParityVector
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# The Terras parity-vector bijection (structural heart of Collatz density theory)

This file formalizes the central structural theorem underlying every density
result in the Terras/Collatz corpus: the **parity-vector bijection**.

For each `n : Nat` and length `k`, define the *parity vector*
`Q k n : Fin k → Bool` recording the parities of `n, T n, …, T^{k-1} n`
(where `T` is the accelerated Collatz/Terras step from `TerrasDensity`).
The Terras theorem states that the induced map on residues mod `2^k` is a
**bijection** onto the `2^k` length-`k` parity vectors: every length-`k`
parity vector is realized by *exactly one* residue class mod `2^k`, hence
each parity vector occurs with density exactly `2^{-k}`.

## Main results
* `pvMap_injective` — the parity-vector map `Fin (2^k) → (Fin k → Bool)`
  is injective (packaged from `parity_vector_residue_lemma_nat`).
* `pv_residue_injective` — restatement: `PVEq m n k` with `m, n < 2^k`
  forces `m = n`; more generally `PVEq m n k → m ≡ n [MOD 2^k]`.
* `pvMap_bijective` — **HEADLINE**: the parity-vector map is a bijection.
* `parity_vector_equidistribution` — corollary: every length-`k` parity
  vector is realized by exactly one residue in `Fin (2^k)` (the equiv).

All proofs are axiom-clean: `#print axioms` ⊆ `[propext, Classical.choice,
Quot.sound]`.
-/

namespace CollatzParityBijection

open TerrasDensity

/-- The length-`k` **parity vector** of `n`: bit `j` is the parity of `T^j n`. -/
def Q (k n : Nat) : Fin k → Bool := fun j => decide (T_iter n j % 2 = 1)

/-- `Q k m = Q k n` is exactly `PVEq m n k`: the parity vectors agree iff
all the first-`k` parities agree. This is the bridge between the function-valued
encoding `Q` and the predicate `PVEq` from `TerrasDensity`. -/
theorem Q_eq_iff_PVEq (m n k : Nat) : Q k m = Q k n ↔ PVEq m n k := by
  constructor
  · intro h j hj
    -- Evaluate the function equality at the index `j`.
    have hval : Q k m ⟨j, hj⟩ = Q k n ⟨j, hj⟩ := by rw [h]
    simp only [Q] at hval
    -- decide (a % 2 = 1) = decide (b % 2 = 1) and parities are in {0,1}.
    have hm : T_iter m j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hn : T_iter n j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases hc : T_iter m j % 2 = 1
    · have : T_iter n j % 2 = 1 := by
        by_contra hne
        simp [hc, hne] at hval
      omega
    · have hne2 : ¬ T_iter n j % 2 = 1 := by
        intro hcontra
        simp [hc, hcontra] at hval
      omega
  · intro h
    funext j
    simp only [Q]
    have := h j.val j.isLt
    rw [this]

/-- **Parity-vector map** on residues `0, …, 2^k − 1`:
`pvMap k r = Q k r.val`, the length-`k` parity vector of the representative `r`. -/
def pvMap (k : Nat) : Fin (2 ^ k) → (Fin k → Bool) := fun r => Q k r.val

/--
**Injectivity (`pv_residue_injective`, part 1).**
The parity-vector map `Fin (2^k) → (Fin k → Bool)` is injective.

Two residues below `2^k` with the same length-`k` parity vector are equal:
this is `parity_vector_residue_lemma_nat` (same vector ⟹ `2^k ∣ m − n`)
combined with the size constraint `m, n < 2^k`.
-/
theorem pvMap_injective (k : Nat) : Function.Injective (pvMap k) := by
  intro a b hab
  -- From equal parity vectors get PVEq.
  have hpv : PVEq a.val b.val k := (Q_eq_iff_PVEq a.val b.val k).1 hab
  -- Residue lemma: 2^k ∣ (a − b) over ℤ.
  have hdvd : (2 : Int) ^ k ∣ (a.val : Int) - (b.val : Int) :=
    parity_vector_residue_lemma_nat a.val b.val k hpv
  -- a, b < 2^k forces a = b.
  have ha : (a.val : Int) < 2 ^ k := by exact_mod_cast a.isLt
  have hb : (b.val : Int) < 2 ^ k := by exact_mod_cast b.isLt
  have ha0 : (0 : Int) ≤ a.val := by positivity
  have hb0 : (0 : Int) ≤ b.val := by positivity
  -- |a − b| < 2^k and 2^k ∣ (a − b) ⟹ a − b = 0.
  obtain ⟨c, hc⟩ := hdvd
  have hpos : (0 : Int) < 2 ^ k := by positivity
  have : (a.val : Int) - b.val = 0 := by
    rcases lt_trichotomy c 0 with hlt | heq | hgt
    · exfalso
      have : (a.val : Int) - b.val ≤ -(2 ^ k) := by
        rw [hc]; nlinarith [hpos]
      omega
    · rw [hc, heq, mul_zero]
    · exfalso
      have : (2 : Int) ^ k ≤ (a.val : Int) - b.val := by
        rw [hc]; nlinarith [hpos]
      omega
  have : (a.val : Int) = b.val := by omega
  have : a.val = b.val := by exact_mod_cast this
  exact Fin.ext this

/--
**`pv_residue_injective` (predicate form).**
If `m` and `n` have the same length-`k` parity vector, then they are congruent
mod `2^k`. This is the clean ZMod restatement of the residue lemma, and is the
*well-definedness* fact: the parity vector of `n` depends only on `n mod 2^k`.
(The converse direction — well-definedness as a function on `ZMod (2^k)` — is
not needed for the bijection below, which is built directly on representatives
`Fin (2^k)`.)
-/
theorem pv_residue_injective (m n k : Nat) (h : PVEq m n k) :
    m ≡ n [MOD 2 ^ k] := by
  have hdvd : (2 : Int) ^ k ∣ (m : Int) - (n : Int) :=
    parity_vector_residue_lemma_nat m n k h
  -- Translate ℤ-divisibility of the difference into Nat.ModEq.
  rw [Nat.modEq_iff_dvd]
  push_cast
  -- n − m = -(m − n).
  have hneg : (n : Int) - (m : Int) = -((m : Int) - (n : Int)) := by ring
  rw [hneg]
  exact Dvd.dvd.neg_right hdvd

/--
**HEADLINE — `pvMap_bijective`.**
The parity-vector map `pvMap k : Fin (2^k) → (Fin k → Bool)` is a **bijection**.

*Proof.* It is injective (`pvMap_injective`); the domain `Fin (2^k)` and the
codomain `Fin k → Bool` are finite of equal cardinality `2^k`
(`Fintype.card (Fin (2^k)) = 2^k`, `Fintype.card (Fin k → Bool) = 2^k`).
An injective map between finite types of equal cardinality is bijective.
-/
theorem pvMap_bijective (k : Nat) : Function.Bijective (pvMap k) := by
  have hcard : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp [Fintype.card_fin]
  exact (Fintype.bijective_iff_injective_and_card (pvMap k)).2
    ⟨pvMap_injective k, hcard⟩

/--
**`parity_vector_equidistribution` (corollary, equiv form).**
Every length-`k` parity vector is realized by *exactly one* residue in
`Fin (2^k)`: the parity-vector map is an equivalence
`Fin (2^k) ≃ (Fin k → Bool)`. Combined with `Fintype.card (Fin (2^k)) = 2^k`,
this says each of the `2^k` parity vectors occurs with density exactly `2^{-k}`.
-/
noncomputable def parity_vector_equidistribution (k : Nat) :
    Fin (2 ^ k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (pvMap k) (pvMap_bijective k)

/--
**Existence-and-uniqueness restatement of equidistribution.**
For every length-`k` parity vector `v : Fin k → Bool`, there is a *unique*
residue `r : Fin (2^k)` whose parity vector is `v`.
-/
theorem parity_vector_exists_unique (k : Nat) (v : Fin k → Bool) :
    ∃! r : Fin (2 ^ k), pvMap k r = v := by
  obtain ⟨r, hr⟩ := (pvMap_bijective k).surjective v
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact (pvMap_bijective k).injective (by rw [hs, hr])

end CollatzParityBijection
