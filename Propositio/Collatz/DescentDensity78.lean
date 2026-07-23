import Propositio.Collatz.Basic
import Propositio.Collatz.DescentDensityF2
import Propositio.Collatz.DensityCount

/-!
# Natural lower density of Collatz-descending integers is ≥ 7/8

Strengthening of `CollatzDescentDensityF2` (which gives ≥ 3/4).  We show that for
every rational `p/q < 7/8`, the set `{n : DescBy n 5}` (integers whose Terras orbit
dips below the start within **five** steps) has lower natural density at least `p/q`,
i.e. **lower density ≥ 7/8**.

NOTE: this RE-DERIVES the `k=5` case of the existing
`CollatzDensityCount.F_eq_count_over_pow` (density of `{n : DescBy n k}` is pinned
at `D(k)/2^k` for `k ≤ 6`), via the residue-class-union combinators of
`CollatzDescentDensityF2`.  It is NOT a new result; it is an independent worked
example of those reusable combinators.  The descending residues mod `2⁵ = 32`
number `D(5) = 28` (kernel-`decide`d) and `DescBy · 5` is a residue predicate mod
32 (`descBy_mod_invariant_five`); combining the 28 disjoint classes gives 28/32 = 7/8.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace CollatzDescentDensity78

open TerrasDensity
open CollatzDescentDensityF2
open CollatzStoppingF3
open CollatzDensityCount

attribute [local instance] Classical.propDecidable

/-- Ratio monotonicity of lower density: if `p/q ≤ x/y` then a lower bound `x/y`
gives the lower bound `p/q`. -/
theorem dbb_mono {A : Nat → Prop} {p q x y : Nat} (hy : 0 < y)
    (hle : p * y ≤ x * q) (h : density_bounded_below A x y) :
    density_bounded_below A p q := by
  obtain ⟨N0, hh⟩ := h
  refine ⟨N0, fun N hN => ?_⟩
  have hxN := hh N hN
  have step : y * (p * N) ≤ y * (q * count_upto A N) := by
    calc y * (p * N) = p * y * N := by ring
      _ ≤ x * q * N := Nat.mul_le_mul_right N hle
      _ = q * (x * N) := by ring
      _ ≤ q * (y * count_upto A N) := Nat.mul_le_mul_left q hxN
      _ = y * (q * count_upto A N) := by ring
  exact Nat.le_of_mul_le_mul_left step hy

/-- Lower density of a finite disjoint union of (threshold-2) residue classes mod `m`:
`{n : n % m ∈ S ∧ 2 ≤ n}` has lower density `≥ S.card / m` (numerator `S.card * p`
for any `p` with `p*m < q`). -/
theorem dbb_residue_set (m : Nat) (p q : Nat) (hm : 0 < m) (hfrac : p * m < q) :
    ∀ S : Finset Nat, (∀ r ∈ S, r < m) →
      density_bounded_below (fun n => n % m ∈ S ∧ 2 ≤ n) (S.card * p) q := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _
    refine ⟨0, fun N _ => ?_⟩
    simp
  | @insert r S hr ih =>
    intro hmem
    have hmem' : ∀ x ∈ S, x < m := fun x hx => hmem x (Finset.mem_insert_of_mem hx)
    have hrm : r < m := hmem r (Finset.mem_insert_self r S)
    have hS := ih hmem'
    have hr1 : density_bounded_below (fun n => n % m = r ∧ 2 ≤ n) p q :=
      dbb_residue_trunc m r p q 2 hm hrm hfrac
    have hdisj : ∀ n, ¬ ((n % m = r ∧ 2 ≤ n) ∧ (n % m ∈ S ∧ 2 ≤ n)) := by
      intro n hh
      have : r ∈ S := by rw [← hh.1.1]; exact hh.2.1
      exact hr this
    have hu := dbb_union hdisj hr1 hS
    have hpred : (fun n => (n % m = r ∧ 2 ≤ n) ∨ (n % m ∈ S ∧ 2 ≤ n))
        = (fun n => n % m ∈ insert r S ∧ 2 ≤ n) := by
      funext n
      simp only [Finset.mem_insert, eq_iff_iff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    rw [hpred] at hu
    have hcard : (insert r S).card * p = p + S.card * p := by
      rw [Finset.card_insert_of_notMem hr]; ring
    rw [hcard]
    exact hu

/-- The 28 descending residues mod 32 (Terras level 5). -/
def Good5 : Finset Nat := (Finset.range 32).filter (fun r => descByB (r + 32) 5)

theorem good5_card : Good5.card = 28 := by decide

/-- A number whose residue mod 32 is descending (and `≥ 2`) descends within 5 steps. -/
theorem good5_subset_descBy5 (n : Nat) (hn : 2 ≤ n) (h : n % 32 ∈ Good5) :
    DescBy n 5 := by
  unfold Good5 at h
  rw [Finset.mem_filter, Finset.mem_range] at h
  have hb : descByB (n % 32 + 32) 5 = true := h.2
  have hd : DescBy (n % 32 + 32) 5 := (descByB_iff _ _).1 hb
  have hmod : (n % 32 + 32) % 32 = n % 32 := by omega
  exact (descBy_mod_invariant_five (n % 32 + 32) n (by omega) hn hmod).1 hd

/-- **Lower natural density of Collatz-descending integers ≥ 7/8.**
For every `p/q < 7/8`, the set of integers whose Terras orbit drops below the start
within five steps has lower density at least `p/q`. -/
theorem descBy5_density (p q : Nat) (hpq : 8 * p < 7 * q) :
    density_bounded_below (fun n => DescBy n 5) p q := by
  have hset : density_bounded_below (fun n => n % 32 ∈ Good5 ∧ 2 ≤ n)
      (Good5.card * p) (32 * p + 1) :=
    dbb_residue_set 32 p (32 * p + 1) (by norm_num) (by omega) Good5
      (fun r hr => by
        rw [Good5, Finset.mem_filter, Finset.mem_range] at hr; exact hr.1)
  rw [good5_card] at hset
  have hsub : density_bounded_below (fun n => DescBy n 5) (28 * p) (32 * p + 1) :=
    dbb_subset (fun n hh => good5_subset_descBy5 n hh.2 hh.1) hset
  refine dbb_mono (by omega) ?_ hsub
  have hbound : 32 * p + 1 ≤ 28 * q := by omega
  calc p * (32 * p + 1) ≤ p * (28 * q) := Nat.mul_le_mul_left p hbound
    _ = 28 * p * q := by ring

end CollatzDescentDensity78
