/-
# Sunflower Lemma Tightness (Matching Lower Bound)

The Erdős–Rado sunflower lemma (`ErdosRado.exists_isSunflower`, proved in
`ErdosRadoSunflower.lean`) states that any family of more than `k! · s^k` sets of size
at most `k` contains an `s`-sunflower. This file proves the matching **lower bound**:
for every `k, s` with `s ≥ 2` there is a family of exactly `(s - 1)^k` distinct `k`-element
sets containing *no* `s`-sunflower. (The bound in the sunflower lemma itself is not
tight — the true extremal bound is a long-standing open problem, most famously attacked
via the "sunflower conjecture" — but `(s-1)^k` is the classical, elementary, and easily
verified lower bound showing that some exponential-in-`k` dependence is unavoidable.)

## Construction

Fix `k` disjoint "blocks", each of size `s - 1`, realised as the fibres of the first
projection `Fin k × Fin (s - 1) → Fin k`. For a choice function `f : Fin k → Fin (s - 1)`
picking one representative `f i` from each block `i`, let

  `sfSet f := {(i, f i) : i ∈ Fin k}`

be the corresponding "system of distinct representatives" — a `k`-element set with exactly
one point per block. The family `sfFamily k s := {sfSet f : f : Fin k → Fin (s - 1)}` has
exactly `(s - 1)^k` members (since `f ↦ sfSet f` is injective), and contains no `s`-sunflower:
if `S ⊆ sfFamily k s` were an `s`-sunflower with core `C`, take any two representative
functions `f₀ ≠ g₀` from `S`'s preimage and a coordinate `i` where they disagree.  Because
`C = sfSet f₀ ∩ sfSet g₀` and the two disagree at `i`, no pair `(i, c)` can lie in `C`
(the "column" `i` is entirely excluded from the core). But then, since *every* pair of
distinct members of `S` must intersect exactly in `C`, the evaluation map `h ↦ h i` is
injective on the (size `s`) preimage of `S` — landing in `Fin (s - 1)`, which has only
`s - 1` elements: a pigeonhole contradiction.

The headline result is `ErdosRado.exists_sunflower_free_family`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Propositio.Combinatorics.ErdosRadoSunflower

open Finset

namespace ErdosRado

variable {k s : ℕ}

/-- The "system of distinct representatives" associated to a choice function `f`,
picking one element `(i, f i)` from each of the `k` blocks `{i} × Fin (s - 1)`. -/
def sfSet (f : Fin k → Fin (s - 1)) : Finset (Fin k × Fin (s - 1)) :=
  Finset.univ.image (fun i => (i, f i))

@[simp] lemma mem_sfSet {f : Fin k → Fin (s - 1)} {i : Fin k} {c : Fin (s - 1)} :
    (i, c) ∈ sfSet f ↔ c = f i := by
  simp [sfSet, eq_comm]

/-- The map `f ↦ sfSet f` is injective: a system of distinct representatives determines
the choice function that produced it. -/
lemma sfSet_injective : Function.Injective (fun f : Fin k → Fin (s - 1) => sfSet f) := by
  intro f g hfg
  funext i
  have hfg' : sfSet f = sfSet g := hfg
  have hmem : (i, f i) ∈ sfSet f := mem_sfSet.mpr rfl
  rw [hfg'] at hmem
  exact mem_sfSet.mp hmem

/-- The family of all systems of distinct representatives over `k` blocks of size `s - 1`.
Has exactly `(s - 1)^k` members (`sfFamily_card`) and contains no `s`-sunflower
(`sfFamily_no_sunflower`) once `s ≥ 2`. -/
def sfFamily (k s : ℕ) : Finset (Finset (Fin k × Fin (s - 1))) :=
  Finset.univ.image (fun f : Fin k → Fin (s - 1) => sfSet f)

lemma sfFamily_card : (sfFamily k s).card = (s - 1) ^ k := by
  rw [sfFamily, Finset.card_image_of_injective _ sfSet_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Every system of distinct representatives is genuinely a `k`-element set (one point
per block). -/
lemma sfSet_card (f : Fin k → Fin (s - 1)) : (sfSet f).card = k := by
  have hinj : Function.Injective (fun i : Fin k => (i, f i)) := fun i j h => congrArg Prod.fst h
  rw [sfSet, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Every member of `sfFamily k s` is a `k`-element set. -/
lemma sfFamily_mem_card {A : Finset (Fin k × Fin (s - 1))} (hA : A ∈ sfFamily k s) :
    A.card = k := by
  rw [sfFamily, Finset.mem_image] at hA
  obtain ⟨f, _, rfl⟩ := hA
  exact sfSet_card f

/-- The key combinatorial fact: `sfFamily k s` contains no `s`-sunflower (for `s ≥ 2`). -/
lemma sfFamily_no_sunflower (hs : 2 ≤ s) :
    ¬ ∃ S ⊆ sfFamily k s, S.card = s ∧ ∃ C, IsSunflower S C := by
  rintro ⟨S, hSsub, hScard, C, hSun⟩
  classical
  -- `T` is the preimage of `S` under the (injective) map `f ↦ sfSet f`.
  set T : Finset (Fin k → Fin (s - 1)) := Finset.univ.filter (fun f => sfSet f ∈ S) with hT
  have hTS : T.image (fun f => sfSet f) = S := by
    apply Finset.Subset.antisymm
    · intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨f, hf, rfl⟩ := hA
      rw [hT, Finset.mem_filter] at hf
      exact hf.2
    · intro A hA
      have hAF : A ∈ sfFamily k s := hSsub hA
      rw [sfFamily, Finset.mem_image] at hAF
      obtain ⟨f, _, hfA⟩ := hAF
      rw [Finset.mem_image]
      refine ⟨f, ?_, hfA⟩
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ f, hfA ▸ hA⟩
  have hScard' : S.card = T.card := by
    rw [← hTS]
    exact Finset.card_image_of_injective T sfSet_injective
  have hTcard : T.card = s := by omega
  -- `T` has at least two distinct elements.
  have hT1 : 1 < T.card := by omega
  obtain ⟨f0, hf0, g0, hg0, hfg0⟩ := Finset.one_lt_card.mp hT1
  -- `f0 ≠ g0` disagree at some coordinate `i`.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg0
  have hf0S : sfSet f0 ∈ S := by rw [← hTS]; exact Finset.mem_image_of_mem _ hf0
  have hg0S : sfSet g0 ∈ S := by rw [← hTS]; exact Finset.mem_image_of_mem _ hg0
  have hne0 : sfSet f0 ≠ sfSet g0 := fun h => hfg0 (sfSet_injective h)
  have hC : C = sfSet f0 ∩ sfSet g0 := (hSun _ hf0S _ hg0S hne0).symm
  -- Column `i` is entirely excluded from the core `C`.
  have hcol : ∀ c, (i, c) ∉ C := by
    intro c hc
    rw [hC, Finset.mem_inter, mem_sfSet, mem_sfSet] at hc
    exact hi (hc.1.symm.trans hc.2)
  -- The evaluation map `h ↦ h i` is injective on `T`.
  have hinj : Set.InjOn (fun h : Fin k → Fin (s - 1) => h i) T := by
    intro h1 h1T h2 h2T heq
    by_contra hne'
    have hSh1 : sfSet h1 ∈ S := by rw [← hTS]; exact Finset.mem_image_of_mem _ h1T
    have hSh2 : sfSet h2 ∈ S := by rw [← hTS]; exact Finset.mem_image_of_mem _ h2T
    have hneS : sfSet h1 ≠ sfSet h2 := fun h => hne' (sfSet_injective h)
    have hCeq : sfSet h1 ∩ sfSet h2 = C := hSun _ hSh1 _ hSh2 hneS
    have hmem : (i, h1 i) ∈ sfSet h1 ∩ sfSet h2 := by
      rw [Finset.mem_inter, mem_sfSet, mem_sfSet]
      exact ⟨rfl, heq⟩
    rw [hCeq] at hmem
    exact hcol (h1 i) hmem
  -- Pigeonhole: `|T| ≤ |Fin (s - 1)| = s - 1`, contradicting `|T| = s ≥ 2`.
  have hcard_le : T.card ≤ (Finset.univ : Finset (Fin (s - 1))).card :=
    Finset.card_le_card_of_injOn (fun h : Fin k → Fin (s - 1) => h i)
      (fun h _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, Fintype.card_fin, hTcard] at hcard_le
  omega

/-- **Sunflower lemma tightness.** For every `k` and every `s ≥ 2`, there is a family of
exactly `(s - 1)^k` distinct `k`-element sets containing no `s`-sunflower. This matches the
`k! · s^k` upper bound of `exists_isSunflower` up to the elementary `(s-1)^k` exponential
factor: some growth in `s^k` (or `(s-1)^k`) is unavoidable. -/
theorem exists_sunflower_free_family (k s : ℕ) (hs : 2 ≤ s) :
    ∃ F : Finset (Finset (Fin k × Fin (s - 1))), F.card = (s - 1) ^ k ∧
      (∀ A ∈ F, A.card = k) ∧
      ¬ ∃ S ⊆ F, S.card = s ∧ ∃ C, IsSunflower S C :=
  ⟨sfFamily k s, sfFamily_card, fun _ hA => sfFamily_mem_card hA, sfFamily_no_sunflower hs⟩

end ErdosRado
