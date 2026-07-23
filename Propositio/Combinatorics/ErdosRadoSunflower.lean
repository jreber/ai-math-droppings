/-
# The Erdős–Rado Sunflower Lemma

A *sunflower* (a.k.a. *Δ-system*) with `s` petals and core `C` is a family of `s` sets
whose pairwise intersections are all equal to the common set `C`.  Equivalently, the
"petals" (the sets with the core removed) are pairwise disjoint.

The **Erdős–Rado sunflower lemma** states that any family `F` of more than `k! · sᵏ`
finite sets, each of cardinality at most `k`, contains a sunflower with `s` petals.

This file proves the lemma from scratch by the classical Erdős–Rado induction on `k`.
mathlib (as of this writing) does not contain the sunflower lemma; a search of
`Mathlib/Combinatorics/SetFamily/` turns up no `Sunflower`/`IsSunflower` declaration.

The headline result is `ErdosRado.exists_isSunflower`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

open Finset

namespace ErdosRado

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower S C` means the family `S` is a sunflower with core `C`: any two distinct
members of `S` intersect in exactly `C`.  This is the standard ("Δ-system") definition; for
`s ≥ 2` petals it is non-vacuous, and it implies the core is contained in every petal and the
petals-minus-core are pairwise disjoint. -/
def IsSunflower (S : Finset (Finset α)) (C : Finset α) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

/-- **Erdős–Rado sunflower lemma.**  Any family `F` of more than `k! · sᵏ` sets, each of
cardinality at most `k`, contains a sunflower `S ⊆ F` with `s` petals (and some core `C`). -/
theorem exists_isSunflower (s k : ℕ) (hs : 1 ≤ s)
    (F : Finset (Finset α)) (hcard : ∀ A ∈ F, A.card ≤ k)
    (hbound : k.factorial * s ^ k < F.card) :
    ∃ S ⊆ F, S.card = s ∧ ∃ C, IsSunflower S C := by
  classical
  -- Write `s = t + 1` so that no truncated natural subtraction appears.
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  clear hs
  induction k generalizing F with
  | zero =>
    -- Base case: every set is empty, so `|F| ≤ 1`, contradicting `|F| > 0!·s⁰ = 1`.
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      have h0 : A.card ≤ 0 := hcard A hA
      have : A = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h0)
      simp [this]
    have hle : F.card ≤ 1 := by
      calc F.card ≤ ({∅} : Finset (Finset α)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    simp only [Nat.factorial_zero, pow_zero, one_mul] at hbound
    omega
  | succ n IH =>
    -- Pairwise-disjointness predicate on subfamilies.
    set PD : Finset (Finset α) → Prop :=
      fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B with hPD
    -- The family of all pairwise-disjoint subfamilies of `F`.
    set Dfam : Finset (Finset (Finset α)) := F.powerset.filter PD with hDfam
    have hP_ne : Dfam.Nonempty := by
      refine ⟨∅, ?_⟩
      rw [hDfam, Finset.mem_filter]
      exact ⟨Finset.empty_mem_powerset _, by intro A hA; simp at hA⟩
    -- Pick a maximum-cardinality pairwise-disjoint subfamily `M`.
    obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image Dfam Finset.card hP_ne
    rw [hDfam, Finset.mem_filter, Finset.mem_powerset] at hM_mem
    obtain ⟨hMsub, hMpd⟩ := hM_mem
    -- `U` is the union of the chosen disjoint family.
    set U : Finset α := M.biUnion id with hU
    by_cases hcase : t + 1 ≤ M.card
    · -- Case 1: `M` already contains `s = t+1` pairwise-disjoint sets — a sunflower, core `∅`.
      obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hcase
      refine ⟨S, hS_sub.trans hMsub, hS_card, ∅, ?_⟩
      intro A hA B hB hAB
      have : Disjoint A B := hMpd A (hS_sub hA) B (hS_sub hB) hAB
      exact Finset.disjoint_iff_inter_eq_empty.mp this
    · -- Case 2: `M` is small.  Every nonempty set of `F` meets `U`.
      have hMlt : M.card ≤ t := by omega
      -- Every nonempty `A ∈ F` is NOT disjoint from `U` (else `M` was not maximal).
      have hmeet : ∀ A ∈ F, A.Nonempty → ¬ Disjoint A U := by
        intro A hAF hAne hdisj
        by_cases hAM : A ∈ M
        · -- `A ⊆ U`, so `Disjoint A U` forces `A = ∅`.
          have hAU : A ⊆ U := Finset.subset_biUnion_of_mem id hAM
          have heq : A ∩ U = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
          rw [Finset.inter_eq_left.mpr hAU] at heq
          exact (Finset.nonempty_iff_ne_empty.mp hAne) heq
        · -- `insert A M` is a strictly larger pairwise-disjoint family: contradiction.
          have hM'sub : insert A M ⊆ F := Finset.insert_subset hAF hMsub
          have hM'pd : PD (insert A M) := by
            rw [hPD]
            intro X hX Y hY hXY
            rcases Finset.mem_insert.mp hX with rfl | hXM
            · rcases Finset.mem_insert.mp hY with rfl | hYM
              · exact absurd rfl hXY
              · have hYU : Y ⊆ U := Finset.subset_biUnion_of_mem id hYM
                exact hdisj.mono_right hYU
            · rcases Finset.mem_insert.mp hY with rfl | hYM
              · have hXU : X ⊆ U := Finset.subset_biUnion_of_mem id hXM
                exact (hdisj.mono_right hXU).symm
              · exact hMpd X hXM Y hYM hXY
          have hM'mem : insert A M ∈ Dfam := by
            rw [hDfam, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨hM'sub, hM'pd⟩
          have hle := hM_max _ hM'mem
          rw [Finset.card_insert_of_notMem hAM] at hle
          omega
      -- `|U| ≤ t·(n+1)`.
      have hU_card : U.card ≤ t * (n + 1) := by
        have h1 : U.card ≤ M.card * (n + 1) := by
          rw [hU]
          exact Finset.card_biUnion_le_card_mul M id (n + 1)
            (fun A hA => hcard A (hMsub hA))
        exact h1.trans (mul_le_mul_right' hMlt (n + 1))
      -- The induction-hypothesis bound for level `n`.
      set b : ℕ := n.factorial * (t + 1) ^ n with hbdef
      -- Pigeonhole: some `x ∈ U` lies in more than `b` members of `F`.
      have hexists : ∃ x ∈ U, b < (F.filter (fun A => x ∈ A)).card := by
        by_contra hcon
        push_neg at hcon
        -- Nonempty sets of `F` are covered by the fibres over `U`.
        have hsub : F.filter (fun A => A.Nonempty)
            ⊆ U.biUnion (fun x => F.filter (fun A => x ∈ A)) := by
          intro A hA
          rw [Finset.mem_filter] at hA
          obtain ⟨hAF, hAne⟩ := hA
          obtain ⟨x, hx⟩ := not_disjoint_iff_nonempty_inter.mp (hmeet A hAF hAne)
          rw [Finset.mem_inter] at hx
          rw [Finset.mem_biUnion]
          exact ⟨x, hx.2, Finset.mem_filter.mpr ⟨hAF, hx.1⟩⟩
        have hle1 : (F.filter (fun A => A.Nonempty)).card ≤ U.card * b :=
          (Finset.card_le_card hsub).trans
            (Finset.card_biUnion_le_card_mul U _ b hcon)
        -- Lower bound: at most one set of `F` is empty.
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := F) (fun A => A.Nonempty)
        have hneg : (F.filter (fun A => ¬ A.Nonempty)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b' hb'
          rw [Finset.mem_filter] at ha hb'
          rw [Finset.not_nonempty_iff_eq_empty.mp ha.2,
              Finset.not_nonempty_iff_eq_empty.mp hb'.2]
        have hfilt : (n + 1).factorial * (t + 1) ^ (n + 1)
            ≤ (F.filter (fun A => A.Nonempty)).card := by omega
        -- Combine the bounds into a numeric contradiction.
        have hchain : (n + 1).factorial * (t + 1) ^ (n + 1) ≤ t * (n + 1) * b :=
          hfilt.trans (hle1.trans (mul_le_mul_right' hU_card b))
        -- Let `X := (n+1)!·(t+1)ⁿ`.  Then LHS = `(t+1)·X` and RHS = `t·X`.
        have hcontra : (t + 1) * ((n + 1).factorial * (t + 1) ^ n)
            ≤ t * ((n + 1).factorial * (t + 1) ^ n) := by
          calc (t + 1) * ((n + 1).factorial * (t + 1) ^ n)
              = (n + 1).factorial * (t + 1) ^ (n + 1) := by rw [pow_succ]; ring
            _ ≤ t * (n + 1) * b := hchain
            _ = t * ((n + 1).factorial * (t + 1) ^ n) := by
                rw [hbdef, Nat.factorial_succ]; ring
        have hXpos : 0 < (n + 1).factorial * (t + 1) ^ n := by positivity
        have hatom : t * ((n + 1).factorial * (t + 1) ^ n)
            + ((n + 1).factorial * (t + 1) ^ n)
            ≤ t * ((n + 1).factorial * (t + 1) ^ n) := by
          rwa [add_one_mul] at hcontra
        omega
      -- Extract the heavy element `x` and pass to level `n`.
      obtain ⟨x, _hxU, hxcard⟩ := hexists
      -- `erase x` is injective on the sets of `F` containing `x`.
      have hinj : Set.InjOn (fun A => Finset.erase A x)
          (F.filter (fun A => x ∈ A)) := by
        intro A hA B hB hAB
        rw [Finset.mem_coe, Finset.mem_filter] at hA hB
        have hxA : x ∈ A := hA.2
        have hxB : x ∈ B := hB.2
        replace hAB : A.erase x = B.erase x := hAB
        rw [← Finset.insert_erase hxA, hAB, Finset.insert_erase hxB]
      -- The level-`n` family `G`.
      set G : Finset (Finset α) :=
        (F.filter (fun A => x ∈ A)).image (fun A => Finset.erase A x) with hG
      have hGcard : G.card = (F.filter (fun A => x ∈ A)).card := by
        rw [hG]; exact Finset.card_image_of_injOn hinj
      have hGsmall : ∀ B ∈ G, B.card ≤ n := by
        intro B hB
        rw [hG, Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [Finset.mem_filter] at hA
        have hAcard : A.card ≤ n + 1 := hcard A hA.1
        rw [Finset.card_erase_of_mem hA.2]
        omega
      have hGbound : n.factorial * (t + 1) ^ n < G.card := by
        rw [hGcard, ← hbdef]; exact hxcard
      -- Apply the induction hypothesis at level `n`.
      obtain ⟨S, hS_sub, hS_card, C', hC'⟩ := IH G hGsmall hGbound
      -- Lift `S` back to a sunflower in `F` by re-inserting `x`.
      set S' : Finset (Finset α) :=
        (F.filter (fun A => x ∈ A)).filter (fun A => A.erase x ∈ S) with hS'
      have hS'_sub_Fx : S' ⊆ F.filter (fun A => x ∈ A) := by
        rw [hS']; exact Finset.filter_subset _ _
      have hS'image : S'.image (fun A => Finset.erase A x) = S := by
        apply Finset.Subset.antisymm
        · intro B hB
          rw [Finset.mem_image] at hB
          obtain ⟨A, hA, rfl⟩ := hB
          rw [hS', Finset.mem_filter] at hA
          exact hA.2
        · intro B hB
          have hBG : B ∈ G := hS_sub hB
          rw [hG, Finset.mem_image] at hBG
          obtain ⟨A, hA, hAB⟩ := hBG
          rw [Finset.mem_image]
          refine ⟨A, ?_, hAB⟩
          rw [hS', Finset.mem_filter]
          exact ⟨hA, by rw [hAB]; exact hB⟩
      have hinj' : Set.InjOn (fun A => Finset.erase A x) S' :=
        hinj.mono (Finset.coe_subset.mpr hS'_sub_Fx)
      have hS'card : S'.card = t + 1 := by
        rw [← Finset.card_image_of_injOn hinj', hS'image]; exact hS_card
      -- `S'` is a sunflower with core `insert x C'`.
      have hSun : IsSunflower S' (insert x C') := by
        intro A hA B hB hAB
        rw [hS', Finset.mem_filter] at hA hB
        obtain ⟨hAFx, hAS⟩ := hA
        obtain ⟨hBFx, hBS⟩ := hB
        have hxA : x ∈ A := (Finset.mem_filter.mp hAFx).2
        have hxB : x ∈ B := (Finset.mem_filter.mp hBFx).2
        have hne : A.erase x ≠ B.erase x := by
          intro h
          apply hAB
          rw [← Finset.insert_erase hxA, h, Finset.insert_erase hxB]
        have hcore : (A.erase x) ∩ (B.erase x) = C' := hC' _ hAS _ hBS hne
        have hset : (A ∩ B).erase x = (A.erase x) ∩ (B.erase x) := by
          ext y
          simp only [Finset.mem_erase, Finset.mem_inter]
          tauto
        have hxAB : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA, hxB⟩
        calc A ∩ B = insert x ((A ∩ B).erase x) := (Finset.insert_erase hxAB).symm
          _ = insert x C' := by rw [hset, hcore]
      refine ⟨S', ?_, hS'card, insert x C', hSun⟩
      intro A hA
      have hAFx : A ∈ F.filter (fun A => x ∈ A) := hS'_sub_Fx hA
      exact (Finset.mem_filter.mp hAFx).1

end ErdosRado
