/-
# The Erdős–Rado Sunflower Lemma — Sharpened Constant

`ErdosRadoSunflower.lean` proves that any family `F` of more than `k! · sᵏ` finite sets, each
of cardinality *at most* `k`, contains an `s`-sunflower.  This file sharpens the exponential
base from `s` to `s - 1`, matching the standard textbook (Jukna, Erdős–Rado) constant:

  any family `F` of more than `k! · (s-1)ᵏ` finite sets, each of cardinality *exactly* `k`,
  contains an `s`-sunflower.

This is the same bound proved in Isabelle/AFP's `Sunflowers` entry (Thiemann 2021), and it
matches, up to the `k!` factor, the lower bound of `SunflowerTightness.lean`
(`ErdosRado.exists_sunflower_free_family`: there is a family of exactly `(s-1)ᵏ` `k`-element
sets with no `s`-sunflower).  So for `k`-uniform families the codebase's upper and lower
bounds now share the *same* exponential base `(s-1)ᵏ`, and the remaining gap between them is
exactly the `k!` factor (the true extremal bound — the "sunflower conjecture" territory —
replaces `k!` by `Cᵏ` for some constant `C`, and remains a famous open problem).

## Where the sharpening comes from

The proof is the *same* Erdős–Rado induction as `ErdosRadoSunflower.lean` — same maximal
pairwise-disjoint family `M`, same "heavy point" pigeonhole step, same erase-and-recurse — but
restricting the hypothesis to sets of *exact* cardinality `k` (rather than `≤ k`) removes a unit
of slack that the original proof spent on the possibility of an empty set. Tracking `s = t + 1`
(`t = s - 1`):

* In the `≤ k` proof, the induction hypothesis is applied with a bound `b = n! · (t+1)ⁿ`
  ( `= n! · sⁿ` at level `n` ), and the final numeric contradiction compares `(t+1)·X` against
  `t·X` for `X = (n+1)! · (t+1)ⁿ` — a full unit of slack in the coefficient of `X`. That slack
  is exactly what absorbs the weak inequality `|F.filter (¬Nonempty)| ≤ 1` (at most one member
  of `F` can be the empty set, when sets only have card `≤ k`).
* Once every set in `F` has cardinality *exactly* `k = n+1 ≥ 1`, every set is automatically
  nonempty — the `≤ 1` slack term vanishes identically, `F.filter Nonempty = F`, and `hbound`'s
  strict inequality `(n+1)! · t^(n+1) < F.card` transfers verbatim into the pigeonhole chain.
  The induction hypothesis can then be run with the *tighter* bound `b = n! · tⁿ` (i.e. `(s-1)ⁿ`,
  not `sⁿ`), and the chain closes with *zero* slack: assuming every heavy point covers at most
  `b` sets forces `(n+1)! · t^(n+1) < (n+1)! · t^(n+1)`, an immediate contradiction — no residual
  bookkeeping needed.

The headline result is `ErdosRado.exists_isSunflower_tight`.
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
import Propositio.Combinatorics.ErdosRadoSunflower
import Propositio.Combinatorics.SunflowerTightness

open Finset

namespace ErdosRado

variable {α : Type*} [DecidableEq α]

/-- **Erdős–Rado sunflower lemma, sharpened constant.**  Any family `F` of more than
`k! · (s-1)ᵏ` sets, each of cardinality *exactly* `k`, contains a sunflower `S ⊆ F` with `s`
petals (and some core `C`).  This sharpens `ErdosRado.exists_isSunflower`'s `k! · sᵏ` bound to
the textbook-optimal `k! · (s-1)ᵏ`, at the cost of requiring the family to be `k`-uniform
(exact cardinality, not merely bounded by `k`) — see the module docstring for exactly where the
tighter margin comes from. -/
theorem exists_isSunflower_tight (s k : ℕ) (hs : 1 ≤ s)
    (F : Finset (Finset α)) (hcard : ∀ A ∈ F, A.card = k)
    (hbound : k.factorial * (s - 1) ^ k < F.card) :
    ∃ S ⊆ F, S.card = s ∧ ∃ C, IsSunflower S C := by
  classical
  -- Write `s = t + 1` so that no truncated natural subtraction appears.
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  clear hs
  simp only [Nat.add_sub_cancel] at hbound
  induction k generalizing F with
  | zero =>
    -- Base case: every set is empty, so `|F| ≤ 1`, contradicting `|F| > 0!·(s-1)⁰ = 1`.
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      have h0 : A.card = 0 := hcard A hA
      have : A = ∅ := Finset.card_eq_zero.mp h0
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
    · -- Case 2: `M` is small.  Every set of `F` (all nonempty, since `A.card = n+1 ≥ 1`)
      -- meets `U`.
      have hMlt : M.card ≤ t := by omega
      have hAne_all : ∀ A ∈ F, A.Nonempty := by
        intro A hA
        rw [← Finset.card_pos, hcard A hA]
        omega
      have hmeet : ∀ A ∈ F, ¬ Disjoint A U := by
        intro A hAF hdisj
        have hAne := hAne_all A hAF
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
            (fun A hA => (hcard A (hMsub hA)).le)
        exact h1.trans (mul_le_mul_right' hMlt (n + 1))
      -- The SHARPENED induction-hypothesis bound for level `n`: `n! · tⁿ`, not `n! · (t+1)ⁿ`.
      set b : ℕ := n.factorial * t ^ n with hbdef
      -- Pigeonhole: some `x ∈ U` lies in more than `b` members of `F`.  With every set of `F`
      -- nonempty, the chain closes with *zero* slack (contrast with `ErdosRadoSunflower.lean`,
      -- which spends a full unit of slack absorbing the possibility of one empty set).
      have hexists : ∃ x ∈ U, b < (F.filter (fun A => x ∈ A)).card := by
        by_contra hcon
        push_neg at hcon
        -- Every set of `F` is covered by the fibres over `U` (all sets are nonempty here).
        have hsub : F ⊆ U.biUnion (fun x => F.filter (fun A => x ∈ A)) := by
          intro A hA
          obtain ⟨x, hx⟩ := not_disjoint_iff_nonempty_inter.mp (hmeet A hA)
          rw [Finset.mem_inter] at hx
          rw [Finset.mem_biUnion]
          exact ⟨x, hx.2, Finset.mem_filter.mpr ⟨hA, hx.1⟩⟩
        have hle1 : F.card ≤ U.card * b :=
          (Finset.card_le_card hsub).trans
            (Finset.card_biUnion_le_card_mul U _ b hcon)
        have hcontra : (n + 1).factorial * t ^ (n + 1) < t * (n + 1) * b :=
          hbound.trans_le (hle1.trans (mul_le_mul_right' hU_card b))
        have heq : t * (n + 1) * b = (n + 1).factorial * t ^ (n + 1) := by
          rw [hbdef, Nat.factorial_succ]; ring
        rw [heq] at hcontra
        exact lt_irrefl _ hcontra
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
      have hGsmall : ∀ B ∈ G, B.card = n := by
        intro B hB
        rw [hG, Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [Finset.mem_filter] at hA
        have hAcard : A.card = n + 1 := hcard A hA.1
        rw [Finset.card_erase_of_mem hA.2]
        omega
      have hGbound : n.factorial * t ^ n < G.card := by
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

/-- **Matching upper/lower bound for `k`-uniform families, up to `k!`.**  Combining
`exists_isSunflower_tight` (more than `k! · (s-1)ᵏ` `k`-sets force an `s`-sunflower) with
`ErdosRado.exists_sunflower_free_family` (there is a family of exactly `(s-1)ᵏ` `k`-sets with
*no* `s`-sunflower) pins the extremal threshold for `k`-uniform families to within the `k!`
factor: `(s-1)ᵏ` sets can avoid a sunflower, but `k! · (s-1)ᵏ + 1` sets cannot. -/
theorem sunflower_threshold_matches_up_to_factorial (s k : ℕ) (hs : 2 ≤ s) :
    (∃ F : Finset (Finset (Fin k × Fin (s - 1))), F.card = (s - 1) ^ k ∧
        (∀ A ∈ F, A.card = k) ∧
        ¬ ∃ S ⊆ F, S.card = s ∧ ∃ C, IsSunflower S C) ∧
    (∀ F : Finset (Finset (Fin k × Fin (s - 1))), (∀ A ∈ F, A.card = k) →
        k.factorial * (s - 1) ^ k < F.card →
        ∃ S ⊆ F, S.card = s ∧ ∃ C, IsSunflower S C) :=
  ⟨exists_sunflower_free_family k s hs,
    fun F hcard hbound => exists_isSunflower_tight s k (by omega) F hcard hbound⟩

end ErdosRado
