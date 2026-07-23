/-
# Machine-checked non-vacuity witness for the Friendship cluster

The friendship theorems (`friendship_card_eq`, `friendship_card_odd`, `friendship_card_modEq`)
are universally-quantified implications; prior panels flagged that their non-vacuity was only
asserted in prose. This file discharges the hypotheses on a concrete finite graph — the triangle
`K₃ = (⊤ : SimpleGraph (Fin 3))`, a `2`-regular friendship graph — so the whole cluster is
mechanically witnessed to be non-vacuous.
-/
import Propositio.Combinatorics.FriendshipVertexCount
import Propositio.Combinatorics.FriendshipOddOrder
import Propositio.Combinatorics.FriendshipCardMod
import Mathlib.Data.Fintype.Basic

open SimpleGraph FriendshipMatrixEquation

namespace FriendshipK3Example

/-- The triangle `K₃`, as the complete graph on `Fin 3`. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

instance : DecidableRel K3.Adj := fun a b => inferInstanceAs (Decidable (a ≠ b))

/-- `K₃` is a friendship graph: any two distinct vertices have a unique common neighbour. -/
theorem k3_friendship : Friendship K3 := by
  intro u v huv
  fin_cases u <;> fin_cases v <;>
    first
      | exact absurd rfl huv
      | (simp only [ExistsUnique, ne_eq, K3, SimpleGraph.top_adj]; decide)

/-- `K₃` is `2`-regular. -/
theorem k3_regular : K3.IsRegularOfDegree 2 := by
  simpa using
    (SimpleGraph.IsRegularOfDegree.top : (⊤ : SimpleGraph (Fin 3)).IsRegularOfDegree _)

-- The three cluster headlines fire on this concrete witness:
example : (Fintype.card (Fin 3) : ℤ) = (2 : ℤ) ^ 2 - 2 + 1 :=
  FriendshipVertexCount.friendship_card_eq K3 k3_friendship k3_regular

example : Odd (Fintype.card (Fin 3)) :=
  FriendshipOddOrder.friendship_card_odd K3 k3_friendship k3_regular

example : Fintype.card (Fin 3) ≡ 1 [MOD (2 - 1)] :=
  FriendshipCardMod.friendship_card_modEq K3 k3_friendship (by norm_num) k3_regular

end FriendshipK3Example
