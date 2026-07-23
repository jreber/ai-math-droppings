/-
# Friendship vertex count mod (k − 1)

A quick corollary of `FriendshipVertexCount.friendship_card_eq`: since
`n = k² − k + 1 = (k − 1)·k + 1`, the vertex count of a `k`-regular friendship
graph (`k ≥ 1`) is congruent to `1` modulo `k − 1`.
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Nat.ModEq
import Propositio.Combinatorics.FriendshipMatrixEquation
import Propositio.Combinatorics.FriendshipVertexCount

namespace FriendshipCardMod

open SimpleGraph FriendshipVertexCount FriendshipMatrixEquation

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Vertex count mod `k − 1` for regular friendship graphs.**
If `G` is a `k`-regular friendship graph (`k ≥ 1`) on `n = |V|` vertices, then
`n ≡ 1 [MOD (k − 1)]`, since `n = (k − 1)·k + 1`. -/
theorem friendship_card_modEq (hfriend : Friendship G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : G.IsRegularOfDegree k) [Nonempty V] :
    Fintype.card V ≡ 1 [MOD (k - 1)] := by
  have hz := FriendshipVertexCount.friendship_card_eq G hfriend hreg
  have hnat : Fintype.card V = (k - 1) * k + 1 := by
    zify [hk]
    rw [hz]
    ring
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have hdvd : (k - 1) ∣ (Fintype.card V - 1) := by
    rw [hnat, Nat.add_sub_cancel]
    exact dvd_mul_right (k - 1) k
  exact ((Nat.modEq_iff_dvd' h1).mpr hdvd).symm

end FriendshipCardMod
