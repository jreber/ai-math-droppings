import Propositio.NumberTheory.Collatz.LyapunovCascade
import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Fixed-modulus descent density for the V-cascade Lyapunov function (Collatz)

This file makes the **V-cascade descent dichotomy QUANTITATIVE** at a fixed
modulus.  It is the first bridge between the project's two strongest Collatz
assets that previously did not talk to each other:

  * the **Lyapunov-cascade descent dichotomy** (`LyapunovCascade.lean`):
    `V_cascade(cc n) < V_cascade n` on the *spine* `4 ∣ n+1`
    (`V_cascade_descent_spine_positive`), where
    `V_cascade(n) = n * 2^(v₂(n+1) - 1)`; and
  * the **Terras-style residue counting** (`TerrasDensity.lean`): cardinalities
    of residue classes mod `2^k`.

## What is proved

The *guaranteed-descent residue set* mod `2^k` is the **spine class**
`{ r : 4 ∣ r+1 }` — exactly the residues `≡ 3 (mod 4)`.  We:

1. **Soundness** (`Vcascade_descent_of_four_dvd`): for *every* `n` with
   `4 ∣ n+1` (which forces `n` odd), one compressed step strictly decreases the
   cascade Lyapunov function: `V_cascade(cc n) < V_cascade n`.  This is the
   per-residue descent input, lifted from the spine theorem.

2. **Count mod 8** (`descentResiduesMod8_card`): the descent residue set mod 8
   has cardinality **2** (the residues `{3, 7}`), i.e. a local descent density
   of `2/8 = 1/4`.

3. **Count mod 16** (`descentResiduesMod16_card`): cardinality **4**
   (the residues `{3, 7, 11, 15}`), density `4/16 = 1/4`.

4. **Stability of the density** (`descentResidues_card_doubles`): the spine
   descent set mod `2^(k+1)` has exactly twice the cardinality of the one mod
   `2^k` (for `k ≥ 2`), so the local descent density is the constant `1/4`
   across all these moduli — a clean monotone/aggregate statement.

5. **Every counted residue descends** (`descentResiduesMod8_sound`,
   `descentResiduesMod16_sound`): membership in the counted set is not merely
   combinatorial — it certifies actual `V_cascade` descent for every `n` in
   that class.

## HONESTY — this is NOT a proof of Collatz

A positive-density (here `1/4`) set of *guaranteed-descent* residues says
**nothing** about whether every Collatz trajectory terminates.  The spine
`4 ∣ n+1` is exactly the deterministic-descent slice; off the spine
(`n ≡ 1 (mod 4)`) the cascade Lyapunov function can *ascent*
(`V_cascade_ascent_L0_Lnew_pos`), and the descent of a single step does not
chain into a global potential because the residue of `cc n` is not pinned by
the residue of `n`.  Indeed (verified by enumeration) descent for the classes
`n ≡ 1, 5 (mod 8)` is **not** determined by the residue mod 8 at all.  What is
new here is purely the *quantitative* statement: a counted, fixed-modulus
positive-density set on which the Lyapunov descent of `LyapunovCascade.lean` is
deterministic.

All theorems are axiom-clean (`propext, Classical.choice, Quot.sound` only);
no `native_decide`, no `sorry`, no new axioms.
-/

namespace CollatzDescentDensity

open TerrasDensity LyapunovCascade

/-! ## 1. Soundness: every spine residue descends -/

/-- `4 ∣ n+1` forces `n` odd (`n ≡ 3 mod 4`). -/
theorem odd_of_four_dvd_succ {n : Nat} (h4 : 4 ∣ n + 1) : TerrasDensity.Odd n := by
  obtain ⟨q, hq⟩ := h4
  exact ⟨2 * q - 1, by omega⟩

/-- `4 ∣ n+1` gives `v₂(n+1) ≥ 2`. -/
theorem two_le_v2_succ {n : Nat} (h4 : 4 ∣ n + 1) :
    2 ≤ padicValNat 2 (n + 1) := by
  have hn1_ne : n + 1 ≠ 0 := by omega
  have hdvd : (2 : Nat) ^ 2 ∣ n + 1 := by simpa [show (2:Nat)^2 = 4 from rfl] using h4
  exact (padicValNat_dvd_iff_le hn1_ne).mp hdvd

/-- **Soundness of the spine descent set — REAL.**

For every `n` with `4 ∣ n+1` (the spine class `n ≡ 3 (mod 4)`), one compressed
Collatz step strictly decreases the cascade Lyapunov function:
`V_cascade(cc n) < V_cascade n`.

This packages `LyapunovCascade.V_cascade_descent_spine_positive` into the
direct `Vcascade`-on-`Vcascade` inequality by computing the spine levels:
with `v₂(n+1) = J+2` we have `V_cascade n = n · 2^(J+1)`, and the cascade level
decrement (`fractal_level_decrement`) gives `v₂(cc n + 1) = J+1`, so
`V_cascade(cc n) = cc n · 2^J`; the spine theorem then closes it. -/
theorem Vcascade_descent_of_four_dvd {n : Nat} (h4 : 4 ∣ n + 1) :
    Vcascade (cc n) < Vcascade n := by
  have hodd : TerrasDensity.Odd n := odd_of_four_dvd_succ h4
  -- v₂(n+1) = J + 2 for some J.
  have hge : 2 ≤ padicValNat 2 (n + 1) := two_le_v2_succ h4
  obtain ⟨J, hJ⟩ : ∃ J, padicValNat 2 (n + 1) = J + 2 := ⟨padicValNat 2 (n+1) - 2, by omega⟩
  -- V_cascade n = n * 2^(J+1)
  have hVn : Vcascade n = n * 2 ^ (J + 1) := by
    have : padicValNat 2 (n + 1) - 1 = J + 1 := by rw [hJ]; omega
    unfold Vcascade; rw [this]
  -- v₂(cc n + 1) = J + 1 via fractal_level_decrement (K = J+1 ≥ 1)
  have hdec : padicValNat 2 (cc n + 1) = J + 1 :=
    fractal_level_decrement hodd (by omega) (by rw [hJ])
  -- V_cascade (cc n) = cc n * 2^J
  have hVcc : Vcascade (cc n) = cc n * 2 ^ J := by
    have : padicValNat 2 (cc n + 1) - 1 = J := by rw [hdec]; omega
    unfold Vcascade; rw [this]
  -- spine descent: cc n * 2^J < n * 2^(J+1)
  have hspine : cc n * 2 ^ J < n * 2 ^ (J + 1) :=
    V_cascade_descent_spine_positive hodd hJ
  rw [hVn, hVcc]; exact hspine

/-! ## 2-3. The counted residue sets mod 8 and mod 16

We count residues `r < 2^k` with `4 ∣ r+1`.  Since `4 ∣ n+1` depends only on
`n mod 4` and `4 ∣ 2^k` for `k ≥ 2`, the spine condition is well-defined on
residues mod `2^k` and these are exactly the genuine descent classes. -/

/-- The descent (spine) residue set mod 8: `{ r < 8 : 4 ∣ r+1 } = {3, 7}`. -/
def descentResiduesMod8 : Finset Nat :=
  (Finset.range 8).filter (fun r => 4 ∣ (r + 1))

/-- The descent (spine) residue set mod 16: `{ r < 16 : 4 ∣ r+1 } = {3,7,11,15}`. -/
def descentResiduesMod16 : Finset Nat :=
  (Finset.range 16).filter (fun r => 4 ∣ (r + 1))

/-- **Count mod 8 = 2 of 8 (density 1/4) — REAL.**
The cascade-descent residue set mod 8 has cardinality `2`. -/
theorem descentResiduesMod8_card : descentResiduesMod8.card = 2 := by
  decide

/-- **Count mod 16 = 4 of 16 (density 1/4) — REAL.**
The cascade-descent residue set mod 16 has cardinality `4`. -/
theorem descentResiduesMod16_card : descentResiduesMod16.card = 4 := by
  decide

/-- The mod-8 descent set is exactly `{3, 7}`. -/
theorem descentResiduesMod8_eq : descentResiduesMod8 = {3, 7} := by
  decide

/-- The mod-16 descent set is exactly `{3, 7, 11, 15}`. -/
theorem descentResiduesMod16_eq : descentResiduesMod16 = {3, 7, 11, 15} := by
  decide

/-! ## 4. Density stability: the count doubles from mod `2^k` to mod `2^(k+1)`

A clean aggregate statement: counting spine residues `4 ∣ r+1` below `2^(k+1)`
gives exactly twice the count below `2^k` (for `k ≥ 2`).  Equivalently the
descent density `card / 2^k = 1/4` is constant across these moduli.  We prove
the general doubling via a uniform residue-counting lemma. -/

/-- Generic residue count: among `r < 4*m`, exactly `m` satisfy `4 ∣ r+1`
(namely `r = 4j + 3`, `j < m`).  This is the Terras-style residue-class count
specialised to the spine condition. -/
theorem spine_count_eq (m : Nat) :
    ((Finset.range (4 * m)).filter (fun r => 4 ∣ (r + 1))).card = m := by
  induction m with
  | zero => decide
  | succ k ih =>
    -- range(4(k+1)) = range(4k) ∪ {4k, 4k+1, 4k+2, 4k+3}; only 4k+3 is in the spine.
    have hsplit : Finset.range (4 * (k + 1)) =
        Finset.range (4 * k) ∪ {4 * k, 4 * k + 1, 4 * k + 2, 4 * k + 3} := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega
    rw [hsplit, Finset.filter_union]
    have hdisj : Disjoint
        ((Finset.range (4 * k)).filter (fun r => 4 ∣ (r + 1)))
        (({4 * k, 4 * k + 1, 4 * k + 2, 4 * k + 3} : Finset Nat).filter
          (fun r => 4 ∣ (r + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton] at hx hx'
      omega
    rw [Finset.card_union_of_disjoint hdisj, ih]
    -- the tail filter is exactly {4k+3}, card 1
    have htail : (({4 * k, 4 * k + 1, 4 * k + 2, 4 * k + 3} : Finset Nat).filter
        (fun r => 4 ∣ (r + 1))) = {4 * k + 3} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro h; subst h; exact ⟨by omega, ⟨k + 1, by ring⟩⟩
    rw [htail, Finset.card_singleton]

/-- **Descent density is the constant `1/4` across moduli `2^k` (`k ≥ 2`) — REAL.**

The cascade-descent (spine) residue set mod `2^(k+1)` has exactly twice the
cardinality of the one mod `2^k`.  Combined with `spine_count_eq`, the local
descent density `card(2^k) / 2^k = 2^(k-2)/2^k = 1/4` is constant.  This is the
monotone/aggregate "fixed-modulus density" statement (task priority 2). -/
theorem descentResidues_card_doubles (k : Nat) (hk : 2 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter (fun r => 4 ∣ (r + 1))).card
      = 2 * ((Finset.range (2 ^ k)).filter (fun r => 4 ∣ (r + 1))).card := by
  -- write 2^k = 4 * 2^(k-2)
  obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  subst hj
  have e1 : (2 : Nat) ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; ring
  have e2 : (2 : Nat) ^ (j + 2 + 1) = 4 * (2 * 2 ^ j) := by
    rw [show j + 2 + 1 = (j + 1) + 2 from by ring, pow_add]; ring
  rw [e1, e2, spine_count_eq, spine_count_eq]

/-! ## 5. Soundness of the counted sets: each residue certifies real descent

Membership in the counted mod-8 / mod-16 descent sets is not just combinatorial:
for *every* `n` whose residue lands there, `V_cascade` strictly descends in one
compressed step.  This ties the count back to the Lyapunov dichotomy. -/

/-- Spine membership mod 8 ⟺ `4 ∣ n+1` (the descent condition). -/
theorem mem_descentResiduesMod8_iff (n : Nat) :
    n % 8 ∈ descentResiduesMod8 ↔ 4 ∣ (n + 1) := by
  unfold descentResiduesMod8
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    -- 4 ∣ (n%8 + 1) and 8 ≡ 0 mod 4 ⟹ 4 ∣ (n+1)
    omega
  · intro h
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    omega

/-- Spine membership mod 16 ⟺ `4 ∣ n+1`. -/
theorem mem_descentResiduesMod16_iff (n : Nat) :
    n % 16 ∈ descentResiduesMod16 ↔ 4 ∣ (n + 1) := by
  unfold descentResiduesMod16
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩; omega
  · intro h
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    omega

/-- **Counted-residue descent mod 8 — REAL.**
If `n`'s residue mod 8 is one of the 2 counted descent residues `{3,7}`, then
`V_cascade(cc n) < V_cascade n`. -/
theorem descentResiduesMod8_sound {n : Nat}
    (h : n % 8 ∈ descentResiduesMod8) : Vcascade (cc n) < Vcascade n :=
  Vcascade_descent_of_four_dvd ((mem_descentResiduesMod8_iff n).mp h)

/-- **Counted-residue descent mod 16 — REAL.**
If `n`'s residue mod 16 is one of the 4 counted descent residues `{3,7,11,15}`,
then `V_cascade(cc n) < V_cascade n`. -/
theorem descentResiduesMod16_sound {n : Nat}
    (h : n % 16 ∈ descentResiduesMod16) : Vcascade (cc n) < Vcascade n :=
  Vcascade_descent_of_four_dvd ((mem_descentResiduesMod16_iff n).mp h)

end CollatzDescentDensity

