/-
NEW (no LaTTe sibling) — k-variable generalization of BealDensity.pair_solution_count.

For `n > 0`, `k ≥ 1`, coefficients `x : Fin k → ℕ`, the number of solutions of the
single linear congruence `∑ i, xᵢ · vᵢ ≡ 0 (mod n)` in `(ZMod n)^k` is

    n^(k-1) · gcd(n, gcd of all xᵢ).

The k=2 case is `BealDensity.pair_solution_count`.

Route: `linHom : (Fin k → ZMod n) →+ ZMod n`, `v ↦ ∑ i, xᵢ • vᵢ`.
  |ker| · |range| = |domain| = n^k  (Lagrange / first iso),
  range linHom = range (nsmulAddMonoidHom (gcd xᵢ)), of size n / gcd(n, gcd xᵢ),
  ⇒ |ker| = n^k / (n / g) = n^(k-1) · g.
The `⊇` half of the range equality (that `g • c` is a combination of the `xᵢ • ·`)
is proved by induction on the finset of coordinates (`AddSubgroup`-containment),
avoiding explicit multi-variable Bézout coefficients.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Propositio.Beal.Density

open AddMonoidHom

namespace BealDensityKVar

/-- The additive hom `(Fin k → ZMod n) →+ ZMod n`, `v ↦ ∑ i, xᵢ • vᵢ`. -/
noncomputable def linHom (n : ℕ) (k : ℕ) (x : Fin k → ℕ) : (Fin k → ZMod n) →+ ZMod n where
  toFun v := ∑ i, (x i) • v i
  map_zero' := by simp
  map_add' v w := by
    simp only [Pi.add_apply, smul_add]
    rw [Finset.sum_add_distrib]

@[simp] theorem linHom_apply (n k : ℕ) (x : Fin k → ℕ) (v : Fin k → ZMod n) :
    linHom n k x v = ∑ i, (x i) • v i := rfl

/-- Domain cardinality: `|Fin k → ZMod n| = n^k`. -/
theorem card_domain (n k : ℕ) [NeZero n] :
    Nat.card (Fin k → ZMod n) = n ^ k := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Range of `linHom`.** The image of `v ↦ ∑ xᵢ • vᵢ` equals the image of the
single-variable map `c ↦ g • c` for `g = gcd(all xᵢ)`. -/
theorem linHom_range (n k : ℕ) [NeZero n] (x : Fin k → ℕ) :
    (linHom n k x).range
      = (nsmulAddMonoidHom (α := ZMod n) (Finset.univ.gcd x)).range := by
  apply le_antisymm
  · -- ⊆ : each `∑ xᵢ • vᵢ` is a multiple of `g = gcd xᵢ` since `g ∣ xᵢ`.
    rintro _ ⟨v, rfl⟩
    simp only [linHom_apply, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    -- For each i, gcd ∣ xᵢ, so xᵢ • vᵢ = gcd • (qᵢ • vᵢ).
    have hdvd : ∀ i : Fin k, Finset.univ.gcd x ∣ x i := fun i =>
      Finset.gcd_dvd (Finset.mem_univ i)
    choose q hq using hdvd
    refine ⟨∑ i, (q i) • v i, ?_⟩
    rw [← Finset.sum_nsmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, ← hq i]
  · -- ⊇ : `g • c ∈ range linHom`. Reduce to the subgroup containing each generator.
    rintro _ ⟨c, rfl⟩
    simp only [nsmulAddMonoidHom_apply]
    -- It suffices that every `(x i) • c` is in range, and the range is a subgroup
    -- closed under the gcd combination. We prove `g • c ∈ range` by finset induction.
    have key : ∀ (s : Finset (Fin k)),
        (s.gcd x : ℕ) • c ∈ (linHom n k x).range := by
      intro s
      induction s using Finset.induction with
      | empty =>
        simp only [Finset.gcd_empty]
        rw [zero_smul]
        exact zero_mem _
      | @insert a s ha ih =>
        rw [Finset.gcd_insert]
        set sg : ℕ := s.gcd x with hsg
        -- gcd (x a) (s.gcd x) • c : Bézout between (x a) and (s.gcd x).
        -- (x a) • c ∈ range (the single coordinate a), s.gcd x • c ∈ range (ih).
        have hxa : (x a : ℕ) • c ∈ (linHom n k x).range := by
          rw [AddMonoidHom.mem_range]
          refine ⟨Pi.single a c, ?_⟩
          rw [linHom_apply]
          rw [Finset.sum_eq_single a]
          · rw [Pi.single_eq_same]
          · intro b _ hb
            rw [Pi.single_eq_of_ne hb, smul_zero]
          · intro h; exact absurd (Finset.mem_univ a) h
        -- Bézout: gcd(x a, s.gcd x) • c = u·(x a)•c + v·(s.gcd x)•c (over ℤ).
        set d := Nat.gcd (x a) sg with hd
        have hbez : (d : ℤ) • c
            = (Nat.gcdA (x a) sg) • ((x a : ℕ) • c)
              + (Nat.gcdB (x a) sg) • ((sg : ℕ) • c) := by
          have e1 : ((x a : ℕ) • c) = ((x a : ℤ)) • c := by rw [natCast_zsmul]
          have e2 : ((sg : ℕ) • c) = ((sg : ℤ)) • c := by rw [natCast_zsmul]
          rw [e1, e2, smul_smul, smul_smul, ← add_smul]
          rw [show ((Nat.gcdA (x a) sg) * (x a : ℤ)
                    + (Nat.gcdB (x a) sg) * (sg : ℤ))
                = ((x a : ℤ) * Nat.gcdA (x a) sg
                    + (sg : ℤ) * Nat.gcdB (x a) sg) by ring]
          rw [← Nat.gcd_eq_gcd_ab]
        -- conclude membership: range is a subgroup, closed under zsmul and add.
        have hmem : (d : ℕ) • c ∈ (linHom n k x).range := by
          have e3 : (d : ℕ) • c = (d : ℤ) • c := by rw [natCast_zsmul]
          rw [e3, hbez]
          exact AddSubgroup.add_mem _
            (AddSubgroup.zsmul_mem _ hxa _)
            (AddSubgroup.zsmul_mem _ ih _)
        exact hmem
    have := key Finset.univ
    exact this

/-- Range cardinality of `linHom`: `n / gcd(n, gcd xᵢ)`. -/
theorem linHom_range_count (n k : ℕ) [NeZero n] (x : Fin k → ℕ) :
    Nat.card (linHom n k x).range = n / Nat.gcd n (Finset.univ.gcd x) := by
  rw [linHom_range]
  exact BealDensity.image_count n (Finset.univ.gcd x)

/-- **k-variable solution count (HEADLINE).**
For `n > 0` and coefficients `x : Fin k → ℕ`, the number of `v : Fin k → ZMod n`
with `∑ i, xᵢ • vᵢ = 0` equals `n^(k-1) · gcd(n, gcd of all xᵢ)`.

NEW (no LaTTe sibling) — generalizes `BealDensity.pair_solution_count` (k=2). -/
theorem lin_solution_count (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (x : Fin k → ℕ) :
    Nat.card (linHom n k x).ker = n ^ (k - 1) * Nat.gcd n (Finset.univ.gcd x) := by
  -- Lagrange + first iso: |ker| · |range| = |domain| = n^k.
  have hlag : Nat.card (linHom n k x).ker * Nat.card (linHom n k x).range
      = Nat.card (Fin k → ZMod n) := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  rw [card_domain n k] at hlag
  -- Range cardinality.
  rw [linHom_range_count] at hlag
  -- Arithmetic: let g = gcd(n, gcd xᵢ); g ∣ n, n = g·q, n/g = q.
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set g := Nat.gcd n (Finset.univ.gcd x) with hg
  have hg_dvd : g ∣ n := Nat.gcd_dvd_left _ _
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hn_pos
  obtain ⟨q, hq⟩ := hg_dvd
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.mul_zero] at hq; omega
    · exact h
  have hnq : n / g = q := by rw [hq, Nat.mul_div_cancel_left _ hg_pos]
  rw [hnq] at hlag
  -- hlag : |ker| · q = n^k. Want |ker| = n^(k-1)·g. Note n^k = (n^(k-1)·g)·q.
  have hk1 : n ^ k = (n ^ (k - 1) * g) * q := by
    have : k = (k - 1) + 1 := by omega
    rw [this, pow_succ]
    rw [Nat.add_sub_cancel]
    -- n^(k-1) * n = n^(k-1) * g * q  since n = g*q.
    rw [hq]; ring
  rw [hk1] at hlag
  exact Nat.eq_of_mul_eq_mul_right hqpos hlag

/-- k=2 reduction: the headline at `k = 2` with coefficient vector `![x, y]`
recovers `BealDensity.pair_solution_count`, namely `n · gcd(n, gcd x y)`. -/
theorem lin_solution_count_two (n x y : ℕ) [NeZero n] :
    Nat.card (linHom n 2 ![x, y]).ker = n * Nat.gcd n (Nat.gcd x y) := by
  have h := lin_solution_count n 2 (by norm_num) ![x, y]
  rw [h]
  have hg : Finset.univ.gcd (![x, y] : Fin 2 → ℕ) = Nat.gcd x y := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
    rw [Finset.gcd_insert, Finset.gcd_singleton]
    simp [gcd_eq_nat_gcd]
  rw [hg]
  congr 1
  ring

end BealDensityKVar
