import Propositio.NumberTheory.Collatz.Basic

/-!
# Natural lower density of Collatz-descending integers is ≥ 3/4  (Terras F(2))

We prove that for every rational `p/q < 3/4`, the predicate
`Desc2 n := T_iter n 1 < n ∨ T_iter n 2 < n` ("the Terras orbit of `n` dips
below `n` within two steps") satisfies `density_bounded_below Desc2 p q`.
Equivalently, the **lower natural density of integers that descend within two
Terras steps is at least 3/4** — the classical Terras / Everett `F(2) = 3/4`
landing, here assembled as an honest `density_bounded_below` statement by
combining the per-residue descent facts (`n ≡ 0,2 mod 4` descend in one step,
`n ≡ 1 mod 4` in two) with the residue-class density infrastructure of
`TerrasDensity`.

NOTE: this RE-DERIVES the `k=2` case of the existing
`CollatzDensityCount.F_eq_count_over_pow` (which already pins the density of
`{n : DescBy n k}` at `D(k)/2^k` for `k ≤ 6`), via an independent elementary
residue-class-union method.  It is NOT a new result; its value is the reusable
*public* `density_bounded_below` combinators below (the corpus has equivalents
only as private/inlined helpers).  Axiom-clean
(`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace CollatzDescentDensityF2

open TerrasDensity

attribute [local instance] Classical.propDecidable

/-- Descends within two Terras steps. -/
def Desc2 (n : Nat) : Prop := T_iter n 1 < n ∨ T_iter n 2 < n

/-! ## Generic density-bounded-below combinators -/

/-- Disjoint additivity of `count_upto`. -/
theorem count_upto_or_eq {A B : Nat → Prop} (hdisj : ∀ n, ¬ (A n ∧ B n)) (N : Nat) :
    count_upto (fun n => A n ∨ B n) N = count_upto A N + count_upto B N := by
  unfold count_upto
  generalize N + 1 = M
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, ih]
    by_cases hA : A k <;> by_cases hB : B k
    · exact absurd ⟨hA, hB⟩ (hdisj k)
    · rw [if_pos (Or.inl hA), if_pos hA, if_neg hB]; omega
    · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB]; omega
    · rw [if_neg (not_or.2 ⟨hA, hB⟩), if_neg hA, if_neg hB]; omega

/-- Monotonicity of `count_upto` under predicate inclusion. -/
theorem count_upto_mono {A B : Nat → Prop} (hsub : ∀ n, A n → B n) (N : Nat) :
    count_upto A N ≤ count_upto B N := by
  unfold count_upto
  exact Nat.count_mono_left (fun k _ => hsub k)

/-- A lower density is monotone under superset. -/
theorem dbb_subset {A B : Nat → Prop} {p q : Nat}
    (hsub : ∀ n, A n → B n) (hA : density_bounded_below A p q) :
    density_bounded_below B p q := by
  obtain ⟨N0, h⟩ := hA
  refine ⟨N0, fun N hN => ?_⟩
  have hc : count_upto A N ≤ count_upto B N := count_upto_mono hsub N
  exact le_trans (h N hN) (Nat.mul_le_mul_left q hc)

/-- Lower densities add over a disjoint union. -/
theorem dbb_union {A B : Nat → Prop} {pA pB q : Nat}
    (hdisj : ∀ n, ¬ (A n ∧ B n))
    (hA : density_bounded_below A pA q) (hB : density_bounded_below B pB q) :
    density_bounded_below (fun n => A n ∨ B n) (pA + pB) q := by
  obtain ⟨NA, hA'⟩ := hA
  obtain ⟨NB, hB'⟩ := hB
  refine ⟨max NA NB, fun N hN => ?_⟩
  have hcount : count_upto (fun n => A n ∨ B n) N = count_upto A N + count_upto B N :=
    count_upto_or_eq hdisj N
  have h1 := hA' N (le_trans (le_max_left _ _) hN)
  have h2 := hB' N (le_trans (le_max_right _ _) hN)
  rw [hcount]
  calc (pA + pB) * N = pA * N + pB * N := by ring
    _ ≤ q * count_upto A N + q * count_upto B N := add_le_add h1 h2
    _ = q * (count_upto A N + count_upto B N) := by ring

/-- Lower density is monotone (downward) in the numerator. -/
theorem dbb_mono_num {A : Nat → Prop} {p p' q : Nat}
    (hp : p ≤ p') (hA : density_bounded_below A p' q) :
    density_bounded_below A p q := by
  obtain ⟨N0, h⟩ := hA
  refine ⟨N0, fun N hN => ?_⟩
  exact le_trans (Nat.mul_le_mul_right N hp) (h N hN)

/-! ## Truncated residue-class lower density -/

/-- `count_upto (· < t) N ≤ t`. -/
theorem count_upto_lt_le (t N : Nat) : count_upto (fun n => n < t) N ≤ t := by
  have h : Nat.count (fun n => n < t) (N + 1) ≤ t := by
    rw [Nat.count_eq_card_filter_range]
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range t))
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_range.2 hx.2
  calc count_upto (fun n => n < t) N
      = Nat.count (fun n => n < t) (N + 1) := by
        unfold count_upto
        exact congrArg (fun inst => @Nat.count (fun n => n < t) inst (N + 1))
          (Subsingleton.elim _ _)
    _ ≤ t := h

/-- A residue class `{n : n % m = r}` minus an initial segment `{n < t}` still has
lower density `≥ 1/m`: for any `p/q < 1/m`, `density_bounded_below {n%m=r ∧ t≤n} p q`. -/
theorem dbb_residue_trunc (m r p q t : Nat) (hm : 0 < m) (hrm : r < m)
    (hfrac : p * m < q) :
    density_bounded_below (fun n => n % m = r ∧ t ≤ n) p q := by
  refine ⟨q * m * (t + 1), fun N hN => ?_⟩
  -- class count lower bound
  have hclass : (N + 1) / m ≤ count_upto (fun n => n % m = r) N :=
    count_residue_class_lower_bound m r N hm hrm
  -- class ⊆ trunc ∪ {· < t}; the two are disjoint, so counts add.
  have hdisj : ∀ n, ¬ ((n % m = r ∧ t ≤ n) ∧ n < t) := by intro n hh; omega
  have hunion : count_upto (fun n => (n % m = r ∧ t ≤ n) ∨ n < t) N
      = count_upto (fun n => n % m = r ∧ t ≤ n) N + count_upto (fun n => n < t) N :=
    count_upto_or_eq hdisj N
  have hmono : count_upto (fun n => n % m = r) N
      ≤ count_upto (fun n => (n % m = r ∧ t ≤ n) ∨ n < t) N :=
    count_upto_mono (fun k hk => by
      by_cases h : t ≤ k
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr (by omega)) N
  have hlt : count_upto (fun n => n < t) N ≤ t := count_upto_lt_le t N
  have hcc_le : count_upto (fun n => n % m = r) N
      ≤ count_upto (fun n => n % m = r ∧ t ≤ n) N + t := by
    rw [hunion] at hmono; omega
  -- Euclidean: N + 1 ≤ m * cc + m  and hence  N + 1 ≤ m * cu + m * t + m
  have hdm : m * ((N + 1) / m) + (N + 1) % m = N + 1 := Nat.div_add_mod (N + 1) m
  have hmod : (N + 1) % m < m := Nat.mod_lt _ hm
  have h_mcc : m * ((N + 1) / m) ≤ m * count_upto (fun n => n % m = r) N :=
    Nat.mul_le_mul_left m hclass
  have h_mcu : m * count_upto (fun n => n % m = r) N
      ≤ m * count_upto (fun n => n % m = r ∧ t ≤ n) N + m * t := by
    have hmul := Nat.mul_le_mul_left m hcc_le
    calc m * count_upto (fun n => n % m = r) N
        ≤ m * (count_upto (fun n => n % m = r ∧ t ≤ n) N + t) := hmul
      _ = m * count_upto (fun n => n % m = r ∧ t ≤ n) N + m * t := by ring
  have h_Nbound : N + 1 ≤ m * count_upto (fun n => n % m = r ∧ t ≤ n) N + m * t + m := by omega
  -- Goal: p * N ≤ q * cu.  Reduce to m * (p*N) ≤ m * (q*cu).
  apply Nat.le_of_mul_le_mul_left _ hm
  nlinarith [Nat.mul_le_mul_right N hfrac, Nat.mul_le_mul_left q h_Nbound, hN]

/-! ## Per-residue descent facts -/

theorem desc2_of_mod4_eq0 (n : Nat) (h : n % 4 = 0) (ht : 4 ≤ n) : Desc2 n := by
  left
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
  have e : T_iter (4 * k) 1 = 2 * k := by
    show T (4 * k) = 2 * k
    unfold T; rw [if_pos (by omega)]; omega
  rw [e]; omega

theorem desc2_of_mod4_eq2 (n : Nat) (h : n % 4 = 2) : Desc2 n := by
  left
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  have e : T_iter (4 * k + 2) 1 = 2 * k + 1 := by
    show T (4 * k + 2) = 2 * k + 1
    unfold T; rw [if_pos (by omega)]; omega
  rw [e]; omega

theorem desc2_of_mod4_eq1 (n : Nat) (h : n % 4 = 1) (ht : 5 ≤ n) : Desc2 n := by
  right
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
  have hTn : T (4 * k + 1) = 6 * k + 2 := by unfold T; rw [if_neg (by omega)]; omega
  have hTn2 : T (6 * k + 2) = 3 * k + 1 := by unfold T; rw [if_pos (by omega)]; omega
  have e : T_iter (4 * k + 1) 2 = 3 * k + 1 := by
    show T (T (4 * k + 1)) = 3 * k + 1
    rw [hTn, hTn2]
  rw [e]; omega

/-! ## Assembly: lower density of `Desc2` ≥ 3/4 -/

/-- **Terras F(2), density form.**  For every `p/q < 3/4`, the lower natural
density of integers that descend within two Terras steps is at least `p/q`.
Hence the lower density of `Desc2` is `≥ 3/4`. -/
theorem f2_descent_density (p q : Nat) (hpq : 4 * p < 3 * q) :
    density_bounded_below Desc2 p q := by
  -- Three disjoint residue classes mod 4 (residues 0,1,2), each ⊆ Desc2 above a
  -- finite threshold, each of lower density 1/4; their union has density 3/4.
  have hfrac : p * 4 < 3 * q := by omega
  have hA0 : density_bounded_below (fun n => n % 4 = 0 ∧ 4 ≤ n) p (3 * q) :=
    dbb_residue_trunc 4 0 p (3 * q) 4 (by norm_num) (by norm_num) hfrac
  have hA1 : density_bounded_below (fun n => n % 4 = 1 ∧ 5 ≤ n) p (3 * q) :=
    dbb_residue_trunc 4 1 p (3 * q) 5 (by norm_num) (by norm_num) hfrac
  have hA2 : density_bounded_below (fun n => n % 4 = 2 ∧ 0 ≤ n) p (3 * q) :=
    dbb_residue_trunc 4 2 p (3 * q) 0 (by norm_num) (by norm_num) hfrac
  -- disjointness
  have hd01 : ∀ n, ¬ ((n % 4 = 0 ∧ 4 ≤ n) ∧ (n % 4 = 1 ∧ 5 ≤ n)) := by
    intro n hh; omega
  have hU01 : density_bounded_below
      (fun n => (n % 4 = 0 ∧ 4 ≤ n) ∨ (n % 4 = 1 ∧ 5 ≤ n)) (p + p) (3 * q) :=
    dbb_union hd01 hA0 hA1
  have hd012 : ∀ n, ¬ (((n % 4 = 0 ∧ 4 ≤ n) ∨ (n % 4 = 1 ∧ 5 ≤ n)) ∧ (n % 4 = 2 ∧ 0 ≤ n)) := by
    intro n hh; omega
  have hU012 : density_bounded_below
      (fun n => ((n % 4 = 0 ∧ 4 ≤ n) ∨ (n % 4 = 1 ∧ 5 ≤ n)) ∨ (n % 4 = 2 ∧ 0 ≤ n))
      (p + p + p) (3 * q) :=
    dbb_union hd012 hU01 hA2
  -- union ⊆ Desc2
  have hsub : ∀ n, (((n % 4 = 0 ∧ 4 ≤ n) ∨ (n % 4 = 1 ∧ 5 ≤ n)) ∨ (n % 4 = 2 ∧ 0 ≤ n)) → Desc2 n := by
    intro n hh
    rcases hh with (⟨h, ht⟩ | ⟨h, ht⟩) | ⟨h, _⟩
    · exact desc2_of_mod4_eq0 n h ht
    · exact desc2_of_mod4_eq1 n h ht
    · exact desc2_of_mod4_eq2 n h
  have hDesc : density_bounded_below Desc2 (p + p + p) (3 * q) := dbb_subset hsub hU012
  -- p + p + p = 3p, and density_bounded_below A (3p) (3q) ⇒ A p q.
  have h3 : density_bounded_below Desc2 (3 * p) (3 * q) := by
    have : p + p + p = 3 * p := by ring
    rwa [this] at hDesc
  -- scale down by 3
  obtain ⟨N0, h⟩ := h3
  refine ⟨N0, fun N hN => ?_⟩
  have hkey : 3 * (p * N) ≤ 3 * (q * count_upto Desc2 N) := by
    have := h N hN
    calc 3 * (p * N) = 3 * p * N := by ring
      _ ≤ 3 * q * count_upto Desc2 N := this
      _ = 3 * (q * count_upto Desc2 N) := by ring
  exact Nat.le_of_mul_le_mul_left hkey (by norm_num)

end CollatzDescentDensityF2
