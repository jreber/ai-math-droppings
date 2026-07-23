/-
# Lonely Runner `k = 4`: the `FourThreeResidual` "two-different-elements" sub-case

This file attacks `LonelyRunnerCoprimeKernel.FourThreeResidual`, the sole remaining open
piece of the honest `k = 4` Lonely Runner Conjecture (tracked as
`conj-2026-07-09-lonelyrunner-k4-true`; see `docs/kb/conjectures/` for the full reduction
history). `FourThreeResidual` is exactly the Barajas–Serra "arc-compression" regime: three
pairwise-distinct, pairwise-coprime, positive integer speeds containing both a multiple of
`4` and a multiple of `3`.

## Structural observation

Given pairwise-coprime `x, y, z`, **at most one** of them can be even (two even values
would share the factor `2`), and **at most one** can be a multiple of `3`. So whenever both
a multiple of `4` and a multiple of `3` are present, exactly one of two structural cases
occurs:

* **Case A** — a *single* element is divisible by both `4` and `3` (i.e. by `12`);
* **Case B** — *two different* elements carry the two factors: one is `≡ 0 (mod 4)` but not
  `mod 3`, another is `≡ 0 (mod 3)` but not `mod 4` — and (automatically, by coprimality)
  the third is coprime to `12` entirely.

This file completely and unconditionally resolves **Case B**. It does not resolve Case A
(where the descending-valuation Prime Filtering Lemma genuinely seems to be needed — a
numerical check in this session showed that for Case A, the analogous "single closed-form
witness" strategy has *no* modulus-`48`-uniform solution: unlike Case B, no fixed `m`
handles every coprime-to-`48` pair `(y, z)` simultaneously, and the required witness
genuinely depends on deeper structure of the multiple-of-`12` element. See the module's
final remark and the dispatch report for the details of this negative finding.)

## The Case B construction

Write `x = 4a`, `y = 3b` (the two "carrier" elements). Pairwise coprimality forces `a`
coprime to `3` and `b` coprime to `4` (a shared factor would violate `Coprime x y`), and
forces the third element `z` coprime to `12` entirely (a shared factor with `x` or `y`
would violate `Coprime x z` / `Coprime y z`).

Take `t = m / 12` for a specific `m ∈ {1, 5, 7}` chosen by a 4-way case split on
`z mod 12 ∈ {1, 5, 7, 11}` (the units mod `12`, since `z` is coprime to `12`):

* `z ≡ 1 (mod 12)` → `m = 5` (`z·m ≡ 5 (mod 12)`)
* `z ≡ 5 (mod 12)` → `m = 1` (`z·m ≡ 5 (mod 12)`)
* `z ≡ 7 (mod 12)` → `m = 1` (`z·m ≡ 7 (mod 12)`)
* `z ≡ 11 (mod 12)` → `m = 7` (`z·m ≡ 5 (mod 12)`)

In every case `z·m mod 12 ∈ {5, 7} ⊆ [3, 9]`, the "middle band" giving `nid ≥ 1/4` at
denominator `12` (`nid_ge_quarter_of_residue`, reused from `LonelyRunnerCoprimeKernel`).

Meanwhile `x·t = 4a·(m/12) = (a·m)·(1/3)` and `y·t = 3b·(m/12) = (b·m)·(1/4)`. Since
`m ∈ {1, 5, 7}` is never a multiple of `3` or of `4`, and `a` is coprime to `3` / `b` is
coprime to `4`, neither `a·m` is a multiple of `3` nor `b·m` a multiple of `4` — so the
*already proved* reusable witnesses `nid_third_time` / `nid_quarter_time`
(`LonelyRunnerCoprimeKernel`) apply directly, with no new machinery needed for `x, y`.

This is a genuinely elementary, finite-case (4-way), closed-form construction — no
induction, no `decide`/`native_decide` on the main path (only trivial `decide`s for
`¬ d ∣ literal`), no unbounded search.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Propositio.Combinatorics.LonelyRunnerSmallK
import Propositio.Combinatorics.LonelyRunnerFourResidual
import Propositio.Combinatorics.LonelyRunnerCoprimeKernel

namespace LonelyRunnerFourThreeResidualCaseB

open LonelyRunnerSmallK LonelyRunnerFourResidual LonelyRunnerCoprimeKernel

/-- If `a` is coprime to `d` and `d ∤ m`, then `d ∤ (a * m)`. Elementary Euclid's-lemma
consequence, reused twice below (once with `d = 3`, once with `d = 4`). -/
lemma coprime_not_dvd_mul {a m d : ℕ} (hcop : Nat.Coprime a d) (hm : ¬ d ∣ m) :
    ¬ d ∣ (a * m) := by
  intro hdvd
  exact hm (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)

/-- The `z`-side residue witness at denominator `12`: reused instantiation of
`nid_ge_quarter_of_residue` at `n = 12`. -/
lemma nid_z_case (z m : ℕ) (r : ℤ) (hr : ((z : ℤ) * (m : ℤ)) % 12 = r)
    (h1 : (12 : ℝ) ≤ 4 * (r : ℝ)) (h2 : 4 * (r : ℝ) ≤ 3 * 12) :
    (1 : ℝ) / 4 ≤ nid ((z : ℝ) * ((m : ℝ) / 12)) := by
  have hcast : (z : ℝ) * ((m : ℝ) / 12) = (((z : ℤ) * (m : ℤ) : ℤ) : ℝ) / ((12 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  have h2' : 4 * (r : ℝ) ≤ 3 * ((12 : ℕ) : ℝ) := by push_cast; linarith
  have h1' : ((12 : ℕ) : ℝ) ≤ 4 * (r : ℝ) := by push_cast; linarith
  exact nid_ge_quarter_of_residue ((z : ℤ) * (m : ℤ)) 12 (by norm_num) r hr h1' h2'

/-- **Case B assembly.** Given the factorizations `x = 4a`, `y = 3b`, the side-coprimality
facts, and a witness `m` avoiding both `3 ∣ m` and `4 ∣ m` whose product with `z` lands in
the middle band mod `12`, the full triple is solved by `t = m / 12`. -/
lemma case_B_from_m (x y z a b m : ℕ) (ha : x = 4 * a) (hb : y = 3 * b)
    (ha3 : Nat.Coprime a 3) (hb4 : Nat.Coprime b 4)
    (hm3 : ¬ (3 : ℕ) ∣ m) (hm4 : ¬ (4 : ℕ) ∣ m) (r : ℤ)
    (hr : ((z : ℤ) * (m : ℤ)) % 12 = r) (h1 : (12 : ℝ) ≤ 4 * (r : ℝ))
    (h2 : 4 * (r : ℝ) ≤ 3 * 12) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) := by
  refine ⟨(m : ℝ) / 12, ?_, ?_, ?_⟩
  · have hnd3 : ¬ (3 : ℕ) ∣ (a * m) := coprime_not_dvd_mul ha3 hm3
    have e : (x : ℝ) * ((m : ℝ) / 12) = ((a * m : ℕ) : ℝ) * (1 / 3) := by
      rw [ha]; push_cast; ring
    rw [e]; exact nid_third_time (a * m) hnd3
  · have hnd4 : ¬ (4 : ℕ) ∣ (b * m) := coprime_not_dvd_mul hb4 hm4
    have e : (y : ℝ) * ((m : ℝ) / 12) = ((b * m : ℕ) : ℝ) * (1 / 4) := by
      rw [hb]; push_cast; ring
    rw [e]; exact nid_quarter_time (b * m) hnd4
  · exact nid_z_case z m r hr h1 h2

/-- **Case B core.** `x` carries the factor `4` (and, by coprimality with `y`, not `3`);
`y` carries the factor `3` (and, by coprimality with `x`, not `4`). This is exactly the
"two different carriers" sub-case of `FourThreeResidual`. -/
theorem case_B_core (x y z : ℕ) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (cxy : Nat.Coprime x y) (cxz : Nat.Coprime x z) (cyz : Nat.Coprime y z)
    (h4 : 4 ∣ x) (h3 : 3 ∣ y) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t) := by
  -- `x` coprime to `3` (from `y` carrying the `3`), `y` coprime to `4` (from `x` carrying
  -- the `4`), and `z` coprime to both `4` and `3` — all derived BEFORE destructuring
  -- `h4`/`h3` (which are consumed by the `obtain` below).
  have hx3 : Nat.Coprime x 3 := Nat.Coprime.coprime_dvd_right h3 cxy
  have hy4 : Nat.Coprime y 4 := Nat.Coprime.coprime_dvd_right h4 cxy.symm
  have hz4 : Nat.Coprime 4 z := Nat.Coprime.coprime_dvd_left h4 cxz
  have hz3 : Nat.Coprime 3 z := Nat.Coprime.coprime_dvd_left h3 cyz
  obtain ⟨a, ha⟩ := h4
  obtain ⟨b, hb⟩ := h3
  have ha3 : Nat.Coprime a 3 := by
    have h : Nat.Coprime (4 * a) 3 := by rwa [ha] at hx3
    exact (Nat.coprime_mul_iff_left.mp h).2
  have hb4 : Nat.Coprime b 4 := by
    have h : Nat.Coprime (3 * b) 4 := by rwa [hb] at hy4
    exact (Nat.coprime_mul_iff_left.mp h).2
  -- residues mod 2 and mod 3 of `z`.
  have hzmod2 : z % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one z with h | h
    · exfalso
      have hd : (2 : ℕ) ∣ z := Nat.dvd_iff_mod_eq_zero.mpr h
      have hdg : (2 : ℕ) ∣ Nat.gcd 4 z := Nat.dvd_gcd (by norm_num) hd
      rw [hz4.gcd_eq_one] at hdg
      omega
    · exact h
  have hzmod3 : z % 3 ≠ 0 := by
    intro h
    have hd : (3 : ℕ) ∣ z := Nat.dvd_iff_mod_eq_zero.mpr h
    have hdg : (3 : ℕ) ∣ Nat.gcd 3 z := Nat.dvd_gcd (by norm_num) hd
    rw [hz3.gcd_eq_one] at hdg
    omega
  have hz12 : z % 12 = 1 ∨ z % 12 = 5 ∨ z % 12 = 7 ∨ z % 12 = 11 := by omega
  rcases hz12 with h12 | h12 | h12 | h12
  · -- z ≡ 1 (mod 12): m = 5, z*m ≡ 5 (mod 12)
    have hr : ((z : ℤ) * (5 : ℤ)) % 12 = 5 := by
      have hz : (z : ℤ) % 12 = 1 := by exact_mod_cast h12
      omega
    exact case_B_from_m x y z a b 5 ha hb ha3 hb4 (by decide) (by decide) 5 hr
      (by norm_num) (by norm_num)
  · -- z ≡ 5 (mod 12): m = 1, z*m ≡ 5 (mod 12)
    have hr : ((z : ℤ) * (1 : ℤ)) % 12 = 5 := by
      have hz : (z : ℤ) % 12 = 5 := by exact_mod_cast h12
      omega
    exact case_B_from_m x y z a b 1 ha hb ha3 hb4 (by decide) (by decide) 5 hr
      (by norm_num) (by norm_num)
  · -- z ≡ 7 (mod 12): m = 1, z*m ≡ 7 (mod 12)
    have hr : ((z : ℤ) * (1 : ℤ)) % 12 = 7 := by
      have hz : (z : ℤ) % 12 = 7 := by exact_mod_cast h12
      omega
    exact case_B_from_m x y z a b 1 ha hb ha3 hb4 (by decide) (by decide) 7 hr
      (by norm_num) (by norm_num)
  · -- z ≡ 11 (mod 12): m = 7, z*m ≡ 5 (mod 12)
    have hr : ((z : ℤ) * (7 : ℤ)) % 12 = 5 := by
      have hz : (z : ℤ) % 12 = 11 := by exact_mod_cast h12
      omega
    exact case_B_from_m x y z a b 7 ha hb ha3 hb4 (by decide) (by decide) 5 hr
      (by norm_num) (by norm_num)

/-- **`FourThreeResidualCaseA`** — the residual left open by `case_B_core`: pairwise-distinct
pairwise-coprime positive triples where *some single element* is divisible by `12` (carries
both the `4` and the `3` at once). This is exactly the Barajas–Serra "deep valuation" regime
— the part of `FourThreeResidual` this file does **not** resolve. -/
def FourThreeResidualCaseA : Prop :=
  ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → 1 ≤ z → x ≠ y → x ≠ z → y ≠ z →
    Nat.Coprime x y → Nat.Coprime x z → Nat.Coprime y z →
    (12 ∣ x ∨ 12 ∣ y ∨ 12 ∣ z) →
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((x : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((y : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((z : ℝ) * t)

/-- **The reduction: `FourThreeResidual` splits exactly into Case A and Case B.** Given the
(open) Case A hypothesis `H`, the full `FourThreeResidual` statement holds. Case B — two
different carriers — is discharged unconditionally by `case_B_core` above; Case A — a
single element carrying both `4` and `3`, i.e. divisible by `12` — is exactly where `H`
is invoked. -/
theorem fourThreeResidual_of_caseA (H : FourThreeResidualCaseA) :
    LonelyRunnerCoprimeKernel.FourThreeResidual := by
  intro x y z hx hy hz hxy hxz hyz cxy cxz cyz h4 h3
  by_cases h12 : 12 ∣ x ∨ 12 ∣ y ∨ 12 ∣ z
  · exact H x y z hx hy hz hxy hxz hyz cxy cxz cyz h12
  · rw [not_or, not_or] at h12
    obtain ⟨h12x, h12y, h12z⟩ := h12
    have hc43 : Nat.Coprime 4 3 := by decide
    -- Rule out any single element carrying both `4` and `3` (that would force `12 ∣` it).
    rcases h4 with h4x | h4y | h4z <;> rcases h3 with h3x | h3y | h3z
    · -- 4∣x, 3∣x ⇒ 12∣x, contradicting h12x
      exact absurd (by simpa using hc43.mul_dvd_of_dvd_of_dvd h4x h3x) h12x
    · -- 4∣x, 3∣y : Case B, x carries 4, y carries 3, z is the other — matches case_B_core directly
      exact case_B_core x y z hx hy hz hxy hxz hyz cxy cxz cyz h4x h3y
    · -- 4∣x, 3∣z : Case B, x carries 4, z carries 3, y is the other
      obtain ⟨t, htx, htz, hty⟩ :=
        case_B_core x z y hx hz hy hxz hxy hyz.symm cxz cxy cyz.symm h4x h3z
      exact ⟨t, htx, hty, htz⟩
    · -- 4∣y, 3∣x : Case B, y carries 4, x carries 3, z is the other
      obtain ⟨t, hty, htx, htz⟩ :=
        case_B_core y x z hy hx hz hxy.symm hyz hxz cxy.symm cyz cxz h4y h3x
      exact ⟨t, htx, hty, htz⟩
    · -- 4∣y, 3∣y ⇒ 12∣y, contradicting h12y
      exact absurd (by simpa using hc43.mul_dvd_of_dvd_of_dvd h4y h3y) h12y
    · -- 4∣y, 3∣z : Case B, y carries 4, z carries 3, x is the other
      obtain ⟨t, hty, htz, htx⟩ :=
        case_B_core y z x hy hz hx hyz hxy.symm hxz.symm cyz cxy.symm cxz.symm h4y h3z
      exact ⟨t, htx, hty, htz⟩
    · -- 4∣z, 3∣x : Case B, z carries 4, x carries 3, y is the other
      obtain ⟨t, htz, htx, hty⟩ :=
        case_B_core z x y hz hx hy hxz.symm hyz.symm hxy cxz.symm cyz.symm cxy h4z h3x
      exact ⟨t, htx, hty, htz⟩
    · -- 4∣z, 3∣y : Case B, z carries 4, y carries 3, x is the other
      obtain ⟨t, htz, hty, htx⟩ :=
        case_B_core z y x hz hy hx hyz.symm hxz.symm hxy.symm cyz.symm cxz.symm cxy.symm
          h4z h3y
      exact ⟨t, htx, hty, htz⟩
    · -- 4∣z, 3∣z ⇒ 12∣z, contradicting h12z
      exact absurd (by simpa using hc43.mul_dvd_of_dvd_of_dvd h4z h3z) h12z

end LonelyRunnerFourThreeResidualCaseB
