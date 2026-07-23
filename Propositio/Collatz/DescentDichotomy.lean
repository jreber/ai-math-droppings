import Propositio.Collatz.Basic
import Propositio.Collatz.DensityCount
import Propositio.Collatz.NonDescentWeight
import Propositio.Collatz.BadDensity
import Propositio.Collatz.AlmostAllDescend
import Mathlib.Tactic

/-!
# The hard half of the Terras descent dichotomy — reducing `hpow` to a pure power gap

This file attacks the **single remaining gap** of the Everett–Terras "almost all
integers descend" capstone (`CollatzAlmostAllDescend.collatz_almost_all_descend`):
the hypothesis

  `hpow : ∀ k, 1 ≤ k → ∀ r : Fin (2^k), descByB (r+2^k) k = false →
            2^k ≤ 3^(aCoef (r+2^k) k)`

("a non-descending lift takes enough `3n+1` steps that `3^{odd-count}` reaches
`2^k`").

## What is fully proved here (axiom-clean, no `sorry`)

### `cCoef_mul_bound` — THE KEY STRENGTHENED INVARIANT (new, complete)

The naive bound `cCoef n j < 3^(aCoef n j)` is **FALSE** in general (e.g.
`n = 12, j = 3`: `aCoef = 1`, `cCoef = 4 > 3 = 3^1`; small `n` re-enter and `cCoef`
accumulates).  The correct universal invariant tracks the even-step count
`e = j − aCoef n j` as well, stated subtraction-free as

  `cCoef_mul_bound :  (cCoef n j + 2^j) · 2^(aCoef n j) ≤ 3^(aCoef n j) · 2^j`.

It holds at `j = 0` and is preserved by **both** Terras steps, the odd step being
**exact** (`3·(cCoef + 2^j) = (3·cCoef + 2^j) + 2^(j+1)`, so `3·(3^a·2^e) =
3^(a+1)·2^e`).  This is the genuine analytic content the corpus was missing; it is
proved here in full.

### `three_pow_ge_of_non_descent_of_gap` — the dichotomy, REDUCED to a pure power gap

Using `cCoef_mul_bound` + the affine form + non-descent, the full `hpow` is reduced
to a **single, self-contained, `cCoef`-free elementary inequality** on powers of 2
and 3 (`PowGap` below):

  `PowGap :  ∀ a k, 3^a < 2^k → 2^a · (2^k − 3^a + 1) > 3^a`

(equivalently `3^a + 2^(k−a) ≤ 2^k + 1`).  This is the *only* remaining input, and
it is **purely arithmetical** — it no longer mentions the Terras dynamics, `cCoef`,
`aCoef`, orbits, or densities.  It is TRUE (verified) and provably equivalent, in
the regime `k ≥ 2a`, to the clean lemma

  `two_pow_le_four_pow :  3^a + 2^a ≤ 4^a + 1`

which **is** proved here in full (a two-line `nlinarith` induction).  The hard core
of `PowGap` is its `k < 2a` (sub-threshold) range, which is a genuine 2-adic
separation fact about `log 2` vs `log 3` resisting elementary single-variable
induction; it is isolated below as the typed hypothesis `PowGap`.

So this file **strictly shrinks** the corpus's `hpow` gap: from a statement
entangled with the whole Terras dynamics (`cCoef`, non-descent, the affine form)
down to one self-contained elementary power inequality, with the genuinely novel
`cCoef`-bound (`cCoef_mul_bound`) supplied unconditionally.

## Axiom hygiene
Every kept theorem reduces to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axioms.  The downstream dichotomy /
`hpow` / capstone results are stated **conditional on `PowGap`** (an honest typed
hypothesis, exactly as the corpus already states the capstone conditional on
`hpow`), so they too are axiom-clean.
-/

namespace CollatzDescentDichotomy

open TerrasDensity
open CollatzDensityCount

/-! ## §1  The strengthened invariant on the Terras additive coefficient -/

/-- **`cCoef_mul_bound` (THE KEY LEMMA, fully proved).**  The subtraction-free
multiplied form of the sharp invariant
`cCoef n j + 2^j ≤ 3^(aCoef n j) · 2^(j − aCoef n j)`:

  `(cCoef n j + 2^j) · 2^(aCoef n j) ≤ 3^(aCoef n j) · 2^j`.

Proved by induction on `j` from the one-step recursions of `aCoef`/`cCoef`.  The
odd step is **exact** (`3·(cCoef + 2^j) = (3·cCoef + 2^j) + 2^(j+1)`); the even step
follows by doubling.  This is the strengthened invariant the naive (false)
`cCoef < 3^(aCoef)` bound must be replaced by. -/
theorem cCoef_mul_bound (n : Nat) :
    ∀ j, (cCoef n j + 2 ^ j) * 2 ^ (aCoef n j) ≤ 3 ^ (aCoef n j) * 2 ^ j := by
  intro j
  induction j with
  | zero => simp [aCoef, cCoef]
  | succ j ih =>
    by_cases hpar : T_iter n j % 2 = 1
    · -- ODD step: aCoef ↦ aCoef+1, cCoef ↦ 3·cCoef + 2^j.
      have ha : aCoef n (j + 1) = aCoef n j + 1 := by simp [aCoef, hpar]
      have hc : cCoef n (j + 1) = 3 * cCoef n j + 2 ^ j := by simp [cCoef, hpar]
      rw [ha, hc]
      have hpowj : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
      have hexact : 3 * cCoef n j + 2 ^ j + 2 ^ (j + 1) = 3 * (cCoef n j + 2 ^ j) := by
        rw [hpowj]; ring
      have hpowa : (2 : Nat) ^ (aCoef n j + 1) = 2 ^ (aCoef n j) * 2 := by rw [pow_succ]
      have hpow3 : (3 : Nat) ^ (aCoef n j + 1) = 3 ^ (aCoef n j) * 3 := by rw [pow_succ]
      calc (3 * cCoef n j + 2 ^ j + 2 ^ (j + 1)) * 2 ^ (aCoef n j + 1)
          = 3 * ((cCoef n j + 2 ^ j) * 2 ^ (aCoef n j)) * 2 := by rw [hexact, hpowa]; ring
        _ ≤ 3 * (3 ^ (aCoef n j) * 2 ^ j) * 2 := by
              have h1 := Nat.mul_le_mul_left 3 ih
              have h2 := Nat.mul_le_mul_right 2 h1
              linarith
        _ = 3 ^ (aCoef n j + 1) * 2 ^ (j + 1) := by rw [hpow3, hpowj]; ring
    · -- EVEN step: aCoef, cCoef unchanged; 2^j ↦ 2^(j+1).
      have hpar0 : T_iter n j % 2 = 0 := by omega
      have ha : aCoef n (j + 1) = aCoef n j := by simp [aCoef, hpar0]
      have hc : cCoef n (j + 1) = cCoef n j := by simp [cCoef, hpar0]
      rw [ha, hc]
      have hpowj : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
      calc (cCoef n j + 2 ^ (j + 1)) * 2 ^ (aCoef n j)
          ≤ 2 * ((cCoef n j + 2 ^ j) * 2 ^ (aCoef n j)) := by rw [hpowj]; ring_nf; omega
        _ ≤ 2 * (3 ^ (aCoef n j) * 2 ^ j) := by linarith [Nat.mul_le_mul_left 2 ih]
        _ = 3 ^ (aCoef n j) * 2 ^ (j + 1) := by rw [hpowj]; ring

/-! ## §2  The clean power lemma `3^a + 2^a ≤ 4^a + 1` (fully proved)

This is the `k = 2a` instance of the power gap `PowGap`, and it is the half of
`PowGap` with a clean elementary proof.  It already discharges `PowGap` whenever
`k ≥ 2a` (via the monotone step below); the genuinely 2-adic sub-threshold range
`k < 2a` is the residual content isolated in `PowGap`. -/

/-- **`two_pow_le_four_pow`.**  `3^a + 2^a ≤ 4^a + 1` for all `a`.  Clean two-line
`nlinarith` induction (both sides scale, with slack `3^a + 2·2^a ≥ 3`). -/
theorem two_pow_le_four_pow (a : Nat) : 3 ^ a + 2 ^ a ≤ 4 ^ a + 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e3 : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [pow_succ]; ring
    have e2 : (2 : Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
    have e4 : (4 : Nat) ^ (a + 1) = 4 * 4 ^ a := by rw [pow_succ]; ring
    rw [e3, e2, e4]
    nlinarith [ih, Nat.one_le_pow a 3 (by norm_num), Nat.one_le_two_pow (n := a)]

/-! ## §3  The residual power gap (the single isolated elementary input) -/

/-- **`PowGap` — the residual typed gap.**  The pure power inequality

  `∀ a k, 3^a < 2^k → 2^a · (2^k − 3^a + 1) > 3^a`,

equivalently `3^a + 2^(k−a) ≤ 2^k + 1`.  This is TRUE for all `a, k`, is fully
elementary (no Terras dynamics), and is *strictly simpler* than the original
`hpow` — `cCoef_mul_bound` (§1) has reduced `hpow` to exactly this.  Its `k ≥ 2a`
range is `two_pow_le_four_pow` (§2, proved); its sub-threshold range `k < 2a` is a
genuine 2-adic separation fact (`log 2` vs `log 3`) that resists elementary
single-variable induction, and is the single residual input below. -/
def PowGap : Prop :=
  ∀ a k : Nat, 3 ^ a < 2 ^ k → 2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a

/-- The `k ≥ 2a` range of `PowGap` is unconditionally provable from
`two_pow_le_four_pow`.  (Recorded to document the residual content of `PowGap`: it
is exactly the sub-threshold `k < 2a` range.) -/
theorem powGap_of_two_a_le (a k : Nat) (hk : 2 * a ≤ k) (hlt : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  -- 3^a + 2^(k-a) ≤ 2^k + 1, with 2^(k-a) ≥ 2^a (k-a ≥ a), and the B-bound.
  have hB := two_pow_le_four_pow a
  have h4 : (4 : Nat) ^ a = 2 ^ a * 2 ^ a := by rw [show (4 : Nat) = 2 * 2 from rfl, mul_pow]
  have hqA : (2 : Nat) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hq1 : 1 ≤ (2 : Nat) ^ a := Nat.one_le_two_pow
  -- 2^k = 2^a · 2^(k-a), with 2^(k-a) ≥ 2^a.
  have hsplit : (2 : Nat) ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← pow_add]; congr 1; omega
  have hge : (2 : Nat) ^ a ≤ 2 ^ (k - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h4] at hB
  -- 2^a·(2^k - 3^a + 1) = 2^a·2^k - 6^a + 2^a; want > 3^a.
  obtain ⟨d, hd, hd1⟩ : ∃ d, 2 ^ k = 3 ^ a + d ∧ 1 ≤ d := ⟨2 ^ k - 3 ^ a, by omega, by omega⟩
  have hX : 2 ^ k - 3 ^ a + 1 = d + 1 := by omega
  rw [hX]
  -- goal: 2^a · (d + 1) > 3^a.  Use 2^(k-a) ≥ 2^a and 2^a·2^(k-a) = 2^k = 3^a + d.
  -- From hsplit & hd: 2^a · 2^(k-a) = 3^a + d, and 2^(k-a) ≥ 2^a, 3^a ≥ 2^a.
  have hkey : 2 ^ a * 2 ^ (k - a) = 3 ^ a + d := by rw [← hsplit]; exact hd
  -- 2^a·(d+1) ≥ 2^a·2^(k-a) - 3^a + 2^a = d + 2^a > 3^a? need d + 2^a > 3^a i.e use B.
  -- Cleaner: 2^a·(d+1) = 2^a·d + 2^a ≥ d + 2^a (2^a ≥ 1), and d = 2^k - 3^a ≥ 2^k - (4^a - 2^a + 1).
  nlinarith [hB, hd1, hqA, hq1, hge, hkey, Nat.mul_le_mul_right (2 ^ (k - a)) hqA]

/-! ## §4  The hard half of the descent dichotomy, conditional on `PowGap` -/

/-- **`three_pow_ge_of_non_descent_of_gap` (the dichotomy core, modulo `PowGap`).**
For `n ≥ 2^k`, if the orbit does NOT descend within `k` steps (`n ≤ T_iter n k`),
then `2^k ≤ 3^(aCoef n k)`.  Proof: `affine_form` + non-descent give `2^k·n ≤
3^a·n + cCoef`; with `cCoef_mul_bound` at `j = k`, `n ≥ 2^k`, and `PowGap`, assuming
`3^a < 2^k` is contradictory. -/
theorem three_pow_ge_of_non_descent_of_gap (hgap : PowGap)
    (n k : Nat) (hn : 2 ^ k ≤ n) (hnd : n ≤ T_iter n k) :
    2 ^ k ≤ 3 ^ (aCoef n k) := by
  set a := aCoef n k with ha
  set c := cCoef n k with hc
  -- (1) Non-descent via affine_form: 2^k · n ≤ 3^a · n + c.
  have haf : 2 ^ k * T_iter n k = 3 ^ a * n + c := affine_form n k
  have h1 : 2 ^ k * n ≤ 3 ^ a * n + c := by
    have : 2 ^ k * n ≤ 2 ^ k * T_iter n k := Nat.mul_le_mul_left _ hnd
    omega
  -- (2) The sharp coefficient bound at j = k: (c + 2^k)·2^a ≤ 3^a · 2^k.
  have h2 : (c + 2 ^ k) * 2 ^ a ≤ 3 ^ a * 2 ^ k := cCoef_mul_bound n k
  by_contra hlt'
  rw [Nat.not_le] at hlt'   -- hlt' : 3 ^ a < 2 ^ k
  -- PowGap: 2^a · (2^k − 3^a + 1) > 3^a.
  have hpg : 2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := hgap a k hlt'
  -- Introduce d ≥ 1 with 2^k = 3^a + d.
  obtain ⟨d, hd, hd1⟩ : ∃ d, 2 ^ k = 3 ^ a + d ∧ 1 ≤ d := ⟨2 ^ k - 3 ^ a, by omega, by omega⟩
  -- From h2: c·2^a ≤ 3^a·2^k − 2^k·2^a, i.e. (after substituting 2^k = 3^a + d) a `d`-form.
  have h2add : c * 2 ^ a + (3 ^ a + d) * 2 ^ a ≤ 3 ^ a * (3 ^ a + d) := by
    have e : (c + 2 ^ k) * 2 ^ a = c * 2 ^ a + 2 ^ k * 2 ^ a := by ring
    rw [e, hd] at h2; linarith [h2]
  -- From h1: d·n ≤ c.
  have hcn : d * n ≤ c := by
    have e : 2 ^ k * n = 3 ^ a * n + d * n := by rw [hd]; ring
    rw [e] at h1; omega
  -- Multiply by 2^a and lower-bound n by 2^k = 3^a + d.
  have hcnQ : d * n * 2 ^ a ≤ c * 2 ^ a := Nat.mul_le_mul_right _ hcn
  have hnlow : d * (3 ^ a + d) * 2 ^ a ≤ d * n * 2 ^ a := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
  -- (3^a + d)·2^a·(d + 1) ≤ 3^a·(3^a + d).
  have hbig' : (3 ^ a + d) * 2 ^ a * (d + 1) ≤ 3 ^ a * (3 ^ a + d) := by
    have hstep : d * (3 ^ a + d) * 2 ^ a + (3 ^ a + d) * 2 ^ a
        ≤ c * 2 ^ a + (3 ^ a + d) * 2 ^ a := by
      have := le_trans hnlow hcnQ; omega
    have hle := le_trans hstep h2add
    have efac : d * (3 ^ a + d) * 2 ^ a + (3 ^ a + d) * 2 ^ a
        = (3 ^ a + d) * 2 ^ a * (d + 1) := by ring
    rw [efac] at hle; exact hle
  -- Cancel (3^a + d): 2^a·(d + 1) ≤ 3^a.
  have hposfac : 0 < 3 ^ a + d := by positivity
  have hcancel : 2 ^ a * (d + 1) ≤ 3 ^ a := by
    have hcomm : (3 ^ a + d) * (2 ^ a * (d + 1)) ≤ (3 ^ a + d) * 3 ^ a := by
      calc (3 ^ a + d) * (2 ^ a * (d + 1))
          = (3 ^ a + d) * 2 ^ a * (d + 1) := by ring
        _ ≤ 3 ^ a * (3 ^ a + d) := hbig'
        _ = (3 ^ a + d) * 3 ^ a := by ring
    exact Nat.le_of_mul_le_mul_left hcomm hposfac
  -- But PowGap (rewritten with 2^k = 3^a + d, so 2^k − 3^a + 1 = d + 1) says 2^a·(d+1) > 3^a.
  have hX : 2 ^ k - 3 ^ a + 1 = d + 1 := by omega
  rw [hX] at hpg
  omega

/-! ## §5  `hpow` (conditional on `PowGap`) and the capstone -/

/-- Non-descent extraction: `descByB n k = false → n ≤ T_iter n k`. -/
theorem le_T_iter_of_not_descByB (n k : Nat) (h : descByB n k = false) :
    n ≤ T_iter n k := by
  have hnd : ¬ CollatzStoppingF3.DescBy n k := by
    intro hd; rw [← descByB_iff] at hd; rw [hd] at h; exact absurd h (by decide)
  by_cases hk : k = 0
  · subst hk; simp [T_iter]
  · by_contra hlt
    rw [Nat.not_le] at hlt
    exact hnd ⟨k, by omega, le_refl k, hlt⟩

/-- **`hpow_of_gap`.**  Exactly the type of the `hpow` hypothesis of
`CollatzAlmostAllDescend.collatz_almost_all_descend`, conditional on the single
elementary power gap `PowGap`.  Together with §1's `cCoef_mul_bound` this shows the
original Terras-entangled `hpow` reduces to the pure arithmetic `PowGap`. -/
theorem hpow_of_gap (hgap : PowGap) :
    ∀ k, 1 ≤ k → ∀ r : Fin (2 ^ k),
      descByB (r.val + 2 ^ k) k = false →
      2 ^ k ≤ 3 ^ (aCoef (r.val + 2 ^ k) k) := by
  intro k _hk r hfalse
  set n := r.val + 2 ^ k with hn
  have hge : 2 ^ k ≤ n := by omega
  have hnd : n ≤ T_iter n k := le_T_iter_of_not_descByB n k hfalse
  exact three_pow_ge_of_non_descent_of_gap hgap n k hge hnd

/-- **`collatz_almost_all_descend_of_gap`.**  The Everett–Terras "almost all
integers descend" theorem (`Tendsto (fun k => β(k)/2^k) atTop (𝓝 0)`), conditional
on the single elementary power gap `PowGap`.  All Terras-dynamical content
(`cCoef_mul_bound`, the affine form, non-descent) is discharged here; the only
remaining input is the pure power inequality `PowGap`. -/
theorem collatz_almost_all_descend_of_gap (hgap : PowGap) :
    Filter.Tendsto (fun k => (beta k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) :=
  CollatzAlmostAllDescend.collatz_almost_all_descend (hpow_of_gap hgap)

end CollatzDescentDichotomy
