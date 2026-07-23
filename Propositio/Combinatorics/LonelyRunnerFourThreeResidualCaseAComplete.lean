/-
# Lonely Runner `k = 4`: reducing `FourThreeResidualCaseA` to a single elementary residue lemma

This file attacks `LonelyRunnerFourThreeResidualCaseB.FourThreeResidualCaseA`, the sole
remaining open residual of the honest `k = 4` Lonely Runner Conjecture: pairwise-distinct,
pairwise-coprime, positive triples `x, y, z` where a *single* element is divisible by `12`
(carries both the `4` and the `3` factor).

## The construction (a `+`-slaving reduction)

Let `P` be the element divisible by `12` (so `P ≥ 12`), and `Q, R` the other two. Pair `P`
with one of `Q, R` — say `w` — and let `u` be the third. Set the denominator `D = P + w`.
Because `P ≡ -w (mod D)`, the runner `P` is **slaved** to `w`: `‖P·(m/D)‖ = ‖w·(m/D)‖` for
every `m`. So it suffices to find a lattice time `m/D` at which *both* `w` and `u` are in the
"middle band" `[D/4, 3D/4] (mod D)` — then `P` is automatically in the band too (via `w`).

Two facts make this always possible for Case A:

* `D = P + w ≥ 13 ≥ 6`, and `w` is a unit mod `D` (`gcd(w, P+w) = gcd(w, P) = 1`).
* We can *choose* the pairing so the third element `u` is **not** a multiple of `D`: if both
  `(P+R) ∣ Q` and `(P+Q) ∣ R` held, then `Q ≥ P+R > R` and `R ≥ P+Q > Q`, a contradiction.
  So at least one pairing has `D ∤ u`.

Under these two facts the remaining obligation is the purely elementary **band-overlap
lemma** (`BandPair` below): for `D ≥ 6`, `p` a unit mod `D`, and `q` not a multiple of `D`,
there is an `m` with both `p·m` and `q·m` landing in the middle band mod `D`. A finite check
shows the *only* obstruction to `BandPair` is `D = 5` (residues `c ≡ ±2 mod 5`) — which is
excluded here since `P ≥ 12` forces `D ≥ 13`. This isolates Case A down to one self-contained
statement about residues mod `D`; it does **not** require the deep Barajas–Serra
descending-valuation machinery.

`BandPair` is packaged as an explicit hypothesis. `caseA_of_bandPair` proves the full
`FourThreeResidualCaseA` from it, unconditionally and axiom-cleanly (no `sorry`, no `axiom`,
no `native_decide`).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Propositio.Combinatorics.LonelyRunnerSmallK
import Propositio.Combinatorics.LonelyRunnerCoprimeKernel
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseB

namespace LonelyRunnerFourThreeResidualCaseAComplete

open LonelyRunnerSmallK LonelyRunnerCoprimeKernel LonelyRunnerFourThreeResidualCaseB

/-- `n` lands in the closed middle band `[D/4, 3D/4]` modulo `D`, expressed via its residue
`n % D`: `D ≤ 4·(n % D) ≤ 3·D`. This is exactly the condition `nid (n / D) ≥ 1/4`. -/
def inBand (n : ℤ) (D : ℕ) : Prop :=
  (D : ℤ) ≤ 4 * (n % (D : ℤ)) ∧ 4 * (n % (D : ℤ)) ≤ 3 * (D : ℤ)

/-- **The band-overlap hypothesis.** For any modulus `D ≥ 6`, any `p` coprime to `D`, and any
`q` not divisible by `D`, some multiple index `m` puts both `p·m` and `q·m` in the middle
band mod `D`. The single elementary residue lemma to which Case A reduces (only obstruction:
`D = 5`, excluded here). -/
def BandPair : Prop :=
  ∀ (D : ℕ) (p q : ℤ), 6 ≤ D → IsCoprime p (D : ℤ) → ¬ ((D : ℤ) ∣ q) →
    ∃ m : ℤ, inBand (p * m) D ∧ inBand (q * m) D

/-- `inBand` converts to a `nid ≥ 1/4` bound for the rational `v / D`. -/
lemma nid_of_inBand (v : ℤ) (D : ℕ) (hD : 0 < D) (h : inBand v D) :
    (1 : ℝ) / 4 ≤ nid ((v : ℝ) / (D : ℝ)) := by
  obtain ⟨h1, h2⟩ := h
  refine nid_ge_quarter_of_residue v D hD (v % (D : ℤ)) rfl ?_ ?_
  · have : ((D : ℤ) : ℝ) ≤ 4 * ((v % (D : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; linarith
  · have : 4 * ((v % (D : ℤ) : ℤ) : ℝ) ≤ 3 * ((D : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this ⊢; linarith

/-- For an integer speed `s` and lattice time `m / D`, `inBand (s·m) D` gives `nid ≥ 1/4`. -/
lemma nid_speed_time (s m : ℤ) (D : ℕ) (hD : 0 < D) (h : inBand (s * m) D) :
    (1 : ℝ) / 4 ≤ nid ((s : ℝ) * ((m : ℝ) / (D : ℝ))) := by
  have e : (s : ℝ) * ((m : ℝ) / (D : ℝ)) = (((s * m : ℤ)) : ℝ) / (D : ℝ) := by
    push_cast; ring
  rw [e]; exact nid_of_inBand (s * m) D hD h

/-- **Slaving lemma.** If `P + z = D` (as integers) and `z·m` is in the band, then `P·m` is
in the band too, because `P·m ≡ -(z·m) (mod D)` and the band is symmetric about `D/2`. -/
lemma inBand_slave (P z m : ℤ) (D : ℕ) (hD : 0 < D) (hPz : P + z = (D : ℤ))
    (h : inBand (z * m) D) : inBand (P * m) D := by
  have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hDne : ((D : ℤ)) ≠ 0 := ne_of_gt hDZ
  set rx : ℤ := (P * m) % (D : ℤ) with hrx
  set rz : ℤ := (z * m) % (D : ℤ) with hrz
  have hrx0 : 0 ≤ rx := Int.emod_nonneg _ hDne
  have hrxD : rx < (D : ℤ) := Int.emod_lt_of_pos _ hDZ
  have hrz0 : 0 ≤ rz := Int.emod_nonneg _ hDne
  have hrzD : rz < (D : ℤ) := Int.emod_lt_of_pos _ hDZ
  -- `P·m + z·m = D·m`, so the residues sum to a multiple of `D`.
  have hsum : (P * m + z * m) % (D : ℤ) = 0 := by
    have e : P * m + z * m = m * (D : ℤ) := by rw [← hPz]; ring
    rw [e]; exact Int.mul_emod_left _ _
  have hmod : (rx + rz) % (D : ℤ) = 0 := by
    rw [hrx, hrz, ← Int.add_emod]; exact hsum
  have hdvd : (D : ℤ) ∣ (rx + rz) := Int.dvd_of_emod_eq_zero hmod
  obtain ⟨h1, h2⟩ := h
  rw [← hrz] at h1 h2
  -- `rz > 0` (from `4·rz ≥ D > 0`), and `0 ≤ rx + rz < 2D` with `D ∣ (rx+rz)` forces `rx+rz=D`.
  have hrzpos : 0 < rz := by omega
  have hsumD : rx + rz = (D : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd
    have hlt2 : k < 2 := by
      have h2D : (D : ℤ) * k < (D : ℤ) * 2 := by rw [← hk]; omega
      exact lt_of_mul_lt_mul_left h2D (le_of_lt hDZ)
    have hgt0 : 0 < k := by
      have h0D : (D : ℤ) * 0 < (D : ℤ) * k := by rw [← hk]; omega
      exact lt_of_mul_lt_mul_left h0D (le_of_lt hDZ)
    have hk1 : k = 1 := by omega
    rw [hk1, mul_one] at hk; exact hk
  exact ⟨by omega, by omega⟩

/-- **The pairing core.** Given the element `P` divisible by `12` (so `P ≥ 12`), a partner
`w` coprime to `P`, and the third element `u` such that `(P + w) ∤ u`, `BandPair` produces a
lattice time `t = m / (P+w)` at which all three of `P`, `w`, `u` are in the middle band.
`P` gets there for free by slaving to `w` (`P ≡ -w mod (P+w)`). -/
lemma caseA_pair (bp : BandPair) (P w u : ℕ)
    (hP : 12 ≤ P) (hw : 1 ≤ w) (_hu : 1 ≤ u)
    (cPw : Nat.Coprime P w) (hnd : ¬ ((P + w) ∣ u)) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((P : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((w : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((u : ℝ) * t) := by
  have hDpos : 0 < P + w := by omega
  have hD6 : 6 ≤ P + w := by omega
  -- `w` is a unit mod `D = P + w`, because `gcd(w, P+w) = gcd(w, P) = 1`.
  have hcop : IsCoprime (w : ℤ) ((P + w : ℕ) : ℤ) := by
    have h1 : IsCoprime (w : ℤ) (P : ℤ) := (Nat.isCoprime_iff_coprime.mpr cPw).symm
    have h2 : IsCoprime (w : ℤ) ((P : ℤ) + (w : ℤ)) := by
      simpa using h1.add_mul_right_right 1
    rwa [Nat.cast_add]
  -- `u` is not a multiple of `D`.
  have hnd' : ¬ (((P + w : ℕ) : ℤ) ∣ (u : ℤ)) := by
    rw [Int.natCast_dvd_natCast]; exact hnd
  obtain ⟨m, hbw, hbu⟩ := bp (P + w) (w : ℤ) (u : ℤ) hD6 hcop hnd'
  -- `P` is slaved to `w`: `P + w = D`, so `P·m` lands in the band because `w·m` does.
  have hPz : (P : ℤ) + (w : ℤ) = ((P + w : ℕ) : ℤ) := by push_cast; ring
  have hslave : inBand ((P : ℤ) * m) (P + w) :=
    inBand_slave (P : ℤ) (w : ℤ) m (P + w) hDpos hPz hbw
  refine ⟨(m : ℝ) / ((P + w : ℕ) : ℝ), ?_, ?_, ?_⟩
  · have h := nid_speed_time (P : ℤ) m (P + w) hDpos hslave
    simpa using h
  · have h := nid_speed_time (w : ℤ) m (P + w) hDpos hbw
    simpa using h
  · have h := nid_speed_time (u : ℤ) m (P + w) hDpos hbu
    simpa using h

/-- **Triple form.** With `P ≥ 12` (the multiple of `12`) coprime to both partners `Q, R`,
choose the pairing whose third element is not a multiple of the denominator — at least one
of the two pairings works, since `(P+Q) ∣ R` and `(P+R) ∣ Q` together are impossible. -/
lemma caseA_triple (bp : BandPair) (P Q R : ℕ)
    (hP : 12 ≤ P) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (cPQ : Nat.Coprime P Q) (cPR : Nat.Coprime P R) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((P : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((Q : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((R : ℝ) * t) := by
  by_cases hdvd : (P + Q) ∣ R
  · -- `(P+Q) ∣ R`, so the other pairing must have `(P+R) ∤ Q`.
    have hnd : ¬ ((P + R) ∣ Q) := by
      intro h2
      have hR' : P + Q ≤ R := Nat.le_of_dvd (by omega) hdvd
      have hQ' : P + R ≤ Q := Nat.le_of_dvd (by omega) h2
      omega
    obtain ⟨t, hP', hR', hQ'⟩ := caseA_pair bp P R Q hP hR hQ cPR hnd
    exact ⟨t, hP', hQ', hR'⟩
  · obtain ⟨t, hP', hQ', hR'⟩ := caseA_pair bp P Q R hP hQ hR cPQ hdvd
    exact ⟨t, hP', hQ', hR'⟩

/-- **`FourThreeResidualCaseA` from `BandPair`.** The single-element-carries-`12` residual of
the honest `k = 4` Lonely Runner Conjecture reduces entirely to the elementary band-overlap
statement `BandPair`, with no `sorry`, no `axiom`, no `native_decide`. -/
theorem caseA_of_bandPair (bp : BandPair) : FourThreeResidualCaseA := by
  intro x y z hx hy hz _hxy _hxz _hyz cxy cxz cyz h12
  rcases h12 with h | h | h
  · -- `12 ∣ x`: `P = x`, partners `y, z`.
    have hPx : 12 ≤ x := Nat.le_of_dvd (by omega) h
    exact caseA_triple bp x y z hPx hy hz cxy cxz
  · -- `12 ∣ y`: `P = y`, partners `x, z`.
    have hPy : 12 ≤ y := Nat.le_of_dvd (by omega) h
    obtain ⟨t, hy', hx', hz'⟩ := caseA_triple bp y x z hPy hx hz cxy.symm cyz
    exact ⟨t, hx', hy', hz'⟩
  · -- `12 ∣ z`: `P = z`, partners `x, y`.
    have hPz : 12 ≤ z := Nat.le_of_dvd (by omega) h
    obtain ⟨t, hz', hx', hy'⟩ := caseA_triple bp z x y hPz hx hy cxz.symm cyz.symm
    exact ⟨t, hx', hy', hz'⟩

end LonelyRunnerFourThreeResidualCaseAComplete
