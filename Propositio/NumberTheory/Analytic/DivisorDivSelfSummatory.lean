/-
# Average of `d(n)/n`:  `∑_{n≤N} d(n)/n = ½(log N)² + O(log N)`

Let `d(n) = n.divisors.card`.  We prove the classical estimate
    `∑_{n=1}^{N} d(n)/n = ½ (log N)² + O(log N)`
with the leading term `½(log N)²` *exact* and an explicit `O(log N)` error
(`C = 5`, `N₀ = 3`).

Engine:
* a `1/n`-weighted Dirichlet reindexing `∑_{n≤N} d(n)/n = ∑_{k≤N} (1/k)·H_{⌊N/k⌋}`
  (mirror of `DivisorSummatory.sum_divisors_card_eq_sum_floor`);
* `H_{⌊N/k⌋} = log(N/k) + O(1)` from the two-sided harmonic↔log bounds;
* the key elementary lemma `∑_{k≤N} (log k)/k = ½(log N)² + O(log N)`, proved by a
  telescoping comparison against `f j = (log j)²/2` with a per-term bound
  `|(log k)/k − (f k − f (k−1))| ≤ 1/k`.

mathlib has the divisor function and the harmonic↔log bounds, but neither this
asymptotic nor `∑ (log k)/k`; both are new and reusable.
-/
import Propositio.NumberTheory.Analytic.DivisorSummatory
import Propositio.NumberTheory.Analytic.MobiusPartialSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

open Finset

namespace DivisorDivSelfSummatory

/-- Per-term comparison of `(log x)/x` against the increment of `½(log t)²`.
For real `x ≥ 2`,
    `|(log x)/x − ((log x)²/2 − (log (x−1))²/2)| ≤ 1/x`. -/
theorem per_term (x : ℝ) (hx : 2 ≤ x) :
    |Real.log x / x - (Real.log x ^ 2 / 2 - Real.log (x - 1) ^ 2 / 2)| ≤ 1 / x := by
  have hxpos : 0 < x := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hx1pos : 0 < x - 1 := by linarith
  set L := Real.log x with hLdef
  set M := Real.log (x - 1) with hMdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Real.log_nonneg (by linarith)
  have hLub : L ≤ x - 1 := by rw [hLdef]; exact Real.log_le_sub_one_of_pos hxpos
  -- δ := L - M, with `1/x ≤ δ ≤ 1/(x-1)`
  have hdiv : Real.log (x / (x - 1)) = L - M := by
    rw [Real.log_div hx0 (ne_of_gt hx1pos), ← hLdef, ← hMdef]
  have hδup : L - M ≤ 1 / (x - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / (x - 1) by positivity)
    rw [hdiv] at h1
    have he : x / (x - 1) - 1 = 1 / (x - 1) := by field_simp; ring
    linarith [h1, he]
  have hdiv2 : Real.log ((x - 1) / x) = M - L := by
    rw [Real.log_div (ne_of_gt hx1pos) hx0, ← hLdef, ← hMdef]
  have hδlow : 1 / x ≤ L - M := by
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (x - 1) / x by positivity)
    rw [hdiv2] at h1
    have he : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
    linarith [h1, he]
  -- decomposition
  have hAlg : L / x - (L ^ 2 / 2 - M ^ 2 / 2)
      = L * (1 / x - (L - M)) + (L - M) ^ 2 / 2 := by
    field_simp
    ring
  have hfac : (1 / x - (L - M)) ≤ 0 := by linarith [hδlow]
  -- bound A = L * (1/x - (L-M))  ∈ [-(1/x), 0]
  have hAle0 : L * (1 / x - (L - M)) ≤ 0 := by
    nlinarith [mul_nonneg hL0 (neg_nonneg.mpr hfac)]
  have hAge : -(1 / x) ≤ L * (1 / x - (L - M)) := by
    have h2 : (x - 1) * (1 / x - (L - M)) ≤ L * (1 / x - (L - M)) :=
      mul_le_mul_of_nonpos_right hLub hfac
    have h4 : (1 / x - 1 / (x - 1)) ≤ (1 / x - (L - M)) := by linarith [hδup]
    have h5 : (x - 1) * (1 / x - 1 / (x - 1)) = -(1 / x) := by field_simp; ring
    have h6 : (x - 1) * (1 / x - 1 / (x - 1)) ≤ (x - 1) * (1 / x - (L - M)) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    linarith [h2, h5, h6]
  -- bound B = (L-M)²/2  ∈ [0, 1/x]
  have hB0 : 0 ≤ (L - M) ^ 2 / 2 := by positivity
  have hdm0 : 0 ≤ L - M := by linarith [hδlow]
  have hdmle1 : L - M ≤ 1 := by
    have hh : 1 / (x - 1) ≤ 1 := by rw [div_le_one hx1pos]; linarith
    linarith [hδup]
  have hk : (x - 1) * (L - M) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hδup (le_of_lt hx1pos)
    rwa [mul_one_div, div_self (ne_of_gt hx1pos)] at this
  have hxdm : x * (L - M) ≤ 2 := by nlinarith [hk, hdmle1]
  have hBub : (L - M) ^ 2 / 2 ≤ 1 / x := by
    rw [div_le_div_iff₀ (by norm_num) hxpos]
    nlinarith [mul_le_mul hdmle1 hxdm (mul_nonneg (le_of_lt hxpos) hdm0)
      (by norm_num : (0:ℝ) ≤ 1)]
  rw [hAlg, abs_le]
  exact ⟨by linarith [hAge, hB0], by linarith [hAle0, hBub]⟩

/-- For `1 ≤ k ≤ N`, the harmonic number `H_{⌊N/k⌋}` is within `1` of `log N − log k`. -/
theorem harmonic_floor_close (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    |(harmonic (N / k) : ℝ) - (Real.log N - Real.log k)| ≤ 1 := by
  have hkpos : 0 < k := hk
  have hm1 : 1 ≤ N / k := (Nat.le_div_iff_mul_le hkpos).mpr (by simpa using hkN)
  have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hNpos : 0 < N := lt_of_lt_of_le hkpos hkN
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hmr : (0:ℝ) < ((N / k : ℕ) : ℝ) := by exact_mod_cast hm1
  have hlogdiv : Real.log ((N:ℝ) / (k:ℝ)) = Real.log N - Real.log k :=
    Real.log_div (ne_of_gt hNr) (ne_of_gt hkr)
  have hHup : (harmonic (N / k) : ℝ) ≤ 1 + Real.log ((N / k : ℕ) : ℝ) :=
    harmonic_le_one_add_log (N / k)
  have hHlow : Real.log ((N / k : ℕ) + 1 : ℕ) ≤ (harmonic (N / k) : ℝ) :=
    log_add_one_le_harmonic (N / k)
  have hmle : ((N / k : ℕ) : ℝ) ≤ (N:ℝ) / (k:ℝ) := Nat.cast_div_le
  have hub : (N:ℝ) / (k:ℝ) < ((N / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hkr]
    have h1 : k * (N / k) + N % k = N := Nat.div_add_mod N k
    have h2 : N % k < k := Nat.mod_lt N hkpos
    have h3 : N < k * (N / k) + k := by omega
    have hcast : (N:ℝ) < ((k * (N / k) + k : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at hcast
    nlinarith [hcast]
  have hlog_m_le : Real.log ((N / k : ℕ) : ℝ) ≤ Real.log ((N:ℝ) / (k:ℝ)) :=
    Real.log_le_log hmr hmle
  have hUpper : (harmonic (N / k) : ℝ) ≤ 1 + (Real.log N - Real.log k) := by
    calc (harmonic (N / k) : ℝ) ≤ 1 + Real.log ((N / k : ℕ) : ℝ) := hHup
      _ ≤ 1 + Real.log ((N:ℝ) / (k:ℝ)) := by linarith [hlog_m_le]
      _ = 1 + (Real.log N - Real.log k) := by rw [hlogdiv]
  have hlow2 : Real.log ((N:ℝ) / (k:ℝ)) ≤ Real.log (((N / k : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) (le_of_lt hub)
  have hLower : (Real.log N - Real.log k) ≤ (harmonic (N / k) : ℝ) := by
    have hchain : Real.log ((N:ℝ) / (k:ℝ)) ≤ (harmonic (N / k) : ℝ) := by
      calc Real.log ((N:ℝ) / (k:ℝ)) ≤ Real.log (((N / k : ℕ) : ℝ) + 1) := hlow2
        _ = Real.log (((N / k : ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring_nf
        _ ≤ (harmonic (N / k) : ℝ) := hHlow
    rw [hlogdiv] at hchain
    linarith [hchain]
  rw [abs_le]
  exact ⟨by linarith [hLower], by linarith [hUpper]⟩

/-- Inner divisor sum with `1/n` weight: for `1 ≤ k`,
    `∑_{n ≤ N, k ∣ n} 1/n = (1/k)·H_{⌊N/k⌋}`. -/
theorem inner_dvd_sum (N k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ (Finset.Icc 1 N).filter (k ∣ ·), ((n:ℝ))⁻¹
      = ((k:ℝ))⁻¹ * (harmonic (N / k) : ℝ) := by
  have hkpos : 0 < k := hk
  have hset : (Finset.Icc 1 N).filter (k ∣ ·)
      = (Finset.Icc 1 (N / k)).image (fun m => k * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
      refine ⟨n / k, ⟨?_, ?_⟩, ?_⟩
      · exact (Nat.le_div_iff_mul_le hkpos).mpr (by simpa using Nat.le_of_dvd (by omega) hdvd)
      · exact Nat.div_le_div_right hnN
      · exact Nat.mul_div_cancel' hdvd
    · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right k m⟩
      · simpa using Nat.mul_le_mul hk hm1
      · calc k * m ≤ k * (N / k) := Nat.mul_le_mul (le_refl k) hmN
          _ ≤ N := Nat.mul_div_le N k
  rw [hset, Finset.sum_image (by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hkpos hab)]
  have hcast : ∀ m : ℕ, ((k * m : ℕ) : ℝ)⁻¹ = ((k:ℝ))⁻¹ * ((m:ℝ))⁻¹ := by
    intro m; push_cast; rw [mul_inv]
  simp_rw [hcast]
  rw [← Finset.mul_sum, DivisorSummatory.sum_inv_eq_harmonic]

/-- `1/n`-weighted Dirichlet reindexing:
    `∑_{n≤N} d(n)/n = ∑_{k≤N} (1/k)·H_{⌊N/k⌋}`. -/
theorem sum_div_self_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) / (n:ℝ)
      = ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ * (harmonic (N / k) : ℝ) := by
  have hL : ∀ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) / (n:ℝ)
      = ∑ k ∈ Finset.Icc 1 N, (if k ∣ n then ((n:ℝ))⁻¹ else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← Finset.sum_filter, Finset.sum_const,
        ← DivisorSummatory.divisors_eq_filter_Icc hn.1 hn.2, nsmul_eq_mul, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [← Finset.sum_filter]
  exact inner_dvd_sum N k hk.1

/-- **Key elementary lemma.**  `∑_{k≤N} (log k)/k = ½(log N)² + O(log N)`, with explicit
two-sided error `|∑_{k≤N} (log k)/k − ½(log N)²| ≤ H_N`. -/
theorem sum_log_div_self_close (N : ℕ) :
    |∑ k ∈ Finset.Icc 1 N, Real.log k / (k:ℝ) - (1 / 2) * (Real.log N) ^ 2|
      ≤ (harmonic N : ℝ) := by
  set f : ℕ → ℝ := fun j => (Real.log j) ^ 2 / 2 with hf
  have hf0 : f 0 = 0 := by simp [hf, Real.log_zero]
  have hfN : f N = (1 / 2) * (Real.log N) ^ 2 := by rw [hf]; ring
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, (f k - f (k - 1)) = f m - f 0 := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
        have hsub : (n + 1) - 1 = n := by omega
        rw [hsub]; ring
  have hdiff : (∑ k ∈ Finset.Icc 1 N, Real.log k / (k:ℝ)) - (1 / 2) * (Real.log N) ^ 2
      = ∑ k ∈ Finset.Icc 1 N, (Real.log k / (k:ℝ) - (f k - f (k - 1))) := by
    rw [Finset.sum_sub_distrib, htel N, hf0, hfN]; ring
  rw [hdiff]
  calc |∑ k ∈ Finset.Icc 1 N, (Real.log k / (k:ℝ) - (f k - f (k - 1)))|
      ≤ ∑ k ∈ Finset.Icc 1 N, |Real.log k / (k:ℝ) - (f k - f (k - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Icc] at hk
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have hk1 : k = 1 := by omega
          subst hk1
          simp [hf, Real.log_one, Real.log_zero]
        · have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
          have hcast : Real.log ((k - 1 : ℕ) : ℝ) = Real.log ((k:ℝ) - 1) := by
            rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          have hpt := per_term (k:ℝ) hk2'
          rw [one_div] at hpt
          simp only [hf]
          rw [hcast]
          exact hpt
    _ = (harmonic N : ℝ) := DivisorSummatory.sum_inv_eq_harmonic N

/-- **Average of `d(n)/n`.**  `∑_{n=1}^{N} d(n)/n = ½(log N)² + O(log N)`, here with the
explicit constant `C = 5` and threshold `N₀ = 3`:
    `|∑_{n≤N} d(n)/n − ½(log N)²| ≤ 5·log N`  for all `N ≥ 3`. -/
theorem divisor_div_self_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) / (n:ℝ)) - (1 / 2) * (Real.log N) ^ 2|
        ≤ C * Real.log N := by
  refine ⟨5, 3, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hN3 : 3 ≤ N := hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN1
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogN1 : 1 ≤ Real.log N := by
    have he : Real.exp 1 ≤ (N:ℝ) := by
      have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN3
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) he
  rw [sum_div_self_eq N]
  set HN : ℝ := (harmonic N : ℝ) with hHN
  set Slog : ℝ := ∑ k ∈ Finset.Icc 1 N, Real.log k / (k:ℝ) with hSlog
  set R : ℝ := ∑ k ∈ Finset.Icc 1 N,
      ((k:ℝ))⁻¹ * ((harmonic (N / k) : ℝ) - (Real.log N - Real.log k)) with hR
  -- decomposition
  have hTeq : (∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ * (harmonic (N / k) : ℝ))
      = Real.log N * HN - Slog + R := by
    rw [hHN, hSlog, hR, ← DivisorSummatory.sum_inv_eq_harmonic N, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkr : (0:ℝ) < k := by exact_mod_cast hk.1
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkr
    field_simp
    ring
  rw [hTeq]
  -- the three error bounds
  have hSbound : |Slog - (1 / 2) * (Real.log N) ^ 2| ≤ HN := by
    rw [hSlog, hHN]; exact sum_log_div_self_close N
  have hHclose : |HN - Real.log N| ≤ 1 := by
    rw [hHN, abs_le]
    have hup := harmonic_le_one_add_log N
    have hlow : Real.log N ≤ (harmonic N : ℝ) := by
      have h := log_add_one_le_harmonic N
      have hmono : Real.log (N:ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_le_log hNr (by push_cast; linarith)
      linarith [hmono, h]
    exact ⟨by linarith [hup, hlow], by linarith [hup, hlow]⟩
  have hRbound : |R| ≤ HN := by
    rw [hR, hHN, ← DivisorSummatory.sum_inv_eq_harmonic N]
    calc |∑ k ∈ Finset.Icc 1 N,
            ((k:ℝ))⁻¹ * ((harmonic (N / k) : ℝ) - (Real.log N - Real.log k))|
        ≤ ∑ k ∈ Finset.Icc 1 N,
            |((k:ℝ))⁻¹ * ((harmonic (N / k) : ℝ) - (Real.log N - Real.log k))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Icc] at hk
          have hkr : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
          rw [abs_mul, abs_of_nonneg hkr]
          calc (k:ℝ)⁻¹ * |(harmonic (N / k) : ℝ) - (Real.log N - Real.log k)|
              ≤ (k:ℝ)⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left (harmonic_floor_close k N hk.1 hk.2) hkr
            _ = (k:ℝ)⁻¹ := mul_one _
  -- assemble
  have hHub : HN ≤ 1 + Real.log N := by rw [hHN]; exact harmonic_le_one_add_log N
  have hfinal : |Real.log N * HN - Slog + R - (1 / 2) * (Real.log N) ^ 2| ≤ 2 * HN + Real.log N := by
    have hid : Real.log N * HN - Slog + R - (1 / 2) * (Real.log N) ^ 2
        = -(Slog - (1 / 2) * (Real.log N) ^ 2) + Real.log N * (HN - Real.log N) + R := by ring
    rw [hid]
    have t1 : |-(Slog - (1 / 2) * (Real.log N) ^ 2)| ≤ HN := by rw [abs_neg]; exact hSbound
    have t2 : |Real.log N * (HN - Real.log N)| ≤ Real.log N := by
      rw [abs_mul, abs_of_nonneg hlogN0]
      calc Real.log N * |HN - Real.log N| ≤ Real.log N * 1 :=
            mul_le_mul_of_nonneg_left hHclose hlogN0
        _ = Real.log N := mul_one _
    calc |-(Slog - (1 / 2) * (Real.log N) ^ 2) + Real.log N * (HN - Real.log N) + R|
        ≤ |-(Slog - (1 / 2) * (Real.log N) ^ 2) + Real.log N * (HN - Real.log N)| + |R| :=
          abs_add_le _ _
      _ ≤ (|-(Slog - (1 / 2) * (Real.log N) ^ 2)| + |Real.log N * (HN - Real.log N)|) + |R| := by
          have := abs_add_le (-(Slog - (1 / 2) * (Real.log N) ^ 2)) (Real.log N * (HN - Real.log N))
          linarith [this]
      _ ≤ (HN + Real.log N) + HN := by linarith [t1, t2, hRbound]
      _ = 2 * HN + Real.log N := by ring
  calc |Real.log N * HN - Slog + R - (1 / 2) * (Real.log N) ^ 2|
      ≤ 2 * HN + Real.log N := hfinal
    _ ≤ 2 * (1 + Real.log N) + Real.log N := by linarith [hHub]
    _ = 2 + 3 * Real.log N := by ring
    _ ≤ 5 * Real.log N := by linarith [hlogN1]

end DivisorDivSelfSummatory
