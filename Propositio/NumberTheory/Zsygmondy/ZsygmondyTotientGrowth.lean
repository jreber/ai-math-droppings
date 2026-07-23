/-
Zsygmondy: the totient-growth estimate `n ≤ 3 ^ φ(n)` for ALL `n ≥ 1`.

This is the "pure inequality, orthogonal to the NT" gap flagged in the 2026-07-06 frontier
note as the last ingredient needed to discharge the `hsize : n ≤ (a - 1) ^ φ(n)` hypothesis of
`primitive_prime_exists_of_size` (in `ZsygmondyEvenPrime`) unconditionally — but ONLY for bases
`a ≥ 4` (so `a - 1 ≥ 3`).  It is elementary but genuinely needs a real (if short) proof: the
naive per-prime-power induction breaks down exactly at the factor `p = 2, k = 1` (a bare factor
of `2`), which is exactly the reason `n = 6` is a classical Zsygmondy exception at the boundary
base `a - 1 = 2` (`a = 3`) — see the companion file handling that explicit residual case.

## Proof sketch

By strong induction on `n` via `Nat.recOnPrimePow` (peel one prime-power factor `p ^ k` off `n`,
coprime to the remaining part `a`), we prove the STRENGTHENED combined statement

    Q(n) :  n ≤ 3 ^ φ(n)  ∧  (Odd n → 2 * n ≤ 3 ^ φ(n))

The extra `Odd n → 2n ≤ 3^φ(n)` clause is exactly the reinforcement needed to survive peeling a
bare factor of `2` (`p = 2, k = 1`): in that case the remaining coprime part `a` is automatically
ODD (coprimality to `2`), so the *strengthened* clause of the inductive hypothesis for `a` gives
`2a ≤ 3^φ(a) = 3^φ(2a)` directly — no margin/growth argument needed at all for that step.  Every
other case (`p` odd, or `p = 2` with `k ≥ 2`) has a genuine multiplicative margin
(`φ(p^k) ≥ 2`) and closes via the elementary per-prime-power bound `3 * p^k ≤ 3 ^ φ(p^k)`.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Linarith

namespace ZsygmondyTotientGrowth

open Nat

/-! ### Elementary numeric helper lemmas (subtraction-free, indexed by `+1`/`+3`) -/

/-- `q + 1 ≤ 3 ^ q` for all `q ≥ 0`. -/
private theorem succ_le_three_pow (q : ℕ) : q + 1 ≤ 3 ^ q := by
  induction q with
  | zero => norm_num
  | succ n ih =>
    have h3 : (3:ℕ) ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
    omega

/-- `j + 3 ≤ 3 ^ (j + 1)` for all `j ≥ 0` (i.e. `m ≤ 3 ^ (m - 2)` for `m ≥ 3`, subtraction-free). -/
private theorem add_three_le_three_pow_succ (j : ℕ) : j + 3 ≤ 3 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have h3 : (3:ℕ) ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by rw [pow_succ]; ring
    omega

/-- General corollary: `m ≤ 3 ^ (m - 2)` for all `m ≥ 3`. -/
private theorem self_le_three_pow_sub_two {m : ℕ} (hm : 3 ≤ m) : m ≤ 3 ^ (m - 2) := by
  obtain ⟨j, hj⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have h := add_three_le_three_pow_succ j
  have heq : m - 2 = j + 1 := by omega
  rw [heq, hj]
  omega

/-! ### The per-prime-power margin bound, for odd primes -/

/-- For an odd prime `p ≥ 3` and `j ≥ 0` (exponent `k = j + 1`):
`3 * p ^ (j+1) ≤ 3 ^ (p ^ j * (p - 1))`, i.e. `p ^ k ≤ 3 ^ (φ(p^k) - 1)` in multiplicative form.
This is the per-factor margin that lets an odd prime power be absorbed for free. -/
private theorem three_mul_pow_le_three_pow_totient_odd_prime_pow
    {p : ℕ} (hp3 : 3 ≤ p) : ∀ j : ℕ, 3 * p ^ (j + 1) ≤ 3 ^ (p ^ j * (p - 1)) := by
  intro j
  induction j with
  | zero =>
    -- j = 0 : 3 * p ≤ 3 ^ (p - 1)
    simp only [Nat.zero_add, pow_one, pow_zero, one_mul]
    have hbase : p ≤ 3 ^ (p - 2) := self_le_three_pow_sub_two hp3
    have heq2 : (3:ℕ) ^ (p - 1) = 3 * 3 ^ (p - 2) := by
      have : p - 1 = (p - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    omega
  | succ n ih =>
    -- goal: 3 * p ^ (n+2) ≤ 3 ^ (p^(n+1) * (p-1))
    -- from ih: 3 * p ^ (n+1) ≤ 3 ^ (p^n * (p-1))
    set t := p ^ n * (p - 1) with ht
    have ht1 : 1 ≤ t := by
      have hp1 : 1 ≤ p - 1 := by omega
      have hpn : 1 ≤ p ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ p ^ n * (p - 1) := Nat.mul_le_mul hpn hp1
    -- key: p ≤ 3 ^ (t * (p - 1)) via p ≤ 3^(p-1) ≤ 3^(t*(p-1))  [t ≥ 1]
    have hp_le : p ≤ 3 ^ (p - 1) := by
      have hh := succ_le_three_pow (p - 1)
      have heq : p - 1 + 1 = p := by omega
      rwa [heq] at hh
    have hp_le' : p ≤ 3 ^ (t * (p - 1)) := by
      have hmono : (3:ℕ) ^ (p - 1) ≤ 3 ^ (t * (p - 1)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        calc p - 1 = 1 * (p - 1) := by ring
          _ ≤ t * (p - 1) := Nat.mul_le_mul_right _ ht1
      omega
    -- next totient value: p^(n+1)*(p-1) = t * p
    have hnext : p ^ (n + 1) * (p - 1) = t * p := by rw [ht, pow_succ]; ring
    have hexp : (3:ℕ) ^ (t * p) = (3 ^ t) ^ p := by rw [pow_mul]
    rw [hnext, hexp]
    have hp1eq : p - 1 + 1 = p := by omega
    have hchain5 : t * (p - 1) + t = t * p := by
      calc t * (p - 1) + t = t * ((p - 1) + 1) := by ring
        _ = t * p := by rw [hp1eq]
    have hchain1 : 3 * p ^ (n + 2) = p * (3 * p ^ (n + 1)) := by ring
    have hchain2 : p * (3 * p ^ (n + 1)) ≤ p * 3 ^ t := Nat.mul_le_mul_left p ih
    have hchain3 : p * 3 ^ t ≤ 3 ^ (t * (p - 1)) * 3 ^ t := Nat.mul_le_mul_right _ hp_le'
    have hchain4 : (3:ℕ) ^ (t * (p - 1)) * 3 ^ t = 3 ^ (t * (p - 1) + t) := by
      rw [← pow_add]
    calc 3 * p ^ (n + 2) = p * (3 * p ^ (n + 1)) := hchain1
      _ ≤ p * 3 ^ t := hchain2
      _ ≤ 3 ^ (t * (p - 1)) * 3 ^ t := hchain3
      _ = 3 ^ (t * (p - 1) + t) := hchain4
      _ = 3 ^ (t * p) := by rw [hchain5]
      _ = (3 ^ t) ^ p := hexp

/-- **Odd-prime per-factor margin bound.** For an odd prime `p ≥ 3` and `k ≥ 1`:
`3 * p ^ k ≤ 3 ^ (Nat.totient (p ^ k))`. -/
private theorem three_mul_pow_le_three_pow_totient_prime_pow
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    3 * p ^ k ≤ 3 ^ Nat.totient (p ^ k) := by
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact absurd h2 hpodd
    · have := hp.two_le; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.totient_prime_pow hp (by omega)]
  exact three_mul_pow_le_three_pow_totient_odd_prime_pow hp3 j

/-! ### The pure power-of-two bound (`a = 1` sub-case: `p = 2`, no odd cofactor) -/

/-- `2 ^ (k+1) ≤ 3 ^ (2 ^ k)` for `k ≥ 0`, i.e. `2^k ≤ 3^φ(2^k)`: pure powers of `2` need no
margin from any cofactor. -/
private theorem two_pow_le_three_pow_totient_two_pow (k : ℕ) : 2 ^ (k + 1) ≤ 3 ^ (2 ^ k) := by
  induction k with
  | zero => decide
  | succ n ih =>
    have h1 : (2:ℕ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
    have h2 : (3:ℕ) ^ (2 ^ (n + 1)) = (3 ^ (2 ^ n)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    have hXge : (3:ℕ) ≤ 3 ^ (2 ^ n) := by
      calc (3:ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
    have hsq : 2 * 3 ^ (2 ^ n) ≤ (3 ^ (2 ^ n)) ^ 2 := by nlinarith [hXge]
    have hstep : 2 * 2 ^ (n + 1) ≤ 2 * 3 ^ (2 ^ n) := Nat.mul_le_mul_left 2 ih
    calc (2:ℕ) ^ (n + 2) = 2 * 2 ^ (n + 1) := h1
      _ ≤ 2 * 3 ^ (2 ^ n) := hstep
      _ ≤ (3 ^ (2 ^ n)) ^ 2 := hsq
      _ = 3 ^ (2 ^ (n + 1)) := h2.symm

/-! ### Shared margin-absorption helper (used to combine a per-factor margin bound with the
inductive hypothesis on the coprime remainder) -/

/-- If `3 * c ≤ 3 ^ t` (a per-factor margin bound) and `X ≤ 3 ^ e` (`e ≥ 1`), then
`c * X ≤ 3 ^ (t * e)`.  This is the generic combining step used both for `GOAL1` (with
`X = a`) and `GOAL2` (with `X = 2a`) once a margin bound on the peeled prime-power factor is
in hand. -/
private theorem margin_absorb {c t X e : ℕ} (hmargin : 3 * c ≤ 3 ^ t) (ht1 : 1 ≤ t)
    (hXe : X ≤ 3 ^ e) (he1 : 1 ≤ e) : c * X ≤ 3 ^ (t * e) := by
  obtain ⟨q, rfl⟩ : ∃ q, e = q + 1 := ⟨e - 1, by omega⟩
  have hstep1 : c * X ≤ c * 3 ^ (q + 1) := Nat.mul_le_mul_left c hXe
  have hstep2 : c * (3:ℕ) ^ (q + 1) = (3 * c) * 3 ^ q := by
    rw [pow_succ]; ring
  have hstep3 : (3 * c) * 3 ^ q ≤ 3 ^ t * 3 ^ q := Nat.mul_le_mul_right _ hmargin
  have hstep4 : (3:ℕ) ^ t * 3 ^ q ≤ 3 ^ t * (3 ^ t) ^ q := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    calc (3:ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  have hstep5 : (3:ℕ) ^ t * (3 ^ t) ^ q = (3 ^ t) ^ (q + 1) := by
    rw [pow_succ]; ring
  have hstep6 : (3:ℕ) ^ t * (3 ^ t) ^ q = 3 ^ (t * (q + 1)) := by
    rw [hstep5, ← pow_mul]
  calc c * X ≤ c * 3 ^ (q + 1) := hstep1
    _ = (3 * c) * 3 ^ q := hstep2
    _ ≤ 3 ^ t * 3 ^ q := hstep3
    _ ≤ 3 ^ t * (3 ^ t) ^ q := hstep4
    _ = 3 ^ (t * (q + 1)) := hstep6

/-! ### The combined main theorem -/

/-- **Totient growth, combined form.** For every `n : ℕ`:
`n ≤ 3 ^ φ(n)`, and moreover if `n` is odd, `2 * n ≤ 3 ^ φ(n)`.  The `Odd` clause is the
reinforcement that survives peeling a bare factor of `2` (see the file docstring). -/
theorem totient_growth : ∀ n : ℕ,
    n ≤ 3 ^ Nat.totient n ∧ (Odd n → 2 * n ≤ 3 ^ Nat.totient n) := by
  intro n
  induction n using Nat.recOnPrimePow with
  | zero => simp [Nat.totient_zero]
  | one => simp [Nat.totient_one]
  | prime_pow_mul a p k hp hpa hk ih =>
    -- rule out a = 0 (contradicts ¬ p ∣ a)
    have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hcop : (p ^ k).Coprime a :=
      (Nat.coprime_pow_left_iff hk p a).mpr (hp.coprime_iff_not_dvd.mpr hpa)
    have htot : Nat.totient (p ^ k * a) = Nat.totient (p ^ k) * Nat.totient a :=
      Nat.totient_mul hcop
    set t := Nat.totient (p ^ k) with htdef
    have hfa1 : 1 ≤ Nat.totient a := Nat.totient_pos.mpr hapos
    have ht1 : 1 ≤ t := Nat.totient_pos.mpr (pow_pos hp.pos k)
    by_cases hp2 : p = 2
    · -- p = 2 : a is automatically odd; GOAL2 is vacuous (N is even)
      subst hp2
      have haodd : Odd a := by
        rcases Nat.even_or_odd a with he | ho
        · exact absurd (even_iff_two_dvd.mp he) hpa
        · exact ho
      constructor
      · -- GOAL1
        by_cases hk1 : k = 1
        · -- k = 1 : use ih.2 directly (2a ≤ 3^φa = 3^φ(2^1*a))
          subst hk1
          have h2a : 2 * a ≤ 3 ^ Nat.totient a := ih.2 haodd
          have ht_eq : t = 1 := by
            rw [htdef, Nat.totient_prime_pow Nat.prime_two (by norm_num)]
            norm_num
          rw [htot, ht_eq, one_mul]
          simpa [pow_one] using h2a
        · -- k ≥ 2
          have hk2 : 2 ≤ k := by omega
          rw [htot]
          by_cases ha1 : a = 1
          · -- pure power of 2
            subst ha1
            simp only [Nat.totient_one, mul_one]
            obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            have hkey := two_pow_le_three_pow_totient_two_pow j
            rw [hj]
            have htj : t = 2 ^ j := by
              rw [htdef, hj, Nat.totient_prime_pow Nat.prime_two (by omega)]
              have heq1 : j + 1 - 1 = j := by omega
              rw [heq1]; norm_num
            rw [htj]
            simpa [add_comm] using hkey
          · -- a ≥ 3 (odd, ≠ 1)
            have ha3 : 3 ≤ a := by
              rcases haodd with ⟨m, hm⟩; omega
            have hfa2 : 2 ≤ Nat.totient a := by
              have heven : Even (Nat.totient a) := Nat.totient_even (by omega)
              have hpos : 0 < Nat.totient a := Nat.totient_pos.mpr hapos
              obtain ⟨r, hr⟩ := heven
              omega
            -- margin-2 bound: 9 * 2^k ≤ 3^(2t) = (3^t)^2
            have hm2 : 2 ^ k ≤ 3 ^ (2 ^ k - 2) := by
              apply self_le_three_pow_sub_two
              calc (3:ℕ) ≤ 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
            have ht2 : t = 2 ^ (k - 1) := by
              rw [htdef, Nat.totient_prime_pow Nat.prime_two (by omega)]
              norm_num
            have h2t : 2 * t = 2 ^ k := by
              rw [ht2]
              have hkeq : k - 1 + 1 = k := by omega
              calc 2 * 2 ^ (k - 1) = 2 ^ 1 * 2 ^ (k - 1) := by norm_num
                _ = 2 ^ (1 + (k - 1)) := by rw [← pow_add]
                _ = 2 ^ (k - 1 + 1) := by rw [add_comm]
                _ = 2 ^ k := by rw [hkeq]
            have hmargin : 9 * 2 ^ k ≤ 3 ^ (2 * t) := by
              have heq2t : 2 * t - 2 = 2 ^ k - 2 := by omega
              have h9 : (9:ℕ) * 2 ^ k = 3 ^ 2 * 2 ^ k := by norm_num
              rw [h9]
              have hexp : (2:ℕ) * t = (2 * t - 2) + 2 := by omega
              rw [hexp, pow_add, heq2t]
              nlinarith [hm2]
            -- combine: 2^k * a ≤ 3^(t*φ(a))  (φ(a) = q + 2)
            obtain ⟨q, hq⟩ : ∃ q, Nat.totient a = q + 2 := ⟨Nat.totient a - 2, by omega⟩
            have key : (2:ℕ) ^ k * a ≤ 3 ^ (t * Nat.totient a) := by
              rw [hq]
              have ih1' : a ≤ 3 ^ (q + 2) := hq ▸ ih.1
              have hstepA : (2:ℕ) ^ k * a ≤ 2 ^ k * 3 ^ (q + 2) := Nat.mul_le_mul_left _ ih1'
              have hstepB : (2:ℕ) ^ k * 3 ^ (q+2) = (9 * 2 ^ k) * 3 ^ q := by
                have hh : (3:ℕ)^(q+2) = 9 * 3 ^ q := by rw [pow_add]; ring
                rw [hh]; ring
              have hstepC : (9:ℕ) * 2 ^ k * 3 ^ q ≤ 3 ^ (2*t) * 3 ^ q :=
                Nat.mul_le_mul_right _ hmargin
              have hstepD : (3:ℕ) ^ (2*t) * 3 ^ q ≤ (3^t)^2 * (3^t)^q := by
                have he1 : (3:ℕ)^(2*t) = (3^t)^2 := by rw [mul_comm, pow_mul]
                rw [he1]
                apply Nat.mul_le_mul_left
                apply Nat.pow_le_pow_left
                calc (3:ℕ) = 3 ^ 1 := by norm_num
                  _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
              have hstepE : ((3:ℕ)^t) ^ 2 * (3^t)^q = 3 ^ (t * (q+2)) := by
                have e1 : t * (q + 2) = t * q + t * 2 := by ring
                rw [e1, pow_add]
                have e2 : ((3:ℕ)^t) ^ 2 = 3 ^ (t * 2) := by rw [pow_mul]
                have e3 : ((3:ℕ)^t) ^ q = 3 ^ (t * q) := by rw [pow_mul]
                rw [e2, e3]
                ring
              calc (2:ℕ)^k * a ≤ 2^k * 3^(q+2) := hstepA
                _ = 9 * 2^k * 3^q := hstepB
                _ ≤ 3^(2*t) * 3^q := hstepC
                _ ≤ (3^t)^2 * (3^t)^q := hstepD
                _ = 3 ^ (t * (q+2)) := hstepE
            exact key
      · -- GOAL2 vacuous: N = 2^k * a is even
        intro hodd
        exfalso
        have heven : Even (2 ^ k * a) := by
          have h2dvd : (2:ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
          exact even_iff_two_dvd.mpr (Dvd.dvd.mul_right h2dvd a)
        exact (not_odd_iff_even.mpr heven) hodd
    · -- p odd (p ≠ 2, p prime ⇒ p ≥ 3): the generic margin bound applies to BOTH goals
      have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
      have hmargin : 3 * p ^ k ≤ 3 ^ t :=
        three_mul_pow_le_three_pow_totient_prime_pow hp hp2 hk
      refine ⟨?_, ?_⟩
      · rw [htot]
        exact margin_absorb hmargin ht1 ih.1 hfa1
      · intro hoddN
        rw [htot]
        have haodd : Odd a := by
          rw [odd_mul] at hoddN
          exact hoddN.2
        have h2a : 2 * a ≤ 3 ^ Nat.totient a := ih.2 haodd
        have hcomm : 2 * (p ^ k * a) = p ^ k * (2 * a) := by ring
        rw [hcomm]
        exact margin_absorb hmargin ht1 h2a hfa1

end ZsygmondyTotientGrowth
