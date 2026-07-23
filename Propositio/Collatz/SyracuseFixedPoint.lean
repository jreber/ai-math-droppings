import Propositio.Collatz.SyracuseThreeAdicBias

/-!
# The unique fixed point of the Syracuse map

The Syracuse map `Syr` (the odd part of `3N+1`) has, among odd inputs, a single fixed
point: `Syr n = n ↔ n = 1`.

The proof is elementary arithmetic on the exact-division identity
`Syr N · 2^{v₂(3N+1)} = 3N+1` (`Syr_mul_pow`):

* (←) `Syr 1 = (3·1+1)/2^{v₂(4)} = 4/2^2 = 1`.
* (→) If `Syr n = n` then `n · 2^v = 3n+1`.  For `n` odd, `2^v ≥ 4` (else
  `n·2^v ≤ 3n < 3n+1`), so `4n ≤ n·2^v = 3n+1`, giving `n ≤ 1`; with `n ≥ 1`, `n = 1`.
-/

namespace SyracuseThreeAdicBias

theorem Syr_fixed_point_iff_one {n : ℕ} (hn : Odd n) : Syr n = n ↔ n = 1 := by
  have hodd : n % 2 = 1 := Nat.odd_iff.mp hn
  constructor
  · -- forward: Syr n = n ⟹ n = 1
    intro hfix
    -- exact-division identity, with the fixed-point substitution
    have key : n * 2 ^ (padicValNat 2 (3 * n + 1)) = 3 * n + 1 := by
      have h := Syr_mul_pow n
      rw [hfix] at h
      exact h
    set v := padicValNat 2 (3 * n + 1) with hv
    -- show 2^v ≥ 4
    have h4 : 4 ≤ 2 ^ v := by
      by_contra h
      have h := not_le.mp h
      have hle : n * 2 ^ v ≤ n * 3 :=
        Nat.mul_le_mul (le_refl n) (by omega)
      omega
    have hbig : n * 4 ≤ n * 2 ^ v := Nat.mul_le_mul (le_refl n) h4
    omega
  · -- backward: n = 1 ⟹ Syr 1 = 1
    rintro rfl
    have h := Syr_mul_pow 1
    norm_num at h
    have hv : padicValNat 2 4 = 2 := by
      have : (4 : ℕ) = 2 ^ 2 := rfl
      rw [this, padicValNat.prime_pow]
    rw [hv] at h
    omega

end SyracuseThreeAdicBias
