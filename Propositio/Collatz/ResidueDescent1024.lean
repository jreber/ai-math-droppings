import Propositio.Collatz.Basic
import Propositio.Collatz.ResidueDescent256
import Mathlib.Tactic

/-!
# Guaranteed bounded descent for residue classes mod 1024

Twelve new 10-step guaranteed-descent lemmas.
All classes have coefficient 3⁶/2¹⁰ = 729/1024 < 1 (6 odd steps, 4 even).
Density: 960/1024 = 15/16 ≈ 93.75%. -/

namespace CollatzResidueDescent1024

open TerrasDensity

theorem descent_287_mod_1024 {n : ℕ} (hn : n % 1024 = 287) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 287 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 287) = 1536 * k + 431 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 431) = 2304 * k + 647 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 647) = 3456 * k + 971 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 971) = 5184 * k + 1457 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 1457) = 7776 * k + 2186 := by unfold T; split <;> omega
  have h6 : T (7776 * k + 2186) = 3888 * k + 1093 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 1093) = 5832 * k + 1640 := by unfold T; split <;> omega
  have h8 : T (5832 * k + 1640) = 2916 * k + 820 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 820) = 1458 * k + 410 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 410) = 729 * k + 205 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 287) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 287)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_347_mod_1024 {n : ℕ} (hn : n % 1024 = 347) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 347 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 347) = 1536 * k + 521 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 521) = 2304 * k + 782 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 782) = 1152 * k + 391 := by unfold T; split <;> omega
  have h4 : T (1152 * k + 391) = 1728 * k + 587 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 587) = 2592 * k + 881 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 881) = 3888 * k + 1322 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 1322) = 1944 * k + 661 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 661) = 2916 * k + 992 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 992) = 1458 * k + 496 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 496) = 729 * k + 248 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 347) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 347)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_367_mod_1024 {n : ℕ} (hn : n % 1024 = 367) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 367 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 367) = 1536 * k + 551 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 551) = 2304 * k + 827 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 827) = 3456 * k + 1241 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 1241) = 5184 * k + 1862 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 1862) = 2592 * k + 931 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 931) = 3888 * k + 1397 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 1397) = 5832 * k + 2096 := by unfold T; split <;> omega
  have h8 : T (5832 * k + 2096) = 2916 * k + 1048 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 1048) = 1458 * k + 524 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 524) = 729 * k + 262 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 367) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 367)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_423_mod_1024 {n : ℕ} (hn : n % 1024 = 423) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 423 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 423) = 1536 * k + 635 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 635) = 2304 * k + 953 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 953) = 3456 * k + 1430 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 1430) = 1728 * k + 715 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 715) = 2592 * k + 1073 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 1073) = 3888 * k + 1610 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 1610) = 1944 * k + 805 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 805) = 2916 * k + 1208 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 1208) = 1458 * k + 604 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 604) = 729 * k + 302 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 423) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 423)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_507_mod_1024 {n : ℕ} (hn : n % 1024 = 507) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 507 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 507) = 1536 * k + 761 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 761) = 2304 * k + 1142 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 1142) = 1152 * k + 571 := by unfold T; split <;> omega
  have h4 : T (1152 * k + 571) = 1728 * k + 857 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 857) = 2592 * k + 1286 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 1286) = 1296 * k + 643 := by unfold T; split <;> omega
  have h7 : T (1296 * k + 643) = 1944 * k + 965 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 965) = 2916 * k + 1448 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 1448) = 1458 * k + 724 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 724) = 729 * k + 362 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 507) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 507)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_575_mod_1024 {n : ℕ} (hn : n % 1024 = 575) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 575 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 575) = 1536 * k + 863 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 863) = 2304 * k + 1295 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 1295) = 3456 * k + 1943 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 1943) = 5184 * k + 2915 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 2915) = 7776 * k + 4373 := by unfold T; split <;> omega
  have h6 : T (7776 * k + 4373) = 11664 * k + 6560 := by unfold T; split <;> omega
  have h7 : T (11664 * k + 6560) = 5832 * k + 3280 := by unfold T; split <;> omega
  have h8 : T (5832 * k + 3280) = 2916 * k + 1640 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 1640) = 1458 * k + 820 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 820) = 729 * k + 410 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 575) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 575)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_583_mod_1024 {n : ℕ} (hn : n % 1024 = 583) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 583 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 583) = 1536 * k + 875 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 875) = 2304 * k + 1313 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 1313) = 3456 * k + 1970 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 1970) = 1728 * k + 985 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 985) = 2592 * k + 1478 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 1478) = 1296 * k + 739 := by unfold T; split <;> omega
  have h7 : T (1296 * k + 739) = 1944 * k + 1109 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 1109) = 2916 * k + 1664 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 1664) = 1458 * k + 832 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 832) = 729 * k + 416 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 583) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 583)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_735_mod_1024 {n : ℕ} (hn : n % 1024 = 735) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 735 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 735) = 1536 * k + 1103 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 1103) = 2304 * k + 1655 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 1655) = 3456 * k + 2483 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 2483) = 5184 * k + 3725 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 3725) = 7776 * k + 5588 := by unfold T; split <;> omega
  have h6 : T (7776 * k + 5588) = 3888 * k + 2794 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 2794) = 1944 * k + 1397 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 1397) = 2916 * k + 2096 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 2096) = 1458 * k + 1048 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 1048) = 729 * k + 524 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 735) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 735)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_815_mod_1024 {n : ℕ} (hn : n % 1024 = 815) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 815 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 815) = 1536 * k + 1223 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 1223) = 2304 * k + 1835 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 1835) = 3456 * k + 2753 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 2753) = 5184 * k + 4130 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 4130) = 2592 * k + 2065 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 2065) = 3888 * k + 3098 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 3098) = 1944 * k + 1549 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 1549) = 2916 * k + 2324 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 2324) = 1458 * k + 1162 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 1162) = 729 * k + 581 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 815) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 815)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_923_mod_1024 {n : ℕ} (hn : n % 1024 = 923) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 923 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 923) = 1536 * k + 1385 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 1385) = 2304 * k + 2078 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 2078) = 1152 * k + 1039 := by unfold T; split <;> omega
  have h4 : T (1152 * k + 1039) = 1728 * k + 1559 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 1559) = 2592 * k + 2339 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 2339) = 3888 * k + 3509 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 3509) = 5832 * k + 5264 := by unfold T; split <;> omega
  have h8 : T (5832 * k + 5264) = 2916 * k + 2632 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 2632) = 1458 * k + 1316 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 1316) = 729 * k + 658 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 923) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 923)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_975_mod_1024 {n : ℕ} (hn : n % 1024 = 975) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 975 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 975) = 1536 * k + 1463 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 1463) = 2304 * k + 2195 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 2195) = 3456 * k + 3293 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 3293) = 5184 * k + 4940 := by unfold T; split <;> omega
  have h5 : T (5184 * k + 4940) = 2592 * k + 2470 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 2470) = 1296 * k + 1235 := by unfold T; split <;> omega
  have h7 : T (1296 * k + 1235) = 1944 * k + 1853 := by unfold T; split <;> omega
  have h8 : T (1944 * k + 1853) = 2916 * k + 2780 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 2780) = 1458 * k + 1390 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 1390) = 729 * k + 695 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 975) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 975)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_999_mod_1024 {n : ℕ} (hn : n % 1024 = 999) : T_iter n 10 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1024 * k + 999 := ⟨n / 1024, by omega⟩
  have h1 : T (1024 * k + 999) = 1536 * k + 1499 := by unfold T; split <;> omega
  have h2 : T (1536 * k + 1499) = 2304 * k + 2249 := by unfold T; split <;> omega
  have h3 : T (2304 * k + 2249) = 3456 * k + 3374 := by unfold T; split <;> omega
  have h4 : T (3456 * k + 3374) = 1728 * k + 1687 := by unfold T; split <;> omega
  have h5 : T (1728 * k + 1687) = 2592 * k + 2531 := by unfold T; split <;> omega
  have h6 : T (2592 * k + 2531) = 3888 * k + 3797 := by unfold T; split <;> omega
  have h7 : T (3888 * k + 3797) = 5832 * k + 5696 := by unfold T; split <;> omega
  have h8 : T (5832 * k + 5696) = 2916 * k + 2848 := by unfold T; split <;> omega
  have h9 : T (2916 * k + 2848) = 1458 * k + 1424 := by unfold T; split <;> omega
  have h10 : T (1458 * k + 1424) = 729 * k + 712 := by unfold T; split <;> omega
  have e : T_iter (1024 * k + 999) 10 =
      T (T (T (T (T (T (T (T (T (T (1024 * k + 999)))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; omega

theorem descent_within_ten {n : ℕ}
    (h : n % 16 = 3
         ∨ n % 32 = 11
         ∨ n % 32 = 19
         ∨ n % 32 = 23
         ∨ n % 64 = 35
         ∨ n % 64 = 43
         ∨ n % 64 = 51
         ∨ n % 128 = 7
         ∨ n % 128 = 15
         ∨ n % 128 = 59
         ∨ n % 256 = 39
         ∨ n % 256 = 79
         ∨ n % 256 = 95
         ∨ n % 256 = 123
         ∨ n % 256 = 175
         ∨ n % 256 = 199
         ∨ n % 256 = 219
         ∨ n % 1024 = 287
         ∨ n % 1024 = 347
         ∨ n % 1024 = 367
         ∨ n % 1024 = 423
         ∨ n % 1024 = 507
         ∨ n % 1024 = 575
         ∨ n % 1024 = 583
         ∨ n % 1024 = 735
         ∨ n % 1024 = 815
         ∨ n % 1024 = 923
         ∨ n % 1024 = 975
         ∨ n % 1024 = 999
         ) :
    ∃ k, 1 ≤ k ∧ k ≤ 10 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, hkb, hd⟩ := CollatzResidueDescent256.descent_within_eight
        (by tauto); exact ⟨k, hk, by omega, hd⟩
  · exact ⟨10, by norm_num, by norm_num, descent_287_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_347_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_367_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_423_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_507_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_575_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_583_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_735_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_815_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_923_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_975_mod_1024 (by assumption)⟩
  · exact ⟨10, by norm_num, by norm_num, descent_999_mod_1024 (by assumption)⟩

end CollatzResidueDescent1024

