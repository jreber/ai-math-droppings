import Propositio.Collatz.Basic
import Propositio.Collatz.ResidueDescent1024
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent4096

open TerrasDensity

theorem descent_231_mod_4096 {n : ℕ} (hn : n % 4096 = 231) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 231 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 231) = 6144 * k + 347 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 347) = 9216 * k + 521 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 521) = 13824 * k + 782 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 782) = 6912 * k + 391 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 391) = 10368 * k + 587 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 587) = 15552 * k + 881 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 881) = 23328 * k + 1322 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 1322) = 11664 * k + 661 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 661) = 17496 * k + 992 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 992) = 8748 * k + 496 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 496) = 4374 * k + 248 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 248) = 2187 * k + 124 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 231) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 231)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_383_mod_4096 {n : ℕ} (hn : n % 4096 = 383) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 383 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 383) = 6144 * k + 575 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 575) = 9216 * k + 863 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 863) = 13824 * k + 1295 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 1295) = 20736 * k + 1943 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 1943) = 31104 * k + 2915 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 2915) = 46656 * k + 4373 := by unfold T; split <;> omega
  have h7 : T (46656 * k + 4373) = 69984 * k + 6560 := by unfold T; split <;> omega
  have h8 : T (69984 * k + 6560) = 34992 * k + 3280 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 3280) = 17496 * k + 1640 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 1640) = 8748 * k + 820 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 820) = 4374 * k + 410 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 410) = 2187 * k + 205 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 383) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 383)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_463_mod_4096 {n : ℕ} (hn : n % 4096 = 463) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 463 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 463) = 6144 * k + 695 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 695) = 9216 * k + 1043 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 1043) = 13824 * k + 1565 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 1565) = 20736 * k + 2348 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 2348) = 10368 * k + 1174 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 1174) = 5184 * k + 587 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 587) = 7776 * k + 881 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 881) = 11664 * k + 1322 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 1322) = 5832 * k + 661 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 661) = 8748 * k + 992 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 992) = 4374 * k + 496 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 496) = 2187 * k + 248 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 463) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 463)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_615_mod_4096 {n : ℕ} (hn : n % 4096 = 615) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 615 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 615) = 6144 * k + 923 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 923) = 9216 * k + 1385 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 1385) = 13824 * k + 2078 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 2078) = 6912 * k + 1039 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 1039) = 10368 * k + 1559 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 1559) = 15552 * k + 2339 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 2339) = 23328 * k + 3509 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 3509) = 34992 * k + 5264 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 5264) = 17496 * k + 2632 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 2632) = 8748 * k + 1316 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 1316) = 4374 * k + 658 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 658) = 2187 * k + 329 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 615) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 615)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_879_mod_4096 {n : ℕ} (hn : n % 4096 = 879) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 879 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 879) = 6144 * k + 1319 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 1319) = 9216 * k + 1979 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 1979) = 13824 * k + 2969 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 2969) = 20736 * k + 4454 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 4454) = 10368 * k + 2227 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 2227) = 15552 * k + 3341 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 3341) = 23328 * k + 5012 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 5012) = 11664 * k + 2506 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 2506) = 5832 * k + 1253 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 1253) = 8748 * k + 1880 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 1880) = 4374 * k + 940 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 940) = 2187 * k + 470 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 879) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 879)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_935_mod_4096 {n : ℕ} (hn : n % 4096 = 935) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 935 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 935) = 6144 * k + 1403 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 1403) = 9216 * k + 2105 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 2105) = 13824 * k + 3158 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 3158) = 6912 * k + 1579 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 1579) = 10368 * k + 2369 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 2369) = 15552 * k + 3554 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 3554) = 7776 * k + 1777 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 1777) = 11664 * k + 2666 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 2666) = 5832 * k + 1333 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 1333) = 8748 * k + 2000 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 2000) = 4374 * k + 1000 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1000) = 2187 * k + 500 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 935) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 935)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1019_mod_4096 {n : ℕ} (hn : n % 4096 = 1019) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1019 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1019) = 6144 * k + 1529 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 1529) = 9216 * k + 2294 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 2294) = 4608 * k + 1147 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 1147) = 6912 * k + 1721 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 1721) = 10368 * k + 2582 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 2582) = 5184 * k + 1291 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 1291) = 7776 * k + 1937 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 1937) = 11664 * k + 2906 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 2906) = 5832 * k + 1453 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 1453) = 8748 * k + 2180 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 2180) = 4374 * k + 1090 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1090) = 2187 * k + 545 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1019) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1019)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1087_mod_4096 {n : ℕ} (hn : n % 4096 = 1087) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1087 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1087) = 6144 * k + 1631 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 1631) = 9216 * k + 2447 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 2447) = 13824 * k + 3671 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 3671) = 20736 * k + 5507 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 5507) = 31104 * k + 8261 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 8261) = 46656 * k + 12392 := by unfold T; split <;> omega
  have h7 : T (46656 * k + 12392) = 23328 * k + 6196 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 6196) = 11664 * k + 3098 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 3098) = 5832 * k + 1549 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 1549) = 8748 * k + 2324 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 2324) = 4374 * k + 1162 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1162) = 2187 * k + 581 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1087) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1087)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1231_mod_4096 {n : ℕ} (hn : n % 4096 = 1231) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1231 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1231) = 6144 * k + 1847 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 1847) = 9216 * k + 2771 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 2771) = 13824 * k + 4157 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 4157) = 20736 * k + 6236 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 6236) = 10368 * k + 3118 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 3118) = 5184 * k + 1559 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 1559) = 7776 * k + 2339 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 2339) = 11664 * k + 3509 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 3509) = 17496 * k + 5264 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 5264) = 8748 * k + 2632 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 2632) = 4374 * k + 1316 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1316) = 2187 * k + 658 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1231) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1231)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1435_mod_4096 {n : ℕ} (hn : n % 4096 = 1435) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1435 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1435) = 6144 * k + 2153 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2153) = 9216 * k + 3230 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 3230) = 4608 * k + 1615 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 1615) = 6912 * k + 2423 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 2423) = 10368 * k + 3635 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 3635) = 15552 * k + 5453 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 5453) = 23328 * k + 8180 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 8180) = 11664 * k + 4090 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 4090) = 5832 * k + 2045 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 2045) = 8748 * k + 3068 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3068) = 4374 * k + 1534 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1534) = 2187 * k + 767 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1435) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1435)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1647_mod_4096 {n : ℕ} (hn : n % 4096 = 1647) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1647 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1647) = 6144 * k + 2471 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2471) = 9216 * k + 3707 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 3707) = 13824 * k + 5561 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 5561) = 20736 * k + 8342 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 8342) = 10368 * k + 4171 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 4171) = 15552 * k + 6257 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 6257) = 23328 * k + 9386 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 9386) = 11664 * k + 4693 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 4693) = 17496 * k + 7040 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 7040) = 8748 * k + 3520 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3520) = 4374 * k + 1760 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1760) = 2187 * k + 880 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1647) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1647)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1703_mod_4096 {n : ℕ} (hn : n % 4096 = 1703) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1703 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1703) = 6144 * k + 2555 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2555) = 9216 * k + 3833 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 3833) = 13824 * k + 5750 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 5750) = 6912 * k + 2875 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 2875) = 10368 * k + 4313 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 4313) = 15552 * k + 6470 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 6470) = 7776 * k + 3235 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 3235) = 11664 * k + 4853 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 4853) = 17496 * k + 7280 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 7280) = 8748 * k + 3640 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3640) = 4374 * k + 1820 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1820) = 2187 * k + 910 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1703) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1703)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1787_mod_4096 {n : ℕ} (hn : n % 4096 = 1787) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1787 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1787) = 6144 * k + 2681 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2681) = 9216 * k + 4022 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 4022) = 4608 * k + 2011 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 2011) = 6912 * k + 3017 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 3017) = 10368 * k + 4526 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 4526) = 5184 * k + 2263 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 2263) = 7776 * k + 3395 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 3395) = 11664 * k + 5093 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 5093) = 17496 * k + 7640 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 7640) = 8748 * k + 3820 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3820) = 4374 * k + 1910 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1910) = 2187 * k + 955 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1787) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1787)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1823_mod_4096 {n : ℕ} (hn : n % 4096 = 1823) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1823 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1823) = 6144 * k + 2735 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2735) = 9216 * k + 4103 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 4103) = 13824 * k + 6155 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 6155) = 20736 * k + 9233 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 9233) = 31104 * k + 13850 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 13850) = 15552 * k + 6925 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 6925) = 23328 * k + 10388 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 10388) = 11664 * k + 5194 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 5194) = 5832 * k + 2597 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 2597) = 8748 * k + 3896 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3896) = 4374 * k + 1948 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1948) = 2187 * k + 974 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1823) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1823)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_1855_mod_4096 {n : ℕ} (hn : n % 4096 = 1855) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 1855 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 1855) = 6144 * k + 2783 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 2783) = 9216 * k + 4175 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 4175) = 13824 * k + 6263 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 6263) = 20736 * k + 9395 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 9395) = 31104 * k + 14093 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 14093) = 46656 * k + 21140 := by unfold T; split <;> omega
  have h7 : T (46656 * k + 21140) = 23328 * k + 10570 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 10570) = 11664 * k + 5285 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 5285) = 17496 * k + 7928 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 7928) = 8748 * k + 3964 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 3964) = 4374 * k + 1982 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 1982) = 2187 * k + 991 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 1855) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 1855)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2031_mod_4096 {n : ℕ} (hn : n % 4096 = 2031) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2031 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2031) = 6144 * k + 3047 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3047) = 9216 * k + 4571 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 4571) = 13824 * k + 6857 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 6857) = 20736 * k + 10286 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 10286) = 10368 * k + 5143 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 5143) = 15552 * k + 7715 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 7715) = 23328 * k + 11573 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 11573) = 34992 * k + 17360 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 17360) = 17496 * k + 8680 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 8680) = 8748 * k + 4340 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 4340) = 4374 * k + 2170 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2170) = 2187 * k + 1085 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2031) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2031)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2203_mod_4096 {n : ℕ} (hn : n % 4096 = 2203) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2203 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2203) = 6144 * k + 3305 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3305) = 9216 * k + 4958 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 4958) = 4608 * k + 2479 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 2479) = 6912 * k + 3719 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 3719) = 10368 * k + 5579 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 5579) = 15552 * k + 8369 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 8369) = 23328 * k + 12554 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 12554) = 11664 * k + 6277 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 6277) = 17496 * k + 9416 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 9416) = 8748 * k + 4708 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 4708) = 4374 * k + 2354 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2354) = 2187 * k + 1177 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2203) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2203)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2239_mod_4096 {n : ℕ} (hn : n % 4096 = 2239) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2239 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2239) = 6144 * k + 3359 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3359) = 9216 * k + 5039 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 5039) = 13824 * k + 7559 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 7559) = 20736 * k + 11339 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 11339) = 31104 * k + 17009 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 17009) = 46656 * k + 25514 := by unfold T; split <;> omega
  have h7 : T (46656 * k + 25514) = 23328 * k + 12757 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 12757) = 34992 * k + 19136 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 19136) = 17496 * k + 9568 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 9568) = 8748 * k + 4784 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 4784) = 4374 * k + 2392 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2392) = 2187 * k + 1196 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2239) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2239)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2351_mod_4096 {n : ℕ} (hn : n % 4096 = 2351) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2351 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2351) = 6144 * k + 3527 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3527) = 9216 * k + 5291 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 5291) = 13824 * k + 7937 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 7937) = 20736 * k + 11906 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 11906) = 10368 * k + 5953 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 5953) = 15552 * k + 8930 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 8930) = 7776 * k + 4465 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 4465) = 11664 * k + 6698 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 6698) = 5832 * k + 3349 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 3349) = 8748 * k + 5024 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 5024) = 4374 * k + 2512 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2512) = 2187 * k + 1256 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2351) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2351)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2587_mod_4096 {n : ℕ} (hn : n % 4096 = 2587) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2587 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2587) = 6144 * k + 3881 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3881) = 9216 * k + 5822 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 5822) = 4608 * k + 2911 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 2911) = 6912 * k + 4367 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 4367) = 10368 * k + 6551 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 6551) = 15552 * k + 9827 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 9827) = 23328 * k + 14741 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 14741) = 34992 * k + 22112 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 22112) = 17496 * k + 11056 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 11056) = 8748 * k + 5528 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 5528) = 4374 * k + 2764 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2764) = 2187 * k + 1382 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2587) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2587)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2591_mod_4096 {n : ℕ} (hn : n % 4096 = 2591) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2591 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2591) = 6144 * k + 3887 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 3887) = 9216 * k + 5831 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 5831) = 13824 * k + 8747 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 8747) = 20736 * k + 13121 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 13121) = 31104 * k + 19682 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 19682) = 15552 * k + 9841 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 9841) = 23328 * k + 14762 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 14762) = 11664 * k + 7381 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 7381) = 17496 * k + 11072 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 11072) = 8748 * k + 5536 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 5536) = 4374 * k + 2768 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 2768) = 2187 * k + 1384 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2591) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2591)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2907_mod_4096 {n : ℕ} (hn : n % 4096 = 2907) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2907 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2907) = 6144 * k + 4361 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 4361) = 9216 * k + 6542 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 6542) = 4608 * k + 3271 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 3271) = 6912 * k + 4907 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 4907) = 10368 * k + 7361 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 7361) = 15552 * k + 11042 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 11042) = 7776 * k + 5521 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 5521) = 11664 * k + 8282 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 8282) = 5832 * k + 4141 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 4141) = 8748 * k + 6212 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 6212) = 4374 * k + 3106 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3106) = 2187 * k + 1553 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2907) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2907)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_2975_mod_4096 {n : ℕ} (hn : n % 4096 = 2975) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 2975 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 2975) = 6144 * k + 4463 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 4463) = 9216 * k + 6695 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 6695) = 13824 * k + 10043 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 10043) = 20736 * k + 15065 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 15065) = 31104 * k + 22598 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 22598) = 15552 * k + 11299 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 11299) = 23328 * k + 16949 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 16949) = 34992 * k + 25424 := by unfold T; split <;> omega
  have h9 : T (34992 * k + 25424) = 17496 * k + 12712 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 12712) = 8748 * k + 6356 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 6356) = 4374 * k + 3178 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3178) = 2187 * k + 1589 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 2975) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 2975)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3119_mod_4096 {n : ℕ} (hn : n % 4096 = 3119) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3119 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3119) = 6144 * k + 4679 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 4679) = 9216 * k + 7019 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 7019) = 13824 * k + 10529 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 10529) = 20736 * k + 15794 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 15794) = 10368 * k + 7897 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 7897) = 15552 * k + 11846 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 11846) = 7776 * k + 5923 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 5923) = 11664 * k + 8885 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 8885) = 17496 * k + 13328 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 13328) = 8748 * k + 6664 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 6664) = 4374 * k + 3332 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3332) = 2187 * k + 1666 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3119) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3119)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3143_mod_4096 {n : ℕ} (hn : n % 4096 = 3143) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3143 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3143) = 6144 * k + 4715 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 4715) = 9216 * k + 7073 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 7073) = 13824 * k + 10610 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 10610) = 6912 * k + 5305 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 5305) = 10368 * k + 7958 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 7958) = 5184 * k + 3979 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 3979) = 7776 * k + 5969 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 5969) = 11664 * k + 8954 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 8954) = 5832 * k + 4477 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 4477) = 8748 * k + 6716 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 6716) = 4374 * k + 3358 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3358) = 2187 * k + 1679 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3143) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3143)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3295_mod_4096 {n : ℕ} (hn : n % 4096 = 3295) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3295 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3295) = 6144 * k + 4943 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 4943) = 9216 * k + 7415 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 7415) = 13824 * k + 11123 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 11123) = 20736 * k + 16685 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 16685) = 31104 * k + 25028 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 25028) = 15552 * k + 12514 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 12514) = 7776 * k + 6257 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 6257) = 11664 * k + 9386 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 9386) = 5832 * k + 4693 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 4693) = 8748 * k + 7040 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 7040) = 4374 * k + 3520 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3520) = 2187 * k + 1760 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3295) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3295)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3559_mod_4096 {n : ℕ} (hn : n % 4096 = 3559) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3559 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3559) = 6144 * k + 5339 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 5339) = 9216 * k + 8009 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 8009) = 13824 * k + 12014 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 12014) = 6912 * k + 6007 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 6007) = 10368 * k + 9011 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 9011) = 15552 * k + 13517 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 13517) = 23328 * k + 20276 := by unfold T; split <;> omega
  have h8 : T (23328 * k + 20276) = 11664 * k + 10138 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 10138) = 5832 * k + 5069 := by unfold T; split <;> omega
  have h10 : T (5832 * k + 5069) = 8748 * k + 7604 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 7604) = 4374 * k + 3802 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3802) = 2187 * k + 1901 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3559) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3559)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3675_mod_4096 {n : ℕ} (hn : n % 4096 = 3675) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3675 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3675) = 6144 * k + 5513 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 5513) = 9216 * k + 8270 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 8270) = 4608 * k + 4135 := by unfold T; split <;> omega
  have h4 : T (4608 * k + 4135) = 6912 * k + 6203 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 6203) = 10368 * k + 9305 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 9305) = 15552 * k + 13958 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 13958) = 7776 * k + 6979 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 6979) = 11664 * k + 10469 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 10469) = 17496 * k + 15704 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 15704) = 8748 * k + 7852 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 7852) = 4374 * k + 3926 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 3926) = 2187 * k + 1963 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3675) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3675)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_3911_mod_4096 {n : ℕ} (hn : n % 4096 = 3911) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 3911 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 3911) = 6144 * k + 5867 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 5867) = 9216 * k + 8801 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 8801) = 13824 * k + 13202 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 13202) = 6912 * k + 6601 := by unfold T; split <;> omega
  have h5 : T (6912 * k + 6601) = 10368 * k + 9902 := by unfold T; split <;> omega
  have h6 : T (10368 * k + 9902) = 5184 * k + 4951 := by unfold T; split <;> omega
  have h7 : T (5184 * k + 4951) = 7776 * k + 7427 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 7427) = 11664 * k + 11141 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 11141) = 17496 * k + 16712 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 16712) = 8748 * k + 8356 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 8356) = 4374 * k + 4178 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 4178) = 2187 * k + 2089 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 3911) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 3911)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_4063_mod_4096 {n : ℕ} (hn : n % 4096 = 4063) : T_iter n 12 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4096 * k + 4063 := ⟨n / 4096, by omega⟩
  have h1 : T (4096 * k + 4063) = 6144 * k + 6095 := by unfold T; split <;> omega
  have h2 : T (6144 * k + 6095) = 9216 * k + 9143 := by unfold T; split <;> omega
  have h3 : T (9216 * k + 9143) = 13824 * k + 13715 := by unfold T; split <;> omega
  have h4 : T (13824 * k + 13715) = 20736 * k + 20573 := by unfold T; split <;> omega
  have h5 : T (20736 * k + 20573) = 31104 * k + 30860 := by unfold T; split <;> omega
  have h6 : T (31104 * k + 30860) = 15552 * k + 15430 := by unfold T; split <;> omega
  have h7 : T (15552 * k + 15430) = 7776 * k + 7715 := by unfold T; split <;> omega
  have h8 : T (7776 * k + 7715) = 11664 * k + 11573 := by unfold T; split <;> omega
  have h9 : T (11664 * k + 11573) = 17496 * k + 17360 := by unfold T; split <;> omega
  have h10 : T (17496 * k + 17360) = 8748 * k + 8680 := by unfold T; split <;> omega
  have h11 : T (8748 * k + 8680) = 4374 * k + 4340 := by unfold T; split <;> omega
  have h12 : T (4374 * k + 4340) = 2187 * k + 2170 := by unfold T; split <;> omega
  have e : T_iter (4096 * k + 4063) 12 =
      T (T (T (T (T (T (T (T (T (T (T (T (4096 * k + 4063)))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; omega

theorem descent_within_twelve {n : ℕ}
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
           ∨ n % 4096 = 231
           ∨ n % 4096 = 383
           ∨ n % 4096 = 463
           ∨ n % 4096 = 615
           ∨ n % 4096 = 879
           ∨ n % 4096 = 935
           ∨ n % 4096 = 1019
           ∨ n % 4096 = 1087
           ∨ n % 4096 = 1231
           ∨ n % 4096 = 1435
           ∨ n % 4096 = 1647
           ∨ n % 4096 = 1703
           ∨ n % 4096 = 1787
           ∨ n % 4096 = 1823
           ∨ n % 4096 = 1855
           ∨ n % 4096 = 2031
           ∨ n % 4096 = 2203
           ∨ n % 4096 = 2239
           ∨ n % 4096 = 2351
           ∨ n % 4096 = 2587
           ∨ n % 4096 = 2591
           ∨ n % 4096 = 2907
           ∨ n % 4096 = 2975
           ∨ n % 4096 = 3119
           ∨ n % 4096 = 3143
           ∨ n % 4096 = 3295
           ∨ n % 4096 = 3559
           ∨ n % 4096 = 3675
           ∨ n % 4096 = 3911
           ∨ n % 4096 = 4063
        ) :
    ∃ k, 1 ≤ k ∧ k ≤ 12 ∧ T_iter n k < n := by
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · obtain ⟨k, hk, _, hd⟩ :=
        CollatzResidueDescent1024.descent_within_ten (by tauto)
    exact ⟨k, hk, by omega, hd⟩
  · exact ⟨12, by norm_num, by norm_num, descent_231_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_383_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_463_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_615_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_879_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_935_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1019_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1087_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1231_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1435_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1647_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1703_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1787_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1823_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_1855_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2031_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2203_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2239_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2351_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2587_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2591_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2907_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_2975_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3119_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3143_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3295_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3559_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3675_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_3911_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num, descent_4063_mod_4096 (by assumption)⟩

end CollatzResidueDescent4096
