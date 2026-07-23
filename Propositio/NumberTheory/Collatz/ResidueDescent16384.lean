import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ResidueDescent4096
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent16384

open TerrasDensity

theorem descent_191_mod_16384 {n : ℕ} (hn : n % 16384 = 191) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 191 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 191) = 24576 * k + 287 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 287) = 36864 * k + 431 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 431) = 55296 * k + 647 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 647) = 82944 * k + 971 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 971) = 124416 * k + 1457 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 1457) = 186624 * k + 2186 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 2186) = 93312 * k + 1093 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 1093) = 139968 * k + 1640 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 1640) = 69984 * k + 820 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 820) = 34992 * k + 410 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 410) = 17496 * k + 205 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 205) = 26244 * k + 308 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 308) = 13122 * k + 154 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 154) = 6561 * k + 77 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 191) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 191)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_303_mod_16384 {n : ℕ} (hn : n % 16384 = 303) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 303 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 303) = 24576 * k + 455 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 455) = 36864 * k + 683 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 683) = 55296 * k + 1025 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 1025) = 82944 * k + 1538 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 1538) = 41472 * k + 769 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 769) = 62208 * k + 1154 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 1154) = 31104 * k + 577 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 577) = 46656 * k + 866 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 866) = 23328 * k + 433 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 433) = 34992 * k + 650 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 650) = 17496 * k + 325 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 325) = 26244 * k + 488 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 488) = 13122 * k + 244 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 244) = 6561 * k + 122 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 303) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 303)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_543_mod_16384 {n : ℕ} (hn : n % 16384 = 543) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 543 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 543) = 24576 * k + 815 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 815) = 36864 * k + 1223 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 1223) = 55296 * k + 1835 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 1835) = 82944 * k + 2753 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 2753) = 124416 * k + 4130 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 4130) = 62208 * k + 2065 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 2065) = 93312 * k + 3098 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 3098) = 46656 * k + 1549 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 1549) = 69984 * k + 2324 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 2324) = 34992 * k + 1162 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 1162) = 17496 * k + 581 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 581) = 26244 * k + 872 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 872) = 13122 * k + 436 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 436) = 6561 * k + 218 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 543) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 543)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_623_mod_16384 {n : ℕ} (hn : n % 16384 = 623) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 623 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 623) = 24576 * k + 935 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 935) = 36864 * k + 1403 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 1403) = 55296 * k + 2105 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 2105) = 82944 * k + 3158 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 3158) = 41472 * k + 1579 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 1579) = 62208 * k + 2369 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 2369) = 93312 * k + 3554 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 3554) = 46656 * k + 1777 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 1777) = 69984 * k + 2666 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 2666) = 34992 * k + 1333 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 1333) = 52488 * k + 2000 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 2000) = 26244 * k + 1000 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 1000) = 13122 * k + 500 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 500) = 6561 * k + 250 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 623) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 623)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1135_mod_16384 {n : ℕ} (hn : n % 16384 = 1135) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1135 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1135) = 24576 * k + 1703 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 1703) = 36864 * k + 2555 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 2555) = 55296 * k + 3833 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 3833) = 82944 * k + 5750 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 5750) = 41472 * k + 2875 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 2875) = 62208 * k + 4313 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 4313) = 93312 * k + 6470 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 6470) = 46656 * k + 3235 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 3235) = 69984 * k + 4853 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 4853) = 104976 * k + 7280 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 7280) = 52488 * k + 3640 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 3640) = 26244 * k + 1820 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 1820) = 13122 * k + 910 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 910) = 6561 * k + 455 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1135) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1135)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1215_mod_16384 {n : ℕ} (hn : n % 16384 = 1215) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1215 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1215) = 24576 * k + 1823 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 1823) = 36864 * k + 2735 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 2735) = 55296 * k + 4103 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 4103) = 82944 * k + 6155 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 6155) = 124416 * k + 9233 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 9233) = 186624 * k + 13850 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 13850) = 93312 * k + 6925 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 6925) = 139968 * k + 10388 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 10388) = 69984 * k + 5194 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 5194) = 34992 * k + 2597 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 2597) = 52488 * k + 3896 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 3896) = 26244 * k + 1948 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 1948) = 13122 * k + 974 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 974) = 6561 * k + 487 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1215) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1215)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1247_mod_16384 {n : ℕ} (hn : n % 16384 = 1247) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1247 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1247) = 24576 * k + 1871 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 1871) = 36864 * k + 2807 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 2807) = 55296 * k + 4211 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 4211) = 82944 * k + 6317 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 6317) = 124416 * k + 9476 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 9476) = 62208 * k + 4738 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 4738) = 31104 * k + 2369 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 2369) = 46656 * k + 3554 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 3554) = 23328 * k + 1777 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 1777) = 34992 * k + 2666 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 2666) = 17496 * k + 1333 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 1333) = 26244 * k + 2000 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 2000) = 13122 * k + 1000 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1000) = 6561 * k + 500 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1247) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1247)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1327_mod_16384 {n : ℕ} (hn : n % 16384 = 1327) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1327 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1327) = 24576 * k + 1991 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 1991) = 36864 * k + 2987 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 2987) = 55296 * k + 4481 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 4481) = 82944 * k + 6722 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 6722) = 41472 * k + 3361 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 3361) = 62208 * k + 5042 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 5042) = 31104 * k + 2521 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 2521) = 46656 * k + 3782 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 3782) = 23328 * k + 1891 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 1891) = 34992 * k + 2837 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 2837) = 52488 * k + 4256 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 4256) = 26244 * k + 2128 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 2128) = 13122 * k + 1064 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1064) = 6561 * k + 532 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1327) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1327)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1567_mod_16384 {n : ℕ} (hn : n % 16384 = 1567) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1567 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1567) = 24576 * k + 2351 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 2351) = 36864 * k + 3527 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 3527) = 55296 * k + 5291 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 5291) = 82944 * k + 7937 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 7937) = 124416 * k + 11906 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 11906) = 62208 * k + 5953 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 5953) = 93312 * k + 8930 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 8930) = 46656 * k + 4465 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 4465) = 69984 * k + 6698 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 6698) = 34992 * k + 3349 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 3349) = 52488 * k + 5024 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 5024) = 26244 * k + 2512 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 2512) = 13122 * k + 1256 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1256) = 6561 * k + 628 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1567) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1567)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_1727_mod_16384 {n : ℕ} (hn : n % 16384 = 1727) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 1727 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 1727) = 24576 * k + 2591 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 2591) = 36864 * k + 3887 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 3887) = 55296 * k + 5831 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 5831) = 82944 * k + 8747 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 8747) = 124416 * k + 13121 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 13121) = 186624 * k + 19682 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 19682) = 93312 * k + 9841 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 9841) = 139968 * k + 14762 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 14762) = 69984 * k + 7381 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 7381) = 104976 * k + 11072 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 11072) = 52488 * k + 5536 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 5536) = 26244 * k + 2768 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 2768) = 13122 * k + 1384 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1384) = 6561 * k + 692 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 1727) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 1727)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_2079_mod_16384 {n : ℕ} (hn : n % 16384 = 2079) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 2079 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 2079) = 24576 * k + 3119 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 3119) = 36864 * k + 4679 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 4679) = 55296 * k + 7019 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 7019) = 82944 * k + 10529 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 10529) = 124416 * k + 15794 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 15794) = 62208 * k + 7897 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 7897) = 93312 * k + 11846 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 11846) = 46656 * k + 5923 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 5923) = 69984 * k + 8885 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 8885) = 104976 * k + 13328 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 13328) = 52488 * k + 6664 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 6664) = 26244 * k + 3332 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 3332) = 13122 * k + 1666 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1666) = 6561 * k + 833 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 2079) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 2079)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_2271_mod_16384 {n : ℕ} (hn : n % 16384 = 2271) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 2271 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 2271) = 24576 * k + 3407 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 3407) = 36864 * k + 5111 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 5111) = 55296 * k + 7667 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 7667) = 82944 * k + 11501 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 11501) = 124416 * k + 17252 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 17252) = 62208 * k + 8626 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 8626) = 31104 * k + 4313 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 4313) = 46656 * k + 6470 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 6470) = 23328 * k + 3235 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 3235) = 34992 * k + 4853 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 4853) = 52488 * k + 7280 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 7280) = 26244 * k + 3640 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 3640) = 13122 * k + 1820 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1820) = 6561 * k + 910 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 2271) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 2271)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_2331_mod_16384 {n : ℕ} (hn : n % 16384 = 2331) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 2331 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 2331) = 24576 * k + 3497 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 3497) = 36864 * k + 5246 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 5246) = 18432 * k + 2623 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 2623) = 27648 * k + 3935 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 3935) = 41472 * k + 5903 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 5903) = 62208 * k + 8855 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 8855) = 93312 * k + 13283 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 13283) = 139968 * k + 19925 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 19925) = 209952 * k + 29888 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 29888) = 104976 * k + 14944 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 14944) = 52488 * k + 7472 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 7472) = 26244 * k + 3736 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 3736) = 13122 * k + 1868 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1868) = 6561 * k + 934 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 2331) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 2331)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_2431_mod_16384 {n : ℕ} (hn : n % 16384 = 2431) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 2431 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 2431) = 24576 * k + 3647 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 3647) = 36864 * k + 5471 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 5471) = 55296 * k + 8207 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 8207) = 82944 * k + 12311 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 12311) = 124416 * k + 18467 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 18467) = 186624 * k + 27701 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 27701) = 279936 * k + 41552 := by unfold T; split <;> omega
  have h8 : T (279936 * k + 41552) = 139968 * k + 20776 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 20776) = 69984 * k + 10388 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 10388) = 34992 * k + 5194 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 5194) = 17496 * k + 2597 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 2597) = 26244 * k + 3896 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 3896) = 13122 * k + 1948 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 1948) = 6561 * k + 974 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 2431) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 2431)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_2663_mod_16384 {n : ℕ} (hn : n % 16384 = 2663) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 2663 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 2663) = 24576 * k + 3995 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 3995) = 36864 * k + 5993 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 5993) = 55296 * k + 8990 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 8990) = 27648 * k + 4495 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 4495) = 41472 * k + 6743 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 6743) = 62208 * k + 10115 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 10115) = 93312 * k + 15173 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 15173) = 139968 * k + 22760 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 22760) = 69984 * k + 11380 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 11380) = 34992 * k + 5690 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 5690) = 17496 * k + 2845 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 2845) = 26244 * k + 4268 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 4268) = 13122 * k + 2134 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 2134) = 6561 * k + 1067 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 2663) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 2663)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_3067_mod_16384 {n : ℕ} (hn : n % 16384 = 3067) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 3067 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 3067) = 24576 * k + 4601 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 4601) = 36864 * k + 6902 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 6902) = 18432 * k + 3451 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 3451) = 27648 * k + 5177 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 5177) = 41472 * k + 7766 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 7766) = 20736 * k + 3883 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 3883) = 31104 * k + 5825 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 5825) = 46656 * k + 8738 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 8738) = 23328 * k + 4369 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 4369) = 34992 * k + 6554 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 6554) = 17496 * k + 3277 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 3277) = 26244 * k + 4916 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 4916) = 13122 * k + 2458 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 2458) = 6561 * k + 1229 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 3067) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 3067)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_3135_mod_16384 {n : ℕ} (hn : n % 16384 = 3135) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 3135 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 3135) = 24576 * k + 4703 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 4703) = 36864 * k + 7055 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 7055) = 55296 * k + 10583 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 10583) = 82944 * k + 15875 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 15875) = 124416 * k + 23813 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 23813) = 186624 * k + 35720 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 35720) = 93312 * k + 17860 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 17860) = 46656 * k + 8930 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 8930) = 23328 * k + 4465 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 4465) = 34992 * k + 6698 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 6698) = 17496 * k + 3349 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 3349) = 26244 * k + 5024 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 5024) = 13122 * k + 2512 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 2512) = 6561 * k + 1256 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 3135) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 3135)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_3455_mod_16384 {n : ℕ} (hn : n % 16384 = 3455) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 3455 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 3455) = 24576 * k + 5183 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 5183) = 36864 * k + 7775 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 7775) = 55296 * k + 11663 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 11663) = 82944 * k + 17495 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 17495) = 124416 * k + 26243 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 26243) = 186624 * k + 39365 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 39365) = 279936 * k + 59048 := by unfold T; split <;> omega
  have h8 : T (279936 * k + 59048) = 139968 * k + 29524 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 29524) = 69984 * k + 14762 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 14762) = 34992 * k + 7381 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 7381) = 52488 * k + 11072 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 11072) = 26244 * k + 5536 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 5536) = 13122 * k + 2768 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 2768) = 6561 * k + 1384 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 3455) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 3455)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_3687_mod_16384 {n : ℕ} (hn : n % 16384 = 3687) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 3687 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 3687) = 24576 * k + 5531 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 5531) = 36864 * k + 8297 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 8297) = 55296 * k + 12446 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 12446) = 27648 * k + 6223 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 6223) = 41472 * k + 9335 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 9335) = 62208 * k + 14003 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 14003) = 93312 * k + 21005 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 21005) = 139968 * k + 31508 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 31508) = 69984 * k + 15754 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 15754) = 34992 * k + 7877 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 7877) = 52488 * k + 11816 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 11816) = 26244 * k + 5908 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 5908) = 13122 * k + 2954 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 2954) = 6561 * k + 1477 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 3687) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 3687)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_3967_mod_16384 {n : ℕ} (hn : n % 16384 = 3967) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 3967 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 3967) = 24576 * k + 5951 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 5951) = 36864 * k + 8927 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 8927) = 55296 * k + 13391 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 13391) = 82944 * k + 20087 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 20087) = 124416 * k + 30131 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 30131) = 186624 * k + 45197 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 45197) = 279936 * k + 67796 := by unfold T; split <;> omega
  have h8 : T (279936 * k + 67796) = 139968 * k + 33898 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 33898) = 69984 * k + 16949 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 16949) = 104976 * k + 25424 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 25424) = 52488 * k + 12712 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 12712) = 26244 * k + 6356 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6356) = 13122 * k + 3178 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3178) = 6561 * k + 1589 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 3967) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 3967)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4079_mod_16384 {n : ℕ} (hn : n % 16384 = 4079) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4079 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4079) = 24576 * k + 6119 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 6119) = 36864 * k + 9179 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 9179) = 55296 * k + 13769 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 13769) = 82944 * k + 20654 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 20654) = 41472 * k + 10327 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 10327) = 62208 * k + 15491 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 15491) = 93312 * k + 23237 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 23237) = 139968 * k + 34856 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 34856) = 69984 * k + 17428 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 17428) = 34992 * k + 8714 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 8714) = 17496 * k + 4357 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 4357) = 26244 * k + 6536 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6536) = 13122 * k + 3268 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3268) = 6561 * k + 1634 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4079) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4079)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4091_mod_16384 {n : ℕ} (hn : n % 16384 = 4091) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4091 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4091) = 24576 * k + 6137 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 6137) = 36864 * k + 9206 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 9206) = 18432 * k + 4603 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 4603) = 27648 * k + 6905 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 6905) = 41472 * k + 10358 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 10358) = 20736 * k + 5179 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 5179) = 31104 * k + 7769 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 7769) = 46656 * k + 11654 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 11654) = 23328 * k + 5827 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 5827) = 34992 * k + 8741 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 8741) = 52488 * k + 13112 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 13112) = 26244 * k + 6556 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6556) = 13122 * k + 3278 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3278) = 6561 * k + 1639 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4091) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4091)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4159_mod_16384 {n : ℕ} (hn : n % 16384 = 4159) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4159 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4159) = 24576 * k + 6239 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 6239) = 36864 * k + 9359 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 9359) = 55296 * k + 14039 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 14039) = 82944 * k + 21059 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 21059) = 124416 * k + 31589 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 31589) = 186624 * k + 47384 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 47384) = 93312 * k + 23692 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 23692) = 46656 * k + 11846 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 11846) = 23328 * k + 5923 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 5923) = 34992 * k + 8885 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 8885) = 52488 * k + 13328 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 13328) = 26244 * k + 6664 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6664) = 13122 * k + 3332 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3332) = 6561 * k + 1666 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4159) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4159)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4199_mod_16384 {n : ℕ} (hn : n % 16384 = 4199) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4199 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4199) = 24576 * k + 6299 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 6299) = 36864 * k + 9449 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 9449) = 55296 * k + 14174 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 14174) = 27648 * k + 7087 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 7087) = 41472 * k + 10631 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 10631) = 62208 * k + 15947 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 15947) = 93312 * k + 23921 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 23921) = 139968 * k + 35882 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 35882) = 69984 * k + 17941 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 17941) = 104976 * k + 26912 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 26912) = 52488 * k + 13456 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 13456) = 26244 * k + 6728 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6728) = 13122 * k + 3364 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3364) = 6561 * k + 1682 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4199) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4199)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4251_mod_16384 {n : ℕ} (hn : n % 16384 = 4251) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4251 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4251) = 24576 * k + 6377 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 6377) = 36864 * k + 9566 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 9566) = 18432 * k + 4783 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 4783) = 27648 * k + 7175 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 7175) = 41472 * k + 10763 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 10763) = 62208 * k + 16145 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 16145) = 93312 * k + 24218 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 24218) = 46656 * k + 12109 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 12109) = 69984 * k + 18164 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 18164) = 34992 * k + 9082 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 9082) = 17496 * k + 4541 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 4541) = 26244 * k + 6812 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 6812) = 13122 * k + 3406 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3406) = 6561 * k + 1703 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4251) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4251)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_4955_mod_16384 {n : ℕ} (hn : n % 16384 = 4955) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 4955 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 4955) = 24576 * k + 7433 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 7433) = 36864 * k + 11150 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 11150) = 18432 * k + 5575 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 5575) = 27648 * k + 8363 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 8363) = 41472 * k + 12545 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 12545) = 62208 * k + 18818 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 18818) = 31104 * k + 9409 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 9409) = 46656 * k + 14114 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 14114) = 23328 * k + 7057 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 7057) = 34992 * k + 10586 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 10586) = 17496 * k + 5293 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 5293) = 26244 * k + 7940 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 7940) = 13122 * k + 3970 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 3970) = 6561 * k + 1985 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 4955) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 4955)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5023_mod_16384 {n : ℕ} (hn : n % 16384 = 5023) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5023 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5023) = 24576 * k + 7535 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 7535) = 36864 * k + 11303 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 11303) = 55296 * k + 16955 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 16955) = 82944 * k + 25433 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 25433) = 124416 * k + 38150 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 38150) = 62208 * k + 19075 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 19075) = 93312 * k + 28613 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 28613) = 139968 * k + 42920 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 42920) = 69984 * k + 21460 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 21460) = 34992 * k + 10730 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 10730) = 17496 * k + 5365 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 5365) = 26244 * k + 8048 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 8048) = 13122 * k + 4024 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4024) = 6561 * k + 2012 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5023) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5023)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5103_mod_16384 {n : ℕ} (hn : n % 16384 = 5103) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5103 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5103) = 24576 * k + 7655 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 7655) = 36864 * k + 11483 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 11483) = 55296 * k + 17225 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 17225) = 82944 * k + 25838 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 25838) = 41472 * k + 12919 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 12919) = 62208 * k + 19379 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 19379) = 93312 * k + 29069 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 29069) = 139968 * k + 43604 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 43604) = 69984 * k + 21802 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 21802) = 34992 * k + 10901 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 10901) = 52488 * k + 16352 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 16352) = 26244 * k + 8176 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 8176) = 13122 * k + 4088 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4088) = 6561 * k + 2044 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5103) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5103)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5275_mod_16384 {n : ℕ} (hn : n % 16384 = 5275) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5275 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5275) = 24576 * k + 7913 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 7913) = 36864 * k + 11870 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 11870) = 18432 * k + 5935 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 5935) = 27648 * k + 8903 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 8903) = 41472 * k + 13355 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 13355) = 62208 * k + 20033 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 20033) = 93312 * k + 30050 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 30050) = 46656 * k + 15025 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 15025) = 69984 * k + 22538 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 22538) = 34992 * k + 11269 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 11269) = 52488 * k + 16904 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 16904) = 26244 * k + 8452 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 8452) = 13122 * k + 4226 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4226) = 6561 * k + 2113 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5275) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5275)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5607_mod_16384 {n : ℕ} (hn : n % 16384 = 5607) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5607 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5607) = 24576 * k + 8411 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 8411) = 36864 * k + 12617 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 12617) = 55296 * k + 18926 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 18926) = 27648 * k + 9463 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 9463) = 41472 * k + 14195 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 14195) = 62208 * k + 21293 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 21293) = 93312 * k + 31940 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 31940) = 46656 * k + 15970 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 15970) = 23328 * k + 7985 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 7985) = 34992 * k + 11978 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 11978) = 17496 * k + 5989 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 5989) = 26244 * k + 8984 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 8984) = 13122 * k + 4492 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4492) = 6561 * k + 2246 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5607) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5607)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5615_mod_16384 {n : ℕ} (hn : n % 16384 = 5615) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5615 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5615) = 24576 * k + 8423 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 8423) = 36864 * k + 12635 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 12635) = 55296 * k + 18953 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 18953) = 82944 * k + 28430 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 28430) = 41472 * k + 14215 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 14215) = 62208 * k + 21323 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 21323) = 93312 * k + 31985 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 31985) = 139968 * k + 47978 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 47978) = 69984 * k + 23989 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 23989) = 104976 * k + 35984 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 35984) = 52488 * k + 17992 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 17992) = 26244 * k + 8996 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 8996) = 13122 * k + 4498 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4498) = 6561 * k + 2249 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5615) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5615)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5787_mod_16384 {n : ℕ} (hn : n % 16384 = 5787) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5787 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5787) = 24576 * k + 8681 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 8681) = 36864 * k + 13022 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 13022) = 18432 * k + 6511 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 6511) = 27648 * k + 9767 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 9767) = 41472 * k + 14651 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 14651) = 62208 * k + 21977 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 21977) = 93312 * k + 32966 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 32966) = 46656 * k + 16483 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 16483) = 69984 * k + 24725 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 24725) = 104976 * k + 37088 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 37088) = 52488 * k + 18544 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 18544) = 26244 * k + 9272 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 9272) = 13122 * k + 4636 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4636) = 6561 * k + 2318 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5787) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5787)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5959_mod_16384 {n : ℕ} (hn : n % 16384 = 5959) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5959 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5959) = 24576 * k + 8939 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 8939) = 36864 * k + 13409 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 13409) = 55296 * k + 20114 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 20114) = 27648 * k + 10057 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 10057) = 41472 * k + 15086 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 15086) = 20736 * k + 7543 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 7543) = 31104 * k + 11315 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 11315) = 46656 * k + 16973 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 16973) = 69984 * k + 25460 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 25460) = 34992 * k + 12730 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 12730) = 17496 * k + 6365 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 6365) = 26244 * k + 9548 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 9548) = 13122 * k + 4774 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4774) = 6561 * k + 2387 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5959) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5959)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_5979_mod_16384 {n : ℕ} (hn : n % 16384 = 5979) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 5979 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 5979) = 24576 * k + 8969 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 8969) = 36864 * k + 13454 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 13454) = 18432 * k + 6727 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 6727) = 27648 * k + 10091 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 10091) = 41472 * k + 15137 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 15137) = 62208 * k + 22706 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 22706) = 31104 * k + 11353 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 11353) = 46656 * k + 17030 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 17030) = 23328 * k + 8515 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 8515) = 34992 * k + 12773 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 12773) = 52488 * k + 19160 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 19160) = 26244 * k + 9580 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 9580) = 13122 * k + 4790 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4790) = 6561 * k + 2395 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 5979) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 5979)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_6047_mod_16384 {n : ℕ} (hn : n % 16384 = 6047) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 6047 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 6047) = 24576 * k + 9071 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 9071) = 36864 * k + 13607 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 13607) = 55296 * k + 20411 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 20411) = 82944 * k + 30617 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 30617) = 124416 * k + 45926 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 45926) = 62208 * k + 22963 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 22963) = 93312 * k + 34445 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 34445) = 139968 * k + 51668 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 51668) = 69984 * k + 25834 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 25834) = 34992 * k + 12917 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 12917) = 52488 * k + 19376 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 19376) = 26244 * k + 9688 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 9688) = 13122 * k + 4844 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 4844) = 6561 * k + 2422 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 6047) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 6047)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_6559_mod_16384 {n : ℕ} (hn : n % 16384 = 6559) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 6559 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 6559) = 24576 * k + 9839 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 9839) = 36864 * k + 14759 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 14759) = 55296 * k + 22139 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 22139) = 82944 * k + 33209 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 33209) = 124416 * k + 49814 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 49814) = 62208 * k + 24907 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 24907) = 93312 * k + 37361 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 37361) = 139968 * k + 56042 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 56042) = 69984 * k + 28021 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 28021) = 104976 * k + 42032 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 42032) = 52488 * k + 21016 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 21016) = 26244 * k + 10508 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 10508) = 13122 * k + 5254 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 5254) = 6561 * k + 2627 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 6559) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 6559)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_6631_mod_16384 {n : ℕ} (hn : n % 16384 = 6631) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 6631 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 6631) = 24576 * k + 9947 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 9947) = 36864 * k + 14921 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 14921) = 55296 * k + 22382 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 22382) = 27648 * k + 11191 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 11191) = 41472 * k + 16787 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 16787) = 62208 * k + 25181 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 25181) = 93312 * k + 37772 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 37772) = 46656 * k + 18886 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 18886) = 23328 * k + 9443 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 9443) = 34992 * k + 14165 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 14165) = 52488 * k + 21248 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 21248) = 26244 * k + 10624 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 10624) = 13122 * k + 5312 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 5312) = 6561 * k + 2656 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 6631) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 6631)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_6983_mod_16384 {n : ℕ} (hn : n % 16384 = 6983) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 6983 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 6983) = 24576 * k + 10475 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 10475) = 36864 * k + 15713 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 15713) = 55296 * k + 23570 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 23570) = 27648 * k + 11785 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 11785) = 41472 * k + 17678 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 17678) = 20736 * k + 8839 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 8839) = 31104 * k + 13259 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 13259) = 46656 * k + 19889 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 19889) = 69984 * k + 29834 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 29834) = 34992 * k + 14917 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 14917) = 52488 * k + 22376 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 22376) = 26244 * k + 11188 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 11188) = 13122 * k + 5594 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 5594) = 6561 * k + 2797 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 6983) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 6983)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_7023_mod_16384 {n : ℕ} (hn : n % 16384 = 7023) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 7023 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 7023) = 24576 * k + 10535 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 10535) = 36864 * k + 15803 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 15803) = 55296 * k + 23705 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 23705) = 82944 * k + 35558 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 35558) = 41472 * k + 17779 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 17779) = 62208 * k + 26669 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 26669) = 93312 * k + 40004 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 40004) = 46656 * k + 20002 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 20002) = 23328 * k + 10001 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 10001) = 34992 * k + 15002 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 15002) = 17496 * k + 7501 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 7501) = 26244 * k + 11252 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 11252) = 13122 * k + 5626 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 5626) = 6561 * k + 2813 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 7023) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 7023)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_7375_mod_16384 {n : ℕ} (hn : n % 16384 = 7375) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 7375 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 7375) = 24576 * k + 11063 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 11063) = 36864 * k + 16595 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 16595) = 55296 * k + 24893 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 24893) = 82944 * k + 37340 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 37340) = 41472 * k + 18670 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 18670) = 20736 * k + 9335 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 9335) = 31104 * k + 14003 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 14003) = 46656 * k + 21005 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 21005) = 69984 * k + 31508 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 31508) = 34992 * k + 15754 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 15754) = 17496 * k + 7877 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 7877) = 26244 * k + 11816 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 11816) = 13122 * k + 5908 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 5908) = 6561 * k + 2954 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 7375) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 7375)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_7495_mod_16384 {n : ℕ} (hn : n % 16384 = 7495) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 7495 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 7495) = 24576 * k + 11243 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 11243) = 36864 * k + 16865 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 16865) = 55296 * k + 25298 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 25298) = 27648 * k + 12649 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 12649) = 41472 * k + 18974 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 18974) = 20736 * k + 9487 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 9487) = 31104 * k + 14231 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 14231) = 46656 * k + 21347 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 21347) = 69984 * k + 32021 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 32021) = 104976 * k + 48032 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 48032) = 52488 * k + 24016 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 24016) = 26244 * k + 12008 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 12008) = 13122 * k + 6004 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6004) = 6561 * k + 3002 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 7495) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 7495)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_7847_mod_16384 {n : ℕ} (hn : n % 16384 = 7847) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 7847 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 7847) = 24576 * k + 11771 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 11771) = 36864 * k + 17657 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 17657) = 55296 * k + 26486 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 26486) = 27648 * k + 13243 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 13243) = 41472 * k + 19865 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 19865) = 62208 * k + 29798 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 29798) = 31104 * k + 14899 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 14899) = 46656 * k + 22349 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 22349) = 69984 * k + 33524 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 33524) = 34992 * k + 16762 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 16762) = 17496 * k + 8381 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 8381) = 26244 * k + 12572 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 12572) = 13122 * k + 6286 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6286) = 6561 * k + 3143 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 7847) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 7847)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_7967_mod_16384 {n : ℕ} (hn : n % 16384 = 7967) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 7967 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 7967) = 24576 * k + 11951 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 11951) = 36864 * k + 17927 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 17927) = 55296 * k + 26891 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 26891) = 82944 * k + 40337 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 40337) = 124416 * k + 60506 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 60506) = 62208 * k + 30253 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 30253) = 93312 * k + 45380 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 45380) = 46656 * k + 22690 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 22690) = 23328 * k + 11345 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 11345) = 34992 * k + 17018 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 17018) = 17496 * k + 8509 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 8509) = 26244 * k + 12764 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 12764) = 13122 * k + 6382 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6382) = 6561 * k + 3191 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 7967) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 7967)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8047_mod_16384 {n : ℕ} (hn : n % 16384 = 8047) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8047 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8047) = 24576 * k + 12071 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 12071) = 36864 * k + 18107 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 18107) = 55296 * k + 27161 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 27161) = 82944 * k + 40742 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 40742) = 41472 * k + 20371 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 20371) = 62208 * k + 30557 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 30557) = 93312 * k + 45836 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 45836) = 46656 * k + 22918 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 22918) = 23328 * k + 11459 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 11459) = 34992 * k + 17189 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 17189) = 52488 * k + 25784 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 25784) = 26244 * k + 12892 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 12892) = 13122 * k + 6446 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6446) = 6561 * k + 3223 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8047) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8047)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8399_mod_16384 {n : ℕ} (hn : n % 16384 = 8399) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8399 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8399) = 24576 * k + 12599 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 12599) = 36864 * k + 18899 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 18899) = 55296 * k + 28349 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 28349) = 82944 * k + 42524 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 42524) = 41472 * k + 21262 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 21262) = 20736 * k + 10631 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 10631) = 31104 * k + 15947 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 15947) = 46656 * k + 23921 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 23921) = 69984 * k + 35882 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 35882) = 34992 * k + 17941 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 17941) = 52488 * k + 26912 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 26912) = 26244 * k + 13456 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 13456) = 13122 * k + 6728 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6728) = 6561 * k + 3364 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8399) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8399)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8447_mod_16384 {n : ℕ} (hn : n % 16384 = 8447) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8447 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8447) = 24576 * k + 12671 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 12671) = 36864 * k + 19007 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 19007) = 55296 * k + 28511 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 28511) = 82944 * k + 42767 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 42767) = 124416 * k + 64151 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 64151) = 186624 * k + 96227 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 96227) = 279936 * k + 144341 := by unfold T; split <;> omega
  have h8 : T (279936 * k + 144341) = 419904 * k + 216512 := by unfold T; split <;> omega
  have h9 : T (419904 * k + 216512) = 209952 * k + 108256 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 108256) = 104976 * k + 54128 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 54128) = 52488 * k + 27064 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 27064) = 26244 * k + 13532 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 13532) = 13122 * k + 6766 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6766) = 6561 * k + 3383 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8447) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8447)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8731_mod_16384 {n : ℕ} (hn : n % 16384 = 8731) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8731 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8731) = 24576 * k + 13097 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 13097) = 36864 * k + 19646 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 19646) = 18432 * k + 9823 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 9823) = 27648 * k + 14735 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 14735) = 41472 * k + 22103 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 22103) = 62208 * k + 33155 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 33155) = 93312 * k + 49733 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 49733) = 139968 * k + 74600 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 74600) = 69984 * k + 37300 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 37300) = 34992 * k + 18650 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 18650) = 17496 * k + 9325 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 9325) = 26244 * k + 13988 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 13988) = 13122 * k + 6994 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 6994) = 6561 * k + 3497 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8731) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8731)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8871_mod_16384 {n : ℕ} (hn : n % 16384 = 8871) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8871 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8871) = 24576 * k + 13307 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 13307) = 36864 * k + 19961 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 19961) = 55296 * k + 29942 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 29942) = 27648 * k + 14971 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 14971) = 41472 * k + 22457 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 22457) = 62208 * k + 33686 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 33686) = 31104 * k + 16843 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 16843) = 46656 * k + 25265 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 25265) = 69984 * k + 37898 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 37898) = 34992 * k + 18949 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 18949) = 52488 * k + 28424 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 28424) = 26244 * k + 14212 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 14212) = 13122 * k + 7106 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7106) = 6561 * k + 3553 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8871) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8871)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8911_mod_16384 {n : ℕ} (hn : n % 16384 = 8911) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8911 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8911) = 24576 * k + 13367 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 13367) = 36864 * k + 20051 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 20051) = 55296 * k + 30077 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 30077) = 82944 * k + 45116 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 45116) = 41472 * k + 22558 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 22558) = 20736 * k + 11279 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 11279) = 31104 * k + 16919 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 16919) = 46656 * k + 25379 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 25379) = 69984 * k + 38069 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 38069) = 104976 * k + 57104 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 57104) = 52488 * k + 28552 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 28552) = 26244 * k + 14276 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 14276) = 13122 * k + 7138 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7138) = 6561 * k + 3569 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8911) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8911)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_8991_mod_16384 {n : ℕ} (hn : n % 16384 = 8991) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 8991 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 8991) = 24576 * k + 13487 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 13487) = 36864 * k + 20231 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 20231) = 55296 * k + 30347 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 30347) = 82944 * k + 45521 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 45521) = 124416 * k + 68282 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 68282) = 62208 * k + 34141 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 34141) = 93312 * k + 51212 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 51212) = 46656 * k + 25606 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 25606) = 23328 * k + 12803 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 12803) = 34992 * k + 19205 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 19205) = 52488 * k + 28808 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 28808) = 26244 * k + 14404 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 14404) = 13122 * k + 7202 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7202) = 6561 * k + 3601 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 8991) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 8991)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_9263_mod_16384 {n : ℕ} (hn : n % 16384 = 9263) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 9263 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 9263) = 24576 * k + 13895 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 13895) = 36864 * k + 20843 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 20843) = 55296 * k + 31265 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 31265) = 82944 * k + 46898 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 46898) = 41472 * k + 23449 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 23449) = 62208 * k + 35174 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 35174) = 31104 * k + 17587 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 17587) = 46656 * k + 26381 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 26381) = 69984 * k + 39572 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 39572) = 34992 * k + 19786 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 19786) = 17496 * k + 9893 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 9893) = 26244 * k + 14840 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 14840) = 13122 * k + 7420 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7420) = 6561 * k + 3710 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 9263) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 9263)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_9383_mod_16384 {n : ℕ} (hn : n % 16384 = 9383) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 9383 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 9383) = 24576 * k + 14075 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 14075) = 36864 * k + 21113 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 21113) = 55296 * k + 31670 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 31670) = 27648 * k + 15835 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 15835) = 41472 * k + 23753 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 23753) = 62208 * k + 35630 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 35630) = 31104 * k + 17815 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 17815) = 46656 * k + 26723 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 26723) = 69984 * k + 40085 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 40085) = 104976 * k + 60128 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 60128) = 52488 * k + 30064 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 30064) = 26244 * k + 15032 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 15032) = 13122 * k + 7516 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7516) = 6561 * k + 3758 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 9383) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 9383)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_9755_mod_16384 {n : ℕ} (hn : n % 16384 = 9755) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 9755 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 9755) = 24576 * k + 14633 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 14633) = 36864 * k + 21950 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 21950) = 18432 * k + 10975 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 10975) = 27648 * k + 16463 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 16463) = 41472 * k + 24695 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 24695) = 62208 * k + 37043 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 37043) = 93312 * k + 55565 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 55565) = 139968 * k + 83348 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 83348) = 69984 * k + 41674 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 41674) = 34992 * k + 20837 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 20837) = 52488 * k + 31256 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 31256) = 26244 * k + 15628 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 15628) = 13122 * k + 7814 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 7814) = 6561 * k + 3907 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 9755) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 9755)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_10175_mod_16384 {n : ℕ} (hn : n % 16384 = 10175) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 10175 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 10175) = 24576 * k + 15263 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 15263) = 36864 * k + 22895 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 22895) = 55296 * k + 34343 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 34343) = 82944 * k + 51515 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 51515) = 124416 * k + 77273 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 77273) = 186624 * k + 115910 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 115910) = 93312 * k + 57955 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 57955) = 139968 * k + 86933 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 86933) = 209952 * k + 130400 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 130400) = 104976 * k + 65200 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 65200) = 52488 * k + 32600 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 32600) = 26244 * k + 16300 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 16300) = 13122 * k + 8150 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8150) = 6561 * k + 4075 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 10175) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 10175)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_10207_mod_16384 {n : ℕ} (hn : n % 16384 = 10207) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 10207 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 10207) = 24576 * k + 15311 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 15311) = 36864 * k + 22967 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 22967) = 55296 * k + 34451 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 34451) = 82944 * k + 51677 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 51677) = 124416 * k + 77516 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 77516) = 62208 * k + 38758 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 38758) = 31104 * k + 19379 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 19379) = 46656 * k + 29069 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 29069) = 69984 * k + 43604 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 43604) = 34992 * k + 21802 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 21802) = 17496 * k + 10901 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 10901) = 26244 * k + 16352 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 16352) = 13122 * k + 8176 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8176) = 6561 * k + 4088 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 10207) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 10207)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_10267_mod_16384 {n : ℕ} (hn : n % 16384 = 10267) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 10267 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 10267) = 24576 * k + 15401 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 15401) = 36864 * k + 23102 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 23102) = 18432 * k + 11551 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 11551) = 27648 * k + 17327 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 17327) = 41472 * k + 25991 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 25991) = 62208 * k + 38987 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 38987) = 93312 * k + 58481 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 58481) = 139968 * k + 87722 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 87722) = 69984 * k + 43861 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 43861) = 104976 * k + 65792 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 65792) = 52488 * k + 32896 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 32896) = 26244 * k + 16448 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 16448) = 13122 * k + 8224 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8224) = 6561 * k + 4112 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 10267) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 10267)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_10287_mod_16384 {n : ℕ} (hn : n % 16384 = 10287) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 10287 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 10287) = 24576 * k + 15431 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 15431) = 36864 * k + 23147 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 23147) = 55296 * k + 34721 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 34721) = 82944 * k + 52082 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 52082) = 41472 * k + 26041 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 26041) = 62208 * k + 39062 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 39062) = 31104 * k + 19531 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 19531) = 46656 * k + 29297 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 29297) = 69984 * k + 43946 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 43946) = 34992 * k + 21973 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 21973) = 52488 * k + 32960 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 32960) = 26244 * k + 16480 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 16480) = 13122 * k + 8240 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8240) = 6561 * k + 4120 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 10287) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 10287)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_10799_mod_16384 {n : ℕ} (hn : n % 16384 = 10799) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 10799 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 10799) = 24576 * k + 16199 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 16199) = 36864 * k + 24299 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 24299) = 55296 * k + 36449 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 36449) = 82944 * k + 54674 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 54674) = 41472 * k + 27337 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 27337) = 62208 * k + 41006 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 41006) = 31104 * k + 20503 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 20503) = 46656 * k + 30755 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 30755) = 69984 * k + 46133 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 46133) = 104976 * k + 69200 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 69200) = 52488 * k + 34600 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 34600) = 26244 * k + 17300 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 17300) = 13122 * k + 8650 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8650) = 6561 * k + 4325 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 10799) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 10799)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_11231_mod_16384 {n : ℕ} (hn : n % 16384 = 11231) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 11231 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 11231) = 24576 * k + 16847 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 16847) = 36864 * k + 25271 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 25271) = 55296 * k + 37907 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 37907) = 82944 * k + 56861 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 56861) = 124416 * k + 85292 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 85292) = 62208 * k + 42646 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 42646) = 31104 * k + 21323 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 21323) = 46656 * k + 31985 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 31985) = 69984 * k + 47978 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 47978) = 34992 * k + 23989 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 23989) = 52488 * k + 35984 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 35984) = 26244 * k + 17992 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 17992) = 13122 * k + 8996 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 8996) = 6561 * k + 4498 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 11231) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 11231)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_11675_mod_16384 {n : ℕ} (hn : n % 16384 = 11675) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 11675 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 11675) = 24576 * k + 17513 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 17513) = 36864 * k + 26270 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 26270) = 18432 * k + 13135 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 13135) = 27648 * k + 19703 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 19703) = 41472 * k + 29555 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 29555) = 62208 * k + 44333 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 44333) = 93312 * k + 66500 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 66500) = 46656 * k + 33250 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 33250) = 23328 * k + 16625 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 16625) = 34992 * k + 24938 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 24938) = 17496 * k + 12469 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 12469) = 26244 * k + 18704 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 18704) = 13122 * k + 9352 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 9352) = 6561 * k + 4676 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 11675) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 11675)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_11743_mod_16384 {n : ℕ} (hn : n % 16384 = 11743) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 11743 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 11743) = 24576 * k + 17615 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 17615) = 36864 * k + 26423 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 26423) = 55296 * k + 39635 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 39635) = 82944 * k + 59453 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 59453) = 124416 * k + 89180 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 89180) = 62208 * k + 44590 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 44590) = 31104 * k + 22295 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 22295) = 46656 * k + 33443 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 33443) = 69984 * k + 50165 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 50165) = 104976 * k + 75248 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 75248) = 52488 * k + 37624 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 37624) = 26244 * k + 18812 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 18812) = 13122 * k + 9406 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 9406) = 6561 * k + 4703 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 11743) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 11743)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_12027_mod_16384 {n : ℕ} (hn : n % 16384 = 12027) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 12027 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 12027) = 24576 * k + 18041 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 18041) = 36864 * k + 27062 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 27062) = 18432 * k + 13531 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 13531) = 27648 * k + 20297 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 20297) = 41472 * k + 30446 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 30446) = 20736 * k + 15223 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 15223) = 31104 * k + 22835 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 22835) = 46656 * k + 34253 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 34253) = 69984 * k + 51380 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 51380) = 34992 * k + 25690 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 25690) = 17496 * k + 12845 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 12845) = 26244 * k + 19268 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 19268) = 13122 * k + 9634 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 9634) = 6561 * k + 4817 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 12027) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 12027)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_12095_mod_16384 {n : ℕ} (hn : n % 16384 = 12095) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 12095 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 12095) = 24576 * k + 18143 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 18143) = 36864 * k + 27215 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 27215) = 55296 * k + 40823 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 40823) = 82944 * k + 61235 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 61235) = 124416 * k + 91853 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 91853) = 186624 * k + 137780 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 137780) = 93312 * k + 68890 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 68890) = 46656 * k + 34445 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 34445) = 69984 * k + 51668 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 51668) = 34992 * k + 25834 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 25834) = 17496 * k + 12917 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 12917) = 26244 * k + 19376 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 19376) = 13122 * k + 9688 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 9688) = 6561 * k + 4844 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 12095) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 12095)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_12415_mod_16384 {n : ℕ} (hn : n % 16384 = 12415) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 12415 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 12415) = 24576 * k + 18623 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 18623) = 36864 * k + 27935 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 27935) = 55296 * k + 41903 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 41903) = 82944 * k + 62855 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 62855) = 124416 * k + 94283 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 94283) = 186624 * k + 141425 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 141425) = 279936 * k + 212138 := by unfold T; split <;> omega
  have h8 : T (279936 * k + 212138) = 139968 * k + 106069 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 106069) = 209952 * k + 159104 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 159104) = 104976 * k + 79552 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 79552) = 52488 * k + 39776 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 39776) = 26244 * k + 19888 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 19888) = 13122 * k + 9944 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 9944) = 6561 * k + 4972 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 12415) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 12415)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_12647_mod_16384 {n : ℕ} (hn : n % 16384 = 12647) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 12647 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 12647) = 24576 * k + 18971 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 18971) = 36864 * k + 28457 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 28457) = 55296 * k + 42686 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 42686) = 27648 * k + 21343 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 21343) = 41472 * k + 32015 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 32015) = 62208 * k + 48023 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 48023) = 93312 * k + 72035 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 72035) = 139968 * k + 108053 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 108053) = 209952 * k + 162080 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 162080) = 104976 * k + 81040 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 81040) = 52488 * k + 40520 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 40520) = 26244 * k + 20260 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 20260) = 13122 * k + 10130 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10130) = 6561 * k + 5065 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 12647) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 12647)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_12699_mod_16384 {n : ℕ} (hn : n % 16384 = 12699) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 12699 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 12699) = 24576 * k + 19049 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 19049) = 36864 * k + 28574 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 28574) = 18432 * k + 14287 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 14287) = 27648 * k + 21431 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 21431) = 41472 * k + 32147 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 32147) = 62208 * k + 48221 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 48221) = 93312 * k + 72332 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 72332) = 46656 * k + 36166 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 36166) = 23328 * k + 18083 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 18083) = 34992 * k + 27125 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 27125) = 52488 * k + 40688 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 40688) = 26244 * k + 20344 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 20344) = 13122 * k + 10172 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10172) = 6561 * k + 5086 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 12699) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 12699)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13051_mod_16384 {n : ℕ} (hn : n % 16384 = 13051) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13051 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13051) = 24576 * k + 19577 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 19577) = 36864 * k + 29366 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 29366) = 18432 * k + 14683 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 14683) = 27648 * k + 22025 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 22025) = 41472 * k + 33038 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 33038) = 20736 * k + 16519 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 16519) = 31104 * k + 24779 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 24779) = 46656 * k + 37169 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 37169) = 69984 * k + 55754 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 55754) = 34992 * k + 27877 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 27877) = 52488 * k + 41816 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 41816) = 26244 * k + 20908 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 20908) = 13122 * k + 10454 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10454) = 6561 * k + 5227 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13051) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13051)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13119_mod_16384 {n : ℕ} (hn : n % 16384 = 13119) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13119 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13119) = 24576 * k + 19679 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 19679) = 36864 * k + 29519 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 29519) = 55296 * k + 44279 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 44279) = 82944 * k + 66419 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 66419) = 124416 * k + 99629 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 99629) = 186624 * k + 149444 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 149444) = 93312 * k + 74722 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 74722) = 46656 * k + 37361 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 37361) = 69984 * k + 56042 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 56042) = 34992 * k + 28021 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 28021) = 52488 * k + 42032 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 42032) = 26244 * k + 21016 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 21016) = 13122 * k + 10508 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10508) = 6561 * k + 5254 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13119) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13119)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13383_mod_16384 {n : ℕ} (hn : n % 16384 = 13383) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13383 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13383) = 24576 * k + 20075 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 20075) = 36864 * k + 30113 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 30113) = 55296 * k + 45170 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 45170) = 27648 * k + 22585 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 22585) = 41472 * k + 33878 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 33878) = 20736 * k + 16939 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 16939) = 31104 * k + 25409 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 25409) = 46656 * k + 38114 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 38114) = 23328 * k + 19057 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 19057) = 34992 * k + 28586 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 28586) = 17496 * k + 14293 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 14293) = 26244 * k + 21440 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 21440) = 13122 * k + 10720 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10720) = 6561 * k + 5360 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13383) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13383)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13563_mod_16384 {n : ℕ} (hn : n % 16384 = 13563) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13563 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13563) = 24576 * k + 20345 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 20345) = 36864 * k + 30518 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 30518) = 18432 * k + 15259 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 15259) = 27648 * k + 22889 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 22889) = 41472 * k + 34334 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 34334) = 20736 * k + 17167 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 17167) = 31104 * k + 25751 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 25751) = 46656 * k + 38627 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 38627) = 69984 * k + 57941 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 57941) = 104976 * k + 86912 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 86912) = 52488 * k + 43456 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 43456) = 26244 * k + 21728 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 21728) = 13122 * k + 10864 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10864) = 6561 * k + 5432 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13563) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13563)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13631_mod_16384 {n : ℕ} (hn : n % 16384 = 13631) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13631 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13631) = 24576 * k + 20447 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 20447) = 36864 * k + 30671 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 30671) = 55296 * k + 46007 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 46007) = 82944 * k + 69011 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 69011) = 124416 * k + 103517 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 103517) = 186624 * k + 155276 := by unfold T; split <;> omega
  have h7 : T (186624 * k + 155276) = 93312 * k + 77638 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 77638) = 46656 * k + 38819 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 38819) = 69984 * k + 58229 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 58229) = 104976 * k + 87344 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 87344) = 52488 * k + 43672 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 43672) = 26244 * k + 21836 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 21836) = 13122 * k + 10918 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 10918) = 6561 * k + 5459 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13631) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13631)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_13915_mod_16384 {n : ℕ} (hn : n % 16384 = 13915) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 13915 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 13915) = 24576 * k + 20873 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 20873) = 36864 * k + 31310 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 31310) = 18432 * k + 15655 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 15655) = 27648 * k + 23483 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 23483) = 41472 * k + 35225 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 35225) = 62208 * k + 52838 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 52838) = 31104 * k + 26419 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 26419) = 46656 * k + 39629 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 39629) = 69984 * k + 59444 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 59444) = 34992 * k + 29722 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 29722) = 17496 * k + 14861 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 14861) = 26244 * k + 22292 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 22292) = 13122 * k + 11146 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11146) = 6561 * k + 5573 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 13915) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 13915)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_14063_mod_16384 {n : ℕ} (hn : n % 16384 = 14063) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 14063 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 14063) = 24576 * k + 21095 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 21095) = 36864 * k + 31643 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 31643) = 55296 * k + 47465 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 47465) = 82944 * k + 71198 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 71198) = 41472 * k + 35599 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 35599) = 62208 * k + 53399 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 53399) = 93312 * k + 80099 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 80099) = 139968 * k + 120149 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 120149) = 209952 * k + 180224 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 180224) = 104976 * k + 90112 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 90112) = 52488 * k + 45056 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 45056) = 26244 * k + 22528 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 22528) = 13122 * k + 11264 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11264) = 6561 * k + 5632 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 14063) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 14063)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_14407_mod_16384 {n : ℕ} (hn : n % 16384 = 14407) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 14407 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 14407) = 24576 * k + 21611 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 21611) = 36864 * k + 32417 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 32417) = 55296 * k + 48626 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 48626) = 27648 * k + 24313 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 24313) = 41472 * k + 36470 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 36470) = 20736 * k + 18235 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 18235) = 31104 * k + 27353 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 27353) = 46656 * k + 41030 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 41030) = 23328 * k + 20515 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 20515) = 34992 * k + 30773 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 30773) = 52488 * k + 46160 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 46160) = 26244 * k + 23080 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 23080) = 13122 * k + 11540 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11540) = 6561 * k + 5770 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 14407) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 14407)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_14567_mod_16384 {n : ℕ} (hn : n % 16384 = 14567) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 14567 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 14567) = 24576 * k + 21851 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 21851) = 36864 * k + 32777 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 32777) = 55296 * k + 49166 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 49166) = 27648 * k + 24583 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 24583) = 41472 * k + 36875 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 36875) = 62208 * k + 55313 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 55313) = 93312 * k + 82970 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 82970) = 46656 * k + 41485 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 41485) = 69984 * k + 62228 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 62228) = 34992 * k + 31114 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 31114) = 17496 * k + 15557 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 15557) = 26244 * k + 23336 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 23336) = 13122 * k + 11668 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11668) = 6561 * k + 5834 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 14567) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 14567)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_14799_mod_16384 {n : ℕ} (hn : n % 16384 = 14799) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 14799 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 14799) = 24576 * k + 22199 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 22199) = 36864 * k + 33299 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 33299) = 55296 * k + 49949 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 49949) = 82944 * k + 74924 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 74924) = 41472 * k + 37462 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 37462) = 20736 * k + 18731 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 18731) = 31104 * k + 28097 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 28097) = 46656 * k + 42146 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 42146) = 23328 * k + 21073 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 21073) = 34992 * k + 31610 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 31610) = 17496 * k + 15805 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 15805) = 26244 * k + 23708 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 23708) = 13122 * k + 11854 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11854) = 6561 * k + 5927 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 14799) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 14799)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_14939_mod_16384 {n : ℕ} (hn : n % 16384 = 14939) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 14939 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 14939) = 24576 * k + 22409 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 22409) = 36864 * k + 33614 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 33614) = 18432 * k + 16807 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 16807) = 27648 * k + 25211 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 25211) = 41472 * k + 37817 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 37817) = 62208 * k + 56726 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 56726) = 31104 * k + 28363 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 28363) = 46656 * k + 42545 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 42545) = 69984 * k + 63818 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 63818) = 34992 * k + 31909 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 31909) = 52488 * k + 47864 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 47864) = 26244 * k + 23932 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 23932) = 13122 * k + 11966 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 11966) = 6561 * k + 5983 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 14939) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 14939)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15007_mod_16384 {n : ℕ} (hn : n % 16384 = 15007) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15007 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15007) = 24576 * k + 22511 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 22511) = 36864 * k + 33767 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 33767) = 55296 * k + 50651 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 50651) = 82944 * k + 75977 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 75977) = 124416 * k + 113966 := by unfold T; split <;> omega
  have h6 : T (124416 * k + 113966) = 62208 * k + 56983 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 56983) = 93312 * k + 85475 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 85475) = 139968 * k + 128213 := by unfold T; split <;> omega
  have h9 : T (139968 * k + 128213) = 209952 * k + 192320 := by unfold T; split <;> omega
  have h10 : T (209952 * k + 192320) = 104976 * k + 96160 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 96160) = 52488 * k + 48080 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 48080) = 26244 * k + 24040 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 24040) = 13122 * k + 12020 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12020) = 6561 * k + 6010 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15007) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15007)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15271_mod_16384 {n : ℕ} (hn : n % 16384 = 15271) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15271 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15271) = 24576 * k + 22907 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 22907) = 36864 * k + 34361 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 34361) = 55296 * k + 51542 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 51542) = 27648 * k + 25771 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 25771) = 41472 * k + 38657 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 38657) = 62208 * k + 57986 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 57986) = 31104 * k + 28993 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 28993) = 46656 * k + 43490 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 43490) = 23328 * k + 21745 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 21745) = 34992 * k + 32618 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 32618) = 17496 * k + 16309 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 16309) = 26244 * k + 24464 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 24464) = 13122 * k + 12232 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12232) = 6561 * k + 6116 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15271) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15271)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15451_mod_16384 {n : ℕ} (hn : n % 16384 = 15451) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15451 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15451) = 24576 * k + 23177 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 23177) = 36864 * k + 34766 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 34766) = 18432 * k + 17383 := by unfold T; split <;> omega
  have h4 : T (18432 * k + 17383) = 27648 * k + 26075 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 26075) = 41472 * k + 39113 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 39113) = 62208 * k + 58670 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 58670) = 31104 * k + 29335 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 29335) = 46656 * k + 44003 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 44003) = 69984 * k + 66005 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 66005) = 104976 * k + 99008 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 99008) = 52488 * k + 49504 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 49504) = 26244 * k + 24752 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 24752) = 13122 * k + 12376 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12376) = 6561 * k + 6188 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15451) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15451)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15591_mod_16384 {n : ℕ} (hn : n % 16384 = 15591) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15591 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15591) = 24576 * k + 23387 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 23387) = 36864 * k + 35081 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 35081) = 55296 * k + 52622 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 52622) = 27648 * k + 26311 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 26311) = 41472 * k + 39467 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 39467) = 62208 * k + 59201 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 59201) = 93312 * k + 88802 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 88802) = 46656 * k + 44401 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 44401) = 69984 * k + 66602 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 66602) = 34992 * k + 33301 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 33301) = 52488 * k + 49952 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 49952) = 26244 * k + 24976 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 24976) = 13122 * k + 12488 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12488) = 6561 * k + 6244 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15591) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15591)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15823_mod_16384 {n : ℕ} (hn : n % 16384 = 15823) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15823 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15823) = 24576 * k + 23735 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 23735) = 36864 * k + 35603 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 35603) = 55296 * k + 53405 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 53405) = 82944 * k + 80108 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 80108) = 41472 * k + 40054 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 40054) = 20736 * k + 20027 := by unfold T; split <;> omega
  have h7 : T (20736 * k + 20027) = 31104 * k + 30041 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 30041) = 46656 * k + 45062 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 45062) = 23328 * k + 22531 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 22531) = 34992 * k + 33797 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 33797) = 52488 * k + 50696 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 50696) = 26244 * k + 25348 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 25348) = 13122 * k + 12674 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12674) = 6561 * k + 6337 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15823) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15823)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_15983_mod_16384 {n : ℕ} (hn : n % 16384 = 15983) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 15983 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 15983) = 24576 * k + 23975 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 23975) = 36864 * k + 35963 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 35963) = 55296 * k + 53945 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 53945) = 82944 * k + 80918 := by unfold T; split <;> omega
  have h5 : T (82944 * k + 80918) = 41472 * k + 40459 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 40459) = 62208 * k + 60689 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 60689) = 93312 * k + 91034 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 91034) = 46656 * k + 45517 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 45517) = 69984 * k + 68276 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 68276) = 34992 * k + 34138 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 34138) = 17496 * k + 17069 := by unfold T; split <;> omega
  have h12 : T (17496 * k + 17069) = 26244 * k + 25604 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 25604) = 13122 * k + 12802 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12802) = 6561 * k + 6401 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 15983) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 15983)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_16103_mod_16384 {n : ℕ} (hn : n % 16384 = 16103) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 16103 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 16103) = 24576 * k + 24155 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 24155) = 36864 * k + 36233 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 36233) = 55296 * k + 54350 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 54350) = 27648 * k + 27175 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 27175) = 41472 * k + 40763 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 40763) = 62208 * k + 61145 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 61145) = 93312 * k + 91718 := by unfold T; split <;> omega
  have h8 : T (93312 * k + 91718) = 46656 * k + 45859 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 45859) = 69984 * k + 68789 := by unfold T; split <;> omega
  have h10 : T (69984 * k + 68789) = 104976 * k + 103184 := by unfold T; split <;> omega
  have h11 : T (104976 * k + 103184) = 52488 * k + 51592 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 51592) = 26244 * k + 25796 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 25796) = 13122 * k + 12898 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 12898) = 6561 * k + 6449 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 16103) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 16103)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_16295_mod_16384 {n : ℕ} (hn : n % 16384 = 16295) : T_iter n 14 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 16384 * k + 16295 := ⟨n / 16384, by omega⟩
  have h1 : T (16384 * k + 16295) = 24576 * k + 24443 := by unfold T; split <;> omega
  have h2 : T (24576 * k + 24443) = 36864 * k + 36665 := by unfold T; split <;> omega
  have h3 : T (36864 * k + 36665) = 55296 * k + 54998 := by unfold T; split <;> omega
  have h4 : T (55296 * k + 54998) = 27648 * k + 27499 := by unfold T; split <;> omega
  have h5 : T (27648 * k + 27499) = 41472 * k + 41249 := by unfold T; split <;> omega
  have h6 : T (41472 * k + 41249) = 62208 * k + 61874 := by unfold T; split <;> omega
  have h7 : T (62208 * k + 61874) = 31104 * k + 30937 := by unfold T; split <;> omega
  have h8 : T (31104 * k + 30937) = 46656 * k + 46406 := by unfold T; split <;> omega
  have h9 : T (46656 * k + 46406) = 23328 * k + 23203 := by unfold T; split <;> omega
  have h10 : T (23328 * k + 23203) = 34992 * k + 34805 := by unfold T; split <;> omega
  have h11 : T (34992 * k + 34805) = 52488 * k + 52208 := by unfold T; split <;> omega
  have h12 : T (52488 * k + 52208) = 26244 * k + 26104 := by unfold T; split <;> omega
  have h13 : T (26244 * k + 26104) = 13122 * k + 13052 := by unfold T; split <;> omega
  have h14 : T (13122 * k + 13052) = 6561 * k + 6526 := by unfold T; split <;> omega
  have e : T_iter (16384 * k + 16295) 14 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (16384 * k + 16295)))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; omega

theorem descent_within_fourteen {n : ℕ}
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
           ∨ n % 16384 = 191
           ∨ n % 16384 = 303
           ∨ n % 16384 = 543
           ∨ n % 16384 = 623
           ∨ n % 16384 = 1135
           ∨ n % 16384 = 1215
           ∨ n % 16384 = 1247
           ∨ n % 16384 = 1327
           ∨ n % 16384 = 1567
           ∨ n % 16384 = 1727
           ∨ n % 16384 = 2079
           ∨ n % 16384 = 2271
           ∨ n % 16384 = 2331
           ∨ n % 16384 = 2431
           ∨ n % 16384 = 2663
           ∨ n % 16384 = 3067
           ∨ n % 16384 = 3135
           ∨ n % 16384 = 3455
           ∨ n % 16384 = 3687
           ∨ n % 16384 = 3967
           ∨ n % 16384 = 4079
           ∨ n % 16384 = 4091
           ∨ n % 16384 = 4159
           ∨ n % 16384 = 4199
           ∨ n % 16384 = 4251
           ∨ n % 16384 = 4955
           ∨ n % 16384 = 5023
           ∨ n % 16384 = 5103
           ∨ n % 16384 = 5275
           ∨ n % 16384 = 5607
           ∨ n % 16384 = 5615
           ∨ n % 16384 = 5787
           ∨ n % 16384 = 5959
           ∨ n % 16384 = 5979
           ∨ n % 16384 = 6047
           ∨ n % 16384 = 6559
           ∨ n % 16384 = 6631
           ∨ n % 16384 = 6983
           ∨ n % 16384 = 7023
           ∨ n % 16384 = 7375
           ∨ n % 16384 = 7495
           ∨ n % 16384 = 7847
           ∨ n % 16384 = 7967
           ∨ n % 16384 = 8047
           ∨ n % 16384 = 8399
           ∨ n % 16384 = 8447
           ∨ n % 16384 = 8731
           ∨ n % 16384 = 8871
           ∨ n % 16384 = 8911
           ∨ n % 16384 = 8991
           ∨ n % 16384 = 9263
           ∨ n % 16384 = 9383
           ∨ n % 16384 = 9755
           ∨ n % 16384 = 10175
           ∨ n % 16384 = 10207
           ∨ n % 16384 = 10267
           ∨ n % 16384 = 10287
           ∨ n % 16384 = 10799
           ∨ n % 16384 = 11231
           ∨ n % 16384 = 11675
           ∨ n % 16384 = 11743
           ∨ n % 16384 = 12027
           ∨ n % 16384 = 12095
           ∨ n % 16384 = 12415
           ∨ n % 16384 = 12647
           ∨ n % 16384 = 12699
           ∨ n % 16384 = 13051
           ∨ n % 16384 = 13119
           ∨ n % 16384 = 13383
           ∨ n % 16384 = 13563
           ∨ n % 16384 = 13631
           ∨ n % 16384 = 13915
           ∨ n % 16384 = 14063
           ∨ n % 16384 = 14407
           ∨ n % 16384 = 14567
           ∨ n % 16384 = 14799
           ∨ n % 16384 = 14939
           ∨ n % 16384 = 15007
           ∨ n % 16384 = 15271
           ∨ n % 16384 = 15451
           ∨ n % 16384 = 15591
           ∨ n % 16384 = 15823
           ∨ n % 16384 = 15983
           ∨ n % 16384 = 16103
           ∨ n % 16384 = 16295
        ) :
    ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ T_iter n k < n := by
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_231_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_383_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_463_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_615_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_879_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_935_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1019_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1087_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1231_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1435_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1647_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1703_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1787_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1823_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_1855_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2031_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2203_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2239_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2351_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2587_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2591_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2907_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_2975_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3119_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3143_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3295_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3559_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3675_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_3911_mod_4096 (by assumption)⟩
  · exact ⟨12, by norm_num, by norm_num,
        CollatzResidueDescent4096.descent_4063_mod_4096 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_191_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_303_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_543_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_623_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1135_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1215_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1247_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1327_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1567_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_1727_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_2079_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_2271_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_2331_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_2431_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_2663_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_3067_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_3135_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_3455_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_3687_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_3967_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4079_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4091_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4159_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4199_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4251_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_4955_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5023_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5103_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5275_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5607_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5615_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5787_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5959_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_5979_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_6047_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_6559_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_6631_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_6983_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_7023_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_7375_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_7495_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_7847_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_7967_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8047_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8399_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8447_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8731_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8871_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8911_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_8991_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_9263_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_9383_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_9755_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_10175_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_10207_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_10267_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_10287_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_10799_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_11231_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_11675_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_11743_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_12027_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_12095_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_12415_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_12647_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_12699_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13051_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13119_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13383_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13563_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13631_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_13915_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_14063_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_14407_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_14567_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_14799_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_14939_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15007_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15271_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15451_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15591_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15823_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_15983_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_16103_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num, descent_16295_mod_16384 (by assumption)⟩

end CollatzResidueDescent16384
