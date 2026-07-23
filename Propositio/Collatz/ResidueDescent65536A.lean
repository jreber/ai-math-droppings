import Propositio.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_127_mod_65536 {n : ℕ} (hn : n % 65536 = 127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 127) = 98304 * k + 191 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 191) = 147456 * k + 287 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 287) = 221184 * k + 431 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 431) = 331776 * k + 647 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 647) = 497664 * k + 971 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 971) = 746496 * k + 1457 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 1457) = 1119744 * k + 2186 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 2186) = 559872 * k + 1093 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 1093) = 839808 * k + 1640 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 1640) = 419904 * k + 820 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 820) = 209952 * k + 410 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 410) = 104976 * k + 205 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 205) = 157464 * k + 308 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 308) = 78732 * k + 154 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 154) = 39366 * k + 77 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 77) = 59049 * k + 116 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_255_mod_65536 {n : ℕ} (hn : n % 65536 = 255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 255) = 98304 * k + 383 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 383) = 147456 * k + 575 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 575) = 221184 * k + 863 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 863) = 331776 * k + 1295 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 1295) = 497664 * k + 1943 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 1943) = 746496 * k + 2915 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 2915) = 1119744 * k + 4373 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 4373) = 1679616 * k + 6560 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 6560) = 839808 * k + 3280 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 3280) = 419904 * k + 1640 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 1640) = 209952 * k + 820 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 820) = 104976 * k + 410 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 410) = 52488 * k + 205 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 205) = 78732 * k + 308 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 308) = 39366 * k + 154 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 154) = 19683 * k + 77 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_359_mod_65536 {n : ℕ} (hn : n % 65536 = 359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 359) = 98304 * k + 539 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 539) = 147456 * k + 809 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 809) = 221184 * k + 1214 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 1214) = 110592 * k + 607 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 607) = 165888 * k + 911 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 911) = 248832 * k + 1367 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 1367) = 373248 * k + 2051 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 2051) = 559872 * k + 3077 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 3077) = 839808 * k + 4616 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 4616) = 419904 * k + 2308 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 2308) = 209952 * k + 1154 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 1154) = 104976 * k + 577 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 577) = 157464 * k + 866 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 866) = 78732 * k + 433 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 433) = 118098 * k + 650 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 650) = 59049 * k + 325 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_411_mod_65536 {n : ℕ} (hn : n % 65536 = 411) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 411 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 411) = 98304 * k + 617 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 617) = 147456 * k + 926 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 926) = 73728 * k + 463 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 463) = 110592 * k + 695 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 695) = 165888 * k + 1043 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1043) = 248832 * k + 1565 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 1565) = 373248 * k + 2348 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 2348) = 186624 * k + 1174 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 1174) = 93312 * k + 587 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 587) = 139968 * k + 881 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 881) = 209952 * k + 1322 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 1322) = 104976 * k + 661 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 661) = 157464 * k + 992 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 992) = 78732 * k + 496 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 496) = 39366 * k + 248 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 248) = 19683 * k + 124 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 411) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 411)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_415_mod_65536 {n : ℕ} (hn : n % 65536 = 415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 415) = 98304 * k + 623 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 623) = 147456 * k + 935 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 935) = 221184 * k + 1403 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 1403) = 331776 * k + 2105 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 2105) = 497664 * k + 3158 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 3158) = 248832 * k + 1579 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 1579) = 373248 * k + 2369 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 2369) = 559872 * k + 3554 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 3554) = 279936 * k + 1777 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 1777) = 419904 * k + 2666 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 2666) = 209952 * k + 1333 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 1333) = 314928 * k + 2000 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 2000) = 157464 * k + 1000 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 1000) = 78732 * k + 500 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 500) = 39366 * k + 250 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 250) = 19683 * k + 125 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_479_mod_65536 {n : ℕ} (hn : n % 65536 = 479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 479) = 98304 * k + 719 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 719) = 147456 * k + 1079 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1079) = 221184 * k + 1619 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 1619) = 331776 * k + 2429 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 2429) = 497664 * k + 3644 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 3644) = 248832 * k + 1822 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 1822) = 124416 * k + 911 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 911) = 186624 * k + 1367 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 1367) = 279936 * k + 2051 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 2051) = 419904 * k + 3077 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 3077) = 629856 * k + 4616 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 4616) = 314928 * k + 2308 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 2308) = 157464 * k + 1154 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 1154) = 78732 * k + 577 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 577) = 118098 * k + 866 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 866) = 59049 * k + 433 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_539_mod_65536 {n : ℕ} (hn : n % 65536 = 539) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 539 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 539) = 98304 * k + 809 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 809) = 147456 * k + 1214 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1214) = 73728 * k + 607 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 607) = 110592 * k + 911 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 911) = 165888 * k + 1367 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1367) = 248832 * k + 2051 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 2051) = 373248 * k + 3077 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 3077) = 559872 * k + 4616 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 4616) = 279936 * k + 2308 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 2308) = 139968 * k + 1154 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1154) = 69984 * k + 577 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 577) = 104976 * k + 866 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 866) = 52488 * k + 433 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 433) = 78732 * k + 650 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 650) = 39366 * k + 325 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 325) = 59049 * k + 488 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 539) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 539)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_559_mod_65536 {n : ℕ} (hn : n % 65536 = 559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 559) = 98304 * k + 839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 839) = 147456 * k + 1259 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1259) = 221184 * k + 1889 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 1889) = 331776 * k + 2834 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 2834) = 165888 * k + 1417 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1417) = 248832 * k + 2126 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 2126) = 124416 * k + 1063 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1063) = 186624 * k + 1595 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 1595) = 279936 * k + 2393 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 2393) = 419904 * k + 3590 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 3590) = 209952 * k + 1795 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 1795) = 314928 * k + 2693 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 2693) = 472392 * k + 4040 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 4040) = 236196 * k + 2020 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 2020) = 118098 * k + 1010 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 1010) = 59049 * k + 505 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_603_mod_65536 {n : ℕ} (hn : n % 65536 = 603) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 603 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 603) = 98304 * k + 905 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 905) = 147456 * k + 1358 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1358) = 73728 * k + 679 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 679) = 110592 * k + 1019 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1019) = 165888 * k + 1529 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1529) = 248832 * k + 2294 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 2294) = 124416 * k + 1147 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1147) = 186624 * k + 1721 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 1721) = 279936 * k + 2582 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 2582) = 139968 * k + 1291 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1291) = 209952 * k + 1937 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 1937) = 314928 * k + 2906 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 2906) = 157464 * k + 1453 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 1453) = 236196 * k + 2180 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 2180) = 118098 * k + 1090 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 1090) = 59049 * k + 545 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 603) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 603)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_679_mod_65536 {n : ℕ} (hn : n % 65536 = 679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 679) = 98304 * k + 1019 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1019) = 147456 * k + 1529 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1529) = 221184 * k + 2294 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2294) = 110592 * k + 1147 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1147) = 165888 * k + 1721 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1721) = 248832 * k + 2582 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 2582) = 124416 * k + 1291 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1291) = 186624 * k + 1937 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 1937) = 279936 * k + 2906 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 2906) = 139968 * k + 1453 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1453) = 209952 * k + 2180 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 2180) = 104976 * k + 1090 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1090) = 52488 * k + 545 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 545) = 78732 * k + 818 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 818) = 39366 * k + 409 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 409) = 59049 * k + 614 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_719_mod_65536 {n : ℕ} (hn : n % 65536 = 719) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 719 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 719) = 98304 * k + 1079 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1079) = 147456 * k + 1619 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1619) = 221184 * k + 2429 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2429) = 331776 * k + 3644 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 3644) = 165888 * k + 1822 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 1822) = 82944 * k + 911 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 911) = 124416 * k + 1367 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1367) = 186624 * k + 2051 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 2051) = 279936 * k + 3077 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 3077) = 419904 * k + 4616 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 4616) = 209952 * k + 2308 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 2308) = 104976 * k + 1154 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1154) = 52488 * k + 577 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 577) = 78732 * k + 866 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 866) = 39366 * k + 433 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 433) = 59049 * k + 650 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 719) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 719)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_767_mod_65536 {n : ℕ} (hn : n % 65536 = 767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 767) = 98304 * k + 1151 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1151) = 147456 * k + 1727 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1727) = 221184 * k + 2591 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2591) = 331776 * k + 3887 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 3887) = 497664 * k + 5831 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 5831) = 746496 * k + 8747 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 8747) = 1119744 * k + 13121 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 13121) = 1679616 * k + 19682 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 19682) = 839808 * k + 9841 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 9841) = 1259712 * k + 14762 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 14762) = 629856 * k + 7381 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 7381) = 944784 * k + 11072 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 11072) = 472392 * k + 5536 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 5536) = 236196 * k + 2768 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 2768) = 118098 * k + 1384 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 1384) = 59049 * k + 692 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_799_mod_65536 {n : ℕ} (hn : n % 65536 = 799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 799) = 98304 * k + 1199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1199) = 147456 * k + 1799 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1799) = 221184 * k + 2699 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2699) = 331776 * k + 4049 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 4049) = 497664 * k + 6074 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 6074) = 248832 * k + 3037 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 3037) = 373248 * k + 4556 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 4556) = 186624 * k + 2278 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 2278) = 93312 * k + 1139 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 1139) = 139968 * k + 1709 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1709) = 209952 * k + 2564 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 2564) = 104976 * k + 1282 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1282) = 52488 * k + 641 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 641) = 78732 * k + 962 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 962) = 39366 * k + 481 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 481) = 59049 * k + 722 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_831_mod_65536 {n : ℕ} (hn : n % 65536 = 831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 831) = 98304 * k + 1247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1247) = 147456 * k + 1871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1871) = 221184 * k + 2807 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2807) = 331776 * k + 4211 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 4211) = 497664 * k + 6317 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 6317) = 746496 * k + 9476 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 9476) = 373248 * k + 4738 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 4738) = 186624 * k + 2369 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 2369) = 279936 * k + 3554 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 3554) = 139968 * k + 1777 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1777) = 209952 * k + 2666 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 2666) = 104976 * k + 1333 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1333) = 157464 * k + 2000 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2000) = 78732 * k + 1000 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1000) = 39366 * k + 500 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 500) = 19683 * k + 250 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_839_mod_65536 {n : ℕ} (hn : n % 65536 = 839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 839) = 98304 * k + 1259 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1259) = 147456 * k + 1889 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1889) = 221184 * k + 2834 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 2834) = 110592 * k + 1417 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1417) = 165888 * k + 2126 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 2126) = 82944 * k + 1063 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 1063) = 124416 * k + 1595 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1595) = 186624 * k + 2393 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 2393) = 279936 * k + 3590 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 3590) = 139968 * k + 1795 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1795) = 209952 * k + 2693 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 2693) = 314928 * k + 4040 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 4040) = 157464 * k + 2020 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2020) = 78732 * k + 1010 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1010) = 39366 * k + 505 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 505) = 59049 * k + 758 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_859_mod_65536 {n : ℕ} (hn : n % 65536 = 859) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 859 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 859) = 98304 * k + 1289 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1289) = 147456 * k + 1934 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 1934) = 73728 * k + 967 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 967) = 110592 * k + 1451 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1451) = 165888 * k + 2177 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 2177) = 248832 * k + 3266 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 3266) = 124416 * k + 1633 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 1633) = 186624 * k + 2450 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 2450) = 93312 * k + 1225 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 1225) = 139968 * k + 1838 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 1838) = 69984 * k + 919 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 919) = 104976 * k + 1379 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1379) = 157464 * k + 2069 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2069) = 236196 * k + 3104 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 3104) = 118098 * k + 1552 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 1552) = 59049 * k + 776 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 859) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 859)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1071_mod_65536 {n : ℕ} (hn : n % 65536 = 1071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1071) = 98304 * k + 1607 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1607) = 147456 * k + 2411 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2411) = 221184 * k + 3617 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 3617) = 331776 * k + 5426 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 5426) = 165888 * k + 2713 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 2713) = 248832 * k + 4070 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 4070) = 124416 * k + 2035 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 2035) = 186624 * k + 3053 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3053) = 279936 * k + 4580 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 4580) = 139968 * k + 2290 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 2290) = 69984 * k + 1145 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 1145) = 104976 * k + 1718 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1718) = 52488 * k + 859 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 859) = 78732 * k + 1289 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1289) = 118098 * k + 1934 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 1934) = 59049 * k + 967 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1095_mod_65536 {n : ℕ} (hn : n % 65536 = 1095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1095) = 98304 * k + 1643 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1643) = 147456 * k + 2465 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2465) = 221184 * k + 3698 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 3698) = 110592 * k + 1849 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1849) = 165888 * k + 2774 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 2774) = 82944 * k + 1387 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 1387) = 124416 * k + 2081 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 2081) = 186624 * k + 3122 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3122) = 93312 * k + 1561 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 1561) = 139968 * k + 2342 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 2342) = 69984 * k + 1171 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 1171) = 104976 * k + 1757 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1757) = 157464 * k + 2636 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2636) = 78732 * k + 1318 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1318) = 39366 * k + 659 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 659) = 59049 * k + 989 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1151_mod_65536 {n : ℕ} (hn : n % 65536 = 1151) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1151 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1151) = 98304 * k + 1727 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1727) = 147456 * k + 2591 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2591) = 221184 * k + 3887 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 3887) = 331776 * k + 5831 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 5831) = 497664 * k + 8747 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 8747) = 746496 * k + 13121 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 13121) = 1119744 * k + 19682 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 19682) = 559872 * k + 9841 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 9841) = 839808 * k + 14762 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 14762) = 419904 * k + 7381 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 7381) = 629856 * k + 11072 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 11072) = 314928 * k + 5536 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 5536) = 157464 * k + 2768 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2768) = 78732 * k + 1384 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1384) = 39366 * k + 692 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 692) = 19683 * k + 346 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1151) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1151)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1179_mod_65536 {n : ℕ} (hn : n % 65536 = 1179) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1179 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1179) = 98304 * k + 1769 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1769) = 147456 * k + 2654 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2654) = 73728 * k + 1327 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 1327) = 110592 * k + 1991 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 1991) = 165888 * k + 2987 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 2987) = 248832 * k + 4481 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 4481) = 373248 * k + 6722 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 6722) = 186624 * k + 3361 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3361) = 279936 * k + 5042 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 5042) = 139968 * k + 2521 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 2521) = 209952 * k + 3782 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 3782) = 104976 * k + 1891 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1891) = 157464 * k + 2837 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2837) = 236196 * k + 4256 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 4256) = 118098 * k + 2128 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2128) = 59049 * k + 1064 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1179) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1179)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1183_mod_65536 {n : ℕ} (hn : n % 65536 = 1183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1183) = 98304 * k + 1775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1775) = 147456 * k + 2663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2663) = 221184 * k + 3995 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 3995) = 331776 * k + 5993 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 5993) = 497664 * k + 8990 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 8990) = 248832 * k + 4495 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 4495) = 373248 * k + 6743 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 6743) = 559872 * k + 10115 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 10115) = 839808 * k + 15173 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 15173) = 1259712 * k + 22760 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 22760) = 629856 * k + 11380 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 11380) = 314928 * k + 5690 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 5690) = 157464 * k + 2845 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 2845) = 236196 * k + 4268 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 4268) = 118098 * k + 2134 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2134) = 59049 * k + 1067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1191_mod_65536 {n : ℕ} (hn : n % 65536 = 1191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1191) = 98304 * k + 1787 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1787) = 147456 * k + 2681 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2681) = 221184 * k + 4022 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 4022) = 110592 * k + 2011 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 2011) = 165888 * k + 3017 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 3017) = 248832 * k + 4526 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 4526) = 124416 * k + 2263 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 2263) = 186624 * k + 3395 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3395) = 279936 * k + 5093 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 5093) = 419904 * k + 7640 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 7640) = 209952 * k + 3820 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 3820) = 104976 * k + 1910 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 1910) = 52488 * k + 955 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 955) = 78732 * k + 1433 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1433) = 118098 * k + 2150 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2150) = 59049 * k + 1075 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1275_mod_65536 {n : ℕ} (hn : n % 65536 = 1275) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1275 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1275) = 98304 * k + 1913 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 1913) = 147456 * k + 2870 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 2870) = 73728 * k + 1435 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 1435) = 110592 * k + 2153 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 2153) = 165888 * k + 3230 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 3230) = 82944 * k + 1615 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 1615) = 124416 * k + 2423 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 2423) = 186624 * k + 3635 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3635) = 279936 * k + 5453 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 5453) = 419904 * k + 8180 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 8180) = 209952 * k + 4090 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 4090) = 104976 * k + 2045 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 2045) = 157464 * k + 3068 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 3068) = 78732 * k + 1534 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1534) = 39366 * k + 767 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 767) = 59049 * k + 1151 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1275) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1275)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1351_mod_65536 {n : ℕ} (hn : n % 65536 = 1351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1351) = 98304 * k + 2027 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2027) = 147456 * k + 3041 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3041) = 221184 * k + 4562 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 4562) = 110592 * k + 2281 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 2281) = 165888 * k + 3422 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 3422) = 82944 * k + 1711 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 1711) = 124416 * k + 2567 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 2567) = 186624 * k + 3851 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 3851) = 279936 * k + 5777 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 5777) = 419904 * k + 8666 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 8666) = 209952 * k + 4333 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 4333) = 314928 * k + 6500 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 6500) = 157464 * k + 3250 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 3250) = 78732 * k + 1625 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1625) = 118098 * k + 2438 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2438) = 59049 * k + 1219 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1519_mod_65536 {n : ℕ} (hn : n % 65536 = 1519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1519) = 98304 * k + 2279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2279) = 147456 * k + 3419 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3419) = 221184 * k + 5129 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 5129) = 331776 * k + 7694 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 7694) = 165888 * k + 3847 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 3847) = 248832 * k + 5771 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 5771) = 373248 * k + 8657 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 8657) = 559872 * k + 12986 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 12986) = 279936 * k + 6493 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 6493) = 419904 * k + 9740 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 9740) = 209952 * k + 4870 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 4870) = 104976 * k + 2435 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 2435) = 157464 * k + 3653 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 3653) = 236196 * k + 5480 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 5480) = 118098 * k + 2740 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2740) = 59049 * k + 1370 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1535_mod_65536 {n : ℕ} (hn : n % 65536 = 1535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1535) = 98304 * k + 2303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2303) = 147456 * k + 3455 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3455) = 221184 * k + 5183 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 5183) = 331776 * k + 7775 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 7775) = 497664 * k + 11663 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 11663) = 746496 * k + 17495 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 17495) = 1119744 * k + 26243 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 26243) = 1679616 * k + 39365 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 39365) = 2519424 * k + 59048 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 59048) = 1259712 * k + 29524 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 29524) = 629856 * k + 14762 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 14762) = 314928 * k + 7381 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 7381) = 472392 * k + 11072 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 11072) = 236196 * k + 5536 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 5536) = 118098 * k + 2768 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2768) = 59049 * k + 1384 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1563_mod_65536 {n : ℕ} (hn : n % 65536 = 1563) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1563 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1563) = 98304 * k + 2345 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2345) = 147456 * k + 3518 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3518) = 73728 * k + 1759 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 1759) = 110592 * k + 2639 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 2639) = 165888 * k + 3959 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 3959) = 248832 * k + 5939 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 5939) = 373248 * k + 8909 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 8909) = 559872 * k + 13364 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 13364) = 279936 * k + 6682 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 6682) = 139968 * k + 3341 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 3341) = 209952 * k + 5012 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 5012) = 104976 * k + 2506 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 2506) = 52488 * k + 1253 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 1253) = 78732 * k + 1880 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1880) = 39366 * k + 940 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 940) = 19683 * k + 470 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1563) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1563)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1627_mod_65536 {n : ℕ} (hn : n % 65536 = 1627) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1627 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1627) = 98304 * k + 2441 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2441) = 147456 * k + 3662 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3662) = 73728 * k + 1831 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 1831) = 110592 * k + 2747 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 2747) = 165888 * k + 4121 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 4121) = 248832 * k + 6182 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 6182) = 124416 * k + 3091 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 3091) = 186624 * k + 4637 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 4637) = 279936 * k + 6956 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 6956) = 139968 * k + 3478 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 3478) = 69984 * k + 1739 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 1739) = 104976 * k + 2609 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 2609) = 157464 * k + 3914 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 3914) = 78732 * k + 1957 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 1957) = 118098 * k + 2936 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 2936) = 59049 * k + 1468 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1627) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1627)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1775_mod_65536 {n : ℕ} (hn : n % 65536 = 1775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1775) = 98304 * k + 2663 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2663) = 147456 * k + 3995 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 3995) = 221184 * k + 5993 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 5993) = 331776 * k + 8990 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 8990) = 165888 * k + 4495 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 4495) = 248832 * k + 6743 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 6743) = 373248 * k + 10115 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 10115) = 559872 * k + 15173 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 15173) = 839808 * k + 22760 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 22760) = 419904 * k + 11380 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 11380) = 209952 * k + 5690 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 5690) = 104976 * k + 2845 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 2845) = 157464 * k + 4268 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 4268) = 78732 * k + 2134 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2134) = 39366 * k + 1067 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1067) = 59049 * k + 1601 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1903_mod_65536 {n : ℕ} (hn : n % 65536 = 1903) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1903 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1903) = 98304 * k + 2855 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2855) = 147456 * k + 4283 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 4283) = 221184 * k + 6425 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 6425) = 331776 * k + 9638 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 9638) = 165888 * k + 4819 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 4819) = 248832 * k + 7229 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 7229) = 373248 * k + 10844 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 10844) = 186624 * k + 5422 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 5422) = 93312 * k + 2711 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 2711) = 139968 * k + 4067 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 4067) = 209952 * k + 6101 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 6101) = 314928 * k + 9152 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 9152) = 157464 * k + 4576 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 4576) = 78732 * k + 2288 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2288) = 39366 * k + 1144 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1144) = 19683 * k + 572 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1903) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1903)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_1983_mod_65536 {n : ℕ} (hn : n % 65536 = 1983) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 1983 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 1983) = 98304 * k + 2975 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 2975) = 147456 * k + 4463 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 4463) = 221184 * k + 6695 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 6695) = 331776 * k + 10043 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 10043) = 497664 * k + 15065 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 15065) = 746496 * k + 22598 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 22598) = 373248 * k + 11299 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 11299) = 559872 * k + 16949 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 16949) = 839808 * k + 25424 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 25424) = 419904 * k + 12712 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 12712) = 209952 * k + 6356 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 6356) = 104976 * k + 3178 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 3178) = 52488 * k + 1589 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 1589) = 78732 * k + 2384 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2384) = 39366 * k + 1192 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1192) = 19683 * k + 596 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 1983) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 1983)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2119_mod_65536 {n : ℕ} (hn : n % 65536 = 2119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2119) = 98304 * k + 3179 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3179) = 147456 * k + 4769 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 4769) = 221184 * k + 7154 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 7154) = 110592 * k + 3577 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 3577) = 165888 * k + 5366 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 5366) = 82944 * k + 2683 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 2683) = 124416 * k + 4025 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 4025) = 186624 * k + 6038 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 6038) = 93312 * k + 3019 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 3019) = 139968 * k + 4529 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 4529) = 209952 * k + 6794 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 6794) = 104976 * k + 3397 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 3397) = 157464 * k + 5096 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 5096) = 78732 * k + 2548 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2548) = 39366 * k + 1274 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1274) = 19683 * k + 637 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2279_mod_65536 {n : ℕ} (hn : n % 65536 = 2279) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2279 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2279) = 98304 * k + 3419 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3419) = 147456 * k + 5129 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5129) = 221184 * k + 7694 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 7694) = 110592 * k + 3847 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 3847) = 165888 * k + 5771 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 5771) = 248832 * k + 8657 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 8657) = 373248 * k + 12986 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 12986) = 186624 * k + 6493 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 6493) = 279936 * k + 9740 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 9740) = 139968 * k + 4870 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 4870) = 69984 * k + 2435 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 2435) = 104976 * k + 3653 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 3653) = 157464 * k + 5480 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 5480) = 78732 * k + 2740 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2740) = 39366 * k + 1370 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1370) = 19683 * k + 685 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2279) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2279)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2299_mod_65536 {n : ℕ} (hn : n % 65536 = 2299) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2299 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2299) = 98304 * k + 3449 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3449) = 147456 * k + 5174 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5174) = 73728 * k + 2587 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 2587) = 110592 * k + 3881 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 3881) = 165888 * k + 5822 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 5822) = 82944 * k + 2911 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 2911) = 124416 * k + 4367 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 4367) = 186624 * k + 6551 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 6551) = 279936 * k + 9827 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 9827) = 419904 * k + 14741 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 14741) = 629856 * k + 22112 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 22112) = 314928 * k + 11056 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 11056) = 157464 * k + 5528 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 5528) = 78732 * k + 2764 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2764) = 39366 * k + 1382 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1382) = 19683 * k + 691 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2299) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2299)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2303_mod_65536 {n : ℕ} (hn : n % 65536 = 2303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2303) = 98304 * k + 3455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3455) = 147456 * k + 5183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5183) = 221184 * k + 7775 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 7775) = 331776 * k + 11663 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 11663) = 497664 * k + 17495 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 17495) = 746496 * k + 26243 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 26243) = 1119744 * k + 39365 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 39365) = 1679616 * k + 59048 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 59048) = 839808 * k + 29524 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 29524) = 419904 * k + 14762 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 14762) = 209952 * k + 7381 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 7381) = 314928 * k + 11072 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 11072) = 157464 * k + 5536 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 5536) = 78732 * k + 2768 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2768) = 39366 * k + 1384 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1384) = 19683 * k + 692 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2367_mod_65536 {n : ℕ} (hn : n % 65536 = 2367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2367) = 98304 * k + 3551 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3551) = 147456 * k + 5327 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5327) = 221184 * k + 7991 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 7991) = 331776 * k + 11987 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 11987) = 497664 * k + 17981 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 17981) = 746496 * k + 26972 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 26972) = 373248 * k + 13486 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 13486) = 186624 * k + 6743 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 6743) = 279936 * k + 10115 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 10115) = 419904 * k + 15173 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 15173) = 629856 * k + 22760 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 22760) = 314928 * k + 11380 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 11380) = 157464 * k + 5690 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 5690) = 78732 * k + 2845 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 2845) = 118098 * k + 4268 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 4268) = 59049 * k + 2134 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2407_mod_65536 {n : ℕ} (hn : n % 65536 = 2407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2407) = 98304 * k + 3611 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3611) = 147456 * k + 5417 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5417) = 221184 * k + 8126 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 8126) = 110592 * k + 4063 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 4063) = 165888 * k + 6095 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 6095) = 248832 * k + 9143 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 9143) = 373248 * k + 13715 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 13715) = 559872 * k + 20573 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 20573) = 839808 * k + 30860 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 30860) = 419904 * k + 15430 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 15430) = 209952 * k + 7715 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 7715) = 314928 * k + 11573 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 11573) = 472392 * k + 17360 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 17360) = 236196 * k + 8680 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 8680) = 118098 * k + 4340 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 4340) = 59049 * k + 2170 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2495_mod_65536 {n : ℕ} (hn : n % 65536 = 2495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2495) = 98304 * k + 3743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3743) = 147456 * k + 5615 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5615) = 221184 * k + 8423 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 8423) = 331776 * k + 12635 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 12635) = 497664 * k + 18953 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 18953) = 746496 * k + 28430 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 28430) = 373248 * k + 14215 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 14215) = 559872 * k + 21323 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 21323) = 839808 * k + 31985 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 31985) = 1259712 * k + 47978 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 47978) = 629856 * k + 23989 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 23989) = 944784 * k + 35984 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 35984) = 472392 * k + 17992 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 17992) = 236196 * k + 8996 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 8996) = 118098 * k + 4498 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 4498) = 59049 * k + 2249 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2607_mod_65536 {n : ℕ} (hn : n % 65536 = 2607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2607) = 98304 * k + 3911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 3911) = 147456 * k + 5867 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 5867) = 221184 * k + 8801 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 8801) = 331776 * k + 13202 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 13202) = 165888 * k + 6601 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 6601) = 248832 * k + 9902 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 9902) = 124416 * k + 4951 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 4951) = 186624 * k + 7427 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 7427) = 279936 * k + 11141 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 11141) = 419904 * k + 16712 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 16712) = 209952 * k + 8356 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 8356) = 104976 * k + 4178 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4178) = 52488 * k + 2089 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 2089) = 78732 * k + 3134 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3134) = 39366 * k + 1567 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1567) = 59049 * k + 2351 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2671_mod_65536 {n : ℕ} (hn : n % 65536 = 2671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2671) = 98304 * k + 4007 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4007) = 147456 * k + 6011 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6011) = 221184 * k + 9017 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9017) = 331776 * k + 13526 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 13526) = 165888 * k + 6763 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 6763) = 248832 * k + 10145 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10145) = 373248 * k + 15218 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 15218) = 186624 * k + 7609 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 7609) = 279936 * k + 11414 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 11414) = 139968 * k + 5707 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 5707) = 209952 * k + 8561 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 8561) = 314928 * k + 12842 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 12842) = 157464 * k + 6421 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6421) = 236196 * k + 9632 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 9632) = 118098 * k + 4816 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 4816) = 59049 * k + 2408 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2687_mod_65536 {n : ℕ} (hn : n % 65536 = 2687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2687) = 98304 * k + 4031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4031) = 147456 * k + 6047 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6047) = 221184 * k + 9071 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9071) = 331776 * k + 13607 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 13607) = 497664 * k + 20411 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 20411) = 746496 * k + 30617 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 30617) = 1119744 * k + 45926 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 45926) = 559872 * k + 22963 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 22963) = 839808 * k + 34445 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 34445) = 1259712 * k + 51668 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 51668) = 629856 * k + 25834 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 25834) = 314928 * k + 12917 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 12917) = 472392 * k + 19376 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 19376) = 236196 * k + 9688 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 9688) = 118098 * k + 4844 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 4844) = 59049 * k + 2422 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2719_mod_65536 {n : ℕ} (hn : n % 65536 = 2719) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2719 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2719) = 98304 * k + 4079 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4079) = 147456 * k + 6119 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6119) = 221184 * k + 9179 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9179) = 331776 * k + 13769 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 13769) = 497664 * k + 20654 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 20654) = 248832 * k + 10327 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10327) = 373248 * k + 15491 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 15491) = 559872 * k + 23237 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 23237) = 839808 * k + 34856 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 34856) = 419904 * k + 17428 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 17428) = 209952 * k + 8714 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 8714) = 104976 * k + 4357 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4357) = 157464 * k + 6536 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6536) = 78732 * k + 3268 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3268) = 39366 * k + 1634 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1634) = 19683 * k + 817 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2719) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2719)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2727_mod_65536 {n : ℕ} (hn : n % 65536 = 2727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2727) = 98304 * k + 4091 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4091) = 147456 * k + 6137 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6137) = 221184 * k + 9206 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9206) = 110592 * k + 4603 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 4603) = 165888 * k + 6905 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 6905) = 248832 * k + 10358 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10358) = 124416 * k + 5179 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 5179) = 186624 * k + 7769 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 7769) = 279936 * k + 11654 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 11654) = 139968 * k + 5827 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 5827) = 209952 * k + 8741 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 8741) = 314928 * k + 13112 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 13112) = 157464 * k + 6556 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6556) = 78732 * k + 3278 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3278) = 39366 * k + 1639 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1639) = 59049 * k + 2459 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2767_mod_65536 {n : ℕ} (hn : n % 65536 = 2767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2767) = 98304 * k + 4151 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4151) = 147456 * k + 6227 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6227) = 221184 * k + 9341 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9341) = 331776 * k + 14012 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 14012) = 165888 * k + 7006 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7006) = 82944 * k + 3503 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 3503) = 124416 * k + 5255 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 5255) = 186624 * k + 7883 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 7883) = 279936 * k + 11825 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 11825) = 419904 * k + 17738 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 17738) = 209952 * k + 8869 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 8869) = 314928 * k + 13304 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 13304) = 157464 * k + 6652 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6652) = 78732 * k + 3326 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3326) = 39366 * k + 1663 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1663) = 59049 * k + 2495 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2791_mod_65536 {n : ℕ} (hn : n % 65536 = 2791) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2791 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2791) = 98304 * k + 4187 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4187) = 147456 * k + 6281 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6281) = 221184 * k + 9422 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9422) = 110592 * k + 4711 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 4711) = 165888 * k + 7067 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7067) = 248832 * k + 10601 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10601) = 373248 * k + 15902 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 15902) = 186624 * k + 7951 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 7951) = 279936 * k + 11927 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 11927) = 419904 * k + 17891 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 17891) = 629856 * k + 26837 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 26837) = 944784 * k + 40256 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 40256) = 472392 * k + 20128 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 20128) = 236196 * k + 10064 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 10064) = 118098 * k + 5032 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5032) = 59049 * k + 2516 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2791) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2791)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2799_mod_65536 {n : ℕ} (hn : n % 65536 = 2799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2799) = 98304 * k + 4199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4199) = 147456 * k + 6299 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6299) = 221184 * k + 9449 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9449) = 331776 * k + 14174 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 14174) = 165888 * k + 7087 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7087) = 248832 * k + 10631 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10631) = 373248 * k + 15947 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 15947) = 559872 * k + 23921 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 23921) = 839808 * k + 35882 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 35882) = 419904 * k + 17941 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 17941) = 629856 * k + 26912 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 26912) = 314928 * k + 13456 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 13456) = 157464 * k + 6728 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6728) = 78732 * k + 3364 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3364) = 39366 * k + 1682 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1682) = 19683 * k + 841 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2847_mod_65536 {n : ℕ} (hn : n % 65536 = 2847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2847) = 98304 * k + 4271 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4271) = 147456 * k + 6407 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6407) = 221184 * k + 9611 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9611) = 331776 * k + 14417 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 14417) = 497664 * k + 21626 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 21626) = 248832 * k + 10813 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 10813) = 373248 * k + 16220 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 16220) = 186624 * k + 8110 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8110) = 93312 * k + 4055 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 4055) = 139968 * k + 6083 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 6083) = 209952 * k + 9125 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 9125) = 314928 * k + 13688 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 13688) = 157464 * k + 6844 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6844) = 78732 * k + 3422 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3422) = 39366 * k + 1711 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1711) = 59049 * k + 2567 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2887_mod_65536 {n : ℕ} (hn : n % 65536 = 2887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2887) = 98304 * k + 4331 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4331) = 147456 * k + 6497 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6497) = 221184 * k + 9746 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9746) = 110592 * k + 4873 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 4873) = 165888 * k + 7310 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7310) = 82944 * k + 3655 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 3655) = 124416 * k + 5483 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 5483) = 186624 * k + 8225 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8225) = 279936 * k + 12338 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 12338) = 139968 * k + 6169 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 6169) = 209952 * k + 9254 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 9254) = 104976 * k + 4627 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4627) = 157464 * k + 6941 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 6941) = 236196 * k + 10412 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 10412) = 118098 * k + 5206 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5206) = 59049 * k + 2603 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2927_mod_65536 {n : ℕ} (hn : n % 65536 = 2927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2927) = 98304 * k + 4391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4391) = 147456 * k + 6587 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6587) = 221184 * k + 9881 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 9881) = 331776 * k + 14822 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 14822) = 165888 * k + 7411 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7411) = 248832 * k + 11117 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 11117) = 373248 * k + 16676 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 16676) = 186624 * k + 8338 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8338) = 93312 * k + 4169 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 4169) = 139968 * k + 6254 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 6254) = 69984 * k + 3127 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 3127) = 104976 * k + 4691 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4691) = 157464 * k + 7037 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 7037) = 236196 * k + 10556 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 10556) = 118098 * k + 5278 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5278) = 59049 * k + 2639 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_2983_mod_65536 {n : ℕ} (hn : n % 65536 = 2983) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 2983 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 2983) = 98304 * k + 4475 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4475) = 147456 * k + 6713 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6713) = 221184 * k + 10070 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 10070) = 110592 * k + 5035 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 5035) = 165888 * k + 7553 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 7553) = 248832 * k + 11330 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 11330) = 124416 * k + 5665 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 5665) = 186624 * k + 8498 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8498) = 93312 * k + 4249 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 4249) = 139968 * k + 6374 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 6374) = 69984 * k + 3187 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 3187) = 104976 * k + 4781 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4781) = 157464 * k + 7172 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 7172) = 78732 * k + 3586 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3586) = 39366 * k + 1793 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1793) = 59049 * k + 2690 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 2983) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 2983)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3039_mod_65536 {n : ℕ} (hn : n % 65536 = 3039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3039) = 98304 * k + 4559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4559) = 147456 * k + 6839 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6839) = 221184 * k + 10259 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 10259) = 331776 * k + 15389 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 15389) = 497664 * k + 23084 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 23084) = 248832 * k + 11542 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 11542) = 124416 * k + 5771 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 5771) = 186624 * k + 8657 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8657) = 279936 * k + 12986 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 12986) = 139968 * k + 6493 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 6493) = 209952 * k + 9740 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 9740) = 104976 * k + 4870 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 4870) = 52488 * k + 2435 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 2435) = 78732 * k + 3653 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3653) = 118098 * k + 5480 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5480) = 59049 * k + 2740 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3103_mod_65536 {n : ℕ} (hn : n % 65536 = 3103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3103) = 98304 * k + 4655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4655) = 147456 * k + 6983 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 6983) = 221184 * k + 10475 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 10475) = 331776 * k + 15713 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 15713) = 497664 * k + 23570 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 23570) = 248832 * k + 11785 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 11785) = 373248 * k + 17678 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 17678) = 186624 * k + 8839 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 8839) = 279936 * k + 13259 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 13259) = 419904 * k + 19889 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 19889) = 629856 * k + 29834 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 29834) = 314928 * k + 14917 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 14917) = 472392 * k + 22376 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 22376) = 236196 * k + 11188 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 11188) = 118098 * k + 5594 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5594) = 59049 * k + 2797 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3163_mod_65536 {n : ℕ} (hn : n % 65536 = 3163) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3163 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3163) = 98304 * k + 4745 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4745) = 147456 * k + 7118 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7118) = 73728 * k + 3559 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 3559) = 110592 * k + 5339 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 5339) = 165888 * k + 8009 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 8009) = 248832 * k + 12014 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 12014) = 124416 * k + 6007 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 6007) = 186624 * k + 9011 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 9011) = 279936 * k + 13517 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 13517) = 419904 * k + 20276 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 20276) = 209952 * k + 10138 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 10138) = 104976 * k + 5069 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 5069) = 157464 * k + 7604 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 7604) = 78732 * k + 3802 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3802) = 39366 * k + 1901 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1901) = 59049 * k + 2852 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3163) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3163)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3239_mod_65536 {n : ℕ} (hn : n % 65536 = 3239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3239) = 98304 * k + 4859 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4859) = 147456 * k + 7289 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7289) = 221184 * k + 10934 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 10934) = 110592 * k + 5467 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 5467) = 165888 * k + 8201 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 8201) = 248832 * k + 12302 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 12302) = 124416 * k + 6151 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 6151) = 186624 * k + 9227 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 9227) = 279936 * k + 13841 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 13841) = 419904 * k + 20762 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 20762) = 209952 * k + 10381 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 10381) = 314928 * k + 15572 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 15572) = 157464 * k + 7786 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 7786) = 78732 * k + 3893 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3893) = 118098 * k + 5840 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 5840) = 59049 * k + 2920 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3303_mod_65536 {n : ℕ} (hn : n % 65536 = 3303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3303) = 98304 * k + 4955 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 4955) = 147456 * k + 7433 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7433) = 221184 * k + 11150 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 11150) = 110592 * k + 5575 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 5575) = 165888 * k + 8363 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 8363) = 248832 * k + 12545 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 12545) = 373248 * k + 18818 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 18818) = 186624 * k + 9409 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 9409) = 279936 * k + 14114 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 14114) = 139968 * k + 7057 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 7057) = 209952 * k + 10586 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 10586) = 104976 * k + 5293 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 5293) = 157464 * k + 7940 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 7940) = 78732 * k + 3970 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 3970) = 39366 * k + 1985 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 1985) = 59049 * k + 2978 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3487_mod_65536 {n : ℕ} (hn : n % 65536 = 3487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3487) = 98304 * k + 5231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5231) = 147456 * k + 7847 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7847) = 221184 * k + 11771 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 11771) = 331776 * k + 17657 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 17657) = 497664 * k + 26486 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 26486) = 248832 * k + 13243 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 13243) = 373248 * k + 19865 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 19865) = 559872 * k + 29798 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 29798) = 279936 * k + 14899 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 14899) = 419904 * k + 22349 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 22349) = 629856 * k + 33524 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 33524) = 314928 * k + 16762 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 16762) = 157464 * k + 8381 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 8381) = 236196 * k + 12572 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 12572) = 118098 * k + 6286 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 6286) = 59049 * k + 3143 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3535_mod_65536 {n : ℕ} (hn : n % 65536 = 3535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3535) = 98304 * k + 5303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5303) = 147456 * k + 7955 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7955) = 221184 * k + 11933 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 11933) = 331776 * k + 17900 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 17900) = 165888 * k + 8950 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 8950) = 82944 * k + 4475 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 4475) = 124416 * k + 6713 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 6713) = 186624 * k + 10070 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 10070) = 93312 * k + 5035 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 5035) = 139968 * k + 7553 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 7553) = 209952 * k + 11330 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 11330) = 104976 * k + 5665 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 5665) = 157464 * k + 8498 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 8498) = 78732 * k + 4249 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4249) = 118098 * k + 6374 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 6374) = 59049 * k + 3187 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3551_mod_65536 {n : ℕ} (hn : n % 65536 = 3551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3551) = 98304 * k + 5327 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5327) = 147456 * k + 7991 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 7991) = 221184 * k + 11987 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 11987) = 331776 * k + 17981 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 17981) = 497664 * k + 26972 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 26972) = 248832 * k + 13486 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 13486) = 124416 * k + 6743 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 6743) = 186624 * k + 10115 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 10115) = 279936 * k + 15173 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 15173) = 419904 * k + 22760 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 22760) = 209952 * k + 11380 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 11380) = 104976 * k + 5690 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 5690) = 52488 * k + 2845 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 2845) = 78732 * k + 4268 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4268) = 39366 * k + 2134 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2134) = 19683 * k + 1067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3611_mod_65536 {n : ℕ} (hn : n % 65536 = 3611) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3611 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3611) = 98304 * k + 5417 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5417) = 147456 * k + 8126 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 8126) = 73728 * k + 4063 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 4063) = 110592 * k + 6095 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 6095) = 165888 * k + 9143 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 9143) = 248832 * k + 13715 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 13715) = 373248 * k + 20573 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 20573) = 559872 * k + 30860 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 30860) = 279936 * k + 15430 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 15430) = 139968 * k + 7715 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 7715) = 209952 * k + 11573 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 11573) = 314928 * k + 17360 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 17360) = 157464 * k + 8680 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 8680) = 78732 * k + 4340 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4340) = 39366 * k + 2170 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2170) = 19683 * k + 1085 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3611) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3611)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3695_mod_65536 {n : ℕ} (hn : n % 65536 = 3695) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3695 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3695) = 98304 * k + 5543 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5543) = 147456 * k + 8315 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 8315) = 221184 * k + 12473 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 12473) = 331776 * k + 18710 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 18710) = 165888 * k + 9355 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 9355) = 248832 * k + 14033 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 14033) = 373248 * k + 21050 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 21050) = 186624 * k + 10525 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 10525) = 279936 * k + 15788 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 15788) = 139968 * k + 7894 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 7894) = 69984 * k + 3947 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 3947) = 104976 * k + 5921 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 5921) = 157464 * k + 8882 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 8882) = 78732 * k + 4441 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4441) = 118098 * k + 6662 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 6662) = 59049 * k + 3331 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3695) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3695)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3743_mod_65536 {n : ℕ} (hn : n % 65536 = 3743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3743) = 98304 * k + 5615 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5615) = 147456 * k + 8423 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 8423) = 221184 * k + 12635 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 12635) = 331776 * k + 18953 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 18953) = 497664 * k + 28430 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 28430) = 248832 * k + 14215 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 14215) = 373248 * k + 21323 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 21323) = 559872 * k + 31985 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 31985) = 839808 * k + 47978 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 47978) = 419904 * k + 23989 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 23989) = 629856 * k + 35984 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 35984) = 314928 * k + 17992 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 17992) = 157464 * k + 8996 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 8996) = 78732 * k + 4498 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4498) = 39366 * k + 2249 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2249) = 59049 * k + 3374 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3815_mod_65536 {n : ℕ} (hn : n % 65536 = 3815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3815) = 98304 * k + 5723 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5723) = 147456 * k + 8585 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 8585) = 221184 * k + 12878 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 12878) = 110592 * k + 6439 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 6439) = 165888 * k + 9659 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 9659) = 248832 * k + 14489 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 14489) = 373248 * k + 21734 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 21734) = 186624 * k + 10867 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 10867) = 279936 * k + 16301 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 16301) = 419904 * k + 24452 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 24452) = 209952 * k + 12226 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 12226) = 104976 * k + 6113 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 6113) = 157464 * k + 9170 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 9170) = 78732 * k + 4585 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4585) = 118098 * k + 6878 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 6878) = 59049 * k + 3439 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_3835_mod_65536 {n : ℕ} (hn : n % 65536 = 3835) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 3835 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 3835) = 98304 * k + 5753 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 5753) = 147456 * k + 8630 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 8630) = 73728 * k + 4315 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 4315) = 110592 * k + 6473 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 6473) = 165888 * k + 9710 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 9710) = 82944 * k + 4855 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 4855) = 124416 * k + 7283 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 7283) = 186624 * k + 10925 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 10925) = 279936 * k + 16388 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 16388) = 139968 * k + 8194 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 8194) = 69984 * k + 4097 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 4097) = 104976 * k + 6146 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 6146) = 52488 * k + 3073 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 3073) = 78732 * k + 4610 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4610) = 39366 * k + 2305 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2305) = 59049 * k + 3458 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 3835) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 3835)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4007_mod_65536 {n : ℕ} (hn : n % 65536 = 4007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4007) = 98304 * k + 6011 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6011) = 147456 * k + 9017 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9017) = 221184 * k + 13526 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 13526) = 110592 * k + 6763 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 6763) = 165888 * k + 10145 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 10145) = 248832 * k + 15218 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 15218) = 124416 * k + 7609 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 7609) = 186624 * k + 11414 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 11414) = 93312 * k + 5707 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 5707) = 139968 * k + 8561 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 8561) = 209952 * k + 12842 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 12842) = 104976 * k + 6421 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 6421) = 157464 * k + 9632 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 9632) = 78732 * k + 4816 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4816) = 39366 * k + 2408 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2408) = 19683 * k + 1204 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4031_mod_65536 {n : ℕ} (hn : n % 65536 = 4031) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4031 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4031) = 98304 * k + 6047 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6047) = 147456 * k + 9071 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9071) = 221184 * k + 13607 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 13607) = 331776 * k + 20411 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 20411) = 497664 * k + 30617 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 30617) = 746496 * k + 45926 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 45926) = 373248 * k + 22963 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 22963) = 559872 * k + 34445 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 34445) = 839808 * k + 51668 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 51668) = 419904 * k + 25834 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 25834) = 209952 * k + 12917 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 12917) = 314928 * k + 19376 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 19376) = 157464 * k + 9688 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 9688) = 78732 * k + 4844 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 4844) = 39366 * k + 2422 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2422) = 19683 * k + 1211 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4031) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4031)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4187_mod_65536 {n : ℕ} (hn : n % 65536 = 4187) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4187 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4187) = 98304 * k + 6281 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6281) = 147456 * k + 9422 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9422) = 73728 * k + 4711 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 4711) = 110592 * k + 7067 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 7067) = 165888 * k + 10601 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 10601) = 248832 * k + 15902 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 15902) = 124416 * k + 7951 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 7951) = 186624 * k + 11927 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 11927) = 279936 * k + 17891 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 17891) = 419904 * k + 26837 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 26837) = 629856 * k + 40256 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 40256) = 314928 * k + 20128 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 20128) = 157464 * k + 10064 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 10064) = 78732 * k + 5032 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5032) = 39366 * k + 2516 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2516) = 19683 * k + 1258 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4187) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4187)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4287_mod_65536 {n : ℕ} (hn : n % 65536 = 4287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4287) = 98304 * k + 6431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6431) = 147456 * k + 9647 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9647) = 221184 * k + 14471 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 14471) = 331776 * k + 21707 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 21707) = 497664 * k + 32561 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 32561) = 746496 * k + 48842 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 48842) = 373248 * k + 24421 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 24421) = 559872 * k + 36632 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 36632) = 279936 * k + 18316 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 18316) = 139968 * k + 9158 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 9158) = 69984 * k + 4579 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 4579) = 104976 * k + 6869 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 6869) = 157464 * k + 10304 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 10304) = 78732 * k + 5152 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5152) = 39366 * k + 2576 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2576) = 19683 * k + 1288 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4319_mod_65536 {n : ℕ} (hn : n % 65536 = 4319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4319) = 98304 * k + 6479 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6479) = 147456 * k + 9719 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9719) = 221184 * k + 14579 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 14579) = 331776 * k + 21869 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 21869) = 497664 * k + 32804 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 32804) = 248832 * k + 16402 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 16402) = 124416 * k + 8201 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 8201) = 186624 * k + 12302 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 12302) = 93312 * k + 6151 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 6151) = 139968 * k + 9227 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 9227) = 209952 * k + 13841 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 13841) = 314928 * k + 20762 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 20762) = 157464 * k + 10381 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 10381) = 236196 * k + 15572 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 15572) = 118098 * k + 7786 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 7786) = 59049 * k + 3893 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4335_mod_65536 {n : ℕ} (hn : n % 65536 = 4335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4335) = 98304 * k + 6503 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6503) = 147456 * k + 9755 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9755) = 221184 * k + 14633 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 14633) = 331776 * k + 21950 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 21950) = 165888 * k + 10975 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 10975) = 248832 * k + 16463 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 16463) = 373248 * k + 24695 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 24695) = 559872 * k + 37043 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 37043) = 839808 * k + 55565 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 55565) = 1259712 * k + 83348 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 83348) = 629856 * k + 41674 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 41674) = 314928 * k + 20837 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 20837) = 472392 * k + 31256 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 31256) = 236196 * k + 15628 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 15628) = 118098 * k + 7814 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 7814) = 59049 * k + 3907 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4379_mod_65536 {n : ℕ} (hn : n % 65536 = 4379) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4379 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4379) = 98304 * k + 6569 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6569) = 147456 * k + 9854 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 9854) = 73728 * k + 4927 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 4927) = 110592 * k + 7391 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 7391) = 165888 * k + 11087 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 11087) = 248832 * k + 16631 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 16631) = 373248 * k + 24947 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 24947) = 559872 * k + 37421 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 37421) = 839808 * k + 56132 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 56132) = 419904 * k + 28066 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 28066) = 209952 * k + 14033 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 14033) = 314928 * k + 21050 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 21050) = 157464 * k + 10525 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 10525) = 236196 * k + 15788 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 15788) = 118098 * k + 7894 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 7894) = 59049 * k + 3947 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4379) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4379)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4455_mod_65536 {n : ℕ} (hn : n % 65536 = 4455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4455) = 98304 * k + 6683 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6683) = 147456 * k + 10025 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10025) = 221184 * k + 15038 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 15038) = 110592 * k + 7519 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 7519) = 165888 * k + 11279 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 11279) = 248832 * k + 16919 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 16919) = 373248 * k + 25379 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 25379) = 559872 * k + 38069 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 38069) = 839808 * k + 57104 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 57104) = 419904 * k + 28552 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 28552) = 209952 * k + 14276 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 14276) = 104976 * k + 7138 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7138) = 52488 * k + 3569 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 3569) = 78732 * k + 5354 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5354) = 39366 * k + 2677 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2677) = 59049 * k + 4016 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4507_mod_65536 {n : ℕ} (hn : n % 65536 = 4507) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4507 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4507) = 98304 * k + 6761 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6761) = 147456 * k + 10142 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10142) = 73728 * k + 5071 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 5071) = 110592 * k + 7607 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 7607) = 165888 * k + 11411 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 11411) = 248832 * k + 17117 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 17117) = 373248 * k + 25676 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 25676) = 186624 * k + 12838 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 12838) = 93312 * k + 6419 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 6419) = 139968 * k + 9629 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 9629) = 209952 * k + 14444 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 14444) = 104976 * k + 7222 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7222) = 52488 * k + 3611 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 3611) = 78732 * k + 5417 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5417) = 118098 * k + 8126 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8126) = 59049 * k + 4063 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4507) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4507)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4635_mod_65536 {n : ℕ} (hn : n % 65536 = 4635) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4635 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4635) = 98304 * k + 6953 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6953) = 147456 * k + 10430 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10430) = 73728 * k + 5215 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 5215) = 110592 * k + 7823 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 7823) = 165888 * k + 11735 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 11735) = 248832 * k + 17603 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 17603) = 373248 * k + 26405 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 26405) = 559872 * k + 39608 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 39608) = 279936 * k + 19804 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 19804) = 139968 * k + 9902 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 9902) = 69984 * k + 4951 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 4951) = 104976 * k + 7427 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7427) = 157464 * k + 11141 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 11141) = 236196 * k + 16712 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 16712) = 118098 * k + 8356 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8356) = 59049 * k + 4178 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4635) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4635)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4655_mod_65536 {n : ℕ} (hn : n % 65536 = 4655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4655) = 98304 * k + 6983 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 6983) = 147456 * k + 10475 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10475) = 221184 * k + 15713 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 15713) = 331776 * k + 23570 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 23570) = 165888 * k + 11785 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 11785) = 248832 * k + 17678 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 17678) = 124416 * k + 8839 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 8839) = 186624 * k + 13259 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 13259) = 279936 * k + 19889 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 19889) = 419904 * k + 29834 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 29834) = 209952 * k + 14917 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 14917) = 314928 * k + 22376 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 22376) = 157464 * k + 11188 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 11188) = 78732 * k + 5594 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5594) = 39366 * k + 2797 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2797) = 59049 * k + 4196 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4775_mod_65536 {n : ℕ} (hn : n % 65536 = 4775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4775) = 98304 * k + 7163 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7163) = 147456 * k + 10745 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10745) = 221184 * k + 16118 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16118) = 110592 * k + 8059 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 8059) = 165888 * k + 12089 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 12089) = 248832 * k + 18134 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 18134) = 124416 * k + 9067 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 9067) = 186624 * k + 13601 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 13601) = 279936 * k + 20402 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 20402) = 139968 * k + 10201 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 10201) = 209952 * k + 15302 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 15302) = 104976 * k + 7651 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7651) = 157464 * k + 11477 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 11477) = 236196 * k + 17216 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 17216) = 118098 * k + 8608 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8608) = 59049 * k + 4304 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4799_mod_65536 {n : ℕ} (hn : n % 65536 = 4799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4799) = 98304 * k + 7199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7199) = 147456 * k + 10799 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10799) = 221184 * k + 16199 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16199) = 331776 * k + 24299 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 24299) = 497664 * k + 36449 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 36449) = 746496 * k + 54674 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 54674) = 373248 * k + 27337 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 27337) = 559872 * k + 41006 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 41006) = 279936 * k + 20503 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 20503) = 419904 * k + 30755 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 30755) = 629856 * k + 46133 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 46133) = 944784 * k + 69200 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 69200) = 472392 * k + 34600 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 34600) = 236196 * k + 17300 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 17300) = 118098 * k + 8650 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8650) = 59049 * k + 4325 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4815_mod_65536 {n : ℕ} (hn : n % 65536 = 4815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4815) = 98304 * k + 7223 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7223) = 147456 * k + 10835 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10835) = 221184 * k + 16253 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16253) = 331776 * k + 24380 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 24380) = 165888 * k + 12190 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 12190) = 82944 * k + 6095 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 6095) = 124416 * k + 9143 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 9143) = 186624 * k + 13715 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 13715) = 279936 * k + 20573 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 20573) = 419904 * k + 30860 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 30860) = 209952 * k + 15430 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 15430) = 104976 * k + 7715 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7715) = 157464 * k + 11573 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 11573) = 236196 * k + 17360 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 17360) = 118098 * k + 8680 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8680) = 59049 * k + 4340 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4859_mod_65536 {n : ℕ} (hn : n % 65536 = 4859) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4859 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4859) = 98304 * k + 7289 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7289) = 147456 * k + 10934 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 10934) = 73728 * k + 5467 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 5467) = 110592 * k + 8201 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 8201) = 165888 * k + 12302 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 12302) = 82944 * k + 6151 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 6151) = 124416 * k + 9227 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 9227) = 186624 * k + 13841 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 13841) = 279936 * k + 20762 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 20762) = 139968 * k + 10381 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 10381) = 209952 * k + 15572 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 15572) = 104976 * k + 7786 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7786) = 52488 * k + 3893 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 3893) = 78732 * k + 5840 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5840) = 39366 * k + 2920 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 2920) = 19683 * k + 1460 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4859) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4859)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4895_mod_65536 {n : ℕ} (hn : n % 65536 = 4895) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4895 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4895) = 98304 * k + 7343 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7343) = 147456 * k + 11015 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11015) = 221184 * k + 16523 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16523) = 331776 * k + 24785 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 24785) = 497664 * k + 37178 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 37178) = 248832 * k + 18589 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 18589) = 373248 * k + 27884 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 27884) = 186624 * k + 13942 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 13942) = 93312 * k + 6971 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 6971) = 139968 * k + 10457 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 10457) = 209952 * k + 15686 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 15686) = 104976 * k + 7843 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7843) = 157464 * k + 11765 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 11765) = 236196 * k + 17648 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 17648) = 118098 * k + 8824 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8824) = 59049 * k + 4412 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4895) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4895)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4927_mod_65536 {n : ℕ} (hn : n % 65536 = 4927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4927) = 98304 * k + 7391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7391) = 147456 * k + 11087 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11087) = 221184 * k + 16631 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16631) = 331776 * k + 24947 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 24947) = 497664 * k + 37421 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 37421) = 746496 * k + 56132 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 56132) = 373248 * k + 28066 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 28066) = 186624 * k + 14033 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 14033) = 279936 * k + 21050 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 21050) = 139968 * k + 10525 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 10525) = 209952 * k + 15788 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 15788) = 104976 * k + 7894 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 7894) = 52488 * k + 3947 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 3947) = 78732 * k + 5921 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 5921) = 118098 * k + 8882 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8882) = 59049 * k + 4441 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_4991_mod_65536 {n : ℕ} (hn : n % 65536 = 4991) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 4991 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 4991) = 98304 * k + 7487 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7487) = 147456 * k + 11231 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11231) = 221184 * k + 16847 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 16847) = 331776 * k + 25271 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 25271) = 497664 * k + 37907 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 37907) = 746496 * k + 56861 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 56861) = 1119744 * k + 85292 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 85292) = 559872 * k + 42646 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 42646) = 279936 * k + 21323 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 21323) = 419904 * k + 31985 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 31985) = 629856 * k + 47978 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 47978) = 314928 * k + 23989 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 23989) = 472392 * k + 35984 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 35984) = 236196 * k + 17992 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 17992) = 118098 * k + 8996 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 8996) = 59049 * k + 4498 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 4991) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 4991)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5087_mod_65536 {n : ℕ} (hn : n % 65536 = 5087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5087) = 98304 * k + 7631 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7631) = 147456 * k + 11447 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11447) = 221184 * k + 17171 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 17171) = 331776 * k + 25757 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 25757) = 497664 * k + 38636 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 38636) = 248832 * k + 19318 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 19318) = 124416 * k + 9659 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 9659) = 186624 * k + 14489 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 14489) = 279936 * k + 21734 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 21734) = 139968 * k + 10867 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 10867) = 209952 * k + 16301 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 16301) = 314928 * k + 24452 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 24452) = 157464 * k + 12226 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 12226) = 78732 * k + 6113 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6113) = 118098 * k + 9170 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 9170) = 59049 * k + 4585 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5231_mod_65536 {n : ℕ} (hn : n % 65536 = 5231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5231) = 98304 * k + 7847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7847) = 147456 * k + 11771 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11771) = 221184 * k + 17657 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 17657) = 331776 * k + 26486 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 26486) = 165888 * k + 13243 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 13243) = 248832 * k + 19865 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 19865) = 373248 * k + 29798 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 29798) = 186624 * k + 14899 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 14899) = 279936 * k + 22349 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 22349) = 419904 * k + 33524 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 33524) = 209952 * k + 16762 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 16762) = 104976 * k + 8381 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 8381) = 157464 * k + 12572 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 12572) = 78732 * k + 6286 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6286) = 39366 * k + 3143 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3143) = 59049 * k + 4715 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5311_mod_65536 {n : ℕ} (hn : n % 65536 = 5311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5311) = 98304 * k + 7967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 7967) = 147456 * k + 11951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 11951) = 221184 * k + 17927 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 17927) = 331776 * k + 26891 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 26891) = 497664 * k + 40337 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 40337) = 746496 * k + 60506 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 60506) = 373248 * k + 30253 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 30253) = 559872 * k + 45380 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 45380) = 279936 * k + 22690 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 22690) = 139968 * k + 11345 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 11345) = 209952 * k + 17018 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 17018) = 104976 * k + 8509 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 8509) = 157464 * k + 12764 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 12764) = 78732 * k + 6382 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6382) = 39366 * k + 3191 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3191) = 59049 * k + 4787 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5343_mod_65536 {n : ℕ} (hn : n % 65536 = 5343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5343) = 98304 * k + 8015 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8015) = 147456 * k + 12023 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12023) = 221184 * k + 18035 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18035) = 331776 * k + 27053 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 27053) = 497664 * k + 40580 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 40580) = 248832 * k + 20290 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 20290) = 124416 * k + 10145 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 10145) = 186624 * k + 15218 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 15218) = 93312 * k + 7609 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 7609) = 139968 * k + 11414 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 11414) = 69984 * k + 5707 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 5707) = 104976 * k + 8561 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 8561) = 157464 * k + 12842 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 12842) = 78732 * k + 6421 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6421) = 118098 * k + 9632 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 9632) = 59049 * k + 4816 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5375_mod_65536 {n : ℕ} (hn : n % 65536 = 5375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5375) = 98304 * k + 8063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8063) = 147456 * k + 12095 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12095) = 221184 * k + 18143 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18143) = 331776 * k + 27215 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 27215) = 497664 * k + 40823 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 40823) = 746496 * k + 61235 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 61235) = 1119744 * k + 91853 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 91853) = 1679616 * k + 137780 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 137780) = 839808 * k + 68890 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 68890) = 419904 * k + 34445 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 34445) = 629856 * k + 51668 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 51668) = 314928 * k + 25834 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 25834) = 157464 * k + 12917 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 12917) = 236196 * k + 19376 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 19376) = 118098 * k + 9688 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 9688) = 59049 * k + 4844 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5423_mod_65536 {n : ℕ} (hn : n % 65536 = 5423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5423) = 98304 * k + 8135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8135) = 147456 * k + 12203 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12203) = 221184 * k + 18305 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18305) = 331776 * k + 27458 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 27458) = 165888 * k + 13729 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 13729) = 248832 * k + 20594 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 20594) = 124416 * k + 10297 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 10297) = 186624 * k + 15446 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 15446) = 93312 * k + 7723 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 7723) = 139968 * k + 11585 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 11585) = 209952 * k + 17378 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 17378) = 104976 * k + 8689 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 8689) = 157464 * k + 13034 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 13034) = 78732 * k + 6517 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6517) = 118098 * k + 9776 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 9776) = 59049 * k + 4888 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5439_mod_65536 {n : ℕ} (hn : n % 65536 = 5439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5439) = 98304 * k + 8159 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8159) = 147456 * k + 12239 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12239) = 221184 * k + 18359 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18359) = 331776 * k + 27539 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 27539) = 497664 * k + 41309 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 41309) = 746496 * k + 61964 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 61964) = 373248 * k + 30982 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 30982) = 186624 * k + 15491 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 15491) = 279936 * k + 23237 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 23237) = 419904 * k + 34856 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 34856) = 209952 * k + 17428 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 17428) = 104976 * k + 8714 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 8714) = 52488 * k + 4357 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 4357) = 78732 * k + 6536 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6536) = 39366 * k + 3268 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3268) = 19683 * k + 1634 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5583_mod_65536 {n : ℕ} (hn : n % 65536 = 5583) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5583 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5583) = 98304 * k + 8375 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8375) = 147456 * k + 12563 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12563) = 221184 * k + 18845 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18845) = 331776 * k + 28268 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 28268) = 165888 * k + 14134 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 14134) = 82944 * k + 7067 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 7067) = 124416 * k + 10601 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 10601) = 186624 * k + 15902 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 15902) = 93312 * k + 7951 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 7951) = 139968 * k + 11927 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 11927) = 209952 * k + 17891 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 17891) = 314928 * k + 26837 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 26837) = 472392 * k + 40256 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 40256) = 236196 * k + 20128 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 20128) = 118098 * k + 10064 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 10064) = 59049 * k + 5032 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5583) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5583)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5599_mod_65536 {n : ℕ} (hn : n % 65536 = 5599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5599) = 98304 * k + 8399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8399) = 147456 * k + 12599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12599) = 221184 * k + 18899 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 18899) = 331776 * k + 28349 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 28349) = 497664 * k + 42524 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 42524) = 248832 * k + 21262 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 21262) = 124416 * k + 10631 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 10631) = 186624 * k + 15947 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 15947) = 279936 * k + 23921 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 23921) = 419904 * k + 35882 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 35882) = 209952 * k + 17941 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 17941) = 314928 * k + 26912 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 26912) = 157464 * k + 13456 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 13456) = 78732 * k + 6728 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6728) = 39366 * k + 3364 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3364) = 19683 * k + 1682 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5631_mod_65536 {n : ℕ} (hn : n % 65536 = 5631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5631) = 98304 * k + 8447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8447) = 147456 * k + 12671 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12671) = 221184 * k + 19007 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 19007) = 331776 * k + 28511 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 28511) = 497664 * k + 42767 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 42767) = 746496 * k + 64151 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 64151) = 1119744 * k + 96227 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 96227) = 1679616 * k + 144341 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 144341) = 2519424 * k + 216512 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 216512) = 1259712 * k + 108256 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 108256) = 629856 * k + 54128 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 54128) = 314928 * k + 27064 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 27064) = 157464 * k + 13532 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 13532) = 78732 * k + 6766 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6766) = 39366 * k + 3383 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3383) = 59049 * k + 5075 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5663_mod_65536 {n : ℕ} (hn : n % 65536 = 5663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5663) = 98304 * k + 8495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8495) = 147456 * k + 12743 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12743) = 221184 * k + 19115 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 19115) = 331776 * k + 28673 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 28673) = 497664 * k + 43010 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 43010) = 248832 * k + 21505 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 21505) = 373248 * k + 32258 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 32258) = 186624 * k + 16129 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 16129) = 279936 * k + 24194 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 24194) = 139968 * k + 12097 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 12097) = 209952 * k + 18146 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 18146) = 104976 * k + 9073 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 9073) = 157464 * k + 13610 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 13610) = 78732 * k + 6805 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6805) = 118098 * k + 10208 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 10208) = 59049 * k + 5104 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5723_mod_65536 {n : ℕ} (hn : n % 65536 = 5723) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5723 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5723) = 98304 * k + 8585 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8585) = 147456 * k + 12878 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 12878) = 73728 * k + 6439 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 6439) = 110592 * k + 9659 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 9659) = 165888 * k + 14489 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 14489) = 248832 * k + 21734 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 21734) = 124416 * k + 10867 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 10867) = 186624 * k + 16301 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 16301) = 279936 * k + 24452 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 24452) = 139968 * k + 12226 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 12226) = 69984 * k + 6113 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 6113) = 104976 * k + 9170 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 9170) = 52488 * k + 4585 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 4585) = 78732 * k + 6878 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6878) = 39366 * k + 3439 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3439) = 59049 * k + 5159 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5723) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5723)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5823_mod_65536 {n : ℕ} (hn : n % 65536 = 5823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5823) = 98304 * k + 8735 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8735) = 147456 * k + 13103 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 13103) = 221184 * k + 19655 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 19655) = 331776 * k + 29483 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 29483) = 497664 * k + 44225 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 44225) = 746496 * k + 66338 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 66338) = 373248 * k + 33169 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 33169) = 559872 * k + 49754 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 49754) = 279936 * k + 24877 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 24877) = 419904 * k + 37316 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 37316) = 209952 * k + 18658 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 18658) = 104976 * k + 9329 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 9329) = 157464 * k + 13994 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 13994) = 78732 * k + 6997 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 6997) = 118098 * k + 10496 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 10496) = 59049 * k + 5248 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_5863_mod_65536 {n : ℕ} (hn : n % 65536 = 5863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 5863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 5863) = 98304 * k + 8795 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 8795) = 147456 * k + 13193 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 13193) = 221184 * k + 19790 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 19790) = 110592 * k + 9895 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 9895) = 165888 * k + 14843 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 14843) = 248832 * k + 22265 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 22265) = 373248 * k + 33398 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 33398) = 186624 * k + 16699 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 16699) = 279936 * k + 25049 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 25049) = 419904 * k + 37574 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 37574) = 209952 * k + 18787 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 18787) = 314928 * k + 28181 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 28181) = 472392 * k + 42272 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 42272) = 236196 * k + 21136 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 21136) = 118098 * k + 10568 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 10568) = 59049 * k + 5284 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 5863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 5863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6175_mod_65536 {n : ℕ} (hn : n % 65536 = 6175) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6175 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6175) = 98304 * k + 9263 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9263) = 147456 * k + 13895 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 13895) = 221184 * k + 20843 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 20843) = 331776 * k + 31265 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 31265) = 497664 * k + 46898 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 46898) = 248832 * k + 23449 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 23449) = 373248 * k + 35174 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 35174) = 186624 * k + 17587 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 17587) = 279936 * k + 26381 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 26381) = 419904 * k + 39572 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 39572) = 209952 * k + 19786 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 19786) = 104976 * k + 9893 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 9893) = 157464 * k + 14840 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 14840) = 78732 * k + 7420 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7420) = 39366 * k + 3710 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3710) = 19683 * k + 1855 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6175) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6175)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6207_mod_65536 {n : ℕ} (hn : n % 65536 = 6207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6207) = 98304 * k + 9311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9311) = 147456 * k + 13967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 13967) = 221184 * k + 20951 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 20951) = 331776 * k + 31427 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 31427) = 497664 * k + 47141 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 47141) = 746496 * k + 70712 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 70712) = 373248 * k + 35356 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 35356) = 186624 * k + 17678 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 17678) = 93312 * k + 8839 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 8839) = 139968 * k + 13259 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 13259) = 209952 * k + 19889 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 19889) = 314928 * k + 29834 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 29834) = 157464 * k + 14917 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 14917) = 236196 * k + 22376 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 22376) = 118098 * k + 11188 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11188) = 59049 * k + 5594 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6215_mod_65536 {n : ℕ} (hn : n % 65536 = 6215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6215) = 98304 * k + 9323 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9323) = 147456 * k + 13985 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 13985) = 221184 * k + 20978 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 20978) = 110592 * k + 10489 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 10489) = 165888 * k + 15734 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 15734) = 82944 * k + 7867 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 7867) = 124416 * k + 11801 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 11801) = 186624 * k + 17702 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 17702) = 93312 * k + 8851 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 8851) = 139968 * k + 13277 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 13277) = 209952 * k + 19916 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 19916) = 104976 * k + 9958 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 9958) = 52488 * k + 4979 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 4979) = 78732 * k + 7469 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7469) = 118098 * k + 11204 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11204) = 59049 * k + 5602 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6247_mod_65536 {n : ℕ} (hn : n % 65536 = 6247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6247) = 98304 * k + 9371 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9371) = 147456 * k + 14057 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14057) = 221184 * k + 21086 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 21086) = 110592 * k + 10543 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 10543) = 165888 * k + 15815 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 15815) = 248832 * k + 23723 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 23723) = 373248 * k + 35585 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 35585) = 559872 * k + 53378 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 53378) = 279936 * k + 26689 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 26689) = 419904 * k + 40034 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 40034) = 209952 * k + 20017 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 20017) = 314928 * k + 30026 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 30026) = 157464 * k + 15013 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 15013) = 236196 * k + 22520 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 22520) = 118098 * k + 11260 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11260) = 59049 * k + 5630 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6255_mod_65536 {n : ℕ} (hn : n % 65536 = 6255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6255) = 98304 * k + 9383 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9383) = 147456 * k + 14075 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14075) = 221184 * k + 21113 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 21113) = 331776 * k + 31670 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 31670) = 165888 * k + 15835 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 15835) = 248832 * k + 23753 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 23753) = 373248 * k + 35630 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 35630) = 186624 * k + 17815 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 17815) = 279936 * k + 26723 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 26723) = 419904 * k + 40085 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 40085) = 629856 * k + 60128 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 60128) = 314928 * k + 30064 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 30064) = 157464 * k + 15032 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 15032) = 78732 * k + 7516 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7516) = 39366 * k + 3758 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3758) = 19683 * k + 1879 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6375_mod_65536 {n : ℕ} (hn : n % 65536 = 6375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6375) = 98304 * k + 9563 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9563) = 147456 * k + 14345 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14345) = 221184 * k + 21518 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 21518) = 110592 * k + 10759 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 10759) = 165888 * k + 16139 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16139) = 248832 * k + 24209 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 24209) = 373248 * k + 36314 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 36314) = 186624 * k + 18157 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 18157) = 279936 * k + 27236 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 27236) = 139968 * k + 13618 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 13618) = 69984 * k + 6809 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 6809) = 104976 * k + 10214 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10214) = 52488 * k + 5107 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 5107) = 78732 * k + 7661 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7661) = 118098 * k + 11492 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11492) = 59049 * k + 5746 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6503_mod_65536 {n : ℕ} (hn : n % 65536 = 6503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6503) = 98304 * k + 9755 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9755) = 147456 * k + 14633 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14633) = 221184 * k + 21950 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 21950) = 110592 * k + 10975 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 10975) = 165888 * k + 16463 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16463) = 248832 * k + 24695 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 24695) = 373248 * k + 37043 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 37043) = 559872 * k + 55565 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 55565) = 839808 * k + 83348 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 83348) = 419904 * k + 41674 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 41674) = 209952 * k + 20837 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 20837) = 314928 * k + 31256 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 31256) = 157464 * k + 15628 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 15628) = 78732 * k + 7814 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7814) = 39366 * k + 3907 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3907) = 59049 * k + 5861 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6555_mod_65536 {n : ℕ} (hn : n % 65536 = 6555) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6555 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6555) = 98304 * k + 9833 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9833) = 147456 * k + 14750 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14750) = 73728 * k + 7375 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 7375) = 110592 * k + 11063 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 11063) = 165888 * k + 16595 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16595) = 248832 * k + 24893 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 24893) = 373248 * k + 37340 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 37340) = 186624 * k + 18670 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 18670) = 93312 * k + 9335 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 9335) = 139968 * k + 14003 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14003) = 209952 * k + 21005 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 21005) = 314928 * k + 31508 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 31508) = 157464 * k + 15754 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 15754) = 78732 * k + 7877 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7877) = 118098 * k + 11816 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11816) = 59049 * k + 5908 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6555) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6555)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6607_mod_65536 {n : ℕ} (hn : n % 65536 = 6607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6607) = 98304 * k + 9911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9911) = 147456 * k + 14867 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14867) = 221184 * k + 22301 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 22301) = 331776 * k + 33452 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 33452) = 165888 * k + 16726 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16726) = 82944 * k + 8363 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 8363) = 124416 * k + 12545 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 12545) = 186624 * k + 18818 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 18818) = 93312 * k + 9409 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 9409) = 139968 * k + 14114 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14114) = 69984 * k + 7057 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 7057) = 104976 * k + 10586 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10586) = 52488 * k + 5293 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 5293) = 78732 * k + 7940 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 7940) = 39366 * k + 3970 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 3970) = 19683 * k + 1985 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6639_mod_65536 {n : ℕ} (hn : n % 65536 = 6639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6639) = 98304 * k + 9959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 9959) = 147456 * k + 14939 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 14939) = 221184 * k + 22409 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 22409) = 331776 * k + 33614 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 33614) = 165888 * k + 16807 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16807) = 248832 * k + 25211 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 25211) = 373248 * k + 37817 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 37817) = 559872 * k + 56726 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 56726) = 279936 * k + 28363 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 28363) = 419904 * k + 42545 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 42545) = 629856 * k + 63818 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 63818) = 314928 * k + 31909 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 31909) = 472392 * k + 47864 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 47864) = 236196 * k + 23932 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 23932) = 118098 * k + 11966 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 11966) = 59049 * k + 5983 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6703_mod_65536 {n : ℕ} (hn : n % 65536 = 6703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6703) = 98304 * k + 10055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10055) = 147456 * k + 15083 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15083) = 221184 * k + 22625 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 22625) = 331776 * k + 33938 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 33938) = 165888 * k + 16969 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 16969) = 248832 * k + 25454 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 25454) = 124416 * k + 12727 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 12727) = 186624 * k + 19091 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 19091) = 279936 * k + 28637 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 28637) = 419904 * k + 42956 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 42956) = 209952 * k + 21478 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 21478) = 104976 * k + 10739 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10739) = 157464 * k + 16109 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16109) = 236196 * k + 24164 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 24164) = 118098 * k + 12082 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 12082) = 59049 * k + 6041 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6747_mod_65536 {n : ℕ} (hn : n % 65536 = 6747) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6747 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6747) = 98304 * k + 10121 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10121) = 147456 * k + 15182 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15182) = 73728 * k + 7591 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 7591) = 110592 * k + 11387 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 11387) = 165888 * k + 17081 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 17081) = 248832 * k + 25622 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 25622) = 124416 * k + 12811 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 12811) = 186624 * k + 19217 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 19217) = 279936 * k + 28826 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 28826) = 139968 * k + 14413 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14413) = 209952 * k + 21620 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 21620) = 104976 * k + 10810 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10810) = 52488 * k + 5405 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 5405) = 78732 * k + 8108 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8108) = 39366 * k + 4054 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4054) = 19683 * k + 2027 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6747) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6747)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6759_mod_65536 {n : ℕ} (hn : n % 65536 = 6759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6759) = 98304 * k + 10139 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10139) = 147456 * k + 15209 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15209) = 221184 * k + 22814 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 22814) = 110592 * k + 11407 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 11407) = 165888 * k + 17111 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 17111) = 248832 * k + 25667 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 25667) = 373248 * k + 38501 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 38501) = 559872 * k + 57752 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 57752) = 279936 * k + 28876 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 28876) = 139968 * k + 14438 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14438) = 69984 * k + 7219 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 7219) = 104976 * k + 10829 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10829) = 157464 * k + 16244 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16244) = 78732 * k + 8122 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8122) = 39366 * k + 4061 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4061) = 59049 * k + 6092 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6783_mod_65536 {n : ℕ} (hn : n % 65536 = 6783) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6783 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6783) = 98304 * k + 10175 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10175) = 147456 * k + 15263 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15263) = 221184 * k + 22895 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 22895) = 331776 * k + 34343 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 34343) = 497664 * k + 51515 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 51515) = 746496 * k + 77273 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 77273) = 1119744 * k + 115910 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 115910) = 559872 * k + 57955 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 57955) = 839808 * k + 86933 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 86933) = 1259712 * k + 130400 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 130400) = 629856 * k + 65200 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 65200) = 314928 * k + 32600 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 32600) = 157464 * k + 16300 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16300) = 78732 * k + 8150 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8150) = 39366 * k + 4075 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4075) = 59049 * k + 6113 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6783) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6783)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6815_mod_65536 {n : ℕ} (hn : n % 65536 = 6815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6815) = 98304 * k + 10223 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10223) = 147456 * k + 15335 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15335) = 221184 * k + 23003 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 23003) = 331776 * k + 34505 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 34505) = 497664 * k + 51758 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 51758) = 248832 * k + 25879 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 25879) = 373248 * k + 38819 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 38819) = 559872 * k + 58229 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 58229) = 839808 * k + 87344 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 87344) = 419904 * k + 43672 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 43672) = 209952 * k + 21836 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 21836) = 104976 * k + 10918 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 10918) = 52488 * k + 5459 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 5459) = 78732 * k + 8189 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8189) = 118098 * k + 12284 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 12284) = 59049 * k + 6142 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6907_mod_65536 {n : ℕ} (hn : n % 65536 = 6907) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6907 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6907) = 98304 * k + 10361 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10361) = 147456 * k + 15542 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15542) = 73728 * k + 7771 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 7771) = 110592 * k + 11657 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 11657) = 165888 * k + 17486 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 17486) = 82944 * k + 8743 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 8743) = 124416 * k + 13115 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 13115) = 186624 * k + 19673 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 19673) = 279936 * k + 29510 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 29510) = 139968 * k + 14755 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14755) = 209952 * k + 22133 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 22133) = 314928 * k + 33200 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 33200) = 157464 * k + 16600 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16600) = 78732 * k + 8300 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8300) = 39366 * k + 4150 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4150) = 19683 * k + 2075 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6907) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6907)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_6975_mod_65536 {n : ℕ} (hn : n % 65536 = 6975) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 6975 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 6975) = 98304 * k + 10463 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10463) = 147456 * k + 15695 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15695) = 221184 * k + 23543 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 23543) = 331776 * k + 35315 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 35315) = 497664 * k + 52973 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 52973) = 746496 * k + 79460 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 79460) = 373248 * k + 39730 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 39730) = 186624 * k + 19865 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 19865) = 279936 * k + 29798 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 29798) = 139968 * k + 14899 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 14899) = 209952 * k + 22349 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 22349) = 314928 * k + 33524 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 33524) = 157464 * k + 16762 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16762) = 78732 * k + 8381 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8381) = 118098 * k + 12572 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 12572) = 59049 * k + 6286 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 6975) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 6975)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7015_mod_65536 {n : ℕ} (hn : n % 65536 = 7015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7015) = 98304 * k + 10523 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10523) = 147456 * k + 15785 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15785) = 221184 * k + 23678 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 23678) = 110592 * k + 11839 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 11839) = 165888 * k + 17759 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 17759) = 248832 * k + 26639 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 26639) = 373248 * k + 39959 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 39959) = 559872 * k + 59939 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 59939) = 839808 * k + 89909 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 89909) = 1259712 * k + 134864 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 134864) = 629856 * k + 67432 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 67432) = 314928 * k + 33716 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 33716) = 157464 * k + 16858 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 16858) = 78732 * k + 8429 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8429) = 118098 * k + 12644 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 12644) = 59049 * k + 6322 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7103_mod_65536 {n : ℕ} (hn : n % 65536 = 7103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7103) = 98304 * k + 10655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10655) = 147456 * k + 15983 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 15983) = 221184 * k + 23975 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 23975) = 331776 * k + 35963 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 35963) = 497664 * k + 53945 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 53945) = 746496 * k + 80918 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 80918) = 373248 * k + 40459 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 40459) = 559872 * k + 60689 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 60689) = 839808 * k + 91034 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 91034) = 419904 * k + 45517 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 45517) = 629856 * k + 68276 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 68276) = 314928 * k + 34138 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 34138) = 157464 * k + 17069 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17069) = 236196 * k + 25604 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 25604) = 118098 * k + 12802 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 12802) = 59049 * k + 6401 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7163_mod_65536 {n : ℕ} (hn : n % 65536 = 7163) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7163 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7163) = 98304 * k + 10745 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10745) = 147456 * k + 16118 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16118) = 73728 * k + 8059 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 8059) = 110592 * k + 12089 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 12089) = 165888 * k + 18134 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 18134) = 82944 * k + 9067 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 9067) = 124416 * k + 13601 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 13601) = 186624 * k + 20402 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 20402) = 93312 * k + 10201 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 10201) = 139968 * k + 15302 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 15302) = 69984 * k + 7651 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 7651) = 104976 * k + 11477 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 11477) = 157464 * k + 17216 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17216) = 78732 * k + 8608 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8608) = 39366 * k + 4304 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4304) = 19683 * k + 2152 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7163) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7163)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7199_mod_65536 {n : ℕ} (hn : n % 65536 = 7199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7199) = 98304 * k + 10799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10799) = 147456 * k + 16199 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16199) = 221184 * k + 24299 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 24299) = 331776 * k + 36449 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 36449) = 497664 * k + 54674 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 54674) = 248832 * k + 27337 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 27337) = 373248 * k + 41006 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 41006) = 186624 * k + 20503 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 20503) = 279936 * k + 30755 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 30755) = 419904 * k + 46133 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 46133) = 629856 * k + 69200 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 69200) = 314928 * k + 34600 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 34600) = 157464 * k + 17300 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17300) = 78732 * k + 8650 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8650) = 39366 * k + 4325 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4325) = 59049 * k + 6488 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7231_mod_65536 {n : ℕ} (hn : n % 65536 = 7231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7231) = 98304 * k + 10847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 10847) = 147456 * k + 16271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16271) = 221184 * k + 24407 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 24407) = 331776 * k + 36611 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 36611) = 497664 * k + 54917 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 54917) = 746496 * k + 82376 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 82376) = 373248 * k + 41188 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 41188) = 186624 * k + 20594 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 20594) = 93312 * k + 10297 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 10297) = 139968 * k + 15446 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 15446) = 69984 * k + 7723 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 7723) = 104976 * k + 11585 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 11585) = 157464 * k + 17378 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17378) = 78732 * k + 8689 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8689) = 118098 * k + 13034 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 13034) = 59049 * k + 6517 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7451_mod_65536 {n : ℕ} (hn : n % 65536 = 7451) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7451 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7451) = 98304 * k + 11177 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11177) = 147456 * k + 16766 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16766) = 73728 * k + 8383 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 8383) = 110592 * k + 12575 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 12575) = 165888 * k + 18863 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 18863) = 248832 * k + 28295 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 28295) = 373248 * k + 42443 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 42443) = 559872 * k + 63665 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 63665) = 839808 * k + 95498 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 95498) = 419904 * k + 47749 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 47749) = 629856 * k + 71624 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 71624) = 314928 * k + 35812 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 35812) = 157464 * k + 17906 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17906) = 78732 * k + 8953 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8953) = 118098 * k + 13430 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 13430) = 59049 * k + 6715 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7451) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7451)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7471_mod_65536 {n : ℕ} (hn : n % 65536 = 7471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7471) = 98304 * k + 11207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11207) = 147456 * k + 16811 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16811) = 221184 * k + 25217 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 25217) = 331776 * k + 37826 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 37826) = 165888 * k + 18913 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 18913) = 248832 * k + 28370 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 28370) = 124416 * k + 14185 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 14185) = 186624 * k + 21278 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 21278) = 93312 * k + 10639 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 10639) = 139968 * k + 15959 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 15959) = 209952 * k + 23939 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 23939) = 314928 * k + 35909 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 35909) = 472392 * k + 53864 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 53864) = 236196 * k + 26932 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 26932) = 118098 * k + 13466 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 13466) = 59049 * k + 6733 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7487_mod_65536 {n : ℕ} (hn : n % 65536 = 7487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7487) = 98304 * k + 11231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11231) = 147456 * k + 16847 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16847) = 221184 * k + 25271 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 25271) = 331776 * k + 37907 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 37907) = 497664 * k + 56861 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 56861) = 746496 * k + 85292 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 85292) = 373248 * k + 42646 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 42646) = 186624 * k + 21323 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 21323) = 279936 * k + 31985 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 31985) = 419904 * k + 47978 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 47978) = 209952 * k + 23989 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 23989) = 314928 * k + 35984 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 35984) = 157464 * k + 17992 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 17992) = 78732 * k + 8996 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 8996) = 39366 * k + 4498 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4498) = 19683 * k + 2249 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7551_mod_65536 {n : ℕ} (hn : n % 65536 = 7551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7551) = 98304 * k + 11327 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11327) = 147456 * k + 16991 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 16991) = 221184 * k + 25487 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 25487) = 331776 * k + 38231 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 38231) = 497664 * k + 57347 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 57347) = 746496 * k + 86021 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 86021) = 1119744 * k + 129032 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 129032) = 559872 * k + 64516 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 64516) = 279936 * k + 32258 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 32258) = 139968 * k + 16129 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16129) = 209952 * k + 24194 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 24194) = 104976 * k + 12097 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12097) = 157464 * k + 18146 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 18146) = 78732 * k + 9073 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9073) = 118098 * k + 13610 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 13610) = 59049 * k + 6805 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7631_mod_65536 {n : ℕ} (hn : n % 65536 = 7631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7631) = 98304 * k + 11447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11447) = 147456 * k + 17171 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17171) = 221184 * k + 25757 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 25757) = 331776 * k + 38636 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 38636) = 165888 * k + 19318 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 19318) = 82944 * k + 9659 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 9659) = 124416 * k + 14489 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 14489) = 186624 * k + 21734 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 21734) = 93312 * k + 10867 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 10867) = 139968 * k + 16301 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16301) = 209952 * k + 24452 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 24452) = 104976 * k + 12226 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12226) = 52488 * k + 6113 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6113) = 78732 * k + 9170 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9170) = 39366 * k + 4585 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4585) = 59049 * k + 6878 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7711_mod_65536 {n : ℕ} (hn : n % 65536 = 7711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7711) = 98304 * k + 11567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11567) = 147456 * k + 17351 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17351) = 221184 * k + 26027 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 26027) = 331776 * k + 39041 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 39041) = 497664 * k + 58562 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 58562) = 248832 * k + 29281 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 29281) = 373248 * k + 43922 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 43922) = 186624 * k + 21961 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 21961) = 279936 * k + 32942 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 32942) = 139968 * k + 16471 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16471) = 209952 * k + 24707 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 24707) = 314928 * k + 37061 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 37061) = 472392 * k + 55592 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 55592) = 236196 * k + 27796 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 27796) = 118098 * k + 13898 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 13898) = 59049 * k + 6949 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7783_mod_65536 {n : ℕ} (hn : n % 65536 = 7783) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7783 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7783) = 98304 * k + 11675 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11675) = 147456 * k + 17513 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17513) = 221184 * k + 26270 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 26270) = 110592 * k + 13135 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13135) = 165888 * k + 19703 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 19703) = 248832 * k + 29555 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 29555) = 373248 * k + 44333 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 44333) = 559872 * k + 66500 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 66500) = 279936 * k + 33250 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33250) = 139968 * k + 16625 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16625) = 209952 * k + 24938 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 24938) = 104976 * k + 12469 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12469) = 157464 * k + 18704 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 18704) = 78732 * k + 9352 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9352) = 39366 * k + 4676 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4676) = 19683 * k + 2338 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7783) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7783)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7791_mod_65536 {n : ℕ} (hn : n % 65536 = 7791) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7791 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7791) = 98304 * k + 11687 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11687) = 147456 * k + 17531 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17531) = 221184 * k + 26297 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 26297) = 331776 * k + 39446 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 39446) = 165888 * k + 19723 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 19723) = 248832 * k + 29585 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 29585) = 373248 * k + 44378 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 44378) = 186624 * k + 22189 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 22189) = 279936 * k + 33284 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33284) = 139968 * k + 16642 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16642) = 69984 * k + 8321 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 8321) = 104976 * k + 12482 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12482) = 52488 * k + 6241 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6241) = 78732 * k + 9362 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9362) = 39366 * k + 4681 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4681) = 59049 * k + 7022 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7791) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7791)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7835_mod_65536 {n : ℕ} (hn : n % 65536 = 7835) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7835 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7835) = 98304 * k + 11753 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11753) = 147456 * k + 17630 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17630) = 73728 * k + 8815 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 8815) = 110592 * k + 13223 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13223) = 165888 * k + 19835 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 19835) = 248832 * k + 29753 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 29753) = 373248 * k + 44630 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 44630) = 186624 * k + 22315 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 22315) = 279936 * k + 33473 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33473) = 419904 * k + 50210 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 50210) = 209952 * k + 25105 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25105) = 314928 * k + 37658 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 37658) = 157464 * k + 18829 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 18829) = 236196 * k + 28244 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 28244) = 118098 * k + 14122 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14122) = 59049 * k + 7061 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7835) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7835)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7871_mod_65536 {n : ℕ} (hn : n % 65536 = 7871) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7871 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7871) = 98304 * k + 11807 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11807) = 147456 * k + 17711 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17711) = 221184 * k + 26567 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 26567) = 331776 * k + 39851 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 39851) = 497664 * k + 59777 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 59777) = 746496 * k + 89666 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 89666) = 373248 * k + 44833 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 44833) = 559872 * k + 67250 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 67250) = 279936 * k + 33625 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33625) = 419904 * k + 50438 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 50438) = 209952 * k + 25219 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25219) = 314928 * k + 37829 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 37829) = 472392 * k + 56744 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 56744) = 236196 * k + 28372 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 28372) = 118098 * k + 14186 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14186) = 59049 * k + 7093 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7871) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7871)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7911_mod_65536 {n : ℕ} (hn : n % 65536 = 7911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7911) = 98304 * k + 11867 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11867) = 147456 * k + 17801 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17801) = 221184 * k + 26702 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 26702) = 110592 * k + 13351 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13351) = 165888 * k + 20027 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 20027) = 248832 * k + 30041 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 30041) = 373248 * k + 45062 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 45062) = 186624 * k + 22531 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 22531) = 279936 * k + 33797 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33797) = 419904 * k + 50696 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 50696) = 209952 * k + 25348 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25348) = 104976 * k + 12674 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12674) = 52488 * k + 6337 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6337) = 78732 * k + 9506 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9506) = 39366 * k + 4753 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4753) = 59049 * k + 7130 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_7931_mod_65536 {n : ℕ} (hn : n % 65536 = 7931) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 7931 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 7931) = 98304 * k + 11897 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 11897) = 147456 * k + 17846 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 17846) = 73728 * k + 8923 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 8923) = 110592 * k + 13385 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13385) = 165888 * k + 20078 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 20078) = 82944 * k + 10039 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 10039) = 124416 * k + 15059 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 15059) = 186624 * k + 22589 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 22589) = 279936 * k + 33884 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 33884) = 139968 * k + 16942 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 16942) = 69984 * k + 8471 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 8471) = 104976 * k + 12707 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12707) = 157464 * k + 19061 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 19061) = 236196 * k + 28592 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 28592) = 118098 * k + 14296 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14296) = 59049 * k + 7148 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 7931) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 7931)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8063_mod_65536 {n : ℕ} (hn : n % 65536 = 8063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8063) = 98304 * k + 12095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12095) = 147456 * k + 18143 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18143) = 221184 * k + 27215 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 27215) = 331776 * k + 40823 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 40823) = 497664 * k + 61235 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 61235) = 746496 * k + 91853 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 91853) = 1119744 * k + 137780 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 137780) = 559872 * k + 68890 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 68890) = 279936 * k + 34445 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 34445) = 419904 * k + 51668 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 51668) = 209952 * k + 25834 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25834) = 104976 * k + 12917 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12917) = 157464 * k + 19376 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 19376) = 78732 * k + 9688 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9688) = 39366 * k + 4844 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4844) = 19683 * k + 2422 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8095_mod_65536 {n : ℕ} (hn : n % 65536 = 8095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8095) = 98304 * k + 12143 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12143) = 147456 * k + 18215 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18215) = 221184 * k + 27323 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 27323) = 331776 * k + 40985 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 40985) = 497664 * k + 61478 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 61478) = 248832 * k + 30739 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 30739) = 373248 * k + 46109 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 46109) = 559872 * k + 69164 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 69164) = 279936 * k + 34582 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 34582) = 139968 * k + 17291 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17291) = 209952 * k + 25937 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25937) = 314928 * k + 38906 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 38906) = 157464 * k + 19453 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 19453) = 236196 * k + 29180 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 29180) = 118098 * k + 14590 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14590) = 59049 * k + 7295 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8103_mod_65536 {n : ℕ} (hn : n % 65536 = 8103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8103) = 98304 * k + 12155 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12155) = 147456 * k + 18233 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18233) = 221184 * k + 27350 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 27350) = 110592 * k + 13675 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13675) = 165888 * k + 20513 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 20513) = 248832 * k + 30770 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 30770) = 124416 * k + 15385 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 15385) = 186624 * k + 23078 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 23078) = 93312 * k + 11539 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 11539) = 139968 * k + 17309 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17309) = 209952 * k + 25964 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 25964) = 104976 * k + 12982 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 12982) = 52488 * k + 6491 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6491) = 78732 * k + 9737 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9737) = 118098 * k + 14606 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14606) = 59049 * k + 7303 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8187_mod_65536 {n : ℕ} (hn : n % 65536 = 8187) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8187 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8187) = 98304 * k + 12281 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12281) = 147456 * k + 18422 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18422) = 73728 * k + 9211 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 9211) = 110592 * k + 13817 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13817) = 165888 * k + 20726 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 20726) = 82944 * k + 10363 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 10363) = 124416 * k + 15545 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 15545) = 186624 * k + 23318 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 23318) = 93312 * k + 11659 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 11659) = 139968 * k + 17489 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17489) = 209952 * k + 26234 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 26234) = 104976 * k + 13117 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13117) = 157464 * k + 19676 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 19676) = 78732 * k + 9838 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9838) = 39366 * k + 4919 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 4919) = 59049 * k + 7379 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8187) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8187)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8263_mod_65536 {n : ℕ} (hn : n % 65536 = 8263) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8263 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8263) = 98304 * k + 12395 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12395) = 147456 * k + 18593 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18593) = 221184 * k + 27890 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 27890) = 110592 * k + 13945 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 13945) = 165888 * k + 20918 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 20918) = 82944 * k + 10459 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 10459) = 124416 * k + 15689 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 15689) = 186624 * k + 23534 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 23534) = 93312 * k + 11767 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 11767) = 139968 * k + 17651 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17651) = 209952 * k + 26477 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 26477) = 314928 * k + 39716 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 39716) = 157464 * k + 19858 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 19858) = 78732 * k + 9929 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 9929) = 118098 * k + 14894 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 14894) = 59049 * k + 7447 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8263) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8263)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8347_mod_65536 {n : ℕ} (hn : n % 65536 = 8347) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8347 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8347) = 98304 * k + 12521 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12521) = 147456 * k + 18782 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18782) = 73728 * k + 9391 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 9391) = 110592 * k + 14087 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 14087) = 165888 * k + 21131 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 21131) = 248832 * k + 31697 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 31697) = 373248 * k + 47546 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 47546) = 186624 * k + 23773 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 23773) = 279936 * k + 35660 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 35660) = 139968 * k + 17830 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17830) = 69984 * k + 8915 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 8915) = 104976 * k + 13373 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13373) = 157464 * k + 20060 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 20060) = 78732 * k + 10030 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10030) = 39366 * k + 5015 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5015) = 59049 * k + 7523 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8347) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8347)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
