import Propositio.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_16511_mod_65536 {n : ℕ} (hn : n % 65536 = 16511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16511) = 98304 * k + 24767 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24767) = 147456 * k + 37151 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37151) = 221184 * k + 55727 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 55727) = 331776 * k + 83591 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 83591) = 497664 * k + 125387 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 125387) = 746496 * k + 188081 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 188081) = 1119744 * k + 282122 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 282122) = 559872 * k + 141061 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 141061) = 839808 * k + 211592 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 211592) = 419904 * k + 105796 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 105796) = 209952 * k + 52898 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 52898) = 104976 * k + 26449 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 26449) = 157464 * k + 39674 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 39674) = 78732 * k + 19837 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19837) = 118098 * k + 29756 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29756) = 59049 * k + 14878 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16591_mod_65536 {n : ℕ} (hn : n % 65536 = 16591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16591) = 98304 * k + 24887 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24887) = 147456 * k + 37331 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37331) = 221184 * k + 55997 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 55997) = 331776 * k + 83996 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 83996) = 165888 * k + 41998 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 41998) = 82944 * k + 20999 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 20999) = 124416 * k + 31499 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 31499) = 186624 * k + 47249 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 47249) = 279936 * k + 70874 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 70874) = 139968 * k + 35437 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 35437) = 209952 * k + 53156 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 53156) = 104976 * k + 26578 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 26578) = 52488 * k + 13289 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13289) = 78732 * k + 19934 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19934) = 39366 * k + 9967 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9967) = 59049 * k + 14951 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16635_mod_65536 {n : ℕ} (hn : n % 65536 = 16635) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16635 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16635) = 98304 * k + 24953 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24953) = 147456 * k + 37430 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37430) = 73728 * k + 18715 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 18715) = 110592 * k + 28073 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28073) = 165888 * k + 42110 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 42110) = 82944 * k + 21055 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 21055) = 124416 * k + 31583 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 31583) = 186624 * k + 47375 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 47375) = 279936 * k + 71063 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 71063) = 419904 * k + 106595 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 106595) = 629856 * k + 159893 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 159893) = 944784 * k + 239840 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 239840) = 472392 * k + 119920 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 119920) = 236196 * k + 59960 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 59960) = 118098 * k + 29980 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29980) = 59049 * k + 14990 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16635) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16635)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16743_mod_65536 {n : ℕ} (hn : n % 65536 = 16743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16743) = 98304 * k + 25115 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25115) = 147456 * k + 37673 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37673) = 221184 * k + 56510 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 56510) = 110592 * k + 28255 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28255) = 165888 * k + 42383 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 42383) = 248832 * k + 63575 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 63575) = 373248 * k + 95363 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 95363) = 559872 * k + 143045 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 143045) = 839808 * k + 214568 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 214568) = 419904 * k + 107284 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 107284) = 209952 * k + 53642 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 53642) = 104976 * k + 26821 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 26821) = 157464 * k + 40232 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 40232) = 78732 * k + 20116 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20116) = 39366 * k + 10058 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10058) = 19683 * k + 5029 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16831_mod_65536 {n : ℕ} (hn : n % 65536 = 16831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16831) = 98304 * k + 25247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25247) = 147456 * k + 37871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37871) = 221184 * k + 56807 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 56807) = 331776 * k + 85211 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 85211) = 497664 * k + 127817 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 127817) = 746496 * k + 191726 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 191726) = 373248 * k + 95863 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 95863) = 559872 * k + 143795 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 143795) = 839808 * k + 215693 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 215693) = 1259712 * k + 323540 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 323540) = 629856 * k + 161770 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 161770) = 314928 * k + 80885 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 80885) = 472392 * k + 121328 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 121328) = 236196 * k + 60664 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 60664) = 118098 * k + 30332 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30332) = 59049 * k + 15166 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16863_mod_65536 {n : ℕ} (hn : n % 65536 = 16863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16863) = 98304 * k + 25295 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25295) = 147456 * k + 37943 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37943) = 221184 * k + 56915 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 56915) = 331776 * k + 85373 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 85373) = 497664 * k + 128060 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 128060) = 248832 * k + 64030 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 64030) = 124416 * k + 32015 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 32015) = 186624 * k + 48023 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48023) = 279936 * k + 72035 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 72035) = 419904 * k + 108053 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 108053) = 629856 * k + 162080 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 162080) = 314928 * k + 81040 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 81040) = 157464 * k + 40520 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 40520) = 78732 * k + 20260 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20260) = 39366 * k + 10130 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10130) = 19683 * k + 5065 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16871_mod_65536 {n : ℕ} (hn : n % 65536 = 16871) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16871 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16871) = 98304 * k + 25307 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25307) = 147456 * k + 37961 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37961) = 221184 * k + 56942 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 56942) = 110592 * k + 28471 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28471) = 165888 * k + 42707 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 42707) = 248832 * k + 64061 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 64061) = 373248 * k + 96092 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 96092) = 186624 * k + 48046 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48046) = 93312 * k + 24023 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 24023) = 139968 * k + 36035 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36035) = 209952 * k + 54053 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 54053) = 314928 * k + 81080 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 81080) = 157464 * k + 40540 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 40540) = 78732 * k + 20270 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20270) = 39366 * k + 10135 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10135) = 59049 * k + 15203 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16871) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16871)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16923_mod_65536 {n : ℕ} (hn : n % 65536 = 16923) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16923 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16923) = 98304 * k + 25385 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25385) = 147456 * k + 38078 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38078) = 73728 * k + 19039 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 19039) = 110592 * k + 28559 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28559) = 165888 * k + 42839 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 42839) = 248832 * k + 64259 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 64259) = 373248 * k + 96389 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 96389) = 559872 * k + 144584 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 144584) = 279936 * k + 72292 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 72292) = 139968 * k + 36146 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36146) = 69984 * k + 18073 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 18073) = 104976 * k + 27110 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27110) = 52488 * k + 13555 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13555) = 78732 * k + 20333 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20333) = 118098 * k + 30500 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30500) = 59049 * k + 15250 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16923) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16923)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17055_mod_65536 {n : ℕ} (hn : n % 65536 = 17055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17055) = 98304 * k + 25583 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25583) = 147456 * k + 38375 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38375) = 221184 * k + 57563 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57563) = 331776 * k + 86345 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 86345) = 497664 * k + 129518 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 129518) = 248832 * k + 64759 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 64759) = 373248 * k + 97139 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 97139) = 559872 * k + 145709 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 145709) = 839808 * k + 218564 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 218564) = 419904 * k + 109282 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 109282) = 209952 * k + 54641 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 54641) = 314928 * k + 81962 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 81962) = 157464 * k + 40981 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 40981) = 236196 * k + 61472 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 61472) = 118098 * k + 30736 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30736) = 59049 * k + 15368 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17063_mod_65536 {n : ℕ} (hn : n % 65536 = 17063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17063) = 98304 * k + 25595 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25595) = 147456 * k + 38393 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38393) = 221184 * k + 57590 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57590) = 110592 * k + 28795 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28795) = 165888 * k + 43193 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43193) = 248832 * k + 64790 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 64790) = 124416 * k + 32395 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 32395) = 186624 * k + 48593 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48593) = 279936 * k + 72890 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 72890) = 139968 * k + 36445 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36445) = 209952 * k + 54668 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 54668) = 104976 * k + 27334 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27334) = 52488 * k + 13667 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13667) = 78732 * k + 20501 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20501) = 118098 * k + 30752 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30752) = 59049 * k + 15376 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17103_mod_65536 {n : ℕ} (hn : n % 65536 = 17103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17103) = 98304 * k + 25655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25655) = 147456 * k + 38483 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38483) = 221184 * k + 57725 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57725) = 331776 * k + 86588 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 86588) = 165888 * k + 43294 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43294) = 82944 * k + 21647 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 21647) = 124416 * k + 32471 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 32471) = 186624 * k + 48707 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48707) = 279936 * k + 73061 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 73061) = 419904 * k + 109592 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 109592) = 209952 * k + 54796 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 54796) = 104976 * k + 27398 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27398) = 52488 * k + 13699 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13699) = 78732 * k + 20549 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20549) = 118098 * k + 30824 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30824) = 59049 * k + 15412 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17127_mod_65536 {n : ℕ} (hn : n % 65536 = 17127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17127) = 98304 * k + 25691 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25691) = 147456 * k + 38537 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38537) = 221184 * k + 57806 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57806) = 110592 * k + 28903 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28903) = 165888 * k + 43355 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43355) = 248832 * k + 65033 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 65033) = 373248 * k + 97550 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 97550) = 186624 * k + 48775 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48775) = 279936 * k + 73163 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 73163) = 419904 * k + 109745 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 109745) = 629856 * k + 164618 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 164618) = 314928 * k + 82309 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 82309) = 472392 * k + 123464 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 123464) = 236196 * k + 61732 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 61732) = 118098 * k + 30866 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30866) = 59049 * k + 15433 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17135_mod_65536 {n : ℕ} (hn : n % 65536 = 17135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17135) = 98304 * k + 25703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25703) = 147456 * k + 38555 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38555) = 221184 * k + 57833 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57833) = 331776 * k + 86750 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 86750) = 165888 * k + 43375 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43375) = 248832 * k + 65063 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 65063) = 373248 * k + 97595 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 97595) = 559872 * k + 146393 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 146393) = 839808 * k + 219590 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 219590) = 419904 * k + 109795 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 109795) = 629856 * k + 164693 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 164693) = 944784 * k + 247040 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 247040) = 472392 * k + 123520 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 123520) = 236196 * k + 61760 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 61760) = 118098 * k + 30880 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30880) = 59049 * k + 15440 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17147_mod_65536 {n : ℕ} (hn : n % 65536 = 17147) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17147 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17147) = 98304 * k + 25721 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25721) = 147456 * k + 38582 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38582) = 73728 * k + 19291 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 19291) = 110592 * k + 28937 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 28937) = 165888 * k + 43406 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43406) = 82944 * k + 21703 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 21703) = 124416 * k + 32555 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 32555) = 186624 * k + 48833 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48833) = 279936 * k + 73250 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 73250) = 139968 * k + 36625 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36625) = 209952 * k + 54938 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 54938) = 104976 * k + 27469 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27469) = 157464 * k + 41204 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 41204) = 78732 * k + 20602 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20602) = 39366 * k + 10301 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10301) = 59049 * k + 15452 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17147) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17147)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17183_mod_65536 {n : ℕ} (hn : n % 65536 = 17183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17183) = 98304 * k + 25775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25775) = 147456 * k + 38663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38663) = 221184 * k + 57995 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 57995) = 331776 * k + 86993 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 86993) = 497664 * k + 130490 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 130490) = 248832 * k + 65245 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 65245) = 373248 * k + 97868 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 97868) = 186624 * k + 48934 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 48934) = 93312 * k + 24467 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 24467) = 139968 * k + 36701 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36701) = 209952 * k + 55052 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 55052) = 104976 * k + 27526 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27526) = 52488 * k + 13763 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13763) = 78732 * k + 20645 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20645) = 118098 * k + 30968 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 30968) = 59049 * k + 15484 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17223_mod_65536 {n : ℕ} (hn : n % 65536 = 17223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17223) = 98304 * k + 25835 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25835) = 147456 * k + 38753 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38753) = 221184 * k + 58130 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 58130) = 110592 * k + 29065 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29065) = 165888 * k + 43598 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 43598) = 82944 * k + 21799 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 21799) = 124416 * k + 32699 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 32699) = 186624 * k + 49049 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 49049) = 279936 * k + 73574 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 73574) = 139968 * k + 36787 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36787) = 209952 * k + 55181 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 55181) = 314928 * k + 82772 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 82772) = 157464 * k + 41386 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 41386) = 78732 * k + 20693 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20693) = 118098 * k + 31040 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31040) = 59049 * k + 15520 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17311_mod_65536 {n : ℕ} (hn : n % 65536 = 17311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17311) = 98304 * k + 25967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 25967) = 147456 * k + 38951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 38951) = 221184 * k + 58427 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 58427) = 331776 * k + 87641 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 87641) = 497664 * k + 131462 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 131462) = 248832 * k + 65731 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 65731) = 373248 * k + 98597 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 98597) = 559872 * k + 147896 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 147896) = 279936 * k + 73948 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 73948) = 139968 * k + 36974 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 36974) = 69984 * k + 18487 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 18487) = 104976 * k + 27731 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27731) = 157464 * k + 41597 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 41597) = 236196 * k + 62396 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 62396) = 118098 * k + 31198 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31198) = 59049 * k + 15599 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17391_mod_65536 {n : ℕ} (hn : n % 65536 = 17391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17391) = 98304 * k + 26087 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26087) = 147456 * k + 39131 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39131) = 221184 * k + 58697 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 58697) = 331776 * k + 88046 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 88046) = 165888 * k + 44023 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44023) = 248832 * k + 66035 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 66035) = 373248 * k + 99053 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 99053) = 559872 * k + 148580 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 148580) = 279936 * k + 74290 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 74290) = 139968 * k + 37145 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 37145) = 209952 * k + 55718 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 55718) = 104976 * k + 27859 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27859) = 157464 * k + 41789 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 41789) = 236196 * k + 62684 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 62684) = 118098 * k + 31342 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31342) = 59049 * k + 15671 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17455_mod_65536 {n : ℕ} (hn : n % 65536 = 17455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17455) = 98304 * k + 26183 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26183) = 147456 * k + 39275 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39275) = 221184 * k + 58913 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 58913) = 331776 * k + 88370 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 88370) = 165888 * k + 44185 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44185) = 248832 * k + 66278 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 66278) = 124416 * k + 33139 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 33139) = 186624 * k + 49709 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 49709) = 279936 * k + 74564 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 74564) = 139968 * k + 37282 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 37282) = 69984 * k + 18641 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 18641) = 104976 * k + 27962 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 27962) = 52488 * k + 13981 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 13981) = 78732 * k + 20972 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 20972) = 39366 * k + 10486 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10486) = 19683 * k + 5243 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17479_mod_65536 {n : ℕ} (hn : n % 65536 = 17479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17479) = 98304 * k + 26219 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26219) = 147456 * k + 39329 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39329) = 221184 * k + 58994 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 58994) = 110592 * k + 29497 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29497) = 165888 * k + 44246 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44246) = 82944 * k + 22123 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 22123) = 124416 * k + 33185 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 33185) = 186624 * k + 49778 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 49778) = 93312 * k + 24889 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 24889) = 139968 * k + 37334 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 37334) = 69984 * k + 18667 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 18667) = 104976 * k + 28001 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 28001) = 157464 * k + 42002 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42002) = 78732 * k + 21001 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21001) = 118098 * k + 31502 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31502) = 59049 * k + 15751 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17511_mod_65536 {n : ℕ} (hn : n % 65536 = 17511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17511) = 98304 * k + 26267 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26267) = 147456 * k + 39401 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39401) = 221184 * k + 59102 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 59102) = 110592 * k + 29551 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29551) = 165888 * k + 44327 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44327) = 248832 * k + 66491 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 66491) = 373248 * k + 99737 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 99737) = 559872 * k + 149606 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 149606) = 279936 * k + 74803 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 74803) = 419904 * k + 112205 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 112205) = 629856 * k + 168308 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 168308) = 314928 * k + 84154 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 84154) = 157464 * k + 42077 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42077) = 236196 * k + 63116 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 63116) = 118098 * k + 31558 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31558) = 59049 * k + 15779 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17575_mod_65536 {n : ℕ} (hn : n % 65536 = 17575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17575) = 98304 * k + 26363 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26363) = 147456 * k + 39545 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39545) = 221184 * k + 59318 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 59318) = 110592 * k + 29659 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29659) = 165888 * k + 44489 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44489) = 248832 * k + 66734 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 66734) = 124416 * k + 33367 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 33367) = 186624 * k + 50051 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 50051) = 279936 * k + 75077 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 75077) = 419904 * k + 112616 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 112616) = 209952 * k + 56308 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 56308) = 104976 * k + 28154 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 28154) = 52488 * k + 14077 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 14077) = 78732 * k + 21116 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21116) = 39366 * k + 10558 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10558) = 19683 * k + 5279 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17659_mod_65536 {n : ℕ} (hn : n % 65536 = 17659) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17659 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17659) = 98304 * k + 26489 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26489) = 147456 * k + 39734 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39734) = 73728 * k + 19867 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 19867) = 110592 * k + 29801 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29801) = 165888 * k + 44702 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44702) = 82944 * k + 22351 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 22351) = 124416 * k + 33527 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 33527) = 186624 * k + 50291 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 50291) = 279936 * k + 75437 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 75437) = 419904 * k + 113156 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 113156) = 209952 * k + 56578 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 56578) = 104976 * k + 28289 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 28289) = 157464 * k + 42434 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42434) = 78732 * k + 21217 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21217) = 118098 * k + 31826 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 31826) = 59049 * k + 15913 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17659) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17659)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17727_mod_65536 {n : ℕ} (hn : n % 65536 = 17727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17727) = 98304 * k + 26591 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26591) = 147456 * k + 39887 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39887) = 221184 * k + 59831 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 59831) = 331776 * k + 89747 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 89747) = 497664 * k + 134621 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 134621) = 746496 * k + 201932 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 201932) = 373248 * k + 100966 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 100966) = 186624 * k + 50483 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 50483) = 279936 * k + 75725 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 75725) = 419904 * k + 113588 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 113588) = 209952 * k + 56794 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 56794) = 104976 * k + 28397 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 28397) = 157464 * k + 42596 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42596) = 78732 * k + 21298 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21298) = 39366 * k + 10649 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10649) = 59049 * k + 15974 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17735_mod_65536 {n : ℕ} (hn : n % 65536 = 17735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17735) = 98304 * k + 26603 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26603) = 147456 * k + 39905 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39905) = 221184 * k + 59858 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 59858) = 110592 * k + 29929 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29929) = 165888 * k + 44894 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44894) = 82944 * k + 22447 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 22447) = 124416 * k + 33671 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 33671) = 186624 * k + 50507 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 50507) = 279936 * k + 75761 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 75761) = 419904 * k + 113642 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 113642) = 209952 * k + 56821 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 56821) = 314928 * k + 85232 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 85232) = 157464 * k + 42616 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42616) = 78732 * k + 21308 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21308) = 39366 * k + 10654 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10654) = 19683 * k + 5327 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_17767_mod_65536 {n : ℕ} (hn : n % 65536 = 17767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 17767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 17767) = 98304 * k + 26651 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 26651) = 147456 * k + 39977 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 39977) = 221184 * k + 59966 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 59966) = 110592 * k + 29983 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 29983) = 165888 * k + 44975 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 44975) = 248832 * k + 67463 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 67463) = 373248 * k + 101195 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 101195) = 559872 * k + 151793 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 151793) = 839808 * k + 227690 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 227690) = 419904 * k + 113845 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 113845) = 629856 * k + 170768 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 170768) = 314928 * k + 85384 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 85384) = 157464 * k + 42692 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 42692) = 78732 * k + 21346 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21346) = 39366 * k + 10673 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10673) = 59049 * k + 16010 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 17767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 17767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18011_mod_65536 {n : ℕ} (hn : n % 65536 = 18011) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18011 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18011) = 98304 * k + 27017 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27017) = 147456 * k + 40526 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 40526) = 73728 * k + 20263 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 20263) = 110592 * k + 30395 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 30395) = 165888 * k + 45593 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 45593) = 248832 * k + 68390 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 68390) = 124416 * k + 34195 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 34195) = 186624 * k + 51293 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 51293) = 279936 * k + 76940 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 76940) = 139968 * k + 38470 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 38470) = 69984 * k + 19235 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 19235) = 104976 * k + 28853 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 28853) = 157464 * k + 43280 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 43280) = 78732 * k + 21640 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21640) = 39366 * k + 10820 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 10820) = 19683 * k + 5410 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18011) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18011)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18159_mod_65536 {n : ℕ} (hn : n % 65536 = 18159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18159) = 98304 * k + 27239 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27239) = 147456 * k + 40859 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 40859) = 221184 * k + 61289 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 61289) = 331776 * k + 91934 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 91934) = 165888 * k + 45967 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 45967) = 248832 * k + 68951 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 68951) = 373248 * k + 103427 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 103427) = 559872 * k + 155141 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 155141) = 839808 * k + 232712 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 232712) = 419904 * k + 116356 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 116356) = 209952 * k + 58178 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 58178) = 104976 * k + 29089 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 29089) = 157464 * k + 43634 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 43634) = 78732 * k + 21817 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 21817) = 118098 * k + 32726 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 32726) = 59049 * k + 16363 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18343_mod_65536 {n : ℕ} (hn : n % 65536 = 18343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18343) = 98304 * k + 27515 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27515) = 147456 * k + 41273 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41273) = 221184 * k + 61910 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 61910) = 110592 * k + 30955 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 30955) = 165888 * k + 46433 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 46433) = 248832 * k + 69650 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 69650) = 124416 * k + 34825 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 34825) = 186624 * k + 52238 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 52238) = 93312 * k + 26119 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 26119) = 139968 * k + 39179 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 39179) = 209952 * k + 58769 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 58769) = 314928 * k + 88154 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 88154) = 157464 * k + 44077 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 44077) = 236196 * k + 66116 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 66116) = 118098 * k + 33058 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 33058) = 59049 * k + 16529 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18399_mod_65536 {n : ℕ} (hn : n % 65536 = 18399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18399) = 98304 * k + 27599 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27599) = 147456 * k + 41399 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41399) = 221184 * k + 62099 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 62099) = 331776 * k + 93149 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 93149) = 497664 * k + 139724 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 139724) = 248832 * k + 69862 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 69862) = 124416 * k + 34931 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 34931) = 186624 * k + 52397 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 52397) = 279936 * k + 78596 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 78596) = 139968 * k + 39298 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 39298) = 69984 * k + 19649 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 19649) = 104976 * k + 29474 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 29474) = 52488 * k + 14737 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 14737) = 78732 * k + 22106 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22106) = 39366 * k + 11053 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11053) = 59049 * k + 16580 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18459_mod_65536 {n : ℕ} (hn : n % 65536 = 18459) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18459 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18459) = 98304 * k + 27689 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27689) = 147456 * k + 41534 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41534) = 73728 * k + 20767 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 20767) = 110592 * k + 31151 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 31151) = 165888 * k + 46727 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 46727) = 248832 * k + 70091 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 70091) = 373248 * k + 105137 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 105137) = 559872 * k + 157706 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 157706) = 279936 * k + 78853 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 78853) = 419904 * k + 118280 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 118280) = 209952 * k + 59140 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 59140) = 104976 * k + 29570 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 29570) = 52488 * k + 14785 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 14785) = 78732 * k + 22178 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22178) = 39366 * k + 11089 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11089) = 59049 * k + 16634 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18459) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18459)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18479_mod_65536 {n : ℕ} (hn : n % 65536 = 18479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18479) = 98304 * k + 27719 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27719) = 147456 * k + 41579 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41579) = 221184 * k + 62369 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 62369) = 331776 * k + 93554 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 93554) = 165888 * k + 46777 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 46777) = 248832 * k + 70166 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 70166) = 124416 * k + 35083 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 35083) = 186624 * k + 52625 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 52625) = 279936 * k + 78938 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 78938) = 139968 * k + 39469 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 39469) = 209952 * k + 59204 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 59204) = 104976 * k + 29602 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 29602) = 52488 * k + 14801 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 14801) = 78732 * k + 22202 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22202) = 39366 * k + 11101 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11101) = 59049 * k + 16652 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18523_mod_65536 {n : ℕ} (hn : n % 65536 = 18523) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18523 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18523) = 98304 * k + 27785 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27785) = 147456 * k + 41678 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41678) = 73728 * k + 20839 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 20839) = 110592 * k + 31259 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 31259) = 165888 * k + 46889 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 46889) = 248832 * k + 70334 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 70334) = 124416 * k + 35167 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 35167) = 186624 * k + 52751 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 52751) = 279936 * k + 79127 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 79127) = 419904 * k + 118691 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 118691) = 629856 * k + 178037 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 178037) = 944784 * k + 267056 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 267056) = 472392 * k + 133528 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 133528) = 236196 * k + 66764 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 66764) = 118098 * k + 33382 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 33382) = 59049 * k + 16691 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18523) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18523)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18559_mod_65536 {n : ℕ} (hn : n % 65536 = 18559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18559) = 98304 * k + 27839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27839) = 147456 * k + 41759 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41759) = 221184 * k + 62639 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 62639) = 331776 * k + 93959 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 93959) = 497664 * k + 140939 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 140939) = 746496 * k + 211409 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 211409) = 1119744 * k + 317114 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 317114) = 559872 * k + 158557 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 158557) = 839808 * k + 237836 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 237836) = 419904 * k + 118918 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 118918) = 209952 * k + 59459 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 59459) = 314928 * k + 89189 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 89189) = 472392 * k + 133784 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 133784) = 236196 * k + 66892 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 66892) = 118098 * k + 33446 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 33446) = 59049 * k + 16723 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18639_mod_65536 {n : ℕ} (hn : n % 65536 = 18639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18639) = 98304 * k + 27959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 27959) = 147456 * k + 41939 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 41939) = 221184 * k + 62909 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 62909) = 331776 * k + 94364 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 94364) = 165888 * k + 47182 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 47182) = 82944 * k + 23591 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 23591) = 124416 * k + 35387 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 35387) = 186624 * k + 53081 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 53081) = 279936 * k + 79622 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 79622) = 139968 * k + 39811 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 39811) = 209952 * k + 59717 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 59717) = 314928 * k + 89576 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 89576) = 157464 * k + 44788 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 44788) = 78732 * k + 22394 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22394) = 39366 * k + 11197 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11197) = 59049 * k + 16796 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18751_mod_65536 {n : ℕ} (hn : n % 65536 = 18751) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18751 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18751) = 98304 * k + 28127 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28127) = 147456 * k + 42191 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42191) = 221184 * k + 63287 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 63287) = 331776 * k + 94931 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 94931) = 497664 * k + 142397 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 142397) = 746496 * k + 213596 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 213596) = 373248 * k + 106798 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 106798) = 186624 * k + 53399 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 53399) = 279936 * k + 80099 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 80099) = 419904 * k + 120149 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 120149) = 629856 * k + 180224 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 180224) = 314928 * k + 90112 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 90112) = 157464 * k + 45056 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45056) = 78732 * k + 22528 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22528) = 39366 * k + 11264 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11264) = 19683 * k + 5632 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18751) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18751)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18895_mod_65536 {n : ℕ} (hn : n % 65536 = 18895) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18895 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18895) = 98304 * k + 28343 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28343) = 147456 * k + 42515 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42515) = 221184 * k + 63773 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 63773) = 331776 * k + 95660 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 95660) = 165888 * k + 47830 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 47830) = 82944 * k + 23915 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 23915) = 124416 * k + 35873 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 35873) = 186624 * k + 53810 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 53810) = 93312 * k + 26905 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 26905) = 139968 * k + 40358 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 40358) = 69984 * k + 20179 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 20179) = 104976 * k + 30269 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 30269) = 157464 * k + 45404 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45404) = 78732 * k + 22702 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22702) = 39366 * k + 11351 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11351) = 59049 * k + 17027 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18895) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18895)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18919_mod_65536 {n : ℕ} (hn : n % 65536 = 18919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18919) = 98304 * k + 28379 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28379) = 147456 * k + 42569 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42569) = 221184 * k + 63854 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 63854) = 110592 * k + 31927 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 31927) = 165888 * k + 47891 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 47891) = 248832 * k + 71837 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 71837) = 373248 * k + 107756 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 107756) = 186624 * k + 53878 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 53878) = 93312 * k + 26939 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 26939) = 139968 * k + 40409 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 40409) = 209952 * k + 60614 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 60614) = 104976 * k + 30307 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 30307) = 157464 * k + 45461 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45461) = 236196 * k + 68192 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 68192) = 118098 * k + 34096 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34096) = 59049 * k + 17048 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_18991_mod_65536 {n : ℕ} (hn : n % 65536 = 18991) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 18991 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 18991) = 98304 * k + 28487 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28487) = 147456 * k + 42731 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42731) = 221184 * k + 64097 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64097) = 331776 * k + 96146 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 96146) = 165888 * k + 48073 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 48073) = 248832 * k + 72110 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 72110) = 124416 * k + 36055 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36055) = 186624 * k + 54083 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54083) = 279936 * k + 81125 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81125) = 419904 * k + 121688 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 121688) = 209952 * k + 60844 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 60844) = 104976 * k + 30422 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 30422) = 52488 * k + 15211 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 15211) = 78732 * k + 22817 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22817) = 118098 * k + 34226 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34226) = 59049 * k + 17113 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 18991) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 18991)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19035_mod_65536 {n : ℕ} (hn : n % 65536 = 19035) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19035 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19035) = 98304 * k + 28553 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28553) = 147456 * k + 42830 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42830) = 73728 * k + 21415 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 21415) = 110592 * k + 32123 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 32123) = 165888 * k + 48185 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 48185) = 248832 * k + 72278 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 72278) = 124416 * k + 36139 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36139) = 186624 * k + 54209 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54209) = 279936 * k + 81314 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81314) = 139968 * k + 40657 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 40657) = 209952 * k + 60986 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 60986) = 104976 * k + 30493 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 30493) = 157464 * k + 45740 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45740) = 78732 * k + 22870 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22870) = 39366 * k + 11435 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11435) = 59049 * k + 17153 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19035) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19035)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19099_mod_65536 {n : ℕ} (hn : n % 65536 = 19099) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19099 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19099) = 98304 * k + 28649 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28649) = 147456 * k + 42974 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 42974) = 73728 * k + 21487 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 21487) = 110592 * k + 32231 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 32231) = 165888 * k + 48347 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 48347) = 248832 * k + 72521 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 72521) = 373248 * k + 108782 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 108782) = 186624 * k + 54391 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54391) = 279936 * k + 81587 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81587) = 419904 * k + 122381 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 122381) = 629856 * k + 183572 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 183572) = 314928 * k + 91786 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 91786) = 157464 * k + 45893 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45893) = 236196 * k + 68840 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 68840) = 118098 * k + 34420 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34420) = 59049 * k + 17210 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19099) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19099)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19111_mod_65536 {n : ℕ} (hn : n % 65536 = 19111) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19111 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19111) = 98304 * k + 28667 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28667) = 147456 * k + 43001 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43001) = 221184 * k + 64502 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64502) = 110592 * k + 32251 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 32251) = 165888 * k + 48377 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 48377) = 248832 * k + 72566 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 72566) = 124416 * k + 36283 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36283) = 186624 * k + 54425 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54425) = 279936 * k + 81638 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81638) = 139968 * k + 40819 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 40819) = 209952 * k + 61229 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 61229) = 314928 * k + 91844 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 91844) = 157464 * k + 45922 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 45922) = 78732 * k + 22961 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 22961) = 118098 * k + 34442 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34442) = 59049 * k + 17221 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19111) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19111)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19135_mod_65536 {n : ℕ} (hn : n % 65536 = 19135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19135) = 98304 * k + 28703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28703) = 147456 * k + 43055 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43055) = 221184 * k + 64583 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64583) = 331776 * k + 96875 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 96875) = 497664 * k + 145313 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 145313) = 746496 * k + 217970 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 217970) = 373248 * k + 108985 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 108985) = 559872 * k + 163478 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 163478) = 279936 * k + 81739 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81739) = 419904 * k + 122609 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 122609) = 629856 * k + 183914 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 183914) = 314928 * k + 91957 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 91957) = 472392 * k + 137936 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 137936) = 236196 * k + 68968 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 68968) = 118098 * k + 34484 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34484) = 59049 * k + 17242 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19151_mod_65536 {n : ℕ} (hn : n % 65536 = 19151) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19151 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19151) = 98304 * k + 28727 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28727) = 147456 * k + 43091 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43091) = 221184 * k + 64637 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64637) = 331776 * k + 96956 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 96956) = 165888 * k + 48478 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 48478) = 82944 * k + 24239 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 24239) = 124416 * k + 36359 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36359) = 186624 * k + 54539 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54539) = 279936 * k + 81809 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 81809) = 419904 * k + 122714 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 122714) = 209952 * k + 61357 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 61357) = 314928 * k + 92036 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 92036) = 157464 * k + 46018 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 46018) = 78732 * k + 23009 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23009) = 118098 * k + 34514 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34514) = 59049 * k + 17257 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19151) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19151)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19199_mod_65536 {n : ℕ} (hn : n % 65536 = 19199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19199) = 98304 * k + 28799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28799) = 147456 * k + 43199 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43199) = 221184 * k + 64799 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64799) = 331776 * k + 97199 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 97199) = 497664 * k + 145799 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 145799) = 746496 * k + 218699 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 218699) = 1119744 * k + 328049 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 328049) = 1679616 * k + 492074 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 492074) = 839808 * k + 246037 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 246037) = 1259712 * k + 369056 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 369056) = 629856 * k + 184528 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 184528) = 314928 * k + 92264 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 92264) = 157464 * k + 46132 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 46132) = 78732 * k + 23066 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23066) = 39366 * k + 11533 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11533) = 59049 * k + 17300 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19231_mod_65536 {n : ℕ} (hn : n % 65536 = 19231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19231) = 98304 * k + 28847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 28847) = 147456 * k + 43271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43271) = 221184 * k + 64907 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 64907) = 331776 * k + 97361 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 97361) = 497664 * k + 146042 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 146042) = 248832 * k + 73021 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 73021) = 373248 * k + 109532 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 109532) = 186624 * k + 54766 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 54766) = 93312 * k + 27383 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 27383) = 139968 * k + 41075 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 41075) = 209952 * k + 61613 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 61613) = 314928 * k + 92420 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 92420) = 157464 * k + 46210 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 46210) = 78732 * k + 23105 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23105) = 118098 * k + 34658 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34658) = 59049 * k + 17329 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19367_mod_65536 {n : ℕ} (hn : n % 65536 = 19367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19367) = 98304 * k + 29051 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29051) = 147456 * k + 43577 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43577) = 221184 * k + 65366 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 65366) = 110592 * k + 32683 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 32683) = 165888 * k + 49025 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 49025) = 248832 * k + 73538 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 73538) = 124416 * k + 36769 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36769) = 186624 * k + 55154 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 55154) = 93312 * k + 27577 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 27577) = 139968 * k + 41366 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 41366) = 69984 * k + 20683 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 20683) = 104976 * k + 31025 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31025) = 157464 * k + 46538 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 46538) = 78732 * k + 23269 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23269) = 118098 * k + 34904 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 34904) = 59049 * k + 17452 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19423_mod_65536 {n : ℕ} (hn : n % 65536 = 19423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19423) = 98304 * k + 29135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29135) = 147456 * k + 43703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43703) = 221184 * k + 65555 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 65555) = 331776 * k + 98333 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 98333) = 497664 * k + 147500 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 147500) = 248832 * k + 73750 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 73750) = 124416 * k + 36875 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 36875) = 186624 * k + 55313 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 55313) = 279936 * k + 82970 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 82970) = 139968 * k + 41485 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 41485) = 209952 * k + 62228 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 62228) = 104976 * k + 31114 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31114) = 52488 * k + 15557 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 15557) = 78732 * k + 23336 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23336) = 39366 * k + 11668 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11668) = 19683 * k + 5834 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19547_mod_65536 {n : ℕ} (hn : n % 65536 = 19547) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19547 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19547) = 98304 * k + 29321 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29321) = 147456 * k + 43982 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 43982) = 73728 * k + 21991 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 21991) = 110592 * k + 32987 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 32987) = 165888 * k + 49481 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 49481) = 248832 * k + 74222 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 74222) = 124416 * k + 37111 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 37111) = 186624 * k + 55667 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 55667) = 279936 * k + 83501 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 83501) = 419904 * k + 125252 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 125252) = 209952 * k + 62626 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 62626) = 104976 * k + 31313 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31313) = 157464 * k + 46970 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 46970) = 78732 * k + 23485 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23485) = 118098 * k + 35228 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 35228) = 59049 * k + 17614 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19547) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19547)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19623_mod_65536 {n : ℕ} (hn : n % 65536 = 19623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19623) = 98304 * k + 29435 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29435) = 147456 * k + 44153 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 44153) = 221184 * k + 66230 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 66230) = 110592 * k + 33115 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 33115) = 165888 * k + 49673 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 49673) = 248832 * k + 74510 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 74510) = 124416 * k + 37255 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 37255) = 186624 * k + 55883 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 55883) = 279936 * k + 83825 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 83825) = 419904 * k + 125738 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 125738) = 209952 * k + 62869 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 62869) = 314928 * k + 94304 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 94304) = 157464 * k + 47152 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 47152) = 78732 * k + 23576 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23576) = 39366 * k + 11788 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11788) = 19683 * k + 5894 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19687_mod_65536 {n : ℕ} (hn : n % 65536 = 19687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19687) = 98304 * k + 29531 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29531) = 147456 * k + 44297 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 44297) = 221184 * k + 66446 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 66446) = 110592 * k + 33223 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 33223) = 165888 * k + 49835 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 49835) = 248832 * k + 74753 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 74753) = 373248 * k + 112130 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 112130) = 186624 * k + 56065 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 56065) = 279936 * k + 84098 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 84098) = 139968 * k + 42049 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 42049) = 209952 * k + 63074 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 63074) = 104976 * k + 31537 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31537) = 157464 * k + 47306 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 47306) = 78732 * k + 23653 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23653) = 118098 * k + 35480 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 35480) = 59049 * k + 17740 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19707_mod_65536 {n : ℕ} (hn : n % 65536 = 19707) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19707 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19707) = 98304 * k + 29561 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29561) = 147456 * k + 44342 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 44342) = 73728 * k + 22171 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 22171) = 110592 * k + 33257 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 33257) = 165888 * k + 49886 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 49886) = 82944 * k + 24943 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 24943) = 124416 * k + 37415 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 37415) = 186624 * k + 56123 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 56123) = 279936 * k + 84185 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 84185) = 419904 * k + 126278 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 126278) = 209952 * k + 63139 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 63139) = 314928 * k + 94709 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 94709) = 472392 * k + 142064 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 142064) = 236196 * k + 71032 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 71032) = 118098 * k + 35516 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 35516) = 59049 * k + 17758 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19707) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19707)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19867_mod_65536 {n : ℕ} (hn : n % 65536 = 19867) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19867 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19867) = 98304 * k + 29801 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29801) = 147456 * k + 44702 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 44702) = 73728 * k + 22351 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 22351) = 110592 * k + 33527 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 33527) = 165888 * k + 50291 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 50291) = 248832 * k + 75437 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 75437) = 373248 * k + 113156 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 113156) = 186624 * k + 56578 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 56578) = 93312 * k + 28289 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 28289) = 139968 * k + 42434 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 42434) = 69984 * k + 21217 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 21217) = 104976 * k + 31826 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31826) = 52488 * k + 15913 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 15913) = 78732 * k + 23870 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23870) = 39366 * k + 11935 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11935) = 59049 * k + 17903 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19867) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19867)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_19919_mod_65536 {n : ℕ} (hn : n % 65536 = 19919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 19919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 19919) = 98304 * k + 29879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 29879) = 147456 * k + 44819 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 44819) = 221184 * k + 67229 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 67229) = 331776 * k + 100844 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 100844) = 165888 * k + 50422 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 50422) = 82944 * k + 25211 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 25211) = 124416 * k + 37817 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 37817) = 186624 * k + 56726 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 56726) = 93312 * k + 28363 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 28363) = 139968 * k + 42545 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 42545) = 209952 * k + 63818 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 63818) = 104976 * k + 31909 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 31909) = 157464 * k + 47864 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 47864) = 78732 * k + 23932 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 23932) = 39366 * k + 11966 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 11966) = 19683 * k + 5983 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 19919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 19919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20079_mod_65536 {n : ℕ} (hn : n % 65536 = 20079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20079) = 98304 * k + 30119 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30119) = 147456 * k + 45179 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45179) = 221184 * k + 67769 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 67769) = 331776 * k + 101654 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 101654) = 165888 * k + 50827 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 50827) = 248832 * k + 76241 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 76241) = 373248 * k + 114362 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 114362) = 186624 * k + 57181 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 57181) = 279936 * k + 85772 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 85772) = 139968 * k + 42886 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 42886) = 69984 * k + 21443 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 21443) = 104976 * k + 32165 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 32165) = 157464 * k + 48248 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 48248) = 78732 * k + 24124 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24124) = 39366 * k + 12062 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12062) = 19683 * k + 6031 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20127_mod_65536 {n : ℕ} (hn : n % 65536 = 20127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20127) = 98304 * k + 30191 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30191) = 147456 * k + 45287 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45287) = 221184 * k + 67931 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 67931) = 331776 * k + 101897 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 101897) = 497664 * k + 152846 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 152846) = 248832 * k + 76423 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 76423) = 373248 * k + 114635 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 114635) = 559872 * k + 171953 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 171953) = 839808 * k + 257930 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 257930) = 419904 * k + 128965 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 128965) = 629856 * k + 193448 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 193448) = 314928 * k + 96724 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 96724) = 157464 * k + 48362 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 48362) = 78732 * k + 24181 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24181) = 118098 * k + 36272 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 36272) = 59049 * k + 18136 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20199_mod_65536 {n : ℕ} (hn : n % 65536 = 20199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20199) = 98304 * k + 30299 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30299) = 147456 * k + 45449 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45449) = 221184 * k + 68174 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 68174) = 110592 * k + 34087 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 34087) = 165888 * k + 51131 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 51131) = 248832 * k + 76697 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 76697) = 373248 * k + 115046 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 115046) = 186624 * k + 57523 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 57523) = 279936 * k + 86285 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 86285) = 419904 * k + 129428 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 129428) = 209952 * k + 64714 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 64714) = 104976 * k + 32357 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 32357) = 157464 * k + 48536 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 48536) = 78732 * k + 24268 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24268) = 39366 * k + 12134 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12134) = 19683 * k + 6067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20207_mod_65536 {n : ℕ} (hn : n % 65536 = 20207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20207) = 98304 * k + 30311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30311) = 147456 * k + 45467 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45467) = 221184 * k + 68201 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 68201) = 331776 * k + 102302 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 102302) = 165888 * k + 51151 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 51151) = 248832 * k + 76727 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 76727) = 373248 * k + 115091 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 115091) = 559872 * k + 172637 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 172637) = 839808 * k + 258956 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 258956) = 419904 * k + 129478 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 129478) = 209952 * k + 64739 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 64739) = 314928 * k + 97109 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 97109) = 472392 * k + 145664 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 145664) = 236196 * k + 72832 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 72832) = 118098 * k + 36416 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 36416) = 59049 * k + 18208 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20219_mod_65536 {n : ℕ} (hn : n % 65536 = 20219) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20219 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20219) = 98304 * k + 30329 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30329) = 147456 * k + 45494 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45494) = 73728 * k + 22747 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 22747) = 110592 * k + 34121 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 34121) = 165888 * k + 51182 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 51182) = 82944 * k + 25591 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 25591) = 124416 * k + 38387 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 38387) = 186624 * k + 57581 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 57581) = 279936 * k + 86372 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 86372) = 139968 * k + 43186 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 43186) = 69984 * k + 21593 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 21593) = 104976 * k + 32390 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 32390) = 52488 * k + 16195 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 16195) = 78732 * k + 24293 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24293) = 118098 * k + 36440 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 36440) = 59049 * k + 18220 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20219) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20219)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20287_mod_65536 {n : ℕ} (hn : n % 65536 = 20287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20287) = 98304 * k + 30431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30431) = 147456 * k + 45647 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 45647) = 221184 * k + 68471 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 68471) = 331776 * k + 102707 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 102707) = 497664 * k + 154061 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 154061) = 746496 * k + 231092 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 231092) = 373248 * k + 115546 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 115546) = 186624 * k + 57773 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 57773) = 279936 * k + 86660 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 86660) = 139968 * k + 43330 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 43330) = 69984 * k + 21665 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 21665) = 104976 * k + 32498 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 32498) = 52488 * k + 16249 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 16249) = 78732 * k + 24374 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24374) = 39366 * k + 12187 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12187) = 59049 * k + 18281 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20507_mod_65536 {n : ℕ} (hn : n % 65536 = 20507) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20507 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20507) = 98304 * k + 30761 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30761) = 147456 * k + 46142 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46142) = 73728 * k + 23071 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 23071) = 110592 * k + 34607 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 34607) = 165888 * k + 51911 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 51911) = 248832 * k + 77867 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 77867) = 373248 * k + 116801 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 116801) = 559872 * k + 175202 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 175202) = 279936 * k + 87601 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 87601) = 419904 * k + 131402 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 131402) = 209952 * k + 65701 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 65701) = 314928 * k + 98552 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 98552) = 157464 * k + 49276 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49276) = 78732 * k + 24638 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24638) = 39366 * k + 12319 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12319) = 59049 * k + 18479 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20507) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20507)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20511_mod_65536 {n : ℕ} (hn : n % 65536 = 20511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20511) = 98304 * k + 30767 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30767) = 147456 * k + 46151 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46151) = 221184 * k + 69227 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 69227) = 331776 * k + 103841 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 103841) = 497664 * k + 155762 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 155762) = 248832 * k + 77881 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 77881) = 373248 * k + 116822 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 116822) = 186624 * k + 58411 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 58411) = 279936 * k + 87617 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 87617) = 419904 * k + 131426 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 131426) = 209952 * k + 65713 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 65713) = 314928 * k + 98570 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 98570) = 157464 * k + 49285 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49285) = 236196 * k + 73928 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 73928) = 118098 * k + 36964 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 36964) = 59049 * k + 18482 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20527_mod_65536 {n : ℕ} (hn : n % 65536 = 20527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20527) = 98304 * k + 30791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30791) = 147456 * k + 46187 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46187) = 221184 * k + 69281 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 69281) = 331776 * k + 103922 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 103922) = 165888 * k + 51961 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 51961) = 248832 * k + 77942 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 77942) = 124416 * k + 38971 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 38971) = 186624 * k + 58457 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 58457) = 279936 * k + 87686 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 87686) = 139968 * k + 43843 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 43843) = 209952 * k + 65765 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 65765) = 314928 * k + 98648 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 98648) = 157464 * k + 49324 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49324) = 78732 * k + 24662 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24662) = 39366 * k + 12331 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12331) = 59049 * k + 18497 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20591_mod_65536 {n : ℕ} (hn : n % 65536 = 20591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20591) = 98304 * k + 30887 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30887) = 147456 * k + 46331 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46331) = 221184 * k + 69497 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 69497) = 331776 * k + 104246 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 104246) = 165888 * k + 52123 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52123) = 248832 * k + 78185 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 78185) = 373248 * k + 117278 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 117278) = 186624 * k + 58639 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 58639) = 279936 * k + 87959 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 87959) = 419904 * k + 131939 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 131939) = 629856 * k + 197909 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 197909) = 944784 * k + 296864 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 296864) = 472392 * k + 148432 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 148432) = 236196 * k + 74216 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 74216) = 118098 * k + 37108 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 37108) = 59049 * k + 18554 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20607_mod_65536 {n : ℕ} (hn : n % 65536 = 20607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20607) = 98304 * k + 30911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 30911) = 147456 * k + 46367 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46367) = 221184 * k + 69551 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 69551) = 331776 * k + 104327 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 104327) = 497664 * k + 156491 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 156491) = 746496 * k + 234737 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 234737) = 1119744 * k + 352106 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 352106) = 559872 * k + 176053 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 176053) = 839808 * k + 264080 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 264080) = 419904 * k + 132040 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 132040) = 209952 * k + 66020 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 66020) = 104976 * k + 33010 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33010) = 52488 * k + 16505 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 16505) = 78732 * k + 24758 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24758) = 39366 * k + 12379 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12379) = 59049 * k + 18569 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20687_mod_65536 {n : ℕ} (hn : n % 65536 = 20687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20687) = 98304 * k + 31031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31031) = 147456 * k + 46547 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46547) = 221184 * k + 69821 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 69821) = 331776 * k + 104732 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 104732) = 165888 * k + 52366 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52366) = 82944 * k + 26183 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 26183) = 124416 * k + 39275 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 39275) = 186624 * k + 58913 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 58913) = 279936 * k + 88370 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 88370) = 139968 * k + 44185 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 44185) = 209952 * k + 66278 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 66278) = 104976 * k + 33139 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33139) = 157464 * k + 49709 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49709) = 236196 * k + 74564 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 74564) = 118098 * k + 37282 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 37282) = 59049 * k + 18641 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20783_mod_65536 {n : ℕ} (hn : n % 65536 = 20783) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20783 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20783) = 98304 * k + 31175 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31175) = 147456 * k + 46763 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46763) = 221184 * k + 70145 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 70145) = 331776 * k + 105218 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 105218) = 165888 * k + 52609 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52609) = 248832 * k + 78914 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 78914) = 124416 * k + 39457 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 39457) = 186624 * k + 59186 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 59186) = 93312 * k + 29593 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 29593) = 139968 * k + 44390 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 44390) = 69984 * k + 22195 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 22195) = 104976 * k + 33293 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33293) = 157464 * k + 49940 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49940) = 78732 * k + 24970 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 24970) = 39366 * k + 12485 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12485) = 59049 * k + 18728 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20783) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20783)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20807_mod_65536 {n : ℕ} (hn : n % 65536 = 20807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20807) = 98304 * k + 31211 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31211) = 147456 * k + 46817 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46817) = 221184 * k + 70226 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 70226) = 110592 * k + 35113 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 35113) = 165888 * k + 52670 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52670) = 82944 * k + 26335 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 26335) = 124416 * k + 39503 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 39503) = 186624 * k + 59255 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 59255) = 279936 * k + 88883 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 88883) = 419904 * k + 133325 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 133325) = 629856 * k + 199988 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 199988) = 314928 * k + 99994 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 99994) = 157464 * k + 49997 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 49997) = 236196 * k + 74996 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 74996) = 118098 * k + 37498 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 37498) = 59049 * k + 18749 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20839_mod_65536 {n : ℕ} (hn : n % 65536 = 20839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20839) = 98304 * k + 31259 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31259) = 147456 * k + 46889 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 46889) = 221184 * k + 70334 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 70334) = 110592 * k + 35167 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 35167) = 165888 * k + 52751 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52751) = 248832 * k + 79127 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 79127) = 373248 * k + 118691 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 118691) = 559872 * k + 178037 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 178037) = 839808 * k + 267056 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 267056) = 419904 * k + 133528 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 133528) = 209952 * k + 66764 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 66764) = 104976 * k + 33382 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33382) = 52488 * k + 16691 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 16691) = 78732 * k + 25037 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25037) = 118098 * k + 37556 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 37556) = 59049 * k + 18778 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20891_mod_65536 {n : ℕ} (hn : n % 65536 = 20891) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20891 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20891) = 98304 * k + 31337 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31337) = 147456 * k + 47006 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47006) = 73728 * k + 23503 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 23503) = 110592 * k + 35255 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 35255) = 165888 * k + 52883 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 52883) = 248832 * k + 79325 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 79325) = 373248 * k + 118988 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 118988) = 186624 * k + 59494 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 59494) = 93312 * k + 29747 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 29747) = 139968 * k + 44621 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 44621) = 209952 * k + 66932 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 66932) = 104976 * k + 33466 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33466) = 52488 * k + 16733 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 16733) = 78732 * k + 25100 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25100) = 39366 * k + 12550 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12550) = 19683 * k + 6275 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20891) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20891)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_20927_mod_65536 {n : ℕ} (hn : n % 65536 = 20927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 20927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 20927) = 98304 * k + 31391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31391) = 147456 * k + 47087 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47087) = 221184 * k + 70631 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 70631) = 331776 * k + 105947 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 105947) = 497664 * k + 158921 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 158921) = 746496 * k + 238382 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 238382) = 373248 * k + 119191 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 119191) = 559872 * k + 178787 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 178787) = 839808 * k + 268181 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 268181) = 1259712 * k + 402272 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 402272) = 629856 * k + 201136 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 201136) = 314928 * k + 100568 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 100568) = 157464 * k + 50284 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 50284) = 78732 * k + 25142 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25142) = 39366 * k + 12571 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12571) = 59049 * k + 18857 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 20927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 20927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21023_mod_65536 {n : ℕ} (hn : n % 65536 = 21023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21023) = 98304 * k + 31535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31535) = 147456 * k + 47303 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47303) = 221184 * k + 70955 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 70955) = 331776 * k + 106433 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 106433) = 497664 * k + 159650 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 159650) = 248832 * k + 79825 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 79825) = 373248 * k + 119738 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 119738) = 186624 * k + 59869 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 59869) = 279936 * k + 89804 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 89804) = 139968 * k + 44902 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 44902) = 69984 * k + 22451 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 22451) = 104976 * k + 33677 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33677) = 157464 * k + 50516 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 50516) = 78732 * k + 25258 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25258) = 39366 * k + 12629 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12629) = 59049 * k + 18944 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21039_mod_65536 {n : ℕ} (hn : n % 65536 = 21039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21039) = 98304 * k + 31559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31559) = 147456 * k + 47339 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47339) = 221184 * k + 71009 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 71009) = 331776 * k + 106514 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 106514) = 165888 * k + 53257 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 53257) = 248832 * k + 79886 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 79886) = 124416 * k + 39943 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 39943) = 186624 * k + 59915 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 59915) = 279936 * k + 89873 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 89873) = 419904 * k + 134810 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 134810) = 209952 * k + 67405 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 67405) = 314928 * k + 101108 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 101108) = 157464 * k + 50554 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 50554) = 78732 * k + 25277 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25277) = 118098 * k + 37916 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 37916) = 59049 * k + 18958 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21103_mod_65536 {n : ℕ} (hn : n % 65536 = 21103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21103) = 98304 * k + 31655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31655) = 147456 * k + 47483 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47483) = 221184 * k + 71225 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 71225) = 331776 * k + 106838 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 106838) = 165888 * k + 53419 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 53419) = 248832 * k + 80129 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 80129) = 373248 * k + 120194 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 120194) = 186624 * k + 60097 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 60097) = 279936 * k + 90146 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 90146) = 139968 * k + 45073 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 45073) = 209952 * k + 67610 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 67610) = 104976 * k + 33805 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 33805) = 157464 * k + 50708 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 50708) = 78732 * k + 25354 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25354) = 39366 * k + 12677 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12677) = 59049 * k + 19016 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21223_mod_65536 {n : ℕ} (hn : n % 65536 = 21223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21223) = 98304 * k + 31835 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31835) = 147456 * k + 47753 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47753) = 221184 * k + 71630 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 71630) = 110592 * k + 35815 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 35815) = 165888 * k + 53723 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 53723) = 248832 * k + 80585 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 80585) = 373248 * k + 120878 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 120878) = 186624 * k + 60439 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 60439) = 279936 * k + 90659 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 90659) = 419904 * k + 135989 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 135989) = 629856 * k + 203984 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 203984) = 314928 * k + 101992 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 101992) = 157464 * k + 50996 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 50996) = 78732 * k + 25498 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25498) = 39366 * k + 12749 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12749) = 59049 * k + 19124 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21311_mod_65536 {n : ℕ} (hn : n % 65536 = 21311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21311) = 98304 * k + 31967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 31967) = 147456 * k + 47951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 47951) = 221184 * k + 71927 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 71927) = 331776 * k + 107891 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 107891) = 497664 * k + 161837 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 161837) = 746496 * k + 242756 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 242756) = 373248 * k + 121378 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 121378) = 186624 * k + 60689 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 60689) = 279936 * k + 91034 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 91034) = 139968 * k + 45517 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 45517) = 209952 * k + 68276 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 68276) = 104976 * k + 34138 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34138) = 52488 * k + 17069 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 17069) = 78732 * k + 25604 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25604) = 39366 * k + 12802 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12802) = 19683 * k + 6401 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21471_mod_65536 {n : ℕ} (hn : n % 65536 = 21471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21471) = 98304 * k + 32207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32207) = 147456 * k + 48311 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48311) = 221184 * k + 72467 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 72467) = 331776 * k + 108701 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 108701) = 497664 * k + 163052 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 163052) = 248832 * k + 81526 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 81526) = 124416 * k + 40763 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 40763) = 186624 * k + 61145 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61145) = 279936 * k + 91718 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 91718) = 139968 * k + 45859 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 45859) = 209952 * k + 68789 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 68789) = 314928 * k + 103184 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 103184) = 157464 * k + 51592 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 51592) = 78732 * k + 25796 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25796) = 39366 * k + 12898 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12898) = 19683 * k + 6449 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21575_mod_65536 {n : ℕ} (hn : n % 65536 = 21575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21575) = 98304 * k + 32363 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32363) = 147456 * k + 48545 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48545) = 221184 * k + 72818 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 72818) = 110592 * k + 36409 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 36409) = 165888 * k + 54614 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 54614) = 82944 * k + 27307 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 27307) = 124416 * k + 40961 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 40961) = 186624 * k + 61442 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61442) = 93312 * k + 30721 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 30721) = 139968 * k + 46082 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 46082) = 69984 * k + 23041 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 23041) = 104976 * k + 34562 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34562) = 52488 * k + 17281 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 17281) = 78732 * k + 25922 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25922) = 39366 * k + 12961 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 12961) = 59049 * k + 19442 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21595_mod_65536 {n : ℕ} (hn : n % 65536 = 21595) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21595 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21595) = 98304 * k + 32393 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32393) = 147456 * k + 48590 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48590) = 73728 * k + 24295 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 24295) = 110592 * k + 36443 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 36443) = 165888 * k + 54665 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 54665) = 248832 * k + 81998 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 81998) = 124416 * k + 40999 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 40999) = 186624 * k + 61499 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61499) = 279936 * k + 92249 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 92249) = 419904 * k + 138374 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 138374) = 209952 * k + 69187 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69187) = 314928 * k + 103781 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 103781) = 472392 * k + 155672 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 155672) = 236196 * k + 77836 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 77836) = 118098 * k + 38918 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 38918) = 59049 * k + 19459 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21595) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21595)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21615_mod_65536 {n : ℕ} (hn : n % 65536 = 21615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21615) = 98304 * k + 32423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32423) = 147456 * k + 48635 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48635) = 221184 * k + 72953 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 72953) = 331776 * k + 109430 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 109430) = 165888 * k + 54715 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 54715) = 248832 * k + 82073 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 82073) = 373248 * k + 123110 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 123110) = 186624 * k + 61555 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61555) = 279936 * k + 92333 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 92333) = 419904 * k + 138500 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 138500) = 209952 * k + 69250 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69250) = 104976 * k + 34625 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34625) = 157464 * k + 51938 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 51938) = 78732 * k + 25969 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 25969) = 118098 * k + 38954 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 38954) = 59049 * k + 19477 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21695_mod_65536 {n : ℕ} (hn : n % 65536 = 21695) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21695 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21695) = 98304 * k + 32543 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32543) = 147456 * k + 48815 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48815) = 221184 * k + 73223 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 73223) = 331776 * k + 109835 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 109835) = 497664 * k + 164753 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 164753) = 746496 * k + 247130 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 247130) = 373248 * k + 123565 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 123565) = 559872 * k + 185348 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 185348) = 279936 * k + 92674 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 92674) = 139968 * k + 46337 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 46337) = 209952 * k + 69506 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69506) = 104976 * k + 34753 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34753) = 157464 * k + 52130 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 52130) = 78732 * k + 26065 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26065) = 118098 * k + 39098 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 39098) = 59049 * k + 19549 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21695) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21695)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21727_mod_65536 {n : ℕ} (hn : n % 65536 = 21727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21727) = 98304 * k + 32591 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32591) = 147456 * k + 48887 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48887) = 221184 * k + 73331 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 73331) = 331776 * k + 109997 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 109997) = 497664 * k + 164996 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 164996) = 248832 * k + 82498 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 82498) = 124416 * k + 41249 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 41249) = 186624 * k + 61874 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61874) = 93312 * k + 30937 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 30937) = 139968 * k + 46406 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 46406) = 69984 * k + 23203 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 23203) = 104976 * k + 34805 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34805) = 157464 * k + 52208 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 52208) = 78732 * k + 26104 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26104) = 39366 * k + 13052 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13052) = 19683 * k + 6526 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21735_mod_65536 {n : ℕ} (hn : n % 65536 = 21735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21735) = 98304 * k + 32603 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32603) = 147456 * k + 48905 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48905) = 221184 * k + 73358 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 73358) = 110592 * k + 36679 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 36679) = 165888 * k + 55019 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 55019) = 248832 * k + 82529 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 82529) = 373248 * k + 123794 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 123794) = 186624 * k + 61897 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61897) = 279936 * k + 92846 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 92846) = 139968 * k + 46423 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 46423) = 209952 * k + 69635 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69635) = 314928 * k + 104453 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 104453) = 472392 * k + 156680 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 156680) = 236196 * k + 78340 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 78340) = 118098 * k + 39170 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 39170) = 59049 * k + 19585 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21755_mod_65536 {n : ℕ} (hn : n % 65536 = 21755) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21755 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21755) = 98304 * k + 32633 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32633) = 147456 * k + 48950 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 48950) = 73728 * k + 24475 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 24475) = 110592 * k + 36713 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 36713) = 165888 * k + 55070 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 55070) = 82944 * k + 27535 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 27535) = 124416 * k + 41303 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 41303) = 186624 * k + 61955 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 61955) = 279936 * k + 92933 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 92933) = 419904 * k + 139400 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 139400) = 209952 * k + 69700 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69700) = 104976 * k + 34850 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34850) = 52488 * k + 17425 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 17425) = 78732 * k + 26138 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26138) = 39366 * k + 13069 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13069) = 59049 * k + 19604 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21755) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21755)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_21807_mod_65536 {n : ℕ} (hn : n % 65536 = 21807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 21807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 21807) = 98304 * k + 32711 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 32711) = 147456 * k + 49067 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49067) = 221184 * k + 73601 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 73601) = 331776 * k + 110402 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 110402) = 165888 * k + 55201 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 55201) = 248832 * k + 82802 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 82802) = 124416 * k + 41401 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 41401) = 186624 * k + 62102 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 62102) = 93312 * k + 31051 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 31051) = 139968 * k + 46577 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 46577) = 209952 * k + 69866 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 69866) = 104976 * k + 34933 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 34933) = 157464 * k + 52400 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 52400) = 78732 * k + 26200 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26200) = 39366 * k + 13100 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13100) = 19683 * k + 6550 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 21807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 21807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22015_mod_65536 {n : ℕ} (hn : n % 65536 = 22015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22015) = 98304 * k + 33023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33023) = 147456 * k + 49535 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49535) = 221184 * k + 74303 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 74303) = 331776 * k + 111455 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 111455) = 497664 * k + 167183 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 167183) = 746496 * k + 250775 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 250775) = 1119744 * k + 376163 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 376163) = 1679616 * k + 564245 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 564245) = 2519424 * k + 846368 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 846368) = 1259712 * k + 423184 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 423184) = 629856 * k + 211592 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 211592) = 314928 * k + 105796 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 105796) = 157464 * k + 52898 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 52898) = 78732 * k + 26449 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26449) = 118098 * k + 39674 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 39674) = 59049 * k + 19837 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22047_mod_65536 {n : ℕ} (hn : n % 65536 = 22047) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22047 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22047) = 98304 * k + 33071 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33071) = 147456 * k + 49607 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49607) = 221184 * k + 74411 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 74411) = 331776 * k + 111617 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 111617) = 497664 * k + 167426 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 167426) = 248832 * k + 83713 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 83713) = 373248 * k + 125570 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 125570) = 186624 * k + 62785 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 62785) = 279936 * k + 94178 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 94178) = 139968 * k + 47089 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 47089) = 209952 * k + 70634 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 70634) = 104976 * k + 35317 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 35317) = 157464 * k + 52976 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 52976) = 78732 * k + 26488 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26488) = 39366 * k + 13244 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13244) = 19683 * k + 6622 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22047) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22047)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22107_mod_65536 {n : ℕ} (hn : n % 65536 = 22107) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22107 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22107) = 98304 * k + 33161 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33161) = 147456 * k + 49742 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49742) = 73728 * k + 24871 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 24871) = 110592 * k + 37307 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 37307) = 165888 * k + 55961 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 55961) = 248832 * k + 83942 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 83942) = 124416 * k + 41971 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 41971) = 186624 * k + 62957 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 62957) = 279936 * k + 94436 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 94436) = 139968 * k + 47218 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 47218) = 69984 * k + 23609 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 23609) = 104976 * k + 35414 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 35414) = 52488 * k + 17707 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 17707) = 78732 * k + 26561 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26561) = 118098 * k + 39842 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 39842) = 59049 * k + 19921 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22107) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22107)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22119_mod_65536 {n : ℕ} (hn : n % 65536 = 22119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22119) = 98304 * k + 33179 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33179) = 147456 * k + 49769 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49769) = 221184 * k + 74654 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 74654) = 110592 * k + 37327 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 37327) = 165888 * k + 55991 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 55991) = 248832 * k + 83987 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 83987) = 373248 * k + 125981 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 125981) = 559872 * k + 188972 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 188972) = 279936 * k + 94486 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 94486) = 139968 * k + 47243 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 47243) = 209952 * k + 70865 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 70865) = 314928 * k + 106298 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 106298) = 157464 * k + 53149 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 53149) = 236196 * k + 79724 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 79724) = 118098 * k + 39862 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 39862) = 59049 * k + 19931 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22207_mod_65536 {n : ℕ} (hn : n % 65536 = 22207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22207) = 98304 * k + 33311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33311) = 147456 * k + 49967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 49967) = 221184 * k + 74951 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 74951) = 331776 * k + 112427 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 112427) = 497664 * k + 168641 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 168641) = 746496 * k + 252962 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 252962) = 373248 * k + 126481 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 126481) = 559872 * k + 189722 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 189722) = 279936 * k + 94861 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 94861) = 419904 * k + 142292 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 142292) = 209952 * k + 71146 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 71146) = 104976 * k + 35573 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 35573) = 157464 * k + 53360 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 53360) = 78732 * k + 26680 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26680) = 39366 * k + 13340 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13340) = 19683 * k + 6670 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22255_mod_65536 {n : ℕ} (hn : n % 65536 = 22255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22255) = 98304 * k + 33383 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33383) = 147456 * k + 50075 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50075) = 221184 * k + 75113 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 75113) = 331776 * k + 112670 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 112670) = 165888 * k + 56335 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 56335) = 248832 * k + 84503 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 84503) = 373248 * k + 126755 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 126755) = 559872 * k + 190133 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 190133) = 839808 * k + 285200 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 285200) = 419904 * k + 142600 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 142600) = 209952 * k + 71300 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 71300) = 104976 * k + 35650 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 35650) = 52488 * k + 17825 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 17825) = 78732 * k + 26738 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 26738) = 39366 * k + 13369 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13369) = 59049 * k + 20054 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22399_mod_65536 {n : ℕ} (hn : n % 65536 = 22399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22399) = 98304 * k + 33599 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33599) = 147456 * k + 50399 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50399) = 221184 * k + 75599 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 75599) = 331776 * k + 113399 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 113399) = 497664 * k + 170099 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 170099) = 746496 * k + 255149 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 255149) = 1119744 * k + 382724 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 382724) = 559872 * k + 191362 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 191362) = 279936 * k + 95681 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 95681) = 419904 * k + 143522 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 143522) = 209952 * k + 71761 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 71761) = 314928 * k + 107642 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 107642) = 157464 * k + 53821 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 53821) = 236196 * k + 80732 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 80732) = 118098 * k + 40366 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 40366) = 59049 * k + 20183 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22495_mod_65536 {n : ℕ} (hn : n % 65536 = 22495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22495) = 98304 * k + 33743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33743) = 147456 * k + 50615 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50615) = 221184 * k + 75923 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 75923) = 331776 * k + 113885 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 113885) = 497664 * k + 170828 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 170828) = 248832 * k + 85414 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 85414) = 124416 * k + 42707 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 42707) = 186624 * k + 64061 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64061) = 279936 * k + 96092 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 96092) = 139968 * k + 48046 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48046) = 69984 * k + 24023 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 24023) = 104976 * k + 36035 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36035) = 157464 * k + 54053 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54053) = 236196 * k + 81080 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 81080) = 118098 * k + 40540 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 40540) = 59049 * k + 20270 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22555_mod_65536 {n : ℕ} (hn : n % 65536 = 22555) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22555 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22555) = 98304 * k + 33833 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33833) = 147456 * k + 50750 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50750) = 73728 * k + 25375 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 25375) = 110592 * k + 38063 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38063) = 165888 * k + 57095 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57095) = 248832 * k + 85643 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 85643) = 373248 * k + 128465 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 128465) = 559872 * k + 192698 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 192698) = 279936 * k + 96349 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 96349) = 419904 * k + 144524 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 144524) = 209952 * k + 72262 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 72262) = 104976 * k + 36131 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36131) = 157464 * k + 54197 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54197) = 236196 * k + 81296 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 81296) = 118098 * k + 40648 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 40648) = 59049 * k + 20324 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22555) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22555)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22575_mod_65536 {n : ℕ} (hn : n % 65536 = 22575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22575) = 98304 * k + 33863 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33863) = 147456 * k + 50795 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50795) = 221184 * k + 76193 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76193) = 331776 * k + 114290 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 114290) = 165888 * k + 57145 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57145) = 248832 * k + 85718 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 85718) = 124416 * k + 42859 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 42859) = 186624 * k + 64289 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64289) = 279936 * k + 96434 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 96434) = 139968 * k + 48217 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48217) = 209952 * k + 72326 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 72326) = 104976 * k + 36163 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36163) = 157464 * k + 54245 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54245) = 236196 * k + 81368 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 81368) = 118098 * k + 40684 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 40684) = 59049 * k + 20342 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22599_mod_65536 {n : ℕ} (hn : n % 65536 = 22599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22599) = 98304 * k + 33899 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33899) = 147456 * k + 50849 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50849) = 221184 * k + 76274 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76274) = 110592 * k + 38137 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38137) = 165888 * k + 57206 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57206) = 82944 * k + 28603 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 28603) = 124416 * k + 42905 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 42905) = 186624 * k + 64358 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64358) = 93312 * k + 32179 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 32179) = 139968 * k + 48269 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48269) = 209952 * k + 72404 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 72404) = 104976 * k + 36202 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36202) = 52488 * k + 18101 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 18101) = 78732 * k + 27152 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27152) = 39366 * k + 13576 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13576) = 19683 * k + 6788 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22655_mod_65536 {n : ℕ} (hn : n % 65536 = 22655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22655) = 98304 * k + 33983 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 33983) = 147456 * k + 50975 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 50975) = 221184 * k + 76463 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76463) = 331776 * k + 114695 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 114695) = 497664 * k + 172043 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 172043) = 746496 * k + 258065 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 258065) = 1119744 * k + 387098 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 387098) = 559872 * k + 193549 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 193549) = 839808 * k + 290324 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 290324) = 419904 * k + 145162 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 145162) = 209952 * k + 72581 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 72581) = 314928 * k + 108872 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 108872) = 157464 * k + 54436 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54436) = 78732 * k + 27218 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27218) = 39366 * k + 13609 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13609) = 59049 * k + 20414 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22695_mod_65536 {n : ℕ} (hn : n % 65536 = 22695) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22695 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22695) = 98304 * k + 34043 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34043) = 147456 * k + 51065 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51065) = 221184 * k + 76598 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76598) = 110592 * k + 38299 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38299) = 165888 * k + 57449 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57449) = 248832 * k + 86174 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 86174) = 124416 * k + 43087 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 43087) = 186624 * k + 64631 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64631) = 279936 * k + 96947 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 96947) = 419904 * k + 145421 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 145421) = 629856 * k + 218132 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 218132) = 314928 * k + 109066 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 109066) = 157464 * k + 54533 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54533) = 236196 * k + 81800 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 81800) = 118098 * k + 40900 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 40900) = 59049 * k + 20450 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22695) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22695)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22751_mod_65536 {n : ℕ} (hn : n % 65536 = 22751) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22751 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22751) = 98304 * k + 34127 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34127) = 147456 * k + 51191 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51191) = 221184 * k + 76787 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76787) = 331776 * k + 115181 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 115181) = 497664 * k + 172772 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 172772) = 248832 * k + 86386 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 86386) = 124416 * k + 43193 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 43193) = 186624 * k + 64790 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64790) = 93312 * k + 32395 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 32395) = 139968 * k + 48593 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48593) = 209952 * k + 72890 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 72890) = 104976 * k + 36445 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36445) = 157464 * k + 54668 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54668) = 78732 * k + 27334 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27334) = 39366 * k + 13667 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13667) = 59049 * k + 20501 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22751) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22751)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22759_mod_65536 {n : ℕ} (hn : n % 65536 = 22759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22759) = 98304 * k + 34139 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34139) = 147456 * k + 51209 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51209) = 221184 * k + 76814 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 76814) = 110592 * k + 38407 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38407) = 165888 * k + 57611 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57611) = 248832 * k + 86417 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 86417) = 373248 * k + 129626 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 129626) = 186624 * k + 64813 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 64813) = 279936 * k + 97220 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 97220) = 139968 * k + 48610 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48610) = 69984 * k + 24305 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 24305) = 104976 * k + 36458 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36458) = 52488 * k + 18229 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 18229) = 78732 * k + 27344 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27344) = 39366 * k + 13672 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13672) = 19683 * k + 6836 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22811_mod_65536 {n : ℕ} (hn : n % 65536 = 22811) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22811 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22811) = 98304 * k + 34217 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34217) = 147456 * k + 51326 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51326) = 73728 * k + 25663 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 25663) = 110592 * k + 38495 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38495) = 165888 * k + 57743 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57743) = 248832 * k + 86615 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 86615) = 373248 * k + 129923 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 129923) = 559872 * k + 194885 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 194885) = 839808 * k + 292328 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 292328) = 419904 * k + 146164 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 146164) = 209952 * k + 73082 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 73082) = 104976 * k + 36541 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36541) = 157464 * k + 54812 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54812) = 78732 * k + 27406 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27406) = 39366 * k + 13703 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13703) = 59049 * k + 20555 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22811) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22811)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22887_mod_65536 {n : ℕ} (hn : n % 65536 = 22887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22887) = 98304 * k + 34331 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34331) = 147456 * k + 51497 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51497) = 221184 * k + 77246 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 77246) = 110592 * k + 38623 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38623) = 165888 * k + 57935 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 57935) = 248832 * k + 86903 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 86903) = 373248 * k + 130355 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 130355) = 559872 * k + 195533 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 195533) = 839808 * k + 293300 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 293300) = 419904 * k + 146650 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 146650) = 209952 * k + 73325 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 73325) = 314928 * k + 109988 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 109988) = 157464 * k + 54994 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 54994) = 78732 * k + 27497 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27497) = 118098 * k + 41246 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 41246) = 59049 * k + 20623 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22911_mod_65536 {n : ℕ} (hn : n % 65536 = 22911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22911) = 98304 * k + 34367 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34367) = 147456 * k + 51551 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51551) = 221184 * k + 77327 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 77327) = 331776 * k + 115991 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 115991) = 497664 * k + 173987 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 173987) = 746496 * k + 260981 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 260981) = 1119744 * k + 391472 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 391472) = 559872 * k + 195736 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 195736) = 279936 * k + 97868 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 97868) = 139968 * k + 48934 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48934) = 69984 * k + 24467 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 24467) = 104976 * k + 36701 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 36701) = 157464 * k + 55052 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 55052) = 78732 * k + 27526 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27526) = 39366 * k + 13763 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13763) = 59049 * k + 20645 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_22939_mod_65536 {n : ℕ} (hn : n % 65536 = 22939) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 22939 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 22939) = 98304 * k + 34409 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34409) = 147456 * k + 51614 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 51614) = 73728 * k + 25807 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 25807) = 110592 * k + 38711 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 38711) = 165888 * k + 58067 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 58067) = 248832 * k + 87101 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 87101) = 373248 * k + 130652 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 130652) = 186624 * k + 65326 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 65326) = 93312 * k + 32663 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 32663) = 139968 * k + 48995 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 48995) = 209952 * k + 73493 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 73493) = 314928 * k + 110240 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 110240) = 157464 * k + 55120 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 55120) = 78732 * k + 27560 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27560) = 39366 * k + 13780 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13780) = 19683 * k + 6890 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 22939) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 22939)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23143_mod_65536 {n : ℕ} (hn : n % 65536 = 23143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23143) = 98304 * k + 34715 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34715) = 147456 * k + 52073 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52073) = 221184 * k + 78110 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78110) = 110592 * k + 39055 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 39055) = 165888 * k + 58583 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 58583) = 248832 * k + 87875 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 87875) = 373248 * k + 131813 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 131813) = 559872 * k + 197720 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 197720) = 279936 * k + 98860 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 98860) = 139968 * k + 49430 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 49430) = 69984 * k + 24715 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 24715) = 104976 * k + 37073 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 37073) = 157464 * k + 55610 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 55610) = 78732 * k + 27805 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27805) = 118098 * k + 41708 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 41708) = 59049 * k + 20854 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23167_mod_65536 {n : ℕ} (hn : n % 65536 = 23167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23167) = 98304 * k + 34751 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34751) = 147456 * k + 52127 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52127) = 221184 * k + 78191 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78191) = 331776 * k + 117287 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 117287) = 497664 * k + 175931 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 175931) = 746496 * k + 263897 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 263897) = 1119744 * k + 395846 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 395846) = 559872 * k + 197923 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 197923) = 839808 * k + 296885 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 296885) = 1259712 * k + 445328 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 445328) = 629856 * k + 222664 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 222664) = 314928 * k + 111332 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 111332) = 157464 * k + 55666 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 55666) = 78732 * k + 27833 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27833) = 118098 * k + 41750 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 41750) = 59049 * k + 20875 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23199_mod_65536 {n : ℕ} (hn : n % 65536 = 23199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23199) = 98304 * k + 34799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34799) = 147456 * k + 52199 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52199) = 221184 * k + 78299 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78299) = 331776 * k + 117449 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 117449) = 497664 * k + 176174 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 176174) = 248832 * k + 88087 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 88087) = 373248 * k + 132131 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 132131) = 559872 * k + 198197 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 198197) = 839808 * k + 297296 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 297296) = 419904 * k + 148648 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 148648) = 209952 * k + 74324 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 74324) = 104976 * k + 37162 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 37162) = 52488 * k + 18581 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 18581) = 78732 * k + 27872 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27872) = 39366 * k + 13936 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13936) = 19683 * k + 6968 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23231_mod_65536 {n : ℕ} (hn : n % 65536 = 23231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23231) = 98304 * k + 34847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 34847) = 147456 * k + 52271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52271) = 221184 * k + 78407 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78407) = 331776 * k + 117611 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 117611) = 497664 * k + 176417 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 176417) = 746496 * k + 264626 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 264626) = 373248 * k + 132313 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 132313) = 559872 * k + 198470 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 198470) = 279936 * k + 99235 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 99235) = 419904 * k + 148853 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 148853) = 629856 * k + 223280 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 223280) = 314928 * k + 111640 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 111640) = 157464 * k + 55820 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 55820) = 78732 * k + 27910 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 27910) = 39366 * k + 13955 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 13955) = 59049 * k + 20933 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23359_mod_65536 {n : ℕ} (hn : n % 65536 = 23359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23359) = 98304 * k + 35039 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35039) = 147456 * k + 52559 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52559) = 221184 * k + 78839 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78839) = 331776 * k + 118259 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 118259) = 497664 * k + 177389 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 177389) = 746496 * k + 266084 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 266084) = 373248 * k + 133042 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 133042) = 186624 * k + 66521 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 66521) = 279936 * k + 99782 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 99782) = 139968 * k + 49891 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 49891) = 209952 * k + 74837 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 74837) = 314928 * k + 112256 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 112256) = 157464 * k + 56128 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 56128) = 78732 * k + 28064 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28064) = 39366 * k + 14032 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14032) = 19683 * k + 7016 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23399_mod_65536 {n : ℕ} (hn : n % 65536 = 23399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23399) = 98304 * k + 35099 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35099) = 147456 * k + 52649 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52649) = 221184 * k + 78974 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 78974) = 110592 * k + 39487 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 39487) = 165888 * k + 59231 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 59231) = 248832 * k + 88847 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 88847) = 373248 * k + 133271 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 133271) = 559872 * k + 199907 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 199907) = 839808 * k + 299861 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 299861) = 1259712 * k + 449792 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 449792) = 629856 * k + 224896 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 224896) = 314928 * k + 112448 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 112448) = 157464 * k + 56224 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 56224) = 78732 * k + 28112 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28112) = 39366 * k + 14056 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14056) = 19683 * k + 7028 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23463_mod_65536 {n : ℕ} (hn : n % 65536 = 23463) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23463 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23463) = 98304 * k + 35195 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35195) = 147456 * k + 52793 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 52793) = 221184 * k + 79190 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 79190) = 110592 * k + 39595 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 39595) = 165888 * k + 59393 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 59393) = 248832 * k + 89090 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 89090) = 124416 * k + 44545 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 44545) = 186624 * k + 66818 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 66818) = 93312 * k + 33409 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 33409) = 139968 * k + 50114 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 50114) = 69984 * k + 25057 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 25057) = 104976 * k + 37586 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 37586) = 52488 * k + 18793 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 18793) = 78732 * k + 28190 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28190) = 39366 * k + 14095 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14095) = 59049 * k + 21143 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23463) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23463)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23583_mod_65536 {n : ℕ} (hn : n % 65536 = 23583) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23583 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23583) = 98304 * k + 35375 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35375) = 147456 * k + 53063 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53063) = 221184 * k + 79595 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 79595) = 331776 * k + 119393 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 119393) = 497664 * k + 179090 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 179090) = 248832 * k + 89545 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 89545) = 373248 * k + 134318 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 134318) = 186624 * k + 67159 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67159) = 279936 * k + 100739 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 100739) = 419904 * k + 151109 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 151109) = 629856 * k + 226664 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 226664) = 314928 * k + 113332 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 113332) = 157464 * k + 56666 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 56666) = 78732 * k + 28333 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28333) = 118098 * k + 42500 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 42500) = 59049 * k + 21250 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23583) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23583)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23615_mod_65536 {n : ℕ} (hn : n % 65536 = 23615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23615) = 98304 * k + 35423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35423) = 147456 * k + 53135 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53135) = 221184 * k + 79703 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 79703) = 331776 * k + 119555 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 119555) = 497664 * k + 179333 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 179333) = 746496 * k + 269000 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 269000) = 373248 * k + 134500 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 134500) = 186624 * k + 67250 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67250) = 93312 * k + 33625 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 33625) = 139968 * k + 50438 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 50438) = 69984 * k + 25219 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 25219) = 104976 * k + 37829 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 37829) = 157464 * k + 56744 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 56744) = 78732 * k + 28372 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28372) = 39366 * k + 14186 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14186) = 19683 * k + 7093 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23643_mod_65536 {n : ℕ} (hn : n % 65536 = 23643) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23643 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23643) = 98304 * k + 35465 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35465) = 147456 * k + 53198 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53198) = 73728 * k + 26599 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 26599) = 110592 * k + 39899 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 39899) = 165888 * k + 59849 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 59849) = 248832 * k + 89774 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 89774) = 124416 * k + 44887 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 44887) = 186624 * k + 67331 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67331) = 279936 * k + 100997 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 100997) = 419904 * k + 151496 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 151496) = 209952 * k + 75748 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 75748) = 104976 * k + 37874 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 37874) = 52488 * k + 18937 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 18937) = 78732 * k + 28406 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28406) = 39366 * k + 14203 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14203) = 59049 * k + 21305 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23643) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23643)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23663_mod_65536 {n : ℕ} (hn : n % 65536 = 23663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23663) = 98304 * k + 35495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35495) = 147456 * k + 53243 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53243) = 221184 * k + 79865 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 79865) = 331776 * k + 119798 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 119798) = 165888 * k + 59899 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 59899) = 248832 * k + 89849 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 89849) = 373248 * k + 134774 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 134774) = 186624 * k + 67387 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67387) = 279936 * k + 101081 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 101081) = 419904 * k + 151622 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 151622) = 209952 * k + 75811 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 75811) = 314928 * k + 113717 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 113717) = 472392 * k + 170576 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 170576) = 236196 * k + 85288 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 85288) = 118098 * k + 42644 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 42644) = 59049 * k + 21322 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23707_mod_65536 {n : ℕ} (hn : n % 65536 = 23707) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23707 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23707) = 98304 * k + 35561 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35561) = 147456 * k + 53342 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53342) = 73728 * k + 26671 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 26671) = 110592 * k + 40007 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40007) = 165888 * k + 60011 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60011) = 248832 * k + 90017 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 90017) = 373248 * k + 135026 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 135026) = 186624 * k + 67513 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67513) = 279936 * k + 101270 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 101270) = 139968 * k + 50635 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 50635) = 209952 * k + 75953 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 75953) = 314928 * k + 113930 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 113930) = 157464 * k + 56965 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 56965) = 236196 * k + 85448 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 85448) = 118098 * k + 42724 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 42724) = 59049 * k + 21362 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23707) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23707)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23711_mod_65536 {n : ℕ} (hn : n % 65536 = 23711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23711) = 98304 * k + 35567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35567) = 147456 * k + 53351 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53351) = 221184 * k + 80027 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 80027) = 331776 * k + 120041 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 120041) = 497664 * k + 180062 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 180062) = 248832 * k + 90031 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 90031) = 373248 * k + 135047 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 135047) = 559872 * k + 202571 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 202571) = 839808 * k + 303857 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 303857) = 1259712 * k + 455786 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 455786) = 629856 * k + 227893 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 227893) = 944784 * k + 341840 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 341840) = 472392 * k + 170920 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 170920) = 236196 * k + 85460 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 85460) = 118098 * k + 42730 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 42730) = 59049 * k + 21365 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23743_mod_65536 {n : ℕ} (hn : n % 65536 = 23743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23743) = 98304 * k + 35615 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35615) = 147456 * k + 53423 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53423) = 221184 * k + 80135 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 80135) = 331776 * k + 120203 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 120203) = 497664 * k + 180305 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 180305) = 746496 * k + 270458 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 270458) = 373248 * k + 135229 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 135229) = 559872 * k + 202844 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 202844) = 279936 * k + 101422 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 101422) = 139968 * k + 50711 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 50711) = 209952 * k + 76067 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 76067) = 314928 * k + 114101 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 114101) = 472392 * k + 171152 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 171152) = 236196 * k + 85576 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 85576) = 118098 * k + 42788 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 42788) = 59049 * k + 21394 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23783_mod_65536 {n : ℕ} (hn : n % 65536 = 23783) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23783 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23783) = 98304 * k + 35675 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35675) = 147456 * k + 53513 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53513) = 221184 * k + 80270 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 80270) = 110592 * k + 40135 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40135) = 165888 * k + 60203 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60203) = 248832 * k + 90305 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 90305) = 373248 * k + 135458 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 135458) = 186624 * k + 67729 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67729) = 279936 * k + 101594 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 101594) = 139968 * k + 50797 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 50797) = 209952 * k + 76196 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 76196) = 104976 * k + 38098 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38098) = 52488 * k + 19049 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19049) = 78732 * k + 28574 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28574) = 39366 * k + 14287 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14287) = 59049 * k + 21431 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23783) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23783)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23803_mod_65536 {n : ℕ} (hn : n % 65536 = 23803) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23803 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23803) = 98304 * k + 35705 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35705) = 147456 * k + 53558 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53558) = 73728 * k + 26779 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 26779) = 110592 * k + 40169 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40169) = 165888 * k + 60254 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60254) = 82944 * k + 30127 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 30127) = 124416 * k + 45191 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 45191) = 186624 * k + 67787 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 67787) = 279936 * k + 101681 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 101681) = 419904 * k + 152522 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 152522) = 209952 * k + 76261 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 76261) = 314928 * k + 114392 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 114392) = 157464 * k + 57196 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 57196) = 78732 * k + 28598 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28598) = 39366 * k + 14299 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14299) = 59049 * k + 21449 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23803) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23803)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23835_mod_65536 {n : ℕ} (hn : n % 65536 = 23835) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23835 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23835) = 98304 * k + 35753 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35753) = 147456 * k + 53630 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53630) = 73728 * k + 26815 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 26815) = 110592 * k + 40223 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40223) = 165888 * k + 60335 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60335) = 248832 * k + 90503 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 90503) = 373248 * k + 135755 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 135755) = 559872 * k + 203633 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 203633) = 839808 * k + 305450 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 305450) = 419904 * k + 152725 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 152725) = 629856 * k + 229088 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 229088) = 314928 * k + 114544 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 114544) = 157464 * k + 57272 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 57272) = 78732 * k + 28636 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28636) = 39366 * k + 14318 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14318) = 19683 * k + 7159 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23835) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23835)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23935_mod_65536 {n : ℕ} (hn : n % 65536 = 23935) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23935 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23935) = 98304 * k + 35903 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35903) = 147456 * k + 53855 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53855) = 221184 * k + 80783 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 80783) = 331776 * k + 121175 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 121175) = 497664 * k + 181763 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 181763) = 746496 * k + 272645 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 272645) = 1119744 * k + 408968 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 408968) = 559872 * k + 204484 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 204484) = 279936 * k + 102242 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 102242) = 139968 * k + 51121 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 51121) = 209952 * k + 76682 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 76682) = 104976 * k + 38341 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38341) = 157464 * k + 57512 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 57512) = 78732 * k + 28756 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28756) = 39366 * k + 14378 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14378) = 19683 * k + 7189 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23935) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23935)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_23963_mod_65536 {n : ℕ} (hn : n % 65536 = 23963) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 23963 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 23963) = 98304 * k + 35945 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 35945) = 147456 * k + 53918 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 53918) = 73728 * k + 26959 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 26959) = 110592 * k + 40439 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40439) = 165888 * k + 60659 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60659) = 248832 * k + 90989 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 90989) = 373248 * k + 136484 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 136484) = 186624 * k + 68242 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 68242) = 93312 * k + 34121 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 34121) = 139968 * k + 51182 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 51182) = 69984 * k + 25591 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 25591) = 104976 * k + 38387 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38387) = 157464 * k + 57581 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 57581) = 236196 * k + 86372 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 86372) = 118098 * k + 43186 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43186) = 59049 * k + 21593 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 23963) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 23963)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24015_mod_65536 {n : ℕ} (hn : n % 65536 = 24015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24015) = 98304 * k + 36023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36023) = 147456 * k + 54035 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54035) = 221184 * k + 81053 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 81053) = 331776 * k + 121580 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 121580) = 165888 * k + 60790 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60790) = 82944 * k + 30395 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 30395) = 124416 * k + 45593 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 45593) = 186624 * k + 68390 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 68390) = 93312 * k + 34195 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 34195) = 139968 * k + 51293 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 51293) = 209952 * k + 76940 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 76940) = 104976 * k + 38470 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38470) = 52488 * k + 19235 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19235) = 78732 * k + 28853 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 28853) = 118098 * k + 43280 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43280) = 59049 * k + 21640 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24047_mod_65536 {n : ℕ} (hn : n % 65536 = 24047) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24047 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24047) = 98304 * k + 36071 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36071) = 147456 * k + 54107 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54107) = 221184 * k + 81161 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 81161) = 331776 * k + 121742 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 121742) = 165888 * k + 60871 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 60871) = 248832 * k + 91307 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 91307) = 373248 * k + 136961 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 136961) = 559872 * k + 205442 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 205442) = 279936 * k + 102721 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 102721) = 419904 * k + 154082 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 154082) = 209952 * k + 77041 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 77041) = 314928 * k + 115562 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 115562) = 157464 * k + 57781 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 57781) = 236196 * k + 86672 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 86672) = 118098 * k + 43336 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43336) = 59049 * k + 21668 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24047) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24047)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24175_mod_65536 {n : ℕ} (hn : n % 65536 = 24175) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24175 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24175) = 98304 * k + 36263 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36263) = 147456 * k + 54395 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54395) = 221184 * k + 81593 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 81593) = 331776 * k + 122390 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 122390) = 165888 * k + 61195 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 61195) = 248832 * k + 91793 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 91793) = 373248 * k + 137690 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 137690) = 186624 * k + 68845 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 68845) = 279936 * k + 103268 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 103268) = 139968 * k + 51634 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 51634) = 69984 * k + 25817 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 25817) = 104976 * k + 38726 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38726) = 52488 * k + 19363 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19363) = 78732 * k + 29045 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29045) = 118098 * k + 43568 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43568) = 59049 * k + 21784 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24175) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24175)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24295_mod_65536 {n : ℕ} (hn : n % 65536 = 24295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24295) = 98304 * k + 36443 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36443) = 147456 * k + 54665 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54665) = 221184 * k + 81998 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 81998) = 110592 * k + 40999 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 40999) = 165888 * k + 61499 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 61499) = 248832 * k + 92249 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 92249) = 373248 * k + 138374 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 138374) = 186624 * k + 69187 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 69187) = 279936 * k + 103781 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 103781) = 419904 * k + 155672 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 155672) = 209952 * k + 77836 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 77836) = 104976 * k + 38918 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 38918) = 52488 * k + 19459 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19459) = 78732 * k + 29189 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29189) = 118098 * k + 43784 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43784) = 59049 * k + 21892 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24303_mod_65536 {n : ℕ} (hn : n % 65536 = 24303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24303) = 98304 * k + 36455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36455) = 147456 * k + 54683 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54683) = 221184 * k + 82025 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 82025) = 331776 * k + 123038 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 123038) = 165888 * k + 61519 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 61519) = 248832 * k + 92279 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 92279) = 373248 * k + 138419 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 138419) = 559872 * k + 207629 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 207629) = 839808 * k + 311444 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 311444) = 419904 * k + 155722 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 155722) = 209952 * k + 77861 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 77861) = 314928 * k + 116792 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 116792) = 157464 * k + 58396 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 58396) = 78732 * k + 29198 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29198) = 39366 * k + 14599 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14599) = 59049 * k + 21899 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24383_mod_65536 {n : ℕ} (hn : n % 65536 = 24383) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24383 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24383) = 98304 * k + 36575 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36575) = 147456 * k + 54863 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 54863) = 221184 * k + 82295 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 82295) = 331776 * k + 123443 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 123443) = 497664 * k + 185165 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 185165) = 746496 * k + 277748 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 277748) = 373248 * k + 138874 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 138874) = 186624 * k + 69437 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 69437) = 279936 * k + 104156 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 104156) = 139968 * k + 52078 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52078) = 69984 * k + 26039 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 26039) = 104976 * k + 39059 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39059) = 157464 * k + 58589 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 58589) = 236196 * k + 87884 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 87884) = 118098 * k + 43942 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 43942) = 59049 * k + 21971 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24383) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24383)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24487_mod_65536 {n : ℕ} (hn : n % 65536 = 24487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24487) = 98304 * k + 36731 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36731) = 147456 * k + 55097 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55097) = 221184 * k + 82646 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 82646) = 110592 * k + 41323 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 41323) = 165888 * k + 61985 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 61985) = 248832 * k + 92978 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 92978) = 124416 * k + 46489 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 46489) = 186624 * k + 69734 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 69734) = 93312 * k + 34867 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 34867) = 139968 * k + 52301 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52301) = 209952 * k + 78452 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 78452) = 104976 * k + 39226 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39226) = 52488 * k + 19613 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19613) = 78732 * k + 29420 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29420) = 39366 * k + 14710 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14710) = 19683 * k + 7355 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24559_mod_65536 {n : ℕ} (hn : n % 65536 = 24559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24559) = 98304 * k + 36839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36839) = 147456 * k + 55259 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55259) = 221184 * k + 82889 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 82889) = 331776 * k + 124334 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 124334) = 165888 * k + 62167 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62167) = 248832 * k + 93251 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 93251) = 373248 * k + 139877 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 139877) = 559872 * k + 209816 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 209816) = 279936 * k + 104908 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 104908) = 139968 * k + 52454 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52454) = 69984 * k + 26227 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 26227) = 104976 * k + 39341 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39341) = 157464 * k + 59012 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59012) = 78732 * k + 29506 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29506) = 39366 * k + 14753 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14753) = 59049 * k + 22130 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24571_mod_65536 {n : ℕ} (hn : n % 65536 = 24571) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24571 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24571) = 98304 * k + 36857 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36857) = 147456 * k + 55286 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55286) = 73728 * k + 27643 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 27643) = 110592 * k + 41465 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 41465) = 165888 * k + 62198 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62198) = 82944 * k + 31099 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 31099) = 124416 * k + 46649 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 46649) = 186624 * k + 69974 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 69974) = 93312 * k + 34987 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 34987) = 139968 * k + 52481 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52481) = 209952 * k + 78722 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 78722) = 104976 * k + 39361 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39361) = 157464 * k + 59042 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59042) = 78732 * k + 29521 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29521) = 118098 * k + 44282 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 44282) = 59049 * k + 22141 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24571) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24571)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24639_mod_65536 {n : ℕ} (hn : n % 65536 = 24639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24639) = 98304 * k + 36959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36959) = 147456 * k + 55439 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55439) = 221184 * k + 83159 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83159) = 331776 * k + 124739 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 124739) = 497664 * k + 187109 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 187109) = 746496 * k + 280664 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 280664) = 373248 * k + 140332 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 140332) = 186624 * k + 70166 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 70166) = 93312 * k + 35083 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 35083) = 139968 * k + 52625 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52625) = 209952 * k + 78938 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 78938) = 104976 * k + 39469 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39469) = 157464 * k + 59204 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59204) = 78732 * k + 29602 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29602) = 39366 * k + 14801 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14801) = 59049 * k + 22202 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24647_mod_65536 {n : ℕ} (hn : n % 65536 = 24647) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24647 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24647) = 98304 * k + 36971 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 36971) = 147456 * k + 55457 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55457) = 221184 * k + 83186 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83186) = 110592 * k + 41593 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 41593) = 165888 * k + 62390 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62390) = 82944 * k + 31195 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 31195) = 124416 * k + 46793 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 46793) = 186624 * k + 70190 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 70190) = 93312 * k + 35095 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 35095) = 139968 * k + 52643 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52643) = 209952 * k + 78965 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 78965) = 314928 * k + 118448 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 118448) = 157464 * k + 59224 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59224) = 78732 * k + 29612 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29612) = 39366 * k + 14806 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14806) = 19683 * k + 7403 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24647) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24647)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24679_mod_65536 {n : ℕ} (hn : n % 65536 = 24679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24679) = 98304 * k + 37019 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37019) = 147456 * k + 55529 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55529) = 221184 * k + 83294 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83294) = 110592 * k + 41647 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 41647) = 165888 * k + 62471 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62471) = 248832 * k + 93707 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 93707) = 373248 * k + 140561 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 140561) = 559872 * k + 210842 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 210842) = 279936 * k + 105421 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 105421) = 419904 * k + 158132 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 158132) = 209952 * k + 79066 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 79066) = 104976 * k + 39533 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39533) = 157464 * k + 59300 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59300) = 78732 * k + 29650 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29650) = 39366 * k + 14825 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14825) = 59049 * k + 22238 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
