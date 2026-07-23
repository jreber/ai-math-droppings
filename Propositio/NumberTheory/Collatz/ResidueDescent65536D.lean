import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_24703_mod_65536 {n : ℕ} (hn : n % 65536 = 24703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24703) = 98304 * k + 37055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37055) = 147456 * k + 55583 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55583) = 221184 * k + 83375 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83375) = 331776 * k + 125063 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 125063) = 497664 * k + 187595 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 187595) = 746496 * k + 281393 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 281393) = 1119744 * k + 422090 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 422090) = 559872 * k + 211045 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 211045) = 839808 * k + 316568 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 316568) = 419904 * k + 158284 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 158284) = 209952 * k + 79142 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 79142) = 104976 * k + 39571 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39571) = 157464 * k + 59357 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59357) = 236196 * k + 89036 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 89036) = 118098 * k + 44518 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 44518) = 59049 * k + 22259 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24731_mod_65536 {n : ℕ} (hn : n % 65536 = 24731) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24731 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24731) = 98304 * k + 37097 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37097) = 147456 * k + 55646 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55646) = 73728 * k + 27823 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 27823) = 110592 * k + 41735 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 41735) = 165888 * k + 62603 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62603) = 248832 * k + 93905 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 93905) = 373248 * k + 140858 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 140858) = 186624 * k + 70429 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 70429) = 279936 * k + 105644 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 105644) = 139968 * k + 52822 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52822) = 69984 * k + 26411 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 26411) = 104976 * k + 39617 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39617) = 157464 * k + 59426 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59426) = 78732 * k + 29713 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29713) = 118098 * k + 44570 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 44570) = 59049 * k + 22285 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24731) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24731)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24767_mod_65536 {n : ℕ} (hn : n % 65536 = 24767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24767) = 98304 * k + 37151 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37151) = 147456 * k + 55727 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55727) = 221184 * k + 83591 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83591) = 331776 * k + 125387 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 125387) = 497664 * k + 188081 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 188081) = 746496 * k + 282122 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 282122) = 373248 * k + 141061 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 141061) = 559872 * k + 211592 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 211592) = 279936 * k + 105796 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 105796) = 139968 * k + 52898 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 52898) = 69984 * k + 26449 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 26449) = 104976 * k + 39674 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 39674) = 52488 * k + 19837 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 19837) = 78732 * k + 29756 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29756) = 39366 * k + 14878 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 14878) = 19683 * k + 7439 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_24815_mod_65536 {n : ℕ} (hn : n % 65536 = 24815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 24815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 24815) = 98304 * k + 37223 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37223) = 147456 * k + 55835 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 55835) = 221184 * k + 83753 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 83753) = 331776 * k + 125630 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 125630) = 165888 * k + 62815 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 62815) = 248832 * k + 94223 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 94223) = 373248 * k + 141335 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 141335) = 559872 * k + 212003 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 212003) = 839808 * k + 318005 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 318005) = 1259712 * k + 477008 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 477008) = 629856 * k + 238504 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 238504) = 314928 * k + 119252 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 119252) = 157464 * k + 59626 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 59626) = 78732 * k + 29813 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 29813) = 118098 * k + 44720 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 44720) = 59049 * k + 22360 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 24815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 24815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25247_mod_65536 {n : ℕ} (hn : n % 65536 = 25247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25247) = 98304 * k + 37871 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 37871) = 147456 * k + 56807 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 56807) = 221184 * k + 85211 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 85211) = 331776 * k + 127817 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 127817) = 497664 * k + 191726 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 191726) = 248832 * k + 95863 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 95863) = 373248 * k + 143795 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 143795) = 559872 * k + 215693 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 215693) = 839808 * k + 323540 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 323540) = 419904 * k + 161770 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 161770) = 209952 * k + 80885 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 80885) = 314928 * k + 121328 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 121328) = 157464 * k + 60664 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 60664) = 78732 * k + 30332 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30332) = 39366 * k + 15166 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15166) = 19683 * k + 7583 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25371_mod_65536 {n : ℕ} (hn : n % 65536 = 25371) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25371 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25371) = 98304 * k + 38057 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38057) = 147456 * k + 57086 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57086) = 73728 * k + 28543 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 28543) = 110592 * k + 42815 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 42815) = 165888 * k + 64223 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 64223) = 248832 * k + 96335 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 96335) = 373248 * k + 144503 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 144503) = 559872 * k + 216755 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 216755) = 839808 * k + 325133 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 325133) = 1259712 * k + 487700 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 487700) = 629856 * k + 243850 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 243850) = 314928 * k + 121925 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 121925) = 472392 * k + 182888 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 182888) = 236196 * k + 91444 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 91444) = 118098 * k + 45722 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 45722) = 59049 * k + 22861 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25371) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25371)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25415_mod_65536 {n : ℕ} (hn : n % 65536 = 25415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25415) = 98304 * k + 38123 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38123) = 147456 * k + 57185 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57185) = 221184 * k + 85778 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 85778) = 110592 * k + 42889 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 42889) = 165888 * k + 64334 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 64334) = 82944 * k + 32167 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 32167) = 124416 * k + 48251 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 48251) = 186624 * k + 72377 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 72377) = 279936 * k + 108566 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 108566) = 139968 * k + 54283 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 54283) = 209952 * k + 81425 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 81425) = 314928 * k + 122138 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 122138) = 157464 * k + 61069 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61069) = 236196 * k + 91604 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 91604) = 118098 * k + 45802 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 45802) = 59049 * k + 22901 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25471_mod_65536 {n : ℕ} (hn : n % 65536 = 25471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25471) = 98304 * k + 38207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38207) = 147456 * k + 57311 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57311) = 221184 * k + 85967 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 85967) = 331776 * k + 128951 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 128951) = 497664 * k + 193427 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 193427) = 746496 * k + 290141 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 290141) = 1119744 * k + 435212 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 435212) = 559872 * k + 217606 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 217606) = 279936 * k + 108803 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 108803) = 419904 * k + 163205 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 163205) = 629856 * k + 244808 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 244808) = 314928 * k + 122404 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 122404) = 157464 * k + 61202 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61202) = 78732 * k + 30601 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30601) = 118098 * k + 45902 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 45902) = 59049 * k + 22951 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25503_mod_65536 {n : ℕ} (hn : n % 65536 = 25503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25503) = 98304 * k + 38255 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38255) = 147456 * k + 57383 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57383) = 221184 * k + 86075 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86075) = 331776 * k + 129113 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 129113) = 497664 * k + 193670 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 193670) = 248832 * k + 96835 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 96835) = 373248 * k + 145253 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 145253) = 559872 * k + 217880 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 217880) = 279936 * k + 108940 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 108940) = 139968 * k + 54470 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 54470) = 69984 * k + 27235 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 27235) = 104976 * k + 40853 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 40853) = 157464 * k + 61280 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61280) = 78732 * k + 30640 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30640) = 39366 * k + 15320 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15320) = 19683 * k + 7660 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25583_mod_65536 {n : ℕ} (hn : n % 65536 = 25583) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25583 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25583) = 98304 * k + 38375 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38375) = 147456 * k + 57563 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57563) = 221184 * k + 86345 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86345) = 331776 * k + 129518 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 129518) = 165888 * k + 64759 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 64759) = 248832 * k + 97139 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 97139) = 373248 * k + 145709 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 145709) = 559872 * k + 218564 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 218564) = 279936 * k + 109282 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 109282) = 139968 * k + 54641 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 54641) = 209952 * k + 81962 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 81962) = 104976 * k + 40981 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 40981) = 157464 * k + 61472 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61472) = 78732 * k + 30736 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30736) = 39366 * k + 15368 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15368) = 19683 * k + 7684 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25583) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25583)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25599_mod_65536 {n : ℕ} (hn : n % 65536 = 25599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25599) = 98304 * k + 38399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38399) = 147456 * k + 57599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57599) = 221184 * k + 86399 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86399) = 331776 * k + 129599 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 129599) = 497664 * k + 194399 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 194399) = 746496 * k + 291599 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 291599) = 1119744 * k + 437399 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 437399) = 1679616 * k + 656099 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 656099) = 2519424 * k + 984149 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 984149) = 3779136 * k + 1476224 := by unfold T; split <;> omega
  have h11 : T (3779136 * k + 1476224) = 1889568 * k + 738112 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 738112) = 944784 * k + 369056 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 369056) = 472392 * k + 184528 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 184528) = 236196 * k + 92264 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 92264) = 118098 * k + 46132 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46132) = 59049 * k + 23066 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25671_mod_65536 {n : ℕ} (hn : n % 65536 = 25671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25671) = 98304 * k + 38507 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38507) = 147456 * k + 57761 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57761) = 221184 * k + 86642 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86642) = 110592 * k + 43321 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 43321) = 165888 * k + 64982 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 64982) = 82944 * k + 32491 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 32491) = 124416 * k + 48737 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 48737) = 186624 * k + 73106 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73106) = 93312 * k + 36553 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 36553) = 139968 * k + 54830 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 54830) = 69984 * k + 27415 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 27415) = 104976 * k + 41123 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41123) = 157464 * k + 61685 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61685) = 236196 * k + 92528 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 92528) = 118098 * k + 46264 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46264) = 59049 * k + 23132 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25691_mod_65536 {n : ℕ} (hn : n % 65536 = 25691) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25691 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25691) = 98304 * k + 38537 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38537) = 147456 * k + 57806 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57806) = 73728 * k + 28903 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 28903) = 110592 * k + 43355 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 43355) = 165888 * k + 65033 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65033) = 248832 * k + 97550 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 97550) = 124416 * k + 48775 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 48775) = 186624 * k + 73163 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73163) = 279936 * k + 109745 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 109745) = 419904 * k + 164618 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 164618) = 209952 * k + 82309 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82309) = 314928 * k + 123464 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 123464) = 157464 * k + 61732 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61732) = 78732 * k + 30866 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30866) = 39366 * k + 15433 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15433) = 59049 * k + 23150 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25691) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25691)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25703_mod_65536 {n : ℕ} (hn : n % 65536 = 25703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25703) = 98304 * k + 38555 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38555) = 147456 * k + 57833 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57833) = 221184 * k + 86750 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86750) = 110592 * k + 43375 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 43375) = 165888 * k + 65063 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65063) = 248832 * k + 97595 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 97595) = 373248 * k + 146393 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 146393) = 559872 * k + 219590 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 219590) = 279936 * k + 109795 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 109795) = 419904 * k + 164693 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 164693) = 629856 * k + 247040 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 247040) = 314928 * k + 123520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 123520) = 157464 * k + 61760 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 61760) = 78732 * k + 30880 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30880) = 39366 * k + 15440 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15440) = 19683 * k + 7720 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25711_mod_65536 {n : ℕ} (hn : n % 65536 = 25711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25711) = 98304 * k + 38567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38567) = 147456 * k + 57851 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 57851) = 221184 * k + 86777 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 86777) = 331776 * k + 130166 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 130166) = 165888 * k + 65083 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65083) = 248832 * k + 97625 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 97625) = 373248 * k + 146438 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 146438) = 186624 * k + 73219 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73219) = 279936 * k + 109829 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 109829) = 419904 * k + 164744 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 164744) = 209952 * k + 82372 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82372) = 104976 * k + 41186 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41186) = 52488 * k + 20593 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 20593) = 78732 * k + 30890 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30890) = 39366 * k + 15445 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15445) = 59049 * k + 23168 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25791_mod_65536 {n : ℕ} (hn : n % 65536 = 25791) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25791 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25791) = 98304 * k + 38687 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38687) = 147456 * k + 58031 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58031) = 221184 * k + 87047 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87047) = 331776 * k + 130571 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 130571) = 497664 * k + 195857 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 195857) = 746496 * k + 293786 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 293786) = 373248 * k + 146893 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 146893) = 559872 * k + 220340 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 220340) = 279936 * k + 110170 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 110170) = 139968 * k + 55085 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55085) = 209952 * k + 82628 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82628) = 104976 * k + 41314 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41314) = 52488 * k + 20657 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 20657) = 78732 * k + 30986 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 30986) = 39366 * k + 15493 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15493) = 59049 * k + 23240 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25791) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25791)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25823_mod_65536 {n : ℕ} (hn : n % 65536 = 25823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25823) = 98304 * k + 38735 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38735) = 147456 * k + 58103 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58103) = 221184 * k + 87155 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87155) = 331776 * k + 130733 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 130733) = 497664 * k + 196100 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 196100) = 248832 * k + 98050 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 98050) = 124416 * k + 49025 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 49025) = 186624 * k + 73538 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73538) = 93312 * k + 36769 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 36769) = 139968 * k + 55154 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55154) = 69984 * k + 27577 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 27577) = 104976 * k + 41366 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41366) = 52488 * k + 20683 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 20683) = 78732 * k + 31025 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31025) = 118098 * k + 46538 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46538) = 59049 * k + 23269 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25831_mod_65536 {n : ℕ} (hn : n % 65536 = 25831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25831) = 98304 * k + 38747 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38747) = 147456 * k + 58121 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58121) = 221184 * k + 87182 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87182) = 110592 * k + 43591 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 43591) = 165888 * k + 65387 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65387) = 248832 * k + 98081 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 98081) = 373248 * k + 147122 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 147122) = 186624 * k + 73561 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73561) = 279936 * k + 110342 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 110342) = 139968 * k + 55171 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55171) = 209952 * k + 82757 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82757) = 314928 * k + 124136 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 124136) = 157464 * k + 62068 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 62068) = 78732 * k + 31034 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31034) = 39366 * k + 15517 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15517) = 59049 * k + 23276 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25851_mod_65536 {n : ℕ} (hn : n % 65536 = 25851) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25851 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25851) = 98304 * k + 38777 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38777) = 147456 * k + 58166 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58166) = 73728 * k + 29083 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 29083) = 110592 * k + 43625 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 43625) = 165888 * k + 65438 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65438) = 82944 * k + 32719 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 32719) = 124416 * k + 49079 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 49079) = 186624 * k + 73619 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73619) = 279936 * k + 110429 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 110429) = 419904 * k + 165644 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 165644) = 209952 * k + 82822 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82822) = 104976 * k + 41411 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41411) = 157464 * k + 62117 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 62117) = 236196 * k + 93176 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 93176) = 118098 * k + 46588 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46588) = 59049 * k + 23294 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25851) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25851)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_25903_mod_65536 {n : ℕ} (hn : n % 65536 = 25903) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 25903 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 25903) = 98304 * k + 38855 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 38855) = 147456 * k + 58283 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58283) = 221184 * k + 87425 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87425) = 331776 * k + 131138 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 131138) = 165888 * k + 65569 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65569) = 248832 * k + 98354 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 98354) = 124416 * k + 49177 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 49177) = 186624 * k + 73766 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 73766) = 93312 * k + 36883 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 36883) = 139968 * k + 55325 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55325) = 209952 * k + 82988 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 82988) = 104976 * k + 41494 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41494) = 52488 * k + 20747 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 20747) = 78732 * k + 31121 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31121) = 118098 * k + 46682 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46682) = 59049 * k + 23341 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 25903) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 25903)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26015_mod_65536 {n : ℕ} (hn : n % 65536 = 26015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26015) = 98304 * k + 39023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39023) = 147456 * k + 58535 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58535) = 221184 * k + 87803 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87803) = 331776 * k + 131705 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 131705) = 497664 * k + 197558 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 197558) = 248832 * k + 98779 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 98779) = 373248 * k + 148169 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 148169) = 559872 * k + 222254 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 222254) = 279936 * k + 111127 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 111127) = 419904 * k + 166691 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 166691) = 629856 * k + 250037 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 250037) = 944784 * k + 375056 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 375056) = 472392 * k + 187528 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 187528) = 236196 * k + 93764 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 93764) = 118098 * k + 46882 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46882) = 59049 * k + 23441 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26063_mod_65536 {n : ℕ} (hn : n % 65536 = 26063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26063) = 98304 * k + 39095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39095) = 147456 * k + 58643 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58643) = 221184 * k + 87965 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 87965) = 331776 * k + 131948 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 131948) = 165888 * k + 65974 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 65974) = 82944 * k + 32987 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 32987) = 124416 * k + 49481 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 49481) = 186624 * k + 74222 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 74222) = 93312 * k + 37111 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 37111) = 139968 * k + 55667 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55667) = 209952 * k + 83501 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 83501) = 314928 * k + 125252 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 125252) = 157464 * k + 62626 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 62626) = 78732 * k + 31313 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31313) = 118098 * k + 46970 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 46970) = 59049 * k + 23485 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26087_mod_65536 {n : ℕ} (hn : n % 65536 = 26087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26087) = 98304 * k + 39131 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39131) = 147456 * k + 58697 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58697) = 221184 * k + 88046 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88046) = 110592 * k + 44023 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44023) = 165888 * k + 66035 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66035) = 248832 * k + 99053 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 99053) = 373248 * k + 148580 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 148580) = 186624 * k + 74290 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 74290) = 93312 * k + 37145 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 37145) = 139968 * k + 55718 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55718) = 69984 * k + 27859 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 27859) = 104976 * k + 41789 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41789) = 157464 * k + 62684 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 62684) = 78732 * k + 31342 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31342) = 39366 * k + 15671 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15671) = 59049 * k + 23507 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26143_mod_65536 {n : ℕ} (hn : n % 65536 = 26143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26143) = 98304 * k + 39215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39215) = 147456 * k + 58823 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 58823) = 221184 * k + 88235 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88235) = 331776 * k + 132353 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 132353) = 497664 * k + 198530 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 198530) = 248832 * k + 99265 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 99265) = 373248 * k + 148898 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 148898) = 186624 * k + 74449 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 74449) = 279936 * k + 111674 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 111674) = 139968 * k + 55837 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 55837) = 209952 * k + 83756 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 83756) = 104976 * k + 41878 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 41878) = 52488 * k + 20939 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 20939) = 78732 * k + 31409 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31409) = 118098 * k + 47114 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47114) = 59049 * k + 23557 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26267_mod_65536 {n : ℕ} (hn : n % 65536 = 26267) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26267 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26267) = 98304 * k + 39401 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39401) = 147456 * k + 59102 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59102) = 73728 * k + 29551 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 29551) = 110592 * k + 44327 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44327) = 165888 * k + 66491 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66491) = 248832 * k + 99737 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 99737) = 373248 * k + 149606 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 149606) = 186624 * k + 74803 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 74803) = 279936 * k + 112205 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 112205) = 419904 * k + 168308 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 168308) = 209952 * k + 84154 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84154) = 104976 * k + 42077 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42077) = 157464 * k + 63116 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63116) = 78732 * k + 31558 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31558) = 39366 * k + 15779 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15779) = 59049 * k + 23669 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26267) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26267)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26303_mod_65536 {n : ℕ} (hn : n % 65536 = 26303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26303) = 98304 * k + 39455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39455) = 147456 * k + 59183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59183) = 221184 * k + 88775 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88775) = 331776 * k + 133163 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 133163) = 497664 * k + 199745 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 199745) = 746496 * k + 299618 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 299618) = 373248 * k + 149809 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 149809) = 559872 * k + 224714 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 224714) = 279936 * k + 112357 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 112357) = 419904 * k + 168536 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 168536) = 209952 * k + 84268 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84268) = 104976 * k + 42134 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42134) = 52488 * k + 21067 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 21067) = 78732 * k + 31601 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31601) = 118098 * k + 47402 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47402) = 59049 * k + 23701 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26343_mod_65536 {n : ℕ} (hn : n % 65536 = 26343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26343) = 98304 * k + 39515 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39515) = 147456 * k + 59273 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59273) = 221184 * k + 88910 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88910) = 110592 * k + 44455 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44455) = 165888 * k + 66683 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66683) = 248832 * k + 100025 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 100025) = 373248 * k + 150038 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 150038) = 186624 * k + 75019 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75019) = 279936 * k + 112529 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 112529) = 419904 * k + 168794 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 168794) = 209952 * k + 84397 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84397) = 314928 * k + 126596 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 126596) = 157464 * k + 63298 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63298) = 78732 * k + 31649 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31649) = 118098 * k + 47474 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47474) = 59049 * k + 23737 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26351_mod_65536 {n : ℕ} (hn : n % 65536 = 26351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26351) = 98304 * k + 39527 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39527) = 147456 * k + 59291 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59291) = 221184 * k + 88937 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88937) = 331776 * k + 133406 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 133406) = 165888 * k + 66703 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66703) = 248832 * k + 100055 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 100055) = 373248 * k + 150083 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 150083) = 559872 * k + 225125 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 225125) = 839808 * k + 337688 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 337688) = 419904 * k + 168844 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 168844) = 209952 * k + 84422 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84422) = 104976 * k + 42211 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42211) = 157464 * k + 63317 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63317) = 236196 * k + 94976 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 94976) = 118098 * k + 47488 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47488) = 59049 * k + 23744 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26367_mod_65536 {n : ℕ} (hn : n % 65536 = 26367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26367) = 98304 * k + 39551 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39551) = 147456 * k + 59327 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59327) = 221184 * k + 88991 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 88991) = 331776 * k + 133487 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 133487) = 497664 * k + 200231 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 200231) = 746496 * k + 300347 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 300347) = 1119744 * k + 450521 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 450521) = 1679616 * k + 675782 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 675782) = 839808 * k + 337891 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 337891) = 1259712 * k + 506837 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 506837) = 1889568 * k + 760256 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 760256) = 944784 * k + 380128 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 380128) = 472392 * k + 190064 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 190064) = 236196 * k + 95032 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 95032) = 118098 * k + 47516 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47516) = 59049 * k + 23758 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26439_mod_65536 {n : ℕ} (hn : n % 65536 = 26439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26439) = 98304 * k + 39659 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39659) = 147456 * k + 59489 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59489) = 221184 * k + 89234 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 89234) = 110592 * k + 44617 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44617) = 165888 * k + 66926 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66926) = 82944 * k + 33463 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 33463) = 124416 * k + 50195 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 50195) = 186624 * k + 75293 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75293) = 279936 * k + 112940 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 112940) = 139968 * k + 56470 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 56470) = 69984 * k + 28235 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 28235) = 104976 * k + 42353 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42353) = 157464 * k + 63530 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63530) = 78732 * k + 31765 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31765) = 118098 * k + 47648 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47648) = 59049 * k + 23824 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26459_mod_65536 {n : ℕ} (hn : n % 65536 = 26459) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26459 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26459) = 98304 * k + 39689 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39689) = 147456 * k + 59534 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59534) = 73728 * k + 29767 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 29767) = 110592 * k + 44651 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44651) = 165888 * k + 66977 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 66977) = 248832 * k + 100466 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 100466) = 124416 * k + 50233 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 50233) = 186624 * k + 75350 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75350) = 93312 * k + 37675 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 37675) = 139968 * k + 56513 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 56513) = 209952 * k + 84770 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84770) = 104976 * k + 42385 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42385) = 157464 * k + 63578 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63578) = 78732 * k + 31789 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31789) = 118098 * k + 47684 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47684) = 59049 * k + 23842 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26459) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26459)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26527_mod_65536 {n : ℕ} (hn : n % 65536 = 26527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26527) = 98304 * k + 39791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39791) = 147456 * k + 59687 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59687) = 221184 * k + 89531 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 89531) = 331776 * k + 134297 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 134297) = 497664 * k + 201446 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 201446) = 248832 * k + 100723 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 100723) = 373248 * k + 151085 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 151085) = 559872 * k + 226628 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 226628) = 279936 * k + 113314 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 113314) = 139968 * k + 56657 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 56657) = 209952 * k + 84986 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 84986) = 104976 * k + 42493 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42493) = 157464 * k + 63740 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63740) = 78732 * k + 31870 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31870) = 39366 * k + 15935 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15935) = 59049 * k + 23903 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26535_mod_65536 {n : ℕ} (hn : n % 65536 = 26535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26535) = 98304 * k + 39803 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39803) = 147456 * k + 59705 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59705) = 221184 * k + 89558 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 89558) = 110592 * k + 44779 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44779) = 165888 * k + 67169 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 67169) = 248832 * k + 100754 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 100754) = 124416 * k + 50377 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 50377) = 186624 * k + 75566 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75566) = 93312 * k + 37783 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 37783) = 139968 * k + 56675 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 56675) = 209952 * k + 85013 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 85013) = 314928 * k + 127520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 127520) = 157464 * k + 63760 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 63760) = 78732 * k + 31880 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 31880) = 39366 * k + 15940 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 15940) = 19683 * k + 7970 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26619_mod_65536 {n : ℕ} (hn : n % 65536 = 26619) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26619 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26619) = 98304 * k + 39929 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39929) = 147456 * k + 59894 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59894) = 73728 * k + 29947 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 29947) = 110592 * k + 44921 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 44921) = 165888 * k + 67382 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 67382) = 82944 * k + 33691 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 33691) = 124416 * k + 50537 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 50537) = 186624 * k + 75806 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75806) = 93312 * k + 37903 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 37903) = 139968 * k + 56855 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 56855) = 209952 * k + 85283 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 85283) = 314928 * k + 127925 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 127925) = 472392 * k + 191888 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 191888) = 236196 * k + 95944 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 95944) = 118098 * k + 47972 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 47972) = 59049 * k + 23986 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26619) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26619)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_26655_mod_65536 {n : ℕ} (hn : n % 65536 = 26655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 26655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 26655) = 98304 * k + 39983 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 39983) = 147456 * k + 59975 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 59975) = 221184 * k + 89963 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 89963) = 331776 * k + 134945 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 134945) = 497664 * k + 202418 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 202418) = 248832 * k + 101209 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 101209) = 373248 * k + 151814 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 151814) = 186624 * k + 75907 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 75907) = 279936 * k + 113861 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 113861) = 419904 * k + 170792 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 170792) = 209952 * k + 85396 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 85396) = 104976 * k + 42698 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 42698) = 52488 * k + 21349 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 21349) = 78732 * k + 32024 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32024) = 39366 * k + 16012 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16012) = 19683 * k + 8006 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 26655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 26655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27039_mod_65536 {n : ℕ} (hn : n % 65536 = 27039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27039) = 98304 * k + 40559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40559) = 147456 * k + 60839 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 60839) = 221184 * k + 91259 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 91259) = 331776 * k + 136889 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 136889) = 497664 * k + 205334 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 205334) = 248832 * k + 102667 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 102667) = 373248 * k + 154001 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 154001) = 559872 * k + 231002 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 231002) = 279936 * k + 115501 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 115501) = 419904 * k + 173252 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 173252) = 209952 * k + 86626 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 86626) = 104976 * k + 43313 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 43313) = 157464 * k + 64970 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 64970) = 78732 * k + 32485 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32485) = 118098 * k + 48728 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 48728) = 59049 * k + 24364 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27111_mod_65536 {n : ℕ} (hn : n % 65536 = 27111) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27111 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27111) = 98304 * k + 40667 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40667) = 147456 * k + 61001 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61001) = 221184 * k + 91502 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 91502) = 110592 * k + 45751 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 45751) = 165888 * k + 68627 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 68627) = 248832 * k + 102941 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 102941) = 373248 * k + 154412 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 154412) = 186624 * k + 77206 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 77206) = 93312 * k + 38603 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 38603) = 139968 * k + 57905 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 57905) = 209952 * k + 86858 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 86858) = 104976 * k + 43429 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 43429) = 157464 * k + 65144 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65144) = 78732 * k + 32572 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32572) = 39366 * k + 16286 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16286) = 19683 * k + 8143 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27111) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27111)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27119_mod_65536 {n : ℕ} (hn : n % 65536 = 27119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27119) = 98304 * k + 40679 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40679) = 147456 * k + 61019 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61019) = 221184 * k + 91529 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 91529) = 331776 * k + 137294 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 137294) = 165888 * k + 68647 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 68647) = 248832 * k + 102971 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 102971) = 373248 * k + 154457 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 154457) = 559872 * k + 231686 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 231686) = 279936 * k + 115843 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 115843) = 419904 * k + 173765 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 173765) = 629856 * k + 260648 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 260648) = 314928 * k + 130324 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 130324) = 157464 * k + 65162 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65162) = 78732 * k + 32581 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32581) = 118098 * k + 48872 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 48872) = 59049 * k + 24436 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27239_mod_65536 {n : ℕ} (hn : n % 65536 = 27239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27239) = 98304 * k + 40859 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40859) = 147456 * k + 61289 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61289) = 221184 * k + 91934 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 91934) = 110592 * k + 45967 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 45967) = 165888 * k + 68951 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 68951) = 248832 * k + 103427 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 103427) = 373248 * k + 155141 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 155141) = 559872 * k + 232712 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 232712) = 279936 * k + 116356 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 116356) = 139968 * k + 58178 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 58178) = 69984 * k + 29089 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 29089) = 104976 * k + 43634 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 43634) = 52488 * k + 21817 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 21817) = 78732 * k + 32726 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32726) = 39366 * k + 16363 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16363) = 59049 * k + 24545 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27291_mod_65536 {n : ℕ} (hn : n % 65536 = 27291) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27291 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27291) = 98304 * k + 40937 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40937) = 147456 * k + 61406 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61406) = 73728 * k + 30703 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 30703) = 110592 * k + 46055 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46055) = 165888 * k + 69083 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 69083) = 248832 * k + 103625 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 103625) = 373248 * k + 155438 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 155438) = 186624 * k + 77719 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 77719) = 279936 * k + 116579 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 116579) = 419904 * k + 174869 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 174869) = 629856 * k + 262304 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 262304) = 314928 * k + 131152 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 131152) = 157464 * k + 65576 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65576) = 78732 * k + 32788 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 32788) = 39366 * k + 16394 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16394) = 19683 * k + 8197 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27291) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27291)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27303_mod_65536 {n : ℕ} (hn : n % 65536 = 27303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27303) = 98304 * k + 40955 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 40955) = 147456 * k + 61433 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61433) = 221184 * k + 92150 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 92150) = 110592 * k + 46075 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46075) = 165888 * k + 69113 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 69113) = 248832 * k + 103670 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 103670) = 124416 * k + 51835 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 51835) = 186624 * k + 77753 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 77753) = 279936 * k + 116630 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 116630) = 139968 * k + 58315 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 58315) = 209952 * k + 87473 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 87473) = 314928 * k + 131210 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 131210) = 157464 * k + 65605 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65605) = 236196 * k + 98408 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 98408) = 118098 * k + 49204 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49204) = 59049 * k + 24602 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27343_mod_65536 {n : ℕ} (hn : n % 65536 = 27343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27343) = 98304 * k + 41015 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41015) = 147456 * k + 61523 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61523) = 221184 * k + 92285 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 92285) = 331776 * k + 138428 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 138428) = 165888 * k + 69214 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 69214) = 82944 * k + 34607 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 34607) = 124416 * k + 51911 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 51911) = 186624 * k + 77867 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 77867) = 279936 * k + 116801 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 116801) = 419904 * k + 175202 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 175202) = 209952 * k + 87601 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 87601) = 314928 * k + 131402 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 131402) = 157464 * k + 65701 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65701) = 236196 * k + 98552 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 98552) = 118098 * k + 49276 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49276) = 59049 * k + 24638 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27423_mod_65536 {n : ℕ} (hn : n % 65536 = 27423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27423) = 98304 * k + 41135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41135) = 147456 * k + 61703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 61703) = 221184 * k + 92555 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 92555) = 331776 * k + 138833 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 138833) = 497664 * k + 208250 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 208250) = 248832 * k + 104125 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 104125) = 373248 * k + 156188 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 156188) = 186624 * k + 78094 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 78094) = 93312 * k + 39047 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 39047) = 139968 * k + 58571 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 58571) = 209952 * k + 87857 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 87857) = 314928 * k + 131786 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 131786) = 157464 * k + 65893 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 65893) = 236196 * k + 98840 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 98840) = 118098 * k + 49420 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49420) = 59049 * k + 24710 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27559_mod_65536 {n : ℕ} (hn : n % 65536 = 27559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27559) = 98304 * k + 41339 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41339) = 147456 * k + 62009 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62009) = 221184 * k + 93014 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 93014) = 110592 * k + 46507 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46507) = 165888 * k + 69761 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 69761) = 248832 * k + 104642 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 104642) = 124416 * k + 52321 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 52321) = 186624 * k + 78482 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 78482) = 93312 * k + 39241 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 39241) = 139968 * k + 58862 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 58862) = 69984 * k + 29431 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 29431) = 104976 * k + 44147 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44147) = 157464 * k + 66221 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66221) = 236196 * k + 99332 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 99332) = 118098 * k + 49666 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49666) = 59049 * k + 24833 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27643_mod_65536 {n : ℕ} (hn : n % 65536 = 27643) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27643 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27643) = 98304 * k + 41465 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41465) = 147456 * k + 62198 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62198) = 73728 * k + 31099 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 31099) = 110592 * k + 46649 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46649) = 165888 * k + 69974 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 69974) = 82944 * k + 34987 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 34987) = 124416 * k + 52481 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 52481) = 186624 * k + 78722 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 78722) = 93312 * k + 39361 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 39361) = 139968 * k + 59042 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59042) = 69984 * k + 29521 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 29521) = 104976 * k + 44282 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44282) = 52488 * k + 22141 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22141) = 78732 * k + 33212 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33212) = 39366 * k + 16606 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16606) = 19683 * k + 8303 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27643) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27643)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27675_mod_65536 {n : ℕ} (hn : n % 65536 = 27675) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27675 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27675) = 98304 * k + 41513 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41513) = 147456 * k + 62270 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62270) = 73728 * k + 31135 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 31135) = 110592 * k + 46703 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46703) = 165888 * k + 70055 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70055) = 248832 * k + 105083 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 105083) = 373248 * k + 157625 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 157625) = 559872 * k + 236438 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 236438) = 279936 * k + 118219 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 118219) = 419904 * k + 177329 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 177329) = 629856 * k + 265994 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 265994) = 314928 * k + 132997 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 132997) = 472392 * k + 199496 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 199496) = 236196 * k + 99748 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 99748) = 118098 * k + 49874 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49874) = 59049 * k + 24937 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27675) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27675)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27711_mod_65536 {n : ℕ} (hn : n % 65536 = 27711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27711) = 98304 * k + 41567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41567) = 147456 * k + 62351 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62351) = 221184 * k + 93527 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 93527) = 331776 * k + 140291 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 140291) = 497664 * k + 210437 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 210437) = 746496 * k + 315656 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 315656) = 373248 * k + 157828 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 157828) = 186624 * k + 78914 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 78914) = 93312 * k + 39457 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 39457) = 139968 * k + 59186 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59186) = 69984 * k + 29593 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 29593) = 104976 * k + 44390 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44390) = 52488 * k + 22195 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22195) = 78732 * k + 33293 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33293) = 118098 * k + 49940 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49940) = 59049 * k + 24970 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27739_mod_65536 {n : ℕ} (hn : n % 65536 = 27739) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27739 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27739) = 98304 * k + 41609 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41609) = 147456 * k + 62414 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62414) = 73728 * k + 31207 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 31207) = 110592 * k + 46811 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 46811) = 165888 * k + 70217 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70217) = 248832 * k + 105326 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 105326) = 124416 * k + 52663 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 52663) = 186624 * k + 78995 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 78995) = 279936 * k + 118493 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 118493) = 419904 * k + 177740 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 177740) = 209952 * k + 88870 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 88870) = 104976 * k + 44435 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44435) = 157464 * k + 66653 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66653) = 236196 * k + 99980 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 99980) = 118098 * k + 49990 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 49990) = 59049 * k + 24995 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27739) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27739)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27759_mod_65536 {n : ℕ} (hn : n % 65536 = 27759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27759) = 98304 * k + 41639 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41639) = 147456 * k + 62459 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62459) = 221184 * k + 93689 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 93689) = 331776 * k + 140534 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 140534) = 165888 * k + 70267 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70267) = 248832 * k + 105401 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 105401) = 373248 * k + 158102 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 158102) = 186624 * k + 79051 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 79051) = 279936 * k + 118577 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 118577) = 419904 * k + 177866 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 177866) = 209952 * k + 88933 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 88933) = 314928 * k + 133400 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 133400) = 157464 * k + 66700 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66700) = 78732 * k + 33350 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33350) = 39366 * k + 16675 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16675) = 59049 * k + 25013 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27839_mod_65536 {n : ℕ} (hn : n % 65536 = 27839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27839) = 98304 * k + 41759 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41759) = 147456 * k + 62639 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62639) = 221184 * k + 93959 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 93959) = 331776 * k + 140939 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 140939) = 497664 * k + 211409 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 211409) = 746496 * k + 317114 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 317114) = 373248 * k + 158557 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 158557) = 559872 * k + 237836 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 237836) = 279936 * k + 118918 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 118918) = 139968 * k + 59459 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59459) = 209952 * k + 89189 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 89189) = 314928 * k + 133784 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 133784) = 157464 * k + 66892 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66892) = 78732 * k + 33446 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33446) = 39366 * k + 16723 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16723) = 59049 * k + 25085 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27855_mod_65536 {n : ℕ} (hn : n % 65536 = 27855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27855) = 98304 * k + 41783 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41783) = 147456 * k + 62675 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62675) = 221184 * k + 94013 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94013) = 331776 * k + 141020 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 141020) = 165888 * k + 70510 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70510) = 82944 * k + 35255 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 35255) = 124416 * k + 52883 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 52883) = 186624 * k + 79325 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 79325) = 279936 * k + 118988 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 118988) = 139968 * k + 59494 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59494) = 69984 * k + 29747 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 29747) = 104976 * k + 44621 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44621) = 157464 * k + 66932 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66932) = 78732 * k + 33466 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33466) = 39366 * k + 16733 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16733) = 59049 * k + 25100 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27879_mod_65536 {n : ℕ} (hn : n % 65536 = 27879) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27879 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27879) = 98304 * k + 41819 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41819) = 147456 * k + 62729 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62729) = 221184 * k + 94094 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94094) = 110592 * k + 47047 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 47047) = 165888 * k + 70571 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70571) = 248832 * k + 105857 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 105857) = 373248 * k + 158786 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 158786) = 186624 * k + 79393 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 79393) = 279936 * k + 119090 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 119090) = 139968 * k + 59545 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59545) = 209952 * k + 89318 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 89318) = 104976 * k + 44659 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44659) = 157464 * k + 66989 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 66989) = 236196 * k + 100484 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 100484) = 118098 * k + 50242 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50242) = 59049 * k + 25121 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27879) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27879)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27903_mod_65536 {n : ℕ} (hn : n % 65536 = 27903) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27903 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27903) = 98304 * k + 41855 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41855) = 147456 * k + 62783 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62783) = 221184 * k + 94175 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94175) = 331776 * k + 141263 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 141263) = 497664 * k + 211895 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 211895) = 746496 * k + 317843 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 317843) = 1119744 * k + 476765 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 476765) = 1679616 * k + 715148 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 715148) = 839808 * k + 357574 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 357574) = 419904 * k + 178787 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 178787) = 629856 * k + 268181 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 268181) = 944784 * k + 402272 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 402272) = 472392 * k + 201136 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 201136) = 236196 * k + 100568 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 100568) = 118098 * k + 50284 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50284) = 59049 * k + 25142 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27903) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27903)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27951_mod_65536 {n : ℕ} (hn : n % 65536 = 27951) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27951 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27951) = 98304 * k + 41927 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41927) = 147456 * k + 62891 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62891) = 221184 * k + 94337 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94337) = 331776 * k + 141506 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 141506) = 165888 * k + 70753 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70753) = 248832 * k + 106130 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 106130) = 124416 * k + 53065 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 53065) = 186624 * k + 79598 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 79598) = 93312 * k + 39799 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 39799) = 139968 * k + 59699 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59699) = 209952 * k + 89549 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 89549) = 314928 * k + 134324 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 134324) = 157464 * k + 67162 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 67162) = 78732 * k + 33581 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33581) = 118098 * k + 50372 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50372) = 59049 * k + 25186 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27951) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27951)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_27975_mod_65536 {n : ℕ} (hn : n % 65536 = 27975) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 27975 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 27975) = 98304 * k + 41963 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 41963) = 147456 * k + 62945 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 62945) = 221184 * k + 94418 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94418) = 110592 * k + 47209 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 47209) = 165888 * k + 70814 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 70814) = 82944 * k + 35407 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 35407) = 124416 * k + 53111 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 53111) = 186624 * k + 79667 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 79667) = 279936 * k + 119501 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 119501) = 419904 * k + 179252 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 179252) = 209952 * k + 89626 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 89626) = 104976 * k + 44813 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44813) = 157464 * k + 67220 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 67220) = 78732 * k + 33610 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33610) = 39366 * k + 16805 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16805) = 59049 * k + 25208 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 27975) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 27975)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28031_mod_65536 {n : ℕ} (hn : n % 65536 = 28031) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28031 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28031) = 98304 * k + 42047 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42047) = 147456 * k + 63071 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63071) = 221184 * k + 94607 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94607) = 331776 * k + 141911 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 141911) = 497664 * k + 212867 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 212867) = 746496 * k + 319301 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 319301) = 1119744 * k + 478952 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 478952) = 559872 * k + 239476 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 239476) = 279936 * k + 119738 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 119738) = 139968 * k + 59869 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 59869) = 209952 * k + 89804 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 89804) = 104976 * k + 44902 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 44902) = 52488 * k + 22451 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22451) = 78732 * k + 33677 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33677) = 118098 * k + 50516 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50516) = 59049 * k + 25258 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28031) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28031)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28095_mod_65536 {n : ℕ} (hn : n % 65536 = 28095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28095) = 98304 * k + 42143 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42143) = 147456 * k + 63215 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63215) = 221184 * k + 94823 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 94823) = 331776 * k + 142235 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 142235) = 497664 * k + 213353 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 213353) = 746496 * k + 320030 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 320030) = 373248 * k + 160015 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 160015) = 559872 * k + 240023 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 240023) = 839808 * k + 360035 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 360035) = 1259712 * k + 540053 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 540053) = 1889568 * k + 810080 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 810080) = 944784 * k + 405040 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 405040) = 472392 * k + 202520 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 202520) = 236196 * k + 101260 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 101260) = 118098 * k + 50630 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50630) = 59049 * k + 25315 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28191_mod_65536 {n : ℕ} (hn : n % 65536 = 28191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28191) = 98304 * k + 42287 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42287) = 147456 * k + 63431 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63431) = 221184 * k + 95147 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 95147) = 331776 * k + 142721 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 142721) = 497664 * k + 214082 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 214082) = 248832 * k + 107041 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 107041) = 373248 * k + 160562 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 160562) = 186624 * k + 80281 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 80281) = 279936 * k + 120422 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 120422) = 139968 * k + 60211 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60211) = 209952 * k + 90317 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 90317) = 314928 * k + 135476 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 135476) = 157464 * k + 67738 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 67738) = 78732 * k + 33869 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33869) = 118098 * k + 50804 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 50804) = 59049 * k + 25402 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28263_mod_65536 {n : ℕ} (hn : n % 65536 = 28263) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28263 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28263) = 98304 * k + 42395 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42395) = 147456 * k + 63593 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63593) = 221184 * k + 95390 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 95390) = 110592 * k + 47695 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 47695) = 165888 * k + 71543 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 71543) = 248832 * k + 107315 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 107315) = 373248 * k + 160973 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 160973) = 559872 * k + 241460 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 241460) = 279936 * k + 120730 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 120730) = 139968 * k + 60365 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60365) = 209952 * k + 90548 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 90548) = 104976 * k + 45274 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45274) = 52488 * k + 22637 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22637) = 78732 * k + 33956 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 33956) = 39366 * k + 16978 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 16978) = 19683 * k + 8489 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28263) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28263)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28319_mod_65536 {n : ℕ} (hn : n % 65536 = 28319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28319) = 98304 * k + 42479 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42479) = 147456 * k + 63719 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63719) = 221184 * k + 95579 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 95579) = 331776 * k + 143369 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 143369) = 497664 * k + 215054 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 215054) = 248832 * k + 107527 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 107527) = 373248 * k + 161291 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 161291) = 559872 * k + 241937 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 241937) = 839808 * k + 362906 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 362906) = 419904 * k + 181453 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 181453) = 629856 * k + 272180 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 272180) = 314928 * k + 136090 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 136090) = 157464 * k + 68045 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68045) = 236196 * k + 102068 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 102068) = 118098 * k + 51034 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51034) = 59049 * k + 25517 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28327_mod_65536 {n : ℕ} (hn : n % 65536 = 28327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28327) = 98304 * k + 42491 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42491) = 147456 * k + 63737 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63737) = 221184 * k + 95606 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 95606) = 110592 * k + 47803 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 47803) = 165888 * k + 71705 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 71705) = 248832 * k + 107558 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 107558) = 124416 * k + 53779 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 53779) = 186624 * k + 80669 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 80669) = 279936 * k + 121004 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 121004) = 139968 * k + 60502 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60502) = 69984 * k + 30251 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 30251) = 104976 * k + 45377 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45377) = 157464 * k + 68066 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68066) = 78732 * k + 34033 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34033) = 118098 * k + 51050 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51050) = 59049 * k + 25525 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28351_mod_65536 {n : ℕ} (hn : n % 65536 = 28351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28351) = 98304 * k + 42527 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42527) = 147456 * k + 63791 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 63791) = 221184 * k + 95687 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 95687) = 331776 * k + 143531 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 143531) = 497664 * k + 215297 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 215297) = 746496 * k + 322946 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 322946) = 373248 * k + 161473 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 161473) = 559872 * k + 242210 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 242210) = 279936 * k + 121105 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 121105) = 419904 * k + 181658 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 181658) = 209952 * k + 90829 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 90829) = 314928 * k + 136244 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 136244) = 157464 * k + 68122 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68122) = 78732 * k + 34061 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34061) = 118098 * k + 51092 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51092) = 59049 * k + 25546 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28447_mod_65536 {n : ℕ} (hn : n % 65536 = 28447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28447) = 98304 * k + 42671 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42671) = 147456 * k + 64007 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64007) = 221184 * k + 96011 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 96011) = 331776 * k + 144017 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 144017) = 497664 * k + 216026 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 216026) = 248832 * k + 108013 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 108013) = 373248 * k + 162020 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 162020) = 186624 * k + 81010 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 81010) = 93312 * k + 40505 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 40505) = 139968 * k + 60758 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60758) = 69984 * k + 30379 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 30379) = 104976 * k + 45569 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45569) = 157464 * k + 68354 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68354) = 78732 * k + 34177 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34177) = 118098 * k + 51266 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51266) = 59049 * k + 25633 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28507_mod_65536 {n : ℕ} (hn : n % 65536 = 28507) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28507 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28507) = 98304 * k + 42761 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42761) = 147456 * k + 64142 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64142) = 73728 * k + 32071 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 32071) = 110592 * k + 48107 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 48107) = 165888 * k + 72161 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 72161) = 248832 * k + 108242 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 108242) = 124416 * k + 54121 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 54121) = 186624 * k + 81182 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 81182) = 93312 * k + 40591 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 40591) = 139968 * k + 60887 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60887) = 209952 * k + 91331 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 91331) = 314928 * k + 136997 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 136997) = 472392 * k + 205496 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 205496) = 236196 * k + 102748 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 102748) = 118098 * k + 51374 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51374) = 59049 * k + 25687 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28507) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28507)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28527_mod_65536 {n : ℕ} (hn : n % 65536 = 28527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28527) = 98304 * k + 42791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42791) = 147456 * k + 64187 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64187) = 221184 * k + 96281 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 96281) = 331776 * k + 144422 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 144422) = 165888 * k + 72211 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 72211) = 248832 * k + 108317 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 108317) = 373248 * k + 162476 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 162476) = 186624 * k + 81238 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 81238) = 93312 * k + 40619 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 40619) = 139968 * k + 60929 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 60929) = 209952 * k + 91394 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 91394) = 104976 * k + 45697 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45697) = 157464 * k + 68546 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68546) = 78732 * k + 34273 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34273) = 118098 * k + 51410 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 51410) = 59049 * k + 25705 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28543_mod_65536 {n : ℕ} (hn : n % 65536 = 28543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28543) = 98304 * k + 42815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 42815) = 147456 * k + 64223 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64223) = 221184 * k + 96335 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 96335) = 331776 * k + 144503 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 144503) = 497664 * k + 216755 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 216755) = 746496 * k + 325133 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 325133) = 1119744 * k + 487700 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 487700) = 559872 * k + 243850 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 243850) = 279936 * k + 121925 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 121925) = 419904 * k + 182888 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 182888) = 209952 * k + 91444 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 91444) = 104976 * k + 45722 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45722) = 52488 * k + 22861 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22861) = 78732 * k + 34292 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34292) = 39366 * k + 17146 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17146) = 19683 * k + 8573 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28667_mod_65536 {n : ℕ} (hn : n % 65536 = 28667) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28667 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28667) = 98304 * k + 43001 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43001) = 147456 * k + 64502 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64502) = 73728 * k + 32251 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 32251) = 110592 * k + 48377 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 48377) = 165888 * k + 72566 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 72566) = 82944 * k + 36283 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 36283) = 124416 * k + 54425 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 54425) = 186624 * k + 81638 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 81638) = 93312 * k + 40819 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 40819) = 139968 * k + 61229 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 61229) = 209952 * k + 91844 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 91844) = 104976 * k + 45922 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 45922) = 52488 * k + 22961 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 22961) = 78732 * k + 34442 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34442) = 39366 * k + 17221 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17221) = 59049 * k + 25832 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28667) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28667)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28703_mod_65536 {n : ℕ} (hn : n % 65536 = 28703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28703) = 98304 * k + 43055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43055) = 147456 * k + 64583 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64583) = 221184 * k + 96875 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 96875) = 331776 * k + 145313 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 145313) = 497664 * k + 217970 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 217970) = 248832 * k + 108985 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 108985) = 373248 * k + 163478 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 163478) = 186624 * k + 81739 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 81739) = 279936 * k + 122609 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 122609) = 419904 * k + 183914 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 183914) = 209952 * k + 91957 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 91957) = 314928 * k + 137936 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 137936) = 157464 * k + 68968 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 68968) = 78732 * k + 34484 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34484) = 39366 * k + 17242 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17242) = 19683 * k + 8621 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28827_mod_65536 {n : ℕ} (hn : n % 65536 = 28827) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28827 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28827) = 98304 * k + 43241 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43241) = 147456 * k + 64862 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64862) = 73728 * k + 32431 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 32431) = 110592 * k + 48647 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 48647) = 165888 * k + 72971 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 72971) = 248832 * k + 109457 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 109457) = 373248 * k + 164186 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 164186) = 186624 * k + 82093 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 82093) = 279936 * k + 123140 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 123140) = 139968 * k + 61570 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 61570) = 69984 * k + 30785 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 30785) = 104976 * k + 46178 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 46178) = 52488 * k + 23089 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 23089) = 78732 * k + 34634 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34634) = 39366 * k + 17317 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17317) = 59049 * k + 25976 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28827) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28827)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28879_mod_65536 {n : ℕ} (hn : n % 65536 = 28879) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28879 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28879) = 98304 * k + 43319 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43319) = 147456 * k + 64979 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 64979) = 221184 * k + 97469 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 97469) = 331776 * k + 146204 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 146204) = 165888 * k + 73102 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 73102) = 82944 * k + 36551 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 36551) = 124416 * k + 54827 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 54827) = 186624 * k + 82241 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 82241) = 279936 * k + 123362 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 123362) = 139968 * k + 61681 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 61681) = 209952 * k + 92522 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 92522) = 104976 * k + 46261 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 46261) = 157464 * k + 69392 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 69392) = 78732 * k + 34696 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34696) = 39366 * k + 17348 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17348) = 19683 * k + 8674 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28879) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28879)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28927_mod_65536 {n : ℕ} (hn : n % 65536 = 28927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28927) = 98304 * k + 43391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43391) = 147456 * k + 65087 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 65087) = 221184 * k + 97631 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 97631) = 331776 * k + 146447 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 146447) = 497664 * k + 219671 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 219671) = 746496 * k + 329507 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 329507) = 1119744 * k + 494261 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 494261) = 1679616 * k + 741392 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 741392) = 839808 * k + 370696 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 370696) = 419904 * k + 185348 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 185348) = 209952 * k + 92674 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 92674) = 104976 * k + 46337 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 46337) = 157464 * k + 69506 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 69506) = 78732 * k + 34753 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34753) = 118098 * k + 52130 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 52130) = 59049 * k + 26065 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_28999_mod_65536 {n : ℕ} (hn : n % 65536 = 28999) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 28999 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 28999) = 98304 * k + 43499 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43499) = 147456 * k + 65249 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 65249) = 221184 * k + 97874 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 97874) = 110592 * k + 48937 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 48937) = 165888 * k + 73406 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 73406) = 82944 * k + 36703 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 36703) = 124416 * k + 55055 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 55055) = 186624 * k + 82583 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 82583) = 279936 * k + 123875 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 123875) = 419904 * k + 185813 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 185813) = 629856 * k + 278720 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 278720) = 314928 * k + 139360 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 139360) = 157464 * k + 69680 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 69680) = 78732 * k + 34840 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 34840) = 39366 * k + 17420 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17420) = 19683 * k + 8710 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 28999) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 28999)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29087_mod_65536 {n : ℕ} (hn : n % 65536 = 29087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29087) = 98304 * k + 43631 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43631) = 147456 * k + 65447 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 65447) = 221184 * k + 98171 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 98171) = 331776 * k + 147257 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 147257) = 497664 * k + 220886 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 220886) = 248832 * k + 110443 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 110443) = 373248 * k + 165665 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 165665) = 559872 * k + 248498 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 248498) = 279936 * k + 124249 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 124249) = 419904 * k + 186374 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 186374) = 209952 * k + 93187 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 93187) = 314928 * k + 139781 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 139781) = 472392 * k + 209672 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 209672) = 236196 * k + 104836 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 104836) = 118098 * k + 52418 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 52418) = 59049 * k + 26209 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29231_mod_65536 {n : ℕ} (hn : n % 65536 = 29231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29231) = 98304 * k + 43847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 43847) = 147456 * k + 65771 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 65771) = 221184 * k + 98657 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 98657) = 331776 * k + 147986 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 147986) = 165888 * k + 73993 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 73993) = 248832 * k + 110990 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 110990) = 124416 * k + 55495 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 55495) = 186624 * k + 83243 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 83243) = 279936 * k + 124865 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 124865) = 419904 * k + 187298 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 187298) = 209952 * k + 93649 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 93649) = 314928 * k + 140474 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 140474) = 157464 * k + 70237 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 70237) = 236196 * k + 105356 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 105356) = 118098 * k + 52678 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 52678) = 59049 * k + 26339 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29467_mod_65536 {n : ℕ} (hn : n % 65536 = 29467) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29467 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29467) = 98304 * k + 44201 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44201) = 147456 * k + 66302 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66302) = 73728 * k + 33151 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 33151) = 110592 * k + 49727 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 49727) = 165888 * k + 74591 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 74591) = 248832 * k + 111887 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 111887) = 373248 * k + 167831 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 167831) = 559872 * k + 251747 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 251747) = 839808 * k + 377621 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 377621) = 1259712 * k + 566432 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 566432) = 629856 * k + 283216 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 283216) = 314928 * k + 141608 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 141608) = 157464 * k + 70804 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 70804) = 78732 * k + 35402 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35402) = 39366 * k + 17701 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17701) = 59049 * k + 26552 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29467) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29467)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29531_mod_65536 {n : ℕ} (hn : n % 65536 = 29531) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29531 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29531) = 98304 * k + 44297 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44297) = 147456 * k + 66446 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66446) = 73728 * k + 33223 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 33223) = 110592 * k + 49835 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 49835) = 165888 * k + 74753 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 74753) = 248832 * k + 112130 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 112130) = 124416 * k + 56065 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 56065) = 186624 * k + 84098 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 84098) = 93312 * k + 42049 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 42049) = 139968 * k + 63074 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63074) = 69984 * k + 31537 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 31537) = 104976 * k + 47306 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47306) = 52488 * k + 23653 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 23653) = 78732 * k + 35480 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35480) = 39366 * k + 17740 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17740) = 19683 * k + 8870 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29531) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29531)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29599_mod_65536 {n : ℕ} (hn : n % 65536 = 29599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29599) = 98304 * k + 44399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44399) = 147456 * k + 66599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66599) = 221184 * k + 99899 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 99899) = 331776 * k + 149849 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 149849) = 497664 * k + 224774 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 224774) = 248832 * k + 112387 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 112387) = 373248 * k + 168581 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 168581) = 559872 * k + 252872 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 252872) = 279936 * k + 126436 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 126436) = 139968 * k + 63218 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63218) = 69984 * k + 31609 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 31609) = 104976 * k + 47414 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47414) = 52488 * k + 23707 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 23707) = 78732 * k + 35561 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35561) = 118098 * k + 53342 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53342) = 59049 * k + 26671 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29631_mod_65536 {n : ℕ} (hn : n % 65536 = 29631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29631) = 98304 * k + 44447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44447) = 147456 * k + 66671 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66671) = 221184 * k + 100007 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100007) = 331776 * k + 150011 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 150011) = 497664 * k + 225017 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 225017) = 746496 * k + 337526 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 337526) = 373248 * k + 168763 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 168763) = 559872 * k + 253145 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 253145) = 839808 * k + 379718 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 379718) = 419904 * k + 189859 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 189859) = 629856 * k + 284789 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 284789) = 944784 * k + 427184 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 427184) = 472392 * k + 213592 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 213592) = 236196 * k + 106796 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 106796) = 118098 * k + 53398 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53398) = 59049 * k + 26699 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29679_mod_65536 {n : ℕ} (hn : n % 65536 = 29679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29679) = 98304 * k + 44519 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44519) = 147456 * k + 66779 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66779) = 221184 * k + 100169 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100169) = 331776 * k + 150254 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 150254) = 165888 * k + 75127 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 75127) = 248832 * k + 112691 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 112691) = 373248 * k + 169037 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 169037) = 559872 * k + 253556 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 253556) = 279936 * k + 126778 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 126778) = 139968 * k + 63389 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63389) = 209952 * k + 95084 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 95084) = 104976 * k + 47542 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47542) = 52488 * k + 23771 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 23771) = 78732 * k + 35657 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35657) = 118098 * k + 53486 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53486) = 59049 * k + 26743 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29743_mod_65536 {n : ℕ} (hn : n % 65536 = 29743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29743) = 98304 * k + 44615 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44615) = 147456 * k + 66923 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 66923) = 221184 * k + 100385 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100385) = 331776 * k + 150578 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 150578) = 165888 * k + 75289 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 75289) = 248832 * k + 112934 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 112934) = 124416 * k + 56467 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 56467) = 186624 * k + 84701 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 84701) = 279936 * k + 127052 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 127052) = 139968 * k + 63526 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63526) = 69984 * k + 31763 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 31763) = 104976 * k + 47645 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47645) = 157464 * k + 71468 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 71468) = 78732 * k + 35734 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35734) = 39366 * k + 17867 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17867) = 59049 * k + 26801 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29807_mod_65536 {n : ℕ} (hn : n % 65536 = 29807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29807) = 98304 * k + 44711 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44711) = 147456 * k + 67067 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67067) = 221184 * k + 100601 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100601) = 331776 * k + 150902 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 150902) = 165888 * k + 75451 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 75451) = 248832 * k + 113177 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 113177) = 373248 * k + 169766 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 169766) = 186624 * k + 84883 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 84883) = 279936 * k + 127325 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 127325) = 419904 * k + 190988 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 190988) = 209952 * k + 95494 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 95494) = 104976 * k + 47747 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47747) = 157464 * k + 71621 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 71621) = 236196 * k + 107432 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 107432) = 118098 * k + 53716 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53716) = 59049 * k + 26858 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29823_mod_65536 {n : ℕ} (hn : n % 65536 = 29823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29823) = 98304 * k + 44735 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44735) = 147456 * k + 67103 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67103) = 221184 * k + 100655 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100655) = 331776 * k + 150983 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 150983) = 497664 * k + 226475 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 226475) = 746496 * k + 339713 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 339713) = 1119744 * k + 509570 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 509570) = 559872 * k + 254785 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 254785) = 839808 * k + 382178 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 382178) = 419904 * k + 191089 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 191089) = 629856 * k + 286634 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 286634) = 314928 * k + 143317 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 143317) = 472392 * k + 214976 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 214976) = 236196 * k + 107488 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 107488) = 118098 * k + 53744 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53744) = 59049 * k + 26872 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29851_mod_65536 {n : ℕ} (hn : n % 65536 = 29851) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29851 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29851) = 98304 * k + 44777 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44777) = 147456 * k + 67166 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67166) = 73728 * k + 33583 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 33583) = 110592 * k + 50375 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 50375) = 165888 * k + 75563 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 75563) = 248832 * k + 113345 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 113345) = 373248 * k + 170018 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 170018) = 186624 * k + 85009 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 85009) = 279936 * k + 127514 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 127514) = 139968 * k + 63757 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63757) = 209952 * k + 95636 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 95636) = 104976 * k + 47818 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47818) = 52488 * k + 23909 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 23909) = 78732 * k + 35864 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35864) = 39366 * k + 17932 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17932) = 19683 * k + 8966 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29851) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29851)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29863_mod_65536 {n : ℕ} (hn : n % 65536 = 29863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29863) = 98304 * k + 44795 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44795) = 147456 * k + 67193 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67193) = 221184 * k + 100790 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100790) = 110592 * k + 50395 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 50395) = 165888 * k + 75593 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 75593) = 248832 * k + 113390 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 113390) = 124416 * k + 56695 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 56695) = 186624 * k + 85043 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 85043) = 279936 * k + 127565 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 127565) = 419904 * k + 191348 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 191348) = 209952 * k + 95674 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 95674) = 104976 * k + 47837 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47837) = 157464 * k + 71756 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 71756) = 78732 * k + 35878 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 35878) = 39366 * k + 17939 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 17939) = 59049 * k + 26909 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_29887_mod_65536 {n : ℕ} (hn : n % 65536 = 29887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 29887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 29887) = 98304 * k + 44831 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 44831) = 147456 * k + 67247 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67247) = 221184 * k + 100871 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 100871) = 331776 * k + 151307 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 151307) = 497664 * k + 226961 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 226961) = 746496 * k + 340442 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 340442) = 373248 * k + 170221 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 170221) = 559872 * k + 255332 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 255332) = 279936 * k + 127666 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 127666) = 139968 * k + 63833 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 63833) = 209952 * k + 95750 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 95750) = 104976 * k + 47875 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 47875) = 157464 * k + 71813 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 71813) = 236196 * k + 107720 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 107720) = 118098 * k + 53860 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 53860) = 59049 * k + 26930 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 29887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 29887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30079_mod_65536 {n : ℕ} (hn : n % 65536 = 30079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30079) = 98304 * k + 45119 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45119) = 147456 * k + 67679 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67679) = 221184 * k + 101519 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 101519) = 331776 * k + 152279 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 152279) = 497664 * k + 228419 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 228419) = 746496 * k + 342629 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 342629) = 1119744 * k + 513944 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 513944) = 559872 * k + 256972 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 256972) = 279936 * k + 128486 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 128486) = 139968 * k + 64243 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 64243) = 209952 * k + 96365 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 96365) = 314928 * k + 144548 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 144548) = 157464 * k + 72274 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 72274) = 78732 * k + 36137 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36137) = 118098 * k + 54206 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 54206) = 59049 * k + 27103 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30191_mod_65536 {n : ℕ} (hn : n % 65536 = 30191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30191) = 98304 * k + 45287 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45287) = 147456 * k + 67931 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67931) = 221184 * k + 101897 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 101897) = 331776 * k + 152846 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 152846) = 165888 * k + 76423 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 76423) = 248832 * k + 114635 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 114635) = 373248 * k + 171953 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 171953) = 559872 * k + 257930 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 257930) = 279936 * k + 128965 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 128965) = 419904 * k + 193448 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 193448) = 209952 * k + 96724 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 96724) = 104976 * k + 48362 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 48362) = 52488 * k + 24181 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 24181) = 78732 * k + 36272 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36272) = 39366 * k + 18136 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18136) = 19683 * k + 9068 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30207_mod_65536 {n : ℕ} (hn : n % 65536 = 30207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30207) = 98304 * k + 45311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45311) = 147456 * k + 67967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 67967) = 221184 * k + 101951 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 101951) = 331776 * k + 152927 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 152927) = 497664 * k + 229391 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 229391) = 746496 * k + 344087 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 344087) = 1119744 * k + 516131 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 516131) = 1679616 * k + 774197 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 774197) = 2519424 * k + 1161296 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 1161296) = 1259712 * k + 580648 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 580648) = 629856 * k + 290324 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 290324) = 314928 * k + 145162 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 145162) = 157464 * k + 72581 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 72581) = 236196 * k + 108872 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 108872) = 118098 * k + 54436 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 54436) = 59049 * k + 27218 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30235_mod_65536 {n : ℕ} (hn : n % 65536 = 30235) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30235 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30235) = 98304 * k + 45353 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45353) = 147456 * k + 68030 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68030) = 73728 * k + 34015 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 34015) = 110592 * k + 51023 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51023) = 165888 * k + 76535 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 76535) = 248832 * k + 114803 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 114803) = 373248 * k + 172205 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 172205) = 559872 * k + 258308 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 258308) = 279936 * k + 129154 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 129154) = 139968 * k + 64577 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 64577) = 209952 * k + 96866 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 96866) = 104976 * k + 48433 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 48433) = 157464 * k + 72650 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 72650) = 78732 * k + 36325 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36325) = 118098 * k + 54488 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 54488) = 59049 * k + 27244 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30235) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30235)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30311_mod_65536 {n : ℕ} (hn : n % 65536 = 30311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30311) = 98304 * k + 45467 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45467) = 147456 * k + 68201 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68201) = 221184 * k + 102302 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 102302) = 110592 * k + 51151 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51151) = 165888 * k + 76727 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 76727) = 248832 * k + 115091 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 115091) = 373248 * k + 172637 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 172637) = 559872 * k + 258956 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 258956) = 279936 * k + 129478 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 129478) = 139968 * k + 64739 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 64739) = 209952 * k + 97109 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 97109) = 314928 * k + 145664 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 145664) = 157464 * k + 72832 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 72832) = 78732 * k + 36416 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36416) = 39366 * k + 18208 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18208) = 19683 * k + 9104 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30415_mod_65536 {n : ℕ} (hn : n % 65536 = 30415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30415) = 98304 * k + 45623 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45623) = 147456 * k + 68435 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68435) = 221184 * k + 102653 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 102653) = 331776 * k + 153980 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 153980) = 165888 * k + 76990 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 76990) = 82944 * k + 38495 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 38495) = 124416 * k + 57743 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 57743) = 186624 * k + 86615 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 86615) = 279936 * k + 129923 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 129923) = 419904 * k + 194885 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 194885) = 629856 * k + 292328 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 292328) = 314928 * k + 146164 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 146164) = 157464 * k + 73082 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73082) = 78732 * k + 36541 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36541) = 118098 * k + 54812 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 54812) = 59049 * k + 27406 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30535_mod_65536 {n : ℕ} (hn : n % 65536 = 30535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30535) = 98304 * k + 45803 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45803) = 147456 * k + 68705 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68705) = 221184 * k + 103058 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103058) = 110592 * k + 51529 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51529) = 165888 * k + 77294 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77294) = 82944 * k + 38647 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 38647) = 124416 * k + 57971 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 57971) = 186624 * k + 86957 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 86957) = 279936 * k + 130436 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 130436) = 139968 * k + 65218 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65218) = 69984 * k + 32609 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 32609) = 104976 * k + 48914 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 48914) = 52488 * k + 24457 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 24457) = 78732 * k + 36686 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36686) = 39366 * k + 18343 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18343) = 59049 * k + 27515 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30555_mod_65536 {n : ℕ} (hn : n % 65536 = 30555) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30555 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30555) = 98304 * k + 45833 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45833) = 147456 * k + 68750 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68750) = 73728 * k + 34375 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 34375) = 110592 * k + 51563 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51563) = 165888 * k + 77345 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77345) = 248832 * k + 116018 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 116018) = 124416 * k + 58009 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58009) = 186624 * k + 87014 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87014) = 93312 * k + 43507 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 43507) = 139968 * k + 65261 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65261) = 209952 * k + 97892 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 97892) = 104976 * k + 48946 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 48946) = 52488 * k + 24473 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 24473) = 78732 * k + 36710 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36710) = 39366 * k + 18355 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18355) = 59049 * k + 27533 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30555) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30555)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30575_mod_65536 {n : ℕ} (hn : n % 65536 = 30575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30575) = 98304 * k + 45863 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45863) = 147456 * k + 68795 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68795) = 221184 * k + 103193 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103193) = 331776 * k + 154790 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 154790) = 165888 * k + 77395 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77395) = 248832 * k + 116093 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 116093) = 373248 * k + 174140 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 174140) = 186624 * k + 87070 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87070) = 93312 * k + 43535 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 43535) = 139968 * k + 65303 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65303) = 209952 * k + 97955 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 97955) = 314928 * k + 146933 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 146933) = 472392 * k + 220400 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 220400) = 236196 * k + 110200 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 110200) = 118098 * k + 55100 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 55100) = 59049 * k + 27550 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30591_mod_65536 {n : ℕ} (hn : n % 65536 = 30591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30591) = 98304 * k + 45887 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45887) = 147456 * k + 68831 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68831) = 221184 * k + 103247 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103247) = 331776 * k + 154871 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 154871) = 497664 * k + 232307 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 232307) = 746496 * k + 348461 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 348461) = 1119744 * k + 522692 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 522692) = 559872 * k + 261346 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 261346) = 279936 * k + 130673 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 130673) = 419904 * k + 196010 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 196010) = 209952 * k + 98005 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 98005) = 314928 * k + 147008 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 147008) = 157464 * k + 73504 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73504) = 78732 * k + 36752 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36752) = 39366 * k + 18376 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18376) = 19683 * k + 9188 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30655_mod_65536 {n : ℕ} (hn : n % 65536 = 30655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30655) = 98304 * k + 45983 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 45983) = 147456 * k + 68975 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 68975) = 221184 * k + 103463 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103463) = 331776 * k + 155195 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 155195) = 497664 * k + 232793 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 232793) = 746496 * k + 349190 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 349190) = 373248 * k + 174595 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 174595) = 559872 * k + 261893 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 261893) = 839808 * k + 392840 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 392840) = 419904 * k + 196420 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 196420) = 209952 * k + 98210 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 98210) = 104976 * k + 49105 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49105) = 157464 * k + 73658 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73658) = 78732 * k + 36829 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36829) = 118098 * k + 55244 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 55244) = 59049 * k + 27622 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30687_mod_65536 {n : ℕ} (hn : n % 65536 = 30687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30687) = 98304 * k + 46031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46031) = 147456 * k + 69047 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69047) = 221184 * k + 103571 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103571) = 331776 * k + 155357 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 155357) = 497664 * k + 233036 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 233036) = 248832 * k + 116518 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 116518) = 124416 * k + 58259 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58259) = 186624 * k + 87389 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87389) = 279936 * k + 131084 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 131084) = 139968 * k + 65542 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65542) = 69984 * k + 32771 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 32771) = 104976 * k + 49157 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49157) = 157464 * k + 73736 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73736) = 78732 * k + 36868 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36868) = 39366 * k + 18434 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18434) = 19683 * k + 9217 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30715_mod_65536 {n : ℕ} (hn : n % 65536 = 30715) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30715 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30715) = 98304 * k + 46073 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46073) = 147456 * k + 69110 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69110) = 73728 * k + 34555 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 34555) = 110592 * k + 51833 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51833) = 165888 * k + 77750 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77750) = 82944 * k + 38875 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 38875) = 124416 * k + 58313 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58313) = 186624 * k + 87470 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87470) = 93312 * k + 43735 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 43735) = 139968 * k + 65603 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65603) = 209952 * k + 98405 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 98405) = 314928 * k + 147608 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 147608) = 157464 * k + 73804 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73804) = 78732 * k + 36902 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36902) = 39366 * k + 18451 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18451) = 59049 * k + 27677 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30715) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30715)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30747_mod_65536 {n : ℕ} (hn : n % 65536 = 30747) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30747 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30747) = 98304 * k + 46121 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46121) = 147456 * k + 69182 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69182) = 73728 * k + 34591 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 34591) = 110592 * k + 51887 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 51887) = 165888 * k + 77831 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77831) = 248832 * k + 116747 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 116747) = 373248 * k + 175121 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 175121) = 559872 * k + 262682 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 262682) = 279936 * k + 131341 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 131341) = 419904 * k + 197012 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 197012) = 209952 * k + 98506 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 98506) = 104976 * k + 49253 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49253) = 157464 * k + 73880 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73880) = 78732 * k + 36940 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36940) = 39366 * k + 18470 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18470) = 19683 * k + 9235 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30747) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30747)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30767_mod_65536 {n : ℕ} (hn : n % 65536 = 30767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30767) = 98304 * k + 46151 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46151) = 147456 * k + 69227 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69227) = 221184 * k + 103841 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 103841) = 331776 * k + 155762 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 155762) = 165888 * k + 77881 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 77881) = 248832 * k + 116822 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 116822) = 124416 * k + 58411 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58411) = 186624 * k + 87617 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87617) = 279936 * k + 131426 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 131426) = 139968 * k + 65713 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 65713) = 209952 * k + 98570 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 98570) = 104976 * k + 49285 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49285) = 157464 * k + 73928 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 73928) = 78732 * k + 36964 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 36964) = 39366 * k + 18482 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18482) = 19683 * k + 9241 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30887_mod_65536 {n : ℕ} (hn : n % 65536 = 30887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30887) = 98304 * k + 46331 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46331) = 147456 * k + 69497 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69497) = 221184 * k + 104246 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 104246) = 110592 * k + 52123 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 52123) = 165888 * k + 78185 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 78185) = 248832 * k + 117278 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 117278) = 124416 * k + 58639 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58639) = 186624 * k + 87959 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 87959) = 279936 * k + 131939 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 131939) = 419904 * k + 197909 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 197909) = 629856 * k + 296864 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 296864) = 314928 * k + 148432 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 148432) = 157464 * k + 74216 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 74216) = 78732 * k + 37108 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 37108) = 39366 * k + 18554 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18554) = 19683 * k + 9277 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30971_mod_65536 {n : ℕ} (hn : n % 65536 = 30971) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30971 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30971) = 98304 * k + 46457 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46457) = 147456 * k + 69686 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69686) = 73728 * k + 34843 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 34843) = 110592 * k + 52265 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 52265) = 165888 * k + 78398 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 78398) = 82944 * k + 39199 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 39199) = 124416 * k + 58799 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 58799) = 186624 * k + 88199 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 88199) = 279936 * k + 132299 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 132299) = 419904 * k + 198449 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 198449) = 629856 * k + 297674 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 297674) = 314928 * k + 148837 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 148837) = 472392 * k + 223256 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 223256) = 236196 * k + 111628 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 111628) = 118098 * k + 55814 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 55814) = 59049 * k + 27907 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30971) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30971)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_30975_mod_65536 {n : ℕ} (hn : n % 65536 = 30975) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 30975 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 30975) = 98304 * k + 46463 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46463) = 147456 * k + 69695 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69695) = 221184 * k + 104543 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 104543) = 331776 * k + 156815 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 156815) = 497664 * k + 235223 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 235223) = 746496 * k + 352835 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 352835) = 1119744 * k + 529253 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 529253) = 1679616 * k + 793880 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 793880) = 839808 * k + 396940 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 396940) = 419904 * k + 198470 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 198470) = 209952 * k + 99235 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 99235) = 314928 * k + 148853 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 148853) = 472392 * k + 223280 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 223280) = 236196 * k + 111640 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 111640) = 118098 * k + 55820 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 55820) = 59049 * k + 27910 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 30975) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 30975)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31079_mod_65536 {n : ℕ} (hn : n % 65536 = 31079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31079) = 98304 * k + 46619 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46619) = 147456 * k + 69929 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 69929) = 221184 * k + 104894 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 104894) = 110592 * k + 52447 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 52447) = 165888 * k + 78671 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 78671) = 248832 * k + 118007 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 118007) = 373248 * k + 177011 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 177011) = 559872 * k + 265517 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 265517) = 839808 * k + 398276 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 398276) = 419904 * k + 199138 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 199138) = 209952 * k + 99569 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 99569) = 314928 * k + 149354 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 149354) = 157464 * k + 74677 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 74677) = 236196 * k + 112016 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 112016) = 118098 * k + 56008 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56008) = 59049 * k + 28004 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31135_mod_65536 {n : ℕ} (hn : n % 65536 = 31135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31135) = 98304 * k + 46703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46703) = 147456 * k + 70055 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70055) = 221184 * k + 105083 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 105083) = 331776 * k + 157625 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 157625) = 497664 * k + 236438 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 236438) = 248832 * k + 118219 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 118219) = 373248 * k + 177329 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 177329) = 559872 * k + 265994 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 265994) = 279936 * k + 132997 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 132997) = 419904 * k + 199496 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 199496) = 209952 * k + 99748 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 99748) = 104976 * k + 49874 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49874) = 52488 * k + 24937 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 24937) = 78732 * k + 37406 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 37406) = 39366 * k + 18703 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18703) = 59049 * k + 28055 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31199_mod_65536 {n : ℕ} (hn : n % 65536 = 31199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31199) = 98304 * k + 46799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46799) = 147456 * k + 70199 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70199) = 221184 * k + 105299 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 105299) = 331776 * k + 157949 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 157949) = 497664 * k + 236924 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 236924) = 248832 * k + 118462 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 118462) = 124416 * k + 59231 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 59231) = 186624 * k + 88847 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 88847) = 279936 * k + 133271 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 133271) = 419904 * k + 199907 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 199907) = 629856 * k + 299861 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 299861) = 944784 * k + 449792 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 449792) = 472392 * k + 224896 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 224896) = 236196 * k + 112448 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 112448) = 118098 * k + 56224 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56224) = 59049 * k + 28112 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31207_mod_65536 {n : ℕ} (hn : n % 65536 = 31207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31207) = 98304 * k + 46811 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 46811) = 147456 * k + 70217 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70217) = 221184 * k + 105326 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 105326) = 110592 * k + 52663 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 52663) = 165888 * k + 78995 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 78995) = 248832 * k + 118493 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 118493) = 373248 * k + 177740 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 177740) = 186624 * k + 88870 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 88870) = 93312 * k + 44435 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 44435) = 139968 * k + 66653 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 66653) = 209952 * k + 99980 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 99980) = 104976 * k + 49990 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 49990) = 52488 * k + 24995 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 24995) = 78732 * k + 37493 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 37493) = 118098 * k + 56240 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56240) = 59049 * k + 28120 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31335_mod_65536 {n : ℕ} (hn : n % 65536 = 31335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31335) = 98304 * k + 47003 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47003) = 147456 * k + 70505 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70505) = 221184 * k + 105758 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 105758) = 110592 * k + 52879 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 52879) = 165888 * k + 79319 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 79319) = 248832 * k + 118979 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 118979) = 373248 * k + 178469 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 178469) = 559872 * k + 267704 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 267704) = 279936 * k + 133852 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 133852) = 139968 * k + 66926 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 66926) = 69984 * k + 33463 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 33463) = 104976 * k + 50195 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 50195) = 157464 * k + 75293 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 75293) = 236196 * k + 112940 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 112940) = 118098 * k + 56470 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56470) = 59049 * k + 28235 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31359_mod_65536 {n : ℕ} (hn : n % 65536 = 31359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31359) = 98304 * k + 47039 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47039) = 147456 * k + 70559 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70559) = 221184 * k + 105839 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 105839) = 331776 * k + 158759 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 158759) = 497664 * k + 238139 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 238139) = 746496 * k + 357209 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 357209) = 1119744 * k + 535814 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 535814) = 559872 * k + 267907 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 267907) = 839808 * k + 401861 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 401861) = 1259712 * k + 602792 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 602792) = 629856 * k + 301396 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 301396) = 314928 * k + 150698 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 150698) = 157464 * k + 75349 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 75349) = 236196 * k + 113024 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 113024) = 118098 * k + 56512 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56512) = 59049 * k + 28256 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31471_mod_65536 {n : ℕ} (hn : n % 65536 = 31471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31471) = 98304 * k + 47207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47207) = 147456 * k + 70811 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 70811) = 221184 * k + 106217 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 106217) = 331776 * k + 159326 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 159326) = 165888 * k + 79663 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 79663) = 248832 * k + 119495 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 119495) = 373248 * k + 179243 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 179243) = 559872 * k + 268865 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 268865) = 839808 * k + 403298 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 403298) = 419904 * k + 201649 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 201649) = 629856 * k + 302474 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 302474) = 314928 * k + 151237 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 151237) = 472392 * k + 226856 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 226856) = 236196 * k + 113428 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 113428) = 118098 * k + 56714 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 56714) = 59049 * k + 28357 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31559_mod_65536 {n : ℕ} (hn : n % 65536 = 31559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31559) = 98304 * k + 47339 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47339) = 147456 * k + 71009 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71009) = 221184 * k + 106514 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 106514) = 110592 * k + 53257 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 53257) = 165888 * k + 79886 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 79886) = 82944 * k + 39943 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 39943) = 124416 * k + 59915 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 59915) = 186624 * k + 89873 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 89873) = 279936 * k + 134810 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 134810) = 139968 * k + 67405 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 67405) = 209952 * k + 101108 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 101108) = 104976 * k + 50554 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 50554) = 52488 * k + 25277 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 25277) = 78732 * k + 37916 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 37916) = 39366 * k + 18958 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18958) = 19683 * k + 9479 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31599_mod_65536 {n : ℕ} (hn : n % 65536 = 31599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31599) = 98304 * k + 47399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47399) = 147456 * k + 71099 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71099) = 221184 * k + 106649 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 106649) = 331776 * k + 159974 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 159974) = 165888 * k + 79987 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 79987) = 248832 * k + 119981 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 119981) = 373248 * k + 179972 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 179972) = 186624 * k + 89986 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 89986) = 93312 * k + 44993 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 44993) = 139968 * k + 67490 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 67490) = 69984 * k + 33745 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 33745) = 104976 * k + 50618 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 50618) = 52488 * k + 25309 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 25309) = 78732 * k + 37964 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 37964) = 39366 * k + 18982 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 18982) = 19683 * k + 9491 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31711_mod_65536 {n : ℕ} (hn : n % 65536 = 31711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31711) = 98304 * k + 47567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47567) = 147456 * k + 71351 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71351) = 221184 * k + 107027 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 107027) = 331776 * k + 160541 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 160541) = 497664 * k + 240812 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 240812) = 248832 * k + 120406 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 120406) = 124416 * k + 60203 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 60203) = 186624 * k + 90305 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 90305) = 279936 * k + 135458 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 135458) = 139968 * k + 67729 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 67729) = 209952 * k + 101594 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 101594) = 104976 * k + 50797 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 50797) = 157464 * k + 76196 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 76196) = 78732 * k + 38098 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38098) = 39366 * k + 19049 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19049) = 59049 * k + 28574 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31727_mod_65536 {n : ℕ} (hn : n % 65536 = 31727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31727) = 98304 * k + 47591 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47591) = 147456 * k + 71387 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71387) = 221184 * k + 107081 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 107081) = 331776 * k + 160622 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 160622) = 165888 * k + 80311 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 80311) = 248832 * k + 120467 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 120467) = 373248 * k + 180701 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 180701) = 559872 * k + 271052 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 271052) = 279936 * k + 135526 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 135526) = 139968 * k + 67763 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 67763) = 209952 * k + 101645 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 101645) = 314928 * k + 152468 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 152468) = 157464 * k + 76234 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 76234) = 78732 * k + 38117 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38117) = 118098 * k + 57176 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 57176) = 59049 * k + 28588 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31771_mod_65536 {n : ℕ} (hn : n % 65536 = 31771) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31771 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31771) = 98304 * k + 47657 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47657) = 147456 * k + 71486 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71486) = 73728 * k + 35743 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 35743) = 110592 * k + 53615 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 53615) = 165888 * k + 80423 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 80423) = 248832 * k + 120635 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 120635) = 373248 * k + 180953 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 180953) = 559872 * k + 271430 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 271430) = 279936 * k + 135715 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 135715) = 419904 * k + 203573 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 203573) = 629856 * k + 305360 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 305360) = 314928 * k + 152680 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 152680) = 157464 * k + 76340 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 76340) = 78732 * k + 38170 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38170) = 39366 * k + 19085 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19085) = 59049 * k + 28628 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31771) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31771)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31775_mod_65536 {n : ℕ} (hn : n % 65536 = 31775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31775) = 98304 * k + 47663 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47663) = 147456 * k + 71495 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71495) = 221184 * k + 107243 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 107243) = 331776 * k + 160865 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 160865) = 497664 * k + 241298 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 241298) = 248832 * k + 120649 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 120649) = 373248 * k + 180974 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 180974) = 186624 * k + 90487 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 90487) = 279936 * k + 135731 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 135731) = 419904 * k + 203597 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 203597) = 629856 * k + 305396 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 305396) = 314928 * k + 152698 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 152698) = 157464 * k + 76349 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 76349) = 236196 * k + 114524 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 114524) = 118098 * k + 57262 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 57262) = 59049 * k + 28631 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_31899_mod_65536 {n : ℕ} (hn : n % 65536 = 31899) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 31899 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 31899) = 98304 * k + 47849 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 47849) = 147456 * k + 71774 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 71774) = 73728 * k + 35887 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 35887) = 110592 * k + 53831 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 53831) = 165888 * k + 80747 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 80747) = 248832 * k + 121121 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 121121) = 373248 * k + 181682 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 181682) = 186624 * k + 90841 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 90841) = 279936 * k + 136262 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 136262) = 139968 * k + 68131 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 68131) = 209952 * k + 102197 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 102197) = 314928 * k + 153296 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 153296) = 157464 * k + 76648 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 76648) = 78732 * k + 38324 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38324) = 39366 * k + 19162 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19162) = 19683 * k + 9581 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 31899) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 31899)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32155_mod_65536 {n : ℕ} (hn : n % 65536 = 32155) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32155 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32155) = 98304 * k + 48233 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48233) = 147456 * k + 72350 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72350) = 73728 * k + 36175 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 36175) = 110592 * k + 54263 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 54263) = 165888 * k + 81395 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 81395) = 248832 * k + 122093 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 122093) = 373248 * k + 183140 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 183140) = 186624 * k + 91570 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 91570) = 93312 * k + 45785 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 45785) = 139968 * k + 68678 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 68678) = 69984 * k + 34339 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 34339) = 104976 * k + 51509 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 51509) = 157464 * k + 77264 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 77264) = 78732 * k + 38632 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38632) = 39366 * k + 19316 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19316) = 19683 * k + 9658 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32155) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32155)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32223_mod_65536 {n : ℕ} (hn : n % 65536 = 32223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32223) = 98304 * k + 48335 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48335) = 147456 * k + 72503 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72503) = 221184 * k + 108755 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 108755) = 331776 * k + 163133 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 163133) = 497664 * k + 244700 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 244700) = 248832 * k + 122350 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 122350) = 124416 * k + 61175 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 61175) = 186624 * k + 91763 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 91763) = 279936 * k + 137645 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 137645) = 419904 * k + 206468 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 206468) = 209952 * k + 103234 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 103234) = 104976 * k + 51617 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 51617) = 157464 * k + 77426 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 77426) = 78732 * k + 38713 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38713) = 118098 * k + 58070 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 58070) = 59049 * k + 29035 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32239_mod_65536 {n : ℕ} (hn : n % 65536 = 32239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32239) = 98304 * k + 48359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48359) = 147456 * k + 72539 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72539) = 221184 * k + 108809 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 108809) = 331776 * k + 163214 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 163214) = 165888 * k + 81607 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 81607) = 248832 * k + 122411 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 122411) = 373248 * k + 183617 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 183617) = 559872 * k + 275426 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 275426) = 279936 * k + 137713 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 137713) = 419904 * k + 206570 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 206570) = 209952 * k + 103285 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 103285) = 314928 * k + 154928 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 154928) = 157464 * k + 77464 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 77464) = 78732 * k + 38732 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38732) = 39366 * k + 19366 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19366) = 19683 * k + 9683 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32283_mod_65536 {n : ℕ} (hn : n % 65536 = 32283) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32283 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32283) = 98304 * k + 48425 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48425) = 147456 * k + 72638 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72638) = 73728 * k + 36319 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 36319) = 110592 * k + 54479 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 54479) = 165888 * k + 81719 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 81719) = 248832 * k + 122579 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 122579) = 373248 * k + 183869 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 183869) = 559872 * k + 275804 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 275804) = 279936 * k + 137902 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 137902) = 139968 * k + 68951 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 68951) = 209952 * k + 103427 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 103427) = 314928 * k + 155141 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 155141) = 472392 * k + 232712 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 232712) = 236196 * k + 116356 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 116356) = 118098 * k + 58178 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 58178) = 59049 * k + 29089 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32283) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32283)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32303_mod_65536 {n : ℕ} (hn : n % 65536 = 32303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32303) = 98304 * k + 48455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48455) = 147456 * k + 72683 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72683) = 221184 * k + 109025 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 109025) = 331776 * k + 163538 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 163538) = 165888 * k + 81769 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 81769) = 248832 * k + 122654 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 122654) = 124416 * k + 61327 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 61327) = 186624 * k + 91991 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 91991) = 279936 * k + 137987 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 137987) = 419904 * k + 206981 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 206981) = 629856 * k + 310472 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 310472) = 314928 * k + 155236 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 155236) = 157464 * k + 77618 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 77618) = 78732 * k + 38809 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38809) = 118098 * k + 58214 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 58214) = 59049 * k + 29107 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32423_mod_65536 {n : ℕ} (hn : n % 65536 = 32423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32423) = 98304 * k + 48635 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48635) = 147456 * k + 72953 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 72953) = 221184 * k + 109430 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 109430) = 110592 * k + 54715 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 54715) = 165888 * k + 82073 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 82073) = 248832 * k + 123110 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 123110) = 124416 * k + 61555 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 61555) = 186624 * k + 92333 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 92333) = 279936 * k + 138500 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 138500) = 139968 * k + 69250 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69250) = 69984 * k + 34625 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 34625) = 104976 * k + 51938 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 51938) = 52488 * k + 25969 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 25969) = 78732 * k + 38954 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 38954) = 39366 * k + 19477 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19477) = 59049 * k + 29216 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32543_mod_65536 {n : ℕ} (hn : n % 65536 = 32543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32543) = 98304 * k + 48815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48815) = 147456 * k + 73223 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73223) = 221184 * k + 109835 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 109835) = 331776 * k + 164753 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 164753) = 497664 * k + 247130 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 247130) = 248832 * k + 123565 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 123565) = 373248 * k + 185348 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 185348) = 186624 * k + 92674 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 92674) = 93312 * k + 46337 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 46337) = 139968 * k + 69506 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69506) = 69984 * k + 34753 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 34753) = 104976 * k + 52130 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52130) = 52488 * k + 26065 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26065) = 78732 * k + 39098 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39098) = 39366 * k + 19549 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19549) = 59049 * k + 29324 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32575_mod_65536 {n : ℕ} (hn : n % 65536 = 32575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32575) = 98304 * k + 48863 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48863) = 147456 * k + 73295 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73295) = 221184 * k + 109943 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 109943) = 331776 * k + 164915 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 164915) = 497664 * k + 247373 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 247373) = 746496 * k + 371060 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 371060) = 373248 * k + 185530 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 185530) = 186624 * k + 92765 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 92765) = 279936 * k + 139148 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 139148) = 139968 * k + 69574 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69574) = 69984 * k + 34787 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 34787) = 104976 * k + 52181 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52181) = 157464 * k + 78272 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 78272) = 78732 * k + 39136 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39136) = 39366 * k + 19568 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19568) = 19683 * k + 9784 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32603_mod_65536 {n : ℕ} (hn : n % 65536 = 32603) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32603 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32603) = 98304 * k + 48905 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48905) = 147456 * k + 73358 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73358) = 73728 * k + 36679 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 36679) = 110592 * k + 55019 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 55019) = 165888 * k + 82529 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 82529) = 248832 * k + 123794 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 123794) = 124416 * k + 61897 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 61897) = 186624 * k + 92846 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 92846) = 93312 * k + 46423 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 46423) = 139968 * k + 69635 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69635) = 209952 * k + 104453 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 104453) = 314928 * k + 156680 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 156680) = 157464 * k + 78340 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 78340) = 78732 * k + 39170 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39170) = 39366 * k + 19585 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19585) = 59049 * k + 29378 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32603) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32603)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32623_mod_65536 {n : ℕ} (hn : n % 65536 = 32623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32623) = 98304 * k + 48935 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 48935) = 147456 * k + 73403 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73403) = 221184 * k + 110105 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 110105) = 331776 * k + 165158 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 165158) = 165888 * k + 82579 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 82579) = 248832 * k + 123869 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 123869) = 373248 * k + 185804 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 185804) = 186624 * k + 92902 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 92902) = 93312 * k + 46451 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 46451) = 139968 * k + 69677 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69677) = 209952 * k + 104516 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 104516) = 104976 * k + 52258 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52258) = 52488 * k + 26129 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26129) = 78732 * k + 39194 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39194) = 39366 * k + 19597 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19597) = 59049 * k + 29396 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32703_mod_65536 {n : ℕ} (hn : n % 65536 = 32703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32703) = 98304 * k + 49055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49055) = 147456 * k + 73583 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73583) = 221184 * k + 110375 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 110375) = 331776 * k + 165563 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 165563) = 497664 * k + 248345 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 248345) = 746496 * k + 372518 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 372518) = 373248 * k + 186259 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 186259) = 559872 * k + 279389 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 279389) = 839808 * k + 419084 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 419084) = 419904 * k + 209542 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 209542) = 209952 * k + 104771 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 104771) = 314928 * k + 157157 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 157157) = 472392 * k + 235736 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 235736) = 236196 * k + 117868 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 117868) = 118098 * k + 58934 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 58934) = 59049 * k + 29467 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32763_mod_65536 {n : ℕ} (hn : n % 65536 = 32763) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32763 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32763) = 98304 * k + 49145 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49145) = 147456 * k + 73718 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73718) = 73728 * k + 36859 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 36859) = 110592 * k + 55289 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 55289) = 165888 * k + 82934 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 82934) = 82944 * k + 41467 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 41467) = 124416 * k + 62201 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 62201) = 186624 * k + 93302 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 93302) = 93312 * k + 46651 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 46651) = 139968 * k + 69977 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 69977) = 209952 * k + 104966 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 104966) = 104976 * k + 52483 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52483) = 157464 * k + 78725 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 78725) = 236196 * k + 118088 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 118088) = 118098 * k + 59044 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59044) = 59049 * k + 29522 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32763) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32763)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32859_mod_65536 {n : ℕ} (hn : n % 65536 = 32859) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32859 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32859) = 98304 * k + 49289 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49289) = 147456 * k + 73934 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 73934) = 73728 * k + 36967 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 36967) = 110592 * k + 55451 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 55451) = 165888 * k + 83177 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 83177) = 248832 * k + 124766 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 124766) = 124416 * k + 62383 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 62383) = 186624 * k + 93575 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 93575) = 279936 * k + 140363 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 140363) = 419904 * k + 210545 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 210545) = 629856 * k + 315818 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 315818) = 314928 * k + 157909 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 157909) = 472392 * k + 236864 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 236864) = 236196 * k + 118432 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 118432) = 118098 * k + 59216 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59216) = 59049 * k + 29608 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32859) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32859)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32895_mod_65536 {n : ℕ} (hn : n % 65536 = 32895) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32895 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32895) = 98304 * k + 49343 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49343) = 147456 * k + 74015 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74015) = 221184 * k + 111023 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111023) = 331776 * k + 166535 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 166535) = 497664 * k + 249803 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 249803) = 746496 * k + 374705 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 374705) = 1119744 * k + 562058 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 562058) = 559872 * k + 281029 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 281029) = 839808 * k + 421544 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 421544) = 419904 * k + 210772 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 210772) = 209952 * k + 105386 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 105386) = 104976 * k + 52693 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52693) = 157464 * k + 79040 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79040) = 78732 * k + 39520 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39520) = 39366 * k + 19760 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19760) = 19683 * k + 9880 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32895) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32895)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32923_mod_65536 {n : ℕ} (hn : n % 65536 = 32923) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32923 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32923) = 98304 * k + 49385 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49385) = 147456 * k + 74078 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74078) = 73728 * k + 37039 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 37039) = 110592 * k + 55559 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 55559) = 165888 * k + 83339 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 83339) = 248832 * k + 125009 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 125009) = 373248 * k + 187514 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 187514) = 186624 * k + 93757 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 93757) = 279936 * k + 140636 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 140636) = 139968 * k + 70318 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 70318) = 69984 * k + 35159 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 35159) = 104976 * k + 52739 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52739) = 157464 * k + 79109 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79109) = 236196 * k + 118664 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 118664) = 118098 * k + 59332 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59332) = 59049 * k + 29666 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32923) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32923)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_32975_mod_65536 {n : ℕ} (hn : n % 65536 = 32975) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 32975 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 32975) = 98304 * k + 49463 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49463) = 147456 * k + 74195 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74195) = 221184 * k + 111293 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111293) = 331776 * k + 166940 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 166940) = 165888 * k + 83470 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 83470) = 82944 * k + 41735 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 41735) = 124416 * k + 62603 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 62603) = 186624 * k + 93905 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 93905) = 279936 * k + 140858 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 140858) = 139968 * k + 70429 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 70429) = 209952 * k + 105644 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 105644) = 104976 * k + 52822 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52822) = 52488 * k + 26411 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26411) = 78732 * k + 39617 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39617) = 118098 * k + 59426 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59426) = 59049 * k + 29713 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 32975) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 32975)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33007_mod_65536 {n : ℕ} (hn : n % 65536 = 33007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33007) = 98304 * k + 49511 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49511) = 147456 * k + 74267 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74267) = 221184 * k + 111401 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111401) = 331776 * k + 167102 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 167102) = 165888 * k + 83551 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 83551) = 248832 * k + 125327 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 125327) = 373248 * k + 187991 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 187991) = 559872 * k + 281987 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 281987) = 839808 * k + 422981 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 422981) = 1259712 * k + 634472 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 634472) = 629856 * k + 317236 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 317236) = 314928 * k + 158618 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 158618) = 157464 * k + 79309 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79309) = 236196 * k + 118964 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 118964) = 118098 * k + 59482 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59482) = 59049 * k + 29741 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33023_mod_65536 {n : ℕ} (hn : n % 65536 = 33023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33023) = 98304 * k + 49535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49535) = 147456 * k + 74303 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74303) = 221184 * k + 111455 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111455) = 331776 * k + 167183 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 167183) = 497664 * k + 250775 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 250775) = 746496 * k + 376163 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 376163) = 1119744 * k + 564245 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 564245) = 1679616 * k + 846368 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 846368) = 839808 * k + 423184 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 423184) = 419904 * k + 211592 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 211592) = 209952 * k + 105796 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 105796) = 104976 * k + 52898 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 52898) = 52488 * k + 26449 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26449) = 78732 * k + 39674 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39674) = 39366 * k + 19837 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19837) = 59049 * k + 29756 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
