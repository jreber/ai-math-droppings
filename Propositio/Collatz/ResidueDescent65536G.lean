import Propositio.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_49359_mod_65536 {n : ℕ} (hn : n % 65536 = 49359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49359) = 98304 * k + 74039 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74039) = 147456 * k + 111059 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111059) = 221184 * k + 166589 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 166589) = 331776 * k + 249884 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 249884) = 165888 * k + 124942 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 124942) = 82944 * k + 62471 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 62471) = 124416 * k + 93707 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 93707) = 186624 * k + 140561 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 140561) = 279936 * k + 210842 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 210842) = 139968 * k + 105421 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 105421) = 209952 * k + 158132 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 158132) = 104976 * k + 79066 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 79066) = 52488 * k + 39533 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 39533) = 78732 * k + 59300 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59300) = 39366 * k + 29650 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29650) = 19683 * k + 14825 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49407_mod_65536 {n : ℕ} (hn : n % 65536 = 49407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49407) = 98304 * k + 74111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74111) = 147456 * k + 111167 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111167) = 221184 * k + 166751 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 166751) = 331776 * k + 250127 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 250127) = 497664 * k + 375191 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 375191) = 746496 * k + 562787 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 562787) = 1119744 * k + 844181 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 844181) = 1679616 * k + 1266272 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1266272) = 839808 * k + 633136 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 633136) = 419904 * k + 316568 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 316568) = 209952 * k + 158284 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 158284) = 104976 * k + 79142 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 79142) = 52488 * k + 39571 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 39571) = 78732 * k + 59357 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59357) = 118098 * k + 89036 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 89036) = 59049 * k + 44518 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49511_mod_65536 {n : ℕ} (hn : n % 65536 = 49511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49511) = 98304 * k + 74267 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74267) = 147456 * k + 111401 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111401) = 221184 * k + 167102 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 167102) = 110592 * k + 83551 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 83551) = 165888 * k + 125327 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 125327) = 248832 * k + 187991 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 187991) = 373248 * k + 281987 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 281987) = 559872 * k + 422981 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 422981) = 839808 * k + 634472 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 634472) = 419904 * k + 317236 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 317236) = 209952 * k + 158618 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 158618) = 104976 * k + 79309 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 79309) = 157464 * k + 118964 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 118964) = 78732 * k + 59482 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59482) = 39366 * k + 29741 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29741) = 59049 * k + 44612 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49563_mod_65536 {n : ℕ} (hn : n % 65536 = 49563) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49563 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49563) = 98304 * k + 74345 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74345) = 147456 * k + 111518 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111518) = 73728 * k + 55759 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 55759) = 110592 * k + 83639 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 83639) = 165888 * k + 125459 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 125459) = 248832 * k + 188189 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 188189) = 373248 * k + 282284 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 282284) = 186624 * k + 141142 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 141142) = 93312 * k + 70571 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 70571) = 139968 * k + 105857 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 105857) = 209952 * k + 158786 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 158786) = 104976 * k + 79393 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 79393) = 157464 * k + 119090 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 119090) = 78732 * k + 59545 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59545) = 118098 * k + 89318 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 89318) = 59049 * k + 44659 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49563) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49563)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49567_mod_65536 {n : ℕ} (hn : n % 65536 = 49567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49567) = 98304 * k + 74351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74351) = 147456 * k + 111527 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111527) = 221184 * k + 167291 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 167291) = 331776 * k + 250937 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 250937) = 497664 * k + 376406 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 376406) = 248832 * k + 188203 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 188203) = 373248 * k + 282305 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 282305) = 559872 * k + 423458 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 423458) = 279936 * k + 211729 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 211729) = 419904 * k + 317594 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 317594) = 209952 * k + 158797 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 158797) = 314928 * k + 238196 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 238196) = 157464 * k + 119098 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 119098) = 78732 * k + 59549 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59549) = 118098 * k + 89324 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 89324) = 59049 * k + 44662 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49631_mod_65536 {n : ℕ} (hn : n % 65536 = 49631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49631) = 98304 * k + 74447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74447) = 147456 * k + 111671 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111671) = 221184 * k + 167507 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 167507) = 331776 * k + 251261 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 251261) = 497664 * k + 376892 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 376892) = 248832 * k + 188446 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 188446) = 124416 * k + 94223 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 94223) = 186624 * k + 141335 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 141335) = 279936 * k + 212003 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 212003) = 419904 * k + 318005 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 318005) = 629856 * k + 477008 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 477008) = 314928 * k + 238504 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 238504) = 157464 * k + 119252 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 119252) = 78732 * k + 59626 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59626) = 39366 * k + 29813 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29813) = 59049 * k + 44720 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49639_mod_65536 {n : ℕ} (hn : n % 65536 = 49639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49639) = 98304 * k + 74459 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74459) = 147456 * k + 111689 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 111689) = 221184 * k + 167534 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 167534) = 110592 * k + 83767 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 83767) = 165888 * k + 125651 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 125651) = 248832 * k + 188477 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 188477) = 373248 * k + 282716 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 282716) = 186624 * k + 141358 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 141358) = 93312 * k + 70679 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 70679) = 139968 * k + 106019 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 106019) = 209952 * k + 159029 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 159029) = 314928 * k + 238544 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 238544) = 157464 * k + 119272 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 119272) = 78732 * k + 59636 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59636) = 39366 * k + 29818 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29818) = 19683 * k + 14909 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49915_mod_65536 {n : ℕ} (hn : n % 65536 = 49915) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49915 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49915) = 98304 * k + 74873 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74873) = 147456 * k + 112310 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 112310) = 73728 * k + 56155 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 56155) = 110592 * k + 84233 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 84233) = 165888 * k + 126350 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 126350) = 82944 * k + 63175 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 63175) = 124416 * k + 94763 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 94763) = 186624 * k + 142145 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 142145) = 279936 * k + 213218 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 213218) = 139968 * k + 106609 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 106609) = 209952 * k + 159914 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 159914) = 104976 * k + 79957 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 79957) = 157464 * k + 119936 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 119936) = 78732 * k + 59968 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 59968) = 39366 * k + 29984 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29984) = 19683 * k + 14992 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49915) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49915)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49983_mod_65536 {n : ℕ} (hn : n % 65536 = 49983) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49983 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49983) = 98304 * k + 74975 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 74975) = 147456 * k + 112463 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 112463) = 221184 * k + 168695 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 168695) = 331776 * k + 253043 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 253043) = 497664 * k + 379565 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 379565) = 746496 * k + 569348 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 569348) = 373248 * k + 284674 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 284674) = 186624 * k + 142337 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 142337) = 279936 * k + 213506 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 213506) = 139968 * k + 106753 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 106753) = 209952 * k + 160130 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 160130) = 104976 * k + 80065 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 80065) = 157464 * k + 120098 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 120098) = 78732 * k + 60049 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60049) = 118098 * k + 90074 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 90074) = 59049 * k + 45037 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49983) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49983)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50143_mod_65536 {n : ℕ} (hn : n % 65536 = 50143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50143) = 98304 * k + 75215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75215) = 147456 * k + 112823 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 112823) = 221184 * k + 169235 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 169235) = 331776 * k + 253853 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 253853) = 497664 * k + 380780 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 380780) = 248832 * k + 190390 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 190390) = 124416 * k + 95195 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 95195) = 186624 * k + 142793 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 142793) = 279936 * k + 214190 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 214190) = 139968 * k + 107095 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 107095) = 209952 * k + 160643 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 160643) = 314928 * k + 240965 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 240965) = 472392 * k + 361448 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 361448) = 236196 * k + 180724 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 180724) = 118098 * k + 90362 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 90362) = 59049 * k + 45181 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50223_mod_65536 {n : ℕ} (hn : n % 65536 = 50223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50223) = 98304 * k + 75335 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75335) = 147456 * k + 113003 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113003) = 221184 * k + 169505 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 169505) = 331776 * k + 254258 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 254258) = 165888 * k + 127129 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127129) = 248832 * k + 190694 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 190694) = 124416 * k + 95347 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 95347) = 186624 * k + 143021 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143021) = 279936 * k + 214532 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 214532) = 139968 * k + 107266 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 107266) = 69984 * k + 53633 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 53633) = 104976 * k + 80450 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 80450) = 52488 * k + 40225 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 40225) = 78732 * k + 60338 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60338) = 39366 * k + 30169 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30169) = 59049 * k + 45254 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50267_mod_65536 {n : ℕ} (hn : n % 65536 = 50267) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50267 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50267) = 98304 * k + 75401 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75401) = 147456 * k + 113102 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113102) = 73728 * k + 56551 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 56551) = 110592 * k + 84827 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 84827) = 165888 * k + 127241 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127241) = 248832 * k + 190862 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 190862) = 124416 * k + 95431 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 95431) = 186624 * k + 143147 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143147) = 279936 * k + 214721 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 214721) = 419904 * k + 322082 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 322082) = 209952 * k + 161041 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 161041) = 314928 * k + 241562 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 241562) = 157464 * k + 120781 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 120781) = 236196 * k + 181172 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 181172) = 118098 * k + 90586 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 90586) = 59049 * k + 45293 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50267) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50267)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50303_mod_65536 {n : ℕ} (hn : n % 65536 = 50303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50303) = 98304 * k + 75455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75455) = 147456 * k + 113183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113183) = 221184 * k + 169775 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 169775) = 331776 * k + 254663 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 254663) = 497664 * k + 381995 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 381995) = 746496 * k + 572993 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 572993) = 1119744 * k + 859490 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 859490) = 559872 * k + 429745 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 429745) = 839808 * k + 644618 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 644618) = 419904 * k + 322309 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 322309) = 629856 * k + 483464 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 483464) = 314928 * k + 241732 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 241732) = 157464 * k + 120866 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 120866) = 78732 * k + 60433 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60433) = 118098 * k + 90650 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 90650) = 59049 * k + 45325 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50343_mod_65536 {n : ℕ} (hn : n % 65536 = 50343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50343) = 98304 * k + 75515 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75515) = 147456 * k + 113273 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113273) = 221184 * k + 169910 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 169910) = 110592 * k + 84955 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 84955) = 165888 * k + 127433 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127433) = 248832 * k + 191150 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 191150) = 124416 * k + 95575 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 95575) = 186624 * k + 143363 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143363) = 279936 * k + 215045 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 215045) = 419904 * k + 322568 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 322568) = 209952 * k + 161284 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 161284) = 104976 * k + 80642 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 80642) = 52488 * k + 40321 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 40321) = 78732 * k + 60482 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60482) = 39366 * k + 30241 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30241) = 59049 * k + 45362 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50407_mod_65536 {n : ℕ} (hn : n % 65536 = 50407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50407) = 98304 * k + 75611 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75611) = 147456 * k + 113417 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113417) = 221184 * k + 170126 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 170126) = 110592 * k + 85063 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85063) = 165888 * k + 127595 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127595) = 248832 * k + 191393 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 191393) = 373248 * k + 287090 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 287090) = 186624 * k + 143545 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143545) = 279936 * k + 215318 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 215318) = 139968 * k + 107659 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 107659) = 209952 * k + 161489 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 161489) = 314928 * k + 242234 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 242234) = 157464 * k + 121117 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 121117) = 236196 * k + 181676 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 181676) = 118098 * k + 90838 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 90838) = 59049 * k + 45419 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50495_mod_65536 {n : ℕ} (hn : n % 65536 = 50495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50495) = 98304 * k + 75743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75743) = 147456 * k + 113615 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113615) = 221184 * k + 170423 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 170423) = 331776 * k + 255635 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 255635) = 497664 * k + 383453 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 383453) = 746496 * k + 575180 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 575180) = 373248 * k + 287590 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 287590) = 186624 * k + 143795 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143795) = 279936 * k + 215693 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 215693) = 419904 * k + 323540 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 323540) = 209952 * k + 161770 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 161770) = 104976 * k + 80885 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 80885) = 157464 * k + 121328 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 121328) = 78732 * k + 60664 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60664) = 39366 * k + 30332 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30332) = 19683 * k + 15166 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50503_mod_65536 {n : ℕ} (hn : n % 65536 = 50503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50503) = 98304 * k + 75755 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75755) = 147456 * k + 113633 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113633) = 221184 * k + 170450 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 170450) = 110592 * k + 85225 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85225) = 165888 * k + 127838 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127838) = 82944 * k + 63919 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 63919) = 124416 * k + 95879 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 95879) = 186624 * k + 143819 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 143819) = 279936 * k + 215729 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 215729) = 419904 * k + 323594 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 323594) = 209952 * k + 161797 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 161797) = 314928 * k + 242696 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 242696) = 157464 * k + 121348 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 121348) = 78732 * k + 60674 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60674) = 39366 * k + 30337 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30337) = 59049 * k + 45506 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50535_mod_65536 {n : ℕ} (hn : n % 65536 = 50535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50535) = 98304 * k + 75803 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75803) = 147456 * k + 113705 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113705) = 221184 * k + 170558 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 170558) = 110592 * k + 85279 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85279) = 165888 * k + 127919 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 127919) = 248832 * k + 191879 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 191879) = 373248 * k + 287819 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 287819) = 559872 * k + 431729 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 431729) = 839808 * k + 647594 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 647594) = 419904 * k + 323797 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 323797) = 629856 * k + 485696 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 485696) = 314928 * k + 242848 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 242848) = 157464 * k + 121424 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 121424) = 78732 * k + 60712 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60712) = 39366 * k + 30356 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30356) = 19683 * k + 15178 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50663_mod_65536 {n : ℕ} (hn : n % 65536 = 50663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50663) = 98304 * k + 75995 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 75995) = 147456 * k + 113993 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 113993) = 221184 * k + 170990 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 170990) = 110592 * k + 85495 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85495) = 165888 * k + 128243 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 128243) = 248832 * k + 192365 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 192365) = 373248 * k + 288548 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 288548) = 186624 * k + 144274 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 144274) = 93312 * k + 72137 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 72137) = 139968 * k + 108206 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 108206) = 69984 * k + 54103 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 54103) = 104976 * k + 81155 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81155) = 157464 * k + 121733 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 121733) = 236196 * k + 182600 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 182600) = 118098 * k + 91300 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 91300) = 59049 * k + 45650 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50715_mod_65536 {n : ℕ} (hn : n % 65536 = 50715) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50715 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50715) = 98304 * k + 76073 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76073) = 147456 * k + 114110 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114110) = 73728 * k + 57055 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 57055) = 110592 * k + 85583 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85583) = 165888 * k + 128375 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 128375) = 248832 * k + 192563 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 192563) = 373248 * k + 288845 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 288845) = 559872 * k + 433268 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 433268) = 279936 * k + 216634 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 216634) = 139968 * k + 108317 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 108317) = 209952 * k + 162476 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 162476) = 104976 * k + 81238 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81238) = 52488 * k + 40619 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 40619) = 78732 * k + 60929 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 60929) = 118098 * k + 91394 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 91394) = 59049 * k + 45697 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50715) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50715)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50779_mod_65536 {n : ℕ} (hn : n % 65536 = 50779) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50779 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50779) = 98304 * k + 76169 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76169) = 147456 * k + 114254 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114254) = 73728 * k + 57127 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 57127) = 110592 * k + 85691 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85691) = 165888 * k + 128537 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 128537) = 248832 * k + 192806 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 192806) = 124416 * k + 96403 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 96403) = 186624 * k + 144605 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 144605) = 279936 * k + 216908 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 216908) = 139968 * k + 108454 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 108454) = 69984 * k + 54227 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 54227) = 104976 * k + 81341 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81341) = 157464 * k + 122012 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 122012) = 78732 * k + 61006 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61006) = 39366 * k + 30503 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30503) = 59049 * k + 45755 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50779) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50779)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50843_mod_65536 {n : ℕ} (hn : n % 65536 = 50843) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50843 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50843) = 98304 * k + 76265 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76265) = 147456 * k + 114398 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114398) = 73728 * k + 57199 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 57199) = 110592 * k + 85799 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 85799) = 165888 * k + 128699 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 128699) = 248832 * k + 193049 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 193049) = 373248 * k + 289574 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 289574) = 186624 * k + 144787 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 144787) = 279936 * k + 217181 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 217181) = 419904 * k + 325772 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 325772) = 209952 * k + 162886 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 162886) = 104976 * k + 81443 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81443) = 157464 * k + 122165 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 122165) = 236196 * k + 183248 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 183248) = 118098 * k + 91624 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 91624) = 59049 * k + 45812 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50843) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50843)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_50847_mod_65536 {n : ℕ} (hn : n % 65536 = 50847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 50847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 50847) = 98304 * k + 76271 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76271) = 147456 * k + 114407 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114407) = 221184 * k + 171611 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 171611) = 331776 * k + 257417 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 257417) = 497664 * k + 386126 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 386126) = 248832 * k + 193063 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 193063) = 373248 * k + 289595 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 289595) = 559872 * k + 434393 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 434393) = 839808 * k + 651590 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 651590) = 419904 * k + 325795 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 325795) = 629856 * k + 488693 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 488693) = 944784 * k + 733040 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 733040) = 472392 * k + 366520 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 366520) = 236196 * k + 183260 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 183260) = 118098 * k + 91630 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 91630) = 59049 * k + 45815 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 50847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 50847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51055_mod_65536 {n : ℕ} (hn : n % 65536 = 51055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51055) = 98304 * k + 76583 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76583) = 147456 * k + 114875 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114875) = 221184 * k + 172313 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 172313) = 331776 * k + 258470 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 258470) = 165888 * k + 129235 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 129235) = 248832 * k + 193853 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 193853) = 373248 * k + 290780 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 290780) = 186624 * k + 145390 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 145390) = 93312 * k + 72695 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 72695) = 139968 * k + 109043 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109043) = 209952 * k + 163565 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 163565) = 314928 * k + 245348 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 245348) = 157464 * k + 122674 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 122674) = 78732 * k + 61337 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61337) = 118098 * k + 92006 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92006) = 59049 * k + 46003 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51103_mod_65536 {n : ℕ} (hn : n % 65536 = 51103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51103) = 98304 * k + 76655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76655) = 147456 * k + 114983 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 114983) = 221184 * k + 172475 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 172475) = 331776 * k + 258713 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 258713) = 497664 * k + 388070 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 388070) = 248832 * k + 194035 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 194035) = 373248 * k + 291053 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 291053) = 559872 * k + 436580 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 436580) = 279936 * k + 218290 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 218290) = 139968 * k + 109145 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109145) = 209952 * k + 163718 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 163718) = 104976 * k + 81859 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81859) = 157464 * k + 122789 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 122789) = 236196 * k + 184184 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 184184) = 118098 * k + 92092 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92092) = 59049 * k + 46046 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51135_mod_65536 {n : ℕ} (hn : n % 65536 = 51135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51135) = 98304 * k + 76703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76703) = 147456 * k + 115055 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115055) = 221184 * k + 172583 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 172583) = 331776 * k + 258875 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 258875) = 497664 * k + 388313 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 388313) = 746496 * k + 582470 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 582470) = 373248 * k + 291235 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 291235) = 559872 * k + 436853 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 436853) = 839808 * k + 655280 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 655280) = 419904 * k + 327640 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 327640) = 209952 * k + 163820 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 163820) = 104976 * k + 81910 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81910) = 52488 * k + 40955 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 40955) = 78732 * k + 61433 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61433) = 118098 * k + 92150 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92150) = 59049 * k + 46075 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51167_mod_65536 {n : ℕ} (hn : n % 65536 = 51167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51167) = 98304 * k + 76751 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76751) = 147456 * k + 115127 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115127) = 221184 * k + 172691 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 172691) = 331776 * k + 259037 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 259037) = 497664 * k + 388556 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 388556) = 248832 * k + 194278 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 194278) = 124416 * k + 97139 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 97139) = 186624 * k + 145709 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 145709) = 279936 * k + 218564 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 218564) = 139968 * k + 109282 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109282) = 69984 * k + 54641 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 54641) = 104976 * k + 81962 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 81962) = 52488 * k + 40981 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 40981) = 78732 * k + 61472 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61472) = 39366 * k + 30736 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30736) = 19683 * k + 15368 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51227_mod_65536 {n : ℕ} (hn : n % 65536 = 51227) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51227 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51227) = 98304 * k + 76841 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76841) = 147456 * k + 115262 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115262) = 73728 * k + 57631 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 57631) = 110592 * k + 86447 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 86447) = 165888 * k + 129671 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 129671) = 248832 * k + 194507 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 194507) = 373248 * k + 291761 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 291761) = 559872 * k + 437642 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 437642) = 279936 * k + 218821 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 218821) = 419904 * k + 328232 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 328232) = 209952 * k + 164116 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 164116) = 104976 * k + 82058 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82058) = 52488 * k + 41029 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 41029) = 78732 * k + 61544 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61544) = 39366 * k + 30772 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30772) = 19683 * k + 15386 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51227) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51227)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51247_mod_65536 {n : ℕ} (hn : n % 65536 = 51247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51247) = 98304 * k + 76871 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76871) = 147456 * k + 115307 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115307) = 221184 * k + 172961 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 172961) = 331776 * k + 259442 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 259442) = 165888 * k + 129721 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 129721) = 248832 * k + 194582 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 194582) = 124416 * k + 97291 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 97291) = 186624 * k + 145937 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 145937) = 279936 * k + 218906 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 218906) = 139968 * k + 109453 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109453) = 209952 * k + 164180 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 164180) = 104976 * k + 82090 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82090) = 52488 * k + 41045 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 41045) = 78732 * k + 61568 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61568) = 39366 * k + 30784 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30784) = 19683 * k + 15392 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51271_mod_65536 {n : ℕ} (hn : n % 65536 = 51271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51271) = 98304 * k + 76907 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 76907) = 147456 * k + 115361 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115361) = 221184 * k + 173042 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 173042) = 110592 * k + 86521 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 86521) = 165888 * k + 129782 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 129782) = 82944 * k + 64891 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 64891) = 124416 * k + 97337 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 97337) = 186624 * k + 146006 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146006) = 93312 * k + 73003 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 73003) = 139968 * k + 109505 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109505) = 209952 * k + 164258 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 164258) = 104976 * k + 82129 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82129) = 157464 * k + 123194 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123194) = 78732 * k + 61597 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61597) = 118098 * k + 92396 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92396) = 59049 * k + 46198 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51407_mod_65536 {n : ℕ} (hn : n % 65536 = 51407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51407) = 98304 * k + 77111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77111) = 147456 * k + 115667 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115667) = 221184 * k + 173501 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 173501) = 331776 * k + 260252 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 260252) = 165888 * k + 130126 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 130126) = 82944 * k + 65063 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 65063) = 124416 * k + 97595 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 97595) = 186624 * k + 146393 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146393) = 279936 * k + 219590 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 219590) = 139968 * k + 109795 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109795) = 209952 * k + 164693 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 164693) = 314928 * k + 247040 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 247040) = 157464 * k + 123520 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123520) = 78732 * k + 61760 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61760) = 39366 * k + 30880 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30880) = 19683 * k + 15440 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51431_mod_65536 {n : ℕ} (hn : n % 65536 = 51431) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51431 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51431) = 98304 * k + 77147 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77147) = 147456 * k + 115721 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115721) = 221184 * k + 173582 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 173582) = 110592 * k + 86791 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 86791) = 165888 * k + 130187 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 130187) = 248832 * k + 195281 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 195281) = 373248 * k + 292922 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 292922) = 186624 * k + 146461 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146461) = 279936 * k + 219692 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 219692) = 139968 * k + 109846 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 109846) = 69984 * k + 54923 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 54923) = 104976 * k + 82385 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82385) = 157464 * k + 123578 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123578) = 78732 * k + 61789 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61789) = 118098 * k + 92684 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92684) = 59049 * k + 46342 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51431) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51431)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51451_mod_65536 {n : ℕ} (hn : n % 65536 = 51451) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51451 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51451) = 98304 * k + 77177 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77177) = 147456 * k + 115766 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115766) = 73728 * k + 57883 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 57883) = 110592 * k + 86825 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 86825) = 165888 * k + 130238 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 130238) = 82944 * k + 65119 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 65119) = 124416 * k + 97679 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 97679) = 186624 * k + 146519 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146519) = 279936 * k + 219779 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 219779) = 419904 * k + 329669 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 329669) = 629856 * k + 494504 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 494504) = 314928 * k + 247252 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 247252) = 157464 * k + 123626 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123626) = 78732 * k + 61813 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61813) = 118098 * k + 92720 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92720) = 59049 * k + 46360 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51451) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51451)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51455_mod_65536 {n : ℕ} (hn : n % 65536 = 51455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51455) = 98304 * k + 77183 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77183) = 147456 * k + 115775 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115775) = 221184 * k + 173663 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 173663) = 331776 * k + 260495 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 260495) = 497664 * k + 390743 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 390743) = 746496 * k + 586115 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 586115) = 1119744 * k + 879173 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 879173) = 1679616 * k + 1318760 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1318760) = 839808 * k + 659380 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 659380) = 419904 * k + 329690 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 329690) = 209952 * k + 164845 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 164845) = 314928 * k + 247268 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 247268) = 157464 * k + 123634 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123634) = 78732 * k + 61817 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61817) = 118098 * k + 92726 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 92726) = 59049 * k + 46363 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51519_mod_65536 {n : ℕ} (hn : n % 65536 = 51519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51519) = 98304 * k + 77279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77279) = 147456 * k + 115919 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 115919) = 221184 * k + 173879 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 173879) = 331776 * k + 260819 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 260819) = 497664 * k + 391229 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 391229) = 746496 * k + 586844 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 586844) = 373248 * k + 293422 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 293422) = 186624 * k + 146711 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146711) = 279936 * k + 220067 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 220067) = 419904 * k + 330101 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 330101) = 629856 * k + 495152 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 495152) = 314928 * k + 247576 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 247576) = 157464 * k + 123788 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 123788) = 78732 * k + 61894 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 61894) = 39366 * k + 30947 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 30947) = 59049 * k + 46421 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51611_mod_65536 {n : ℕ} (hn : n % 65536 = 51611) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51611 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51611) = 98304 * k + 77417 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77417) = 147456 * k + 116126 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116126) = 73728 * k + 58063 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 58063) = 110592 * k + 87095 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 87095) = 165888 * k + 130643 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 130643) = 248832 * k + 195965 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 195965) = 373248 * k + 293948 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 293948) = 186624 * k + 146974 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 146974) = 93312 * k + 73487 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 73487) = 139968 * k + 110231 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 110231) = 209952 * k + 165347 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 165347) = 314928 * k + 248021 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 248021) = 472392 * k + 372032 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 372032) = 236196 * k + 186016 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 186016) = 118098 * k + 93008 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 93008) = 59049 * k + 46504 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51611) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51611)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51663_mod_65536 {n : ℕ} (hn : n % 65536 = 51663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51663) = 98304 * k + 77495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77495) = 147456 * k + 116243 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116243) = 221184 * k + 174365 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 174365) = 331776 * k + 261548 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 261548) = 165888 * k + 130774 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 130774) = 82944 * k + 65387 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 65387) = 124416 * k + 98081 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 98081) = 186624 * k + 147122 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 147122) = 93312 * k + 73561 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 73561) = 139968 * k + 110342 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 110342) = 69984 * k + 55171 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 55171) = 104976 * k + 82757 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82757) = 157464 * k + 124136 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 124136) = 78732 * k + 62068 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62068) = 39366 * k + 31034 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31034) = 19683 * k + 15517 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51803_mod_65536 {n : ℕ} (hn : n % 65536 = 51803) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51803 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51803) = 98304 * k + 77705 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77705) = 147456 * k + 116558 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116558) = 73728 * k + 58279 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 58279) = 110592 * k + 87419 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 87419) = 165888 * k + 131129 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 131129) = 248832 * k + 196694 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 196694) = 124416 * k + 98347 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 98347) = 186624 * k + 147521 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 147521) = 279936 * k + 221282 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 221282) = 139968 * k + 110641 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 110641) = 209952 * k + 165962 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 165962) = 104976 * k + 82981 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 82981) = 157464 * k + 124472 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 124472) = 78732 * k + 62236 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62236) = 39366 * k + 31118 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31118) = 19683 * k + 15559 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51803) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51803)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51871_mod_65536 {n : ℕ} (hn : n % 65536 = 51871) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51871 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51871) = 98304 * k + 77807 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77807) = 147456 * k + 116711 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116711) = 221184 * k + 175067 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 175067) = 331776 * k + 262601 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 262601) = 497664 * k + 393902 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 393902) = 248832 * k + 196951 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 196951) = 373248 * k + 295427 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 295427) = 559872 * k + 443141 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 443141) = 839808 * k + 664712 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 664712) = 419904 * k + 332356 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 332356) = 209952 * k + 166178 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 166178) = 104976 * k + 83089 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 83089) = 157464 * k + 124634 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 124634) = 78732 * k + 62317 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62317) = 118098 * k + 93476 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 93476) = 59049 * k + 46738 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51871) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51871)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51951_mod_65536 {n : ℕ} (hn : n % 65536 = 51951) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51951 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51951) = 98304 * k + 77927 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77927) = 147456 * k + 116891 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116891) = 221184 * k + 175337 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 175337) = 331776 * k + 263006 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 263006) = 165888 * k + 131503 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 131503) = 248832 * k + 197255 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 197255) = 373248 * k + 295883 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 295883) = 559872 * k + 443825 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 443825) = 839808 * k + 665738 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 665738) = 419904 * k + 332869 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 332869) = 629856 * k + 499304 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 499304) = 314928 * k + 249652 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 249652) = 157464 * k + 124826 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 124826) = 78732 * k + 62413 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62413) = 118098 * k + 93620 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 93620) = 59049 * k + 46810 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51951) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51951)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_51967_mod_65536 {n : ℕ} (hn : n % 65536 = 51967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 51967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 51967) = 98304 * k + 77951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 77951) = 147456 * k + 116927 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 116927) = 221184 * k + 175391 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 175391) = 331776 * k + 263087 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 263087) = 497664 * k + 394631 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 394631) = 746496 * k + 591947 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 591947) = 1119744 * k + 887921 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 887921) = 1679616 * k + 1331882 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1331882) = 839808 * k + 665941 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 665941) = 1259712 * k + 998912 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 998912) = 629856 * k + 499456 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 499456) = 314928 * k + 249728 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 249728) = 157464 * k + 124864 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 124864) = 78732 * k + 62432 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62432) = 39366 * k + 31216 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31216) = 19683 * k + 15608 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 51967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 51967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52031_mod_65536 {n : ℕ} (hn : n % 65536 = 52031) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52031 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52031) = 98304 * k + 78047 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78047) = 147456 * k + 117071 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117071) = 221184 * k + 175607 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 175607) = 331776 * k + 263411 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 263411) = 497664 * k + 395117 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 395117) = 746496 * k + 592676 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 592676) = 373248 * k + 296338 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 296338) = 186624 * k + 148169 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 148169) = 279936 * k + 222254 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 222254) = 139968 * k + 111127 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 111127) = 209952 * k + 166691 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 166691) = 314928 * k + 250037 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 250037) = 472392 * k + 375056 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 375056) = 236196 * k + 187528 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 187528) = 118098 * k + 93764 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 93764) = 59049 * k + 46882 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52031) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52031)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52071_mod_65536 {n : ℕ} (hn : n % 65536 = 52071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52071) = 98304 * k + 78107 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78107) = 147456 * k + 117161 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117161) = 221184 * k + 175742 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 175742) = 110592 * k + 87871 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 87871) = 165888 * k + 131807 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 131807) = 248832 * k + 197711 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 197711) = 373248 * k + 296567 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 296567) = 559872 * k + 444851 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 444851) = 839808 * k + 667277 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 667277) = 1259712 * k + 1000916 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1000916) = 629856 * k + 500458 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 500458) = 314928 * k + 250229 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 250229) = 472392 * k + 375344 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 375344) = 236196 * k + 187672 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 187672) = 118098 * k + 93836 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 93836) = 59049 * k + 46918 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52191_mod_65536 {n : ℕ} (hn : n % 65536 = 52191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52191) = 98304 * k + 78287 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78287) = 147456 * k + 117431 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117431) = 221184 * k + 176147 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 176147) = 331776 * k + 264221 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 264221) = 497664 * k + 396332 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 396332) = 248832 * k + 198166 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 198166) = 124416 * k + 99083 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 99083) = 186624 * k + 148625 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 148625) = 279936 * k + 222938 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 222938) = 139968 * k + 111469 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 111469) = 209952 * k + 167204 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 167204) = 104976 * k + 83602 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 83602) = 52488 * k + 41801 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 41801) = 78732 * k + 62702 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62702) = 39366 * k + 31351 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31351) = 59049 * k + 47027 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52335_mod_65536 {n : ℕ} (hn : n % 65536 = 52335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52335) = 98304 * k + 78503 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78503) = 147456 * k + 117755 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117755) = 221184 * k + 176633 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 176633) = 331776 * k + 264950 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 264950) = 165888 * k + 132475 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 132475) = 248832 * k + 198713 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 198713) = 373248 * k + 298070 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 298070) = 186624 * k + 149035 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 149035) = 279936 * k + 223553 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 223553) = 419904 * k + 335330 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 335330) = 209952 * k + 167665 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 167665) = 314928 * k + 251498 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 251498) = 157464 * k + 125749 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 125749) = 236196 * k + 188624 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 188624) = 118098 * k + 94312 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94312) = 59049 * k + 47156 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52391_mod_65536 {n : ℕ} (hn : n % 65536 = 52391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52391) = 98304 * k + 78587 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78587) = 147456 * k + 117881 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117881) = 221184 * k + 176822 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 176822) = 110592 * k + 88411 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 88411) = 165888 * k + 132617 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 132617) = 248832 * k + 198926 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 198926) = 124416 * k + 99463 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 99463) = 186624 * k + 149195 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 149195) = 279936 * k + 223793 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 223793) = 419904 * k + 335690 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 335690) = 209952 * k + 167845 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 167845) = 314928 * k + 251768 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 251768) = 157464 * k + 125884 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 125884) = 78732 * k + 62942 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 62942) = 39366 * k + 31471 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31471) = 59049 * k + 47207 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52415_mod_65536 {n : ℕ} (hn : n % 65536 = 52415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52415) = 98304 * k + 78623 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78623) = 147456 * k + 117935 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117935) = 221184 * k + 176903 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 176903) = 331776 * k + 265355 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 265355) = 497664 * k + 398033 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 398033) = 746496 * k + 597050 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 597050) = 373248 * k + 298525 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 298525) = 559872 * k + 447788 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 447788) = 279936 * k + 223894 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 223894) = 139968 * k + 111947 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 111947) = 209952 * k + 167921 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 167921) = 314928 * k + 251882 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 251882) = 157464 * k + 125941 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 125941) = 236196 * k + 188912 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 188912) = 118098 * k + 94456 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94456) = 59049 * k + 47228 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52431_mod_65536 {n : ℕ} (hn : n % 65536 = 52431) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52431 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52431) = 98304 * k + 78647 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78647) = 147456 * k + 117971 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 117971) = 221184 * k + 176957 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 176957) = 331776 * k + 265436 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 265436) = 165888 * k + 132718 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 132718) = 82944 * k + 66359 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 66359) = 124416 * k + 99539 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 99539) = 186624 * k + 149309 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 149309) = 279936 * k + 223964 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 223964) = 139968 * k + 111982 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 111982) = 69984 * k + 55991 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 55991) = 104976 * k + 83987 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 83987) = 157464 * k + 125981 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 125981) = 236196 * k + 188972 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 188972) = 118098 * k + 94486 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94486) = 59049 * k + 47243 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52431) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52431)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52507_mod_65536 {n : ℕ} (hn : n % 65536 = 52507) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52507 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52507) = 98304 * k + 78761 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78761) = 147456 * k + 118142 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118142) = 73728 * k + 59071 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 59071) = 110592 * k + 88607 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 88607) = 165888 * k + 132911 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 132911) = 248832 * k + 199367 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 199367) = 373248 * k + 299051 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 299051) = 559872 * k + 448577 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 448577) = 839808 * k + 672866 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 672866) = 419904 * k + 336433 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 336433) = 629856 * k + 504650 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 504650) = 314928 * k + 252325 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 252325) = 472392 * k + 378488 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 378488) = 236196 * k + 189244 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 189244) = 118098 * k + 94622 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94622) = 59049 * k + 47311 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52507) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52507)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52551_mod_65536 {n : ℕ} (hn : n % 65536 = 52551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52551) = 98304 * k + 78827 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78827) = 147456 * k + 118241 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118241) = 221184 * k + 177362 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 177362) = 110592 * k + 88681 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 88681) = 165888 * k + 133022 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 133022) = 82944 * k + 66511 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 66511) = 124416 * k + 99767 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 99767) = 186624 * k + 149651 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 149651) = 279936 * k + 224477 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 224477) = 419904 * k + 336716 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 336716) = 209952 * k + 168358 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 168358) = 104976 * k + 84179 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84179) = 157464 * k + 126269 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 126269) = 236196 * k + 189404 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 189404) = 118098 * k + 94702 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94702) = 59049 * k + 47351 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52635_mod_65536 {n : ℕ} (hn : n % 65536 = 52635) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52635 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52635) = 98304 * k + 78953 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 78953) = 147456 * k + 118430 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118430) = 73728 * k + 59215 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 59215) = 110592 * k + 88823 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 88823) = 165888 * k + 133235 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 133235) = 248832 * k + 199853 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 199853) = 373248 * k + 299780 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 299780) = 186624 * k + 149890 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 149890) = 93312 * k + 74945 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 74945) = 139968 * k + 112418 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 112418) = 69984 * k + 56209 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 56209) = 104976 * k + 84314 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84314) = 52488 * k + 42157 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 42157) = 78732 * k + 63236 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63236) = 39366 * k + 31618 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31618) = 19683 * k + 15809 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52635) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52635)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52687_mod_65536 {n : ℕ} (hn : n % 65536 = 52687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52687) = 98304 * k + 79031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79031) = 147456 * k + 118547 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118547) = 221184 * k + 177821 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 177821) = 331776 * k + 266732 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 266732) = 165888 * k + 133366 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 133366) = 82944 * k + 66683 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 66683) = 124416 * k + 100025 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 100025) = 186624 * k + 150038 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 150038) = 93312 * k + 75019 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 75019) = 139968 * k + 112529 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 112529) = 209952 * k + 168794 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 168794) = 104976 * k + 84397 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84397) = 157464 * k + 126596 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 126596) = 78732 * k + 63298 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63298) = 39366 * k + 31649 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31649) = 59049 * k + 47474 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52703_mod_65536 {n : ℕ} (hn : n % 65536 = 52703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52703) = 98304 * k + 79055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79055) = 147456 * k + 118583 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118583) = 221184 * k + 177875 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 177875) = 331776 * k + 266813 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 266813) = 497664 * k + 400220 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 400220) = 248832 * k + 200110 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 200110) = 124416 * k + 100055 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 100055) = 186624 * k + 150083 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 150083) = 279936 * k + 225125 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 225125) = 419904 * k + 337688 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 337688) = 209952 * k + 168844 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 168844) = 104976 * k + 84422 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84422) = 52488 * k + 42211 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 42211) = 78732 * k + 63317 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63317) = 118098 * k + 94976 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 94976) = 59049 * k + 47488 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52735_mod_65536 {n : ℕ} (hn : n % 65536 = 52735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52735) = 98304 * k + 79103 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79103) = 147456 * k + 118655 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118655) = 221184 * k + 177983 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 177983) = 331776 * k + 266975 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 266975) = 497664 * k + 400463 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 400463) = 746496 * k + 600695 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 600695) = 1119744 * k + 901043 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 901043) = 1679616 * k + 1351565 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1351565) = 2519424 * k + 2027348 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 2027348) = 1259712 * k + 1013674 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1013674) = 629856 * k + 506837 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 506837) = 944784 * k + 760256 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 760256) = 472392 * k + 380128 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 380128) = 236196 * k + 190064 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 190064) = 118098 * k + 95032 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 95032) = 59049 * k + 47516 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52763_mod_65536 {n : ℕ} (hn : n % 65536 = 52763) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52763 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52763) = 98304 * k + 79145 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79145) = 147456 * k + 118718 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118718) = 73728 * k + 59359 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 59359) = 110592 * k + 89039 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 89039) = 165888 * k + 133559 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 133559) = 248832 * k + 200339 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 200339) = 373248 * k + 300509 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 300509) = 559872 * k + 450764 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 450764) = 279936 * k + 225382 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 225382) = 139968 * k + 112691 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 112691) = 209952 * k + 169037 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 169037) = 314928 * k + 253556 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 253556) = 157464 * k + 126778 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 126778) = 78732 * k + 63389 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63389) = 118098 * k + 95084 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 95084) = 59049 * k + 47542 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52763) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52763)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52847_mod_65536 {n : ℕ} (hn : n % 65536 = 52847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52847) = 98304 * k + 79271 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79271) = 147456 * k + 118907 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 118907) = 221184 * k + 178361 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 178361) = 331776 * k + 267542 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 267542) = 165888 * k + 133771 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 133771) = 248832 * k + 200657 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 200657) = 373248 * k + 300986 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 300986) = 186624 * k + 150493 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 150493) = 279936 * k + 225740 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 225740) = 139968 * k + 112870 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 112870) = 69984 * k + 56435 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 56435) = 104976 * k + 84653 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84653) = 157464 * k + 126980 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 126980) = 78732 * k + 63490 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63490) = 39366 * k + 31745 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31745) = 59049 * k + 47618 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_52967_mod_65536 {n : ℕ} (hn : n % 65536 = 52967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 52967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 52967) = 98304 * k + 79451 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79451) = 147456 * k + 119177 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119177) = 221184 * k + 178766 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 178766) = 110592 * k + 89383 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 89383) = 165888 * k + 134075 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 134075) = 248832 * k + 201113 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 201113) = 373248 * k + 301670 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 301670) = 186624 * k + 150835 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 150835) = 279936 * k + 226253 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 226253) = 419904 * k + 339380 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 339380) = 209952 * k + 169690 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 169690) = 104976 * k + 84845 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84845) = 157464 * k + 127268 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 127268) = 78732 * k + 63634 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63634) = 39366 * k + 31817 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31817) = 59049 * k + 47726 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 52967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 52967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53055_mod_65536 {n : ℕ} (hn : n % 65536 = 53055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53055) = 98304 * k + 79583 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79583) = 147456 * k + 119375 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119375) = 221184 * k + 179063 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 179063) = 331776 * k + 268595 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 268595) = 497664 * k + 402893 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 402893) = 746496 * k + 604340 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 604340) = 373248 * k + 302170 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 302170) = 186624 * k + 151085 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 151085) = 279936 * k + 226628 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 226628) = 139968 * k + 113314 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 113314) = 69984 * k + 56657 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 56657) = 104976 * k + 84986 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 84986) = 52488 * k + 42493 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 42493) = 78732 * k + 63740 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63740) = 39366 * k + 31870 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 31870) = 19683 * k + 15935 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53159_mod_65536 {n : ℕ} (hn : n % 65536 = 53159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53159) = 98304 * k + 79739 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79739) = 147456 * k + 119609 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119609) = 221184 * k + 179414 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 179414) = 110592 * k + 89707 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 89707) = 165888 * k + 134561 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 134561) = 248832 * k + 201842 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 201842) = 124416 * k + 100921 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 100921) = 186624 * k + 151382 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 151382) = 93312 * k + 75691 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 75691) = 139968 * k + 113537 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 113537) = 209952 * k + 170306 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170306) = 104976 * k + 85153 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 85153) = 157464 * k + 127730 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 127730) = 78732 * k + 63865 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63865) = 118098 * k + 95798 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 95798) = 59049 * k + 47899 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53183_mod_65536 {n : ℕ} (hn : n % 65536 = 53183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53183) = 98304 * k + 79775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79775) = 147456 * k + 119663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119663) = 221184 * k + 179495 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 179495) = 331776 * k + 269243 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 269243) = 497664 * k + 403865 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 403865) = 746496 * k + 605798 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 605798) = 373248 * k + 302899 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 302899) = 559872 * k + 454349 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 454349) = 839808 * k + 681524 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 681524) = 419904 * k + 340762 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 340762) = 209952 * k + 170381 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170381) = 314928 * k + 255572 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 255572) = 157464 * k + 127786 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 127786) = 78732 * k + 63893 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 63893) = 118098 * k + 95840 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 95840) = 59049 * k + 47920 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53275_mod_65536 {n : ℕ} (hn : n % 65536 = 53275) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53275 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53275) = 98304 * k + 79913 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79913) = 147456 * k + 119870 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119870) = 73728 * k + 59935 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 59935) = 110592 * k + 89903 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 89903) = 165888 * k + 134855 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 134855) = 248832 * k + 202283 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 202283) = 373248 * k + 303425 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 303425) = 559872 * k + 455138 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 455138) = 279936 * k + 227569 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 227569) = 419904 * k + 341354 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 341354) = 209952 * k + 170677 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170677) = 314928 * k + 256016 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 256016) = 157464 * k + 128008 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 128008) = 78732 * k + 64004 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64004) = 39366 * k + 32002 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32002) = 19683 * k + 16001 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53275) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53275)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53295_mod_65536 {n : ℕ} (hn : n % 65536 = 53295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53295) = 98304 * k + 79943 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79943) = 147456 * k + 119915 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119915) = 221184 * k + 179873 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 179873) = 331776 * k + 269810 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 269810) = 165888 * k + 134905 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 134905) = 248832 * k + 202358 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 202358) = 124416 * k + 101179 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 101179) = 186624 * k + 151769 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 151769) = 279936 * k + 227654 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 227654) = 139968 * k + 113827 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 113827) = 209952 * k + 170741 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170741) = 314928 * k + 256112 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 256112) = 157464 * k + 128056 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 128056) = 78732 * k + 64028 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64028) = 39366 * k + 32014 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32014) = 19683 * k + 16007 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53319_mod_65536 {n : ℕ} (hn : n % 65536 = 53319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53319) = 98304 * k + 79979 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 79979) = 147456 * k + 119969 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 119969) = 221184 * k + 179954 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 179954) = 110592 * k + 89977 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 89977) = 165888 * k + 134966 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 134966) = 82944 * k + 67483 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 67483) = 124416 * k + 101225 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 101225) = 186624 * k + 151838 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 151838) = 93312 * k + 75919 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 75919) = 139968 * k + 113879 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 113879) = 209952 * k + 170819 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170819) = 314928 * k + 256229 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 256229) = 472392 * k + 384344 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 384344) = 236196 * k + 192172 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 192172) = 118098 * k + 96086 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 96086) = 59049 * k + 48043 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53339_mod_65536 {n : ℕ} (hn : n % 65536 = 53339) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53339 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53339) = 98304 * k + 80009 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80009) = 147456 * k + 120014 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120014) = 73728 * k + 60007 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 60007) = 110592 * k + 90011 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 90011) = 165888 * k + 135017 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 135017) = 248832 * k + 202526 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 202526) = 124416 * k + 101263 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 101263) = 186624 * k + 151895 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 151895) = 279936 * k + 227843 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 227843) = 419904 * k + 341765 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 341765) = 629856 * k + 512648 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 512648) = 314928 * k + 256324 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 256324) = 157464 * k + 128162 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 128162) = 78732 * k + 64081 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64081) = 118098 * k + 96122 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 96122) = 59049 * k + 48061 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53339) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53339)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53375_mod_65536 {n : ℕ} (hn : n % 65536 = 53375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53375) = 98304 * k + 80063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80063) = 147456 * k + 120095 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120095) = 221184 * k + 180143 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 180143) = 331776 * k + 270215 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 270215) = 497664 * k + 405323 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 405323) = 746496 * k + 607985 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 607985) = 1119744 * k + 911978 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 911978) = 559872 * k + 455989 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 455989) = 839808 * k + 683984 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 683984) = 419904 * k + 341992 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 341992) = 209952 * k + 170996 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 170996) = 104976 * k + 85498 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 85498) = 52488 * k + 42749 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 42749) = 78732 * k + 64124 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64124) = 39366 * k + 32062 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32062) = 19683 * k + 16031 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53439_mod_65536 {n : ℕ} (hn : n % 65536 = 53439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53439) = 98304 * k + 80159 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80159) = 147456 * k + 120239 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120239) = 221184 * k + 180359 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 180359) = 331776 * k + 270539 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 270539) = 497664 * k + 405809 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 405809) = 746496 * k + 608714 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 608714) = 373248 * k + 304357 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 304357) = 559872 * k + 456536 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 456536) = 279936 * k + 228268 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 228268) = 139968 * k + 114134 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 114134) = 69984 * k + 57067 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 57067) = 104976 * k + 85601 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 85601) = 157464 * k + 128402 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 128402) = 78732 * k + 64201 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64201) = 118098 * k + 96302 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 96302) = 59049 * k + 48151 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53551_mod_65536 {n : ℕ} (hn : n % 65536 = 53551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53551) = 98304 * k + 80327 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80327) = 147456 * k + 120491 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120491) = 221184 * k + 180737 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 180737) = 331776 * k + 271106 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 271106) = 165888 * k + 135553 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 135553) = 248832 * k + 203330 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 203330) = 124416 * k + 101665 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 101665) = 186624 * k + 152498 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 152498) = 93312 * k + 76249 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 76249) = 139968 * k + 114374 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 114374) = 69984 * k + 57187 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 57187) = 104976 * k + 85781 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 85781) = 157464 * k + 128672 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 128672) = 78732 * k + 64336 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64336) = 39366 * k + 32168 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32168) = 19683 * k + 16084 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53659_mod_65536 {n : ℕ} (hn : n % 65536 = 53659) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53659 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53659) = 98304 * k + 80489 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80489) = 147456 * k + 120734 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120734) = 73728 * k + 60367 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 60367) = 110592 * k + 90551 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 90551) = 165888 * k + 135827 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 135827) = 248832 * k + 203741 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 203741) = 373248 * k + 305612 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 305612) = 186624 * k + 152806 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 152806) = 93312 * k + 76403 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 76403) = 139968 * k + 114605 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 114605) = 209952 * k + 171908 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 171908) = 104976 * k + 85954 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 85954) = 52488 * k + 42977 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 42977) = 78732 * k + 64466 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64466) = 39366 * k + 32233 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32233) = 59049 * k + 48350 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53659) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53659)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53695_mod_65536 {n : ℕ} (hn : n % 65536 = 53695) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53695 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53695) = 98304 * k + 80543 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80543) = 147456 * k + 120815 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 120815) = 221184 * k + 181223 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 181223) = 331776 * k + 271835 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 271835) = 497664 * k + 407753 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 407753) = 746496 * k + 611630 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 611630) = 373248 * k + 305815 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 305815) = 559872 * k + 458723 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 458723) = 839808 * k + 688085 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 688085) = 1259712 * k + 1032128 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1032128) = 629856 * k + 516064 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 516064) = 314928 * k + 258032 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 258032) = 157464 * k + 129016 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 129016) = 78732 * k + 64508 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64508) = 39366 * k + 32254 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32254) = 19683 * k + 16127 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53695) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53695)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53791_mod_65536 {n : ℕ} (hn : n % 65536 = 53791) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53791 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53791) = 98304 * k + 80687 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80687) = 147456 * k + 121031 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121031) = 221184 * k + 181547 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 181547) = 331776 * k + 272321 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 272321) = 497664 * k + 408482 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 408482) = 248832 * k + 204241 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 204241) = 373248 * k + 306362 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 306362) = 186624 * k + 153181 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 153181) = 279936 * k + 229772 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 229772) = 139968 * k + 114886 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 114886) = 69984 * k + 57443 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 57443) = 104976 * k + 86165 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 86165) = 157464 * k + 129248 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 129248) = 78732 * k + 64624 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64624) = 39366 * k + 32312 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32312) = 19683 * k + 16156 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53791) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53791)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53871_mod_65536 {n : ℕ} (hn : n % 65536 = 53871) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53871 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53871) = 98304 * k + 80807 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80807) = 147456 * k + 121211 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121211) = 221184 * k + 181817 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 181817) = 331776 * k + 272726 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 272726) = 165888 * k + 136363 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 136363) = 248832 * k + 204545 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 204545) = 373248 * k + 306818 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 306818) = 186624 * k + 153409 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 153409) = 279936 * k + 230114 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 230114) = 139968 * k + 115057 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 115057) = 209952 * k + 172586 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 172586) = 104976 * k + 86293 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 86293) = 157464 * k + 129440 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 129440) = 78732 * k + 64720 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64720) = 39366 * k + 32360 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32360) = 19683 * k + 16180 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53871) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53871)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53887_mod_65536 {n : ℕ} (hn : n % 65536 = 53887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53887) = 98304 * k + 80831 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80831) = 147456 * k + 121247 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121247) = 221184 * k + 181871 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 181871) = 331776 * k + 272807 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 272807) = 497664 * k + 409211 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 409211) = 746496 * k + 613817 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 613817) = 1119744 * k + 920726 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 920726) = 559872 * k + 460363 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 460363) = 839808 * k + 690545 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 690545) = 1259712 * k + 1035818 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1035818) = 629856 * k + 517909 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 517909) = 944784 * k + 776864 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 776864) = 472392 * k + 388432 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 388432) = 236196 * k + 194216 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 194216) = 118098 * k + 97108 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97108) = 59049 * k + 48554 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53919_mod_65536 {n : ℕ} (hn : n % 65536 = 53919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53919) = 98304 * k + 80879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80879) = 147456 * k + 121319 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121319) = 221184 * k + 181979 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 181979) = 331776 * k + 272969 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 272969) = 497664 * k + 409454 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 409454) = 248832 * k + 204727 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 204727) = 373248 * k + 307091 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 307091) = 559872 * k + 460637 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 460637) = 839808 * k + 690956 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 690956) = 419904 * k + 345478 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 345478) = 209952 * k + 172739 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 172739) = 314928 * k + 259109 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 259109) = 472392 * k + 388664 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 388664) = 236196 * k + 194332 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 194332) = 118098 * k + 97166 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97166) = 59049 * k + 48583 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_53991_mod_65536 {n : ℕ} (hn : n % 65536 = 53991) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 53991 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 53991) = 98304 * k + 80987 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 80987) = 147456 * k + 121481 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121481) = 221184 * k + 182222 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 182222) = 110592 * k + 91111 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91111) = 165888 * k + 136667 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 136667) = 248832 * k + 205001 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 205001) = 373248 * k + 307502 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 307502) = 186624 * k + 153751 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 153751) = 279936 * k + 230627 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 230627) = 419904 * k + 345941 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 345941) = 629856 * k + 518912 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 518912) = 314928 * k + 259456 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 259456) = 157464 * k + 129728 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 129728) = 78732 * k + 64864 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64864) = 39366 * k + 32432 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32432) = 19683 * k + 16216 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 53991) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 53991)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54011_mod_65536 {n : ℕ} (hn : n % 65536 = 54011) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54011 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54011) = 98304 * k + 81017 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81017) = 147456 * k + 121526 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121526) = 73728 * k + 60763 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 60763) = 110592 * k + 91145 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91145) = 165888 * k + 136718 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 136718) = 82944 * k + 68359 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 68359) = 124416 * k + 102539 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 102539) = 186624 * k + 153809 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 153809) = 279936 * k + 230714 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 230714) = 139968 * k + 115357 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 115357) = 209952 * k + 173036 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 173036) = 104976 * k + 86518 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 86518) = 52488 * k + 43259 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 43259) = 78732 * k + 64889 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64889) = 118098 * k + 97334 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97334) = 59049 * k + 48667 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54011) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54011)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54043_mod_65536 {n : ℕ} (hn : n % 65536 = 54043) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54043 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54043) = 98304 * k + 81065 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81065) = 147456 * k + 121598 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121598) = 73728 * k + 60799 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 60799) = 110592 * k + 91199 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91199) = 165888 * k + 136799 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 136799) = 248832 * k + 205199 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 205199) = 373248 * k + 307799 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 307799) = 559872 * k + 461699 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 461699) = 839808 * k + 692549 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 692549) = 1259712 * k + 1038824 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1038824) = 629856 * k + 519412 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 519412) = 314928 * k + 259706 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 259706) = 157464 * k + 129853 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 129853) = 236196 * k + 194780 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 194780) = 118098 * k + 97390 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97390) = 59049 * k + 48695 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54043) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54043)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54079_mod_65536 {n : ℕ} (hn : n % 65536 = 54079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54079) = 98304 * k + 81119 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81119) = 147456 * k + 121679 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 121679) = 221184 * k + 182519 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 182519) = 331776 * k + 273779 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 273779) = 497664 * k + 410669 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 410669) = 746496 * k + 616004 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 616004) = 373248 * k + 308002 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 308002) = 186624 * k + 154001 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 154001) = 279936 * k + 231002 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 231002) = 139968 * k + 115501 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 115501) = 209952 * k + 173252 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 173252) = 104976 * k + 86626 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 86626) = 52488 * k + 43313 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 43313) = 78732 * k + 64970 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 64970) = 39366 * k + 32485 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32485) = 59049 * k + 48728 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54239_mod_65536 {n : ℕ} (hn : n % 65536 = 54239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54239) = 98304 * k + 81359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81359) = 147456 * k + 122039 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122039) = 221184 * k + 183059 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183059) = 331776 * k + 274589 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 274589) = 497664 * k + 411884 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 411884) = 248832 * k + 205942 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 205942) = 124416 * k + 102971 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 102971) = 186624 * k + 154457 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 154457) = 279936 * k + 231686 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 231686) = 139968 * k + 115843 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 115843) = 209952 * k + 173765 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 173765) = 314928 * k + 260648 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 260648) = 157464 * k + 130324 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 130324) = 78732 * k + 65162 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65162) = 39366 * k + 32581 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32581) = 59049 * k + 48872 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54303_mod_65536 {n : ℕ} (hn : n % 65536 = 54303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54303) = 98304 * k + 81455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81455) = 147456 * k + 122183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122183) = 221184 * k + 183275 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183275) = 331776 * k + 274913 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 274913) = 497664 * k + 412370 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 412370) = 248832 * k + 206185 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 206185) = 373248 * k + 309278 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 309278) = 186624 * k + 154639 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 154639) = 279936 * k + 231959 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 231959) = 419904 * k + 347939 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 347939) = 629856 * k + 521909 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 521909) = 944784 * k + 782864 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 782864) = 472392 * k + 391432 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 391432) = 236196 * k + 195716 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 195716) = 118098 * k + 97858 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97858) = 59049 * k + 48929 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54319_mod_65536 {n : ℕ} (hn : n % 65536 = 54319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54319) = 98304 * k + 81479 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81479) = 147456 * k + 122219 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122219) = 221184 * k + 183329 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183329) = 331776 * k + 274994 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 274994) = 165888 * k + 137497 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 137497) = 248832 * k + 206246 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 206246) = 124416 * k + 103123 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103123) = 186624 * k + 154685 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 154685) = 279936 * k + 232028 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 232028) = 139968 * k + 116014 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 116014) = 69984 * k + 58007 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 58007) = 104976 * k + 87011 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87011) = 157464 * k + 130517 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 130517) = 236196 * k + 195776 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 195776) = 118098 * k + 97888 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97888) = 59049 * k + 48944 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54343_mod_65536 {n : ℕ} (hn : n % 65536 = 54343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54343) = 98304 * k + 81515 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81515) = 147456 * k + 122273 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122273) = 221184 * k + 183410 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183410) = 110592 * k + 91705 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91705) = 165888 * k + 137558 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 137558) = 82944 * k + 68779 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 68779) = 124416 * k + 103169 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103169) = 186624 * k + 154754 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 154754) = 93312 * k + 77377 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 77377) = 139968 * k + 116066 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 116066) = 69984 * k + 58033 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 58033) = 104976 * k + 87050 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87050) = 52488 * k + 43525 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 43525) = 78732 * k + 65288 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65288) = 39366 * k + 32644 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32644) = 19683 * k + 16322 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54375_mod_65536 {n : ℕ} (hn : n % 65536 = 54375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54375) = 98304 * k + 81563 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81563) = 147456 * k + 122345 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122345) = 221184 * k + 183518 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183518) = 110592 * k + 91759 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91759) = 165888 * k + 137639 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 137639) = 248832 * k + 206459 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 206459) = 373248 * k + 309689 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 309689) = 559872 * k + 464534 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 464534) = 279936 * k + 232267 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 232267) = 419904 * k + 348401 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 348401) = 629856 * k + 522602 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 522602) = 314928 * k + 261301 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 261301) = 472392 * k + 391952 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 391952) = 236196 * k + 195976 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 195976) = 118098 * k + 97988 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 97988) = 59049 * k + 48994 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54439_mod_65536 {n : ℕ} (hn : n % 65536 = 54439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54439) = 98304 * k + 81659 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81659) = 147456 * k + 122489 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122489) = 221184 * k + 183734 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183734) = 110592 * k + 91867 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 91867) = 165888 * k + 137801 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 137801) = 248832 * k + 206702 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 206702) = 124416 * k + 103351 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103351) = 186624 * k + 155027 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155027) = 279936 * k + 232541 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 232541) = 419904 * k + 348812 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 348812) = 209952 * k + 174406 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 174406) = 104976 * k + 87203 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87203) = 157464 * k + 130805 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 130805) = 236196 * k + 196208 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 196208) = 118098 * k + 98104 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 98104) = 59049 * k + 49052 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54495_mod_65536 {n : ℕ} (hn : n % 65536 = 54495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54495) = 98304 * k + 81743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81743) = 147456 * k + 122615 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122615) = 221184 * k + 183923 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 183923) = 331776 * k + 275885 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 275885) = 497664 * k + 413828 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 413828) = 248832 * k + 206914 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 206914) = 124416 * k + 103457 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103457) = 186624 * k + 155186 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155186) = 93312 * k + 77593 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 77593) = 139968 * k + 116390 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 116390) = 69984 * k + 58195 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 58195) = 104976 * k + 87293 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87293) = 157464 * k + 130940 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 130940) = 78732 * k + 65470 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65470) = 39366 * k + 32735 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32735) = 59049 * k + 49103 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54523_mod_65536 {n : ℕ} (hn : n % 65536 = 54523) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54523 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54523) = 98304 * k + 81785 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81785) = 147456 * k + 122678 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122678) = 73728 * k + 61339 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 61339) = 110592 * k + 92009 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 92009) = 165888 * k + 138014 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 138014) = 82944 * k + 69007 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 69007) = 124416 * k + 103511 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103511) = 186624 * k + 155267 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155267) = 279936 * k + 232901 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 232901) = 419904 * k + 349352 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 349352) = 209952 * k + 174676 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 174676) = 104976 * k + 87338 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87338) = 52488 * k + 43669 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 43669) = 78732 * k + 65504 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65504) = 39366 * k + 32752 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32752) = 19683 * k + 16376 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54523) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54523)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54575_mod_65536 {n : ℕ} (hn : n % 65536 = 54575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54575) = 98304 * k + 81863 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81863) = 147456 * k + 122795 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122795) = 221184 * k + 184193 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 184193) = 331776 * k + 276290 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 276290) = 165888 * k + 138145 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 138145) = 248832 * k + 207218 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 207218) = 124416 * k + 103609 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103609) = 186624 * k + 155414 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155414) = 93312 * k + 77707 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 77707) = 139968 * k + 116561 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 116561) = 209952 * k + 174842 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 174842) = 104976 * k + 87421 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87421) = 157464 * k + 131132 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 131132) = 78732 * k + 65566 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65566) = 39366 * k + 32783 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32783) = 59049 * k + 49175 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54591_mod_65536 {n : ℕ} (hn : n % 65536 = 54591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54591) = 98304 * k + 81887 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 81887) = 147456 * k + 122831 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 122831) = 221184 * k + 184247 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 184247) = 331776 * k + 276371 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 276371) = 497664 * k + 414557 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 414557) = 746496 * k + 621836 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 621836) = 373248 * k + 310918 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 310918) = 186624 * k + 155459 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155459) = 279936 * k + 233189 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 233189) = 419904 * k + 349784 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 349784) = 209952 * k + 174892 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 174892) = 104976 * k + 87446 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87446) = 52488 * k + 43723 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 43723) = 78732 * k + 65585 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65585) = 118098 * k + 98378 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 98378) = 59049 * k + 49189 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54751_mod_65536 {n : ℕ} (hn : n % 65536 = 54751) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54751 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54751) = 98304 * k + 82127 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82127) = 147456 * k + 123191 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 123191) = 221184 * k + 184787 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 184787) = 331776 * k + 277181 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 277181) = 497664 * k + 415772 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 415772) = 248832 * k + 207886 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 207886) = 124416 * k + 103943 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 103943) = 186624 * k + 155915 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 155915) = 279936 * k + 233873 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 233873) = 419904 * k + 350810 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 350810) = 209952 * k + 175405 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 175405) = 314928 * k + 263108 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 263108) = 157464 * k + 131554 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 131554) = 78732 * k + 65777 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65777) = 118098 * k + 98666 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 98666) = 59049 * k + 49333 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54751) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54751)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54815_mod_65536 {n : ℕ} (hn : n % 65536 = 54815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54815) = 98304 * k + 82223 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82223) = 147456 * k + 123335 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 123335) = 221184 * k + 185003 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 185003) = 331776 * k + 277505 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 277505) = 497664 * k + 416258 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 416258) = 248832 * k + 208129 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 208129) = 373248 * k + 312194 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 312194) = 186624 * k + 156097 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 156097) = 279936 * k + 234146 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 234146) = 139968 * k + 117073 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 117073) = 209952 * k + 175610 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 175610) = 104976 * k + 87805 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 87805) = 157464 * k + 131708 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 131708) = 78732 * k + 65854 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 65854) = 39366 * k + 32927 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 32927) = 59049 * k + 49391 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_54975_mod_65536 {n : ℕ} (hn : n % 65536 = 54975) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 54975 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 54975) = 98304 * k + 82463 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82463) = 147456 * k + 123695 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 123695) = 221184 * k + 185543 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 185543) = 331776 * k + 278315 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 278315) = 497664 * k + 417473 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 417473) = 746496 * k + 626210 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 626210) = 373248 * k + 313105 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 313105) = 559872 * k + 469658 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 469658) = 279936 * k + 234829 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 234829) = 419904 * k + 352244 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 352244) = 209952 * k + 176122 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 176122) = 104976 * k + 88061 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88061) = 157464 * k + 132092 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 132092) = 78732 * k + 66046 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66046) = 39366 * k + 33023 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33023) = 59049 * k + 49535 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 54975) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 54975)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55023_mod_65536 {n : ℕ} (hn : n % 65536 = 55023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55023) = 98304 * k + 82535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82535) = 147456 * k + 123803 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 123803) = 221184 * k + 185705 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 185705) = 331776 * k + 278558 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 278558) = 165888 * k + 139279 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 139279) = 248832 * k + 208919 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 208919) = 373248 * k + 313379 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 313379) = 559872 * k + 470069 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 470069) = 839808 * k + 705104 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 705104) = 419904 * k + 352552 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 352552) = 209952 * k + 176276 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 176276) = 104976 * k + 88138 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88138) = 52488 * k + 44069 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44069) = 78732 * k + 66104 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66104) = 39366 * k + 33052 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33052) = 19683 * k + 16526 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55207_mod_65536 {n : ℕ} (hn : n % 65536 = 55207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55207) = 98304 * k + 82811 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82811) = 147456 * k + 124217 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124217) = 221184 * k + 186326 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 186326) = 110592 * k + 93163 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 93163) = 165888 * k + 139745 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 139745) = 248832 * k + 209618 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 209618) = 124416 * k + 104809 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 104809) = 186624 * k + 157214 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 157214) = 93312 * k + 78607 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 78607) = 139968 * k + 117911 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 117911) = 209952 * k + 176867 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 176867) = 314928 * k + 265301 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 265301) = 472392 * k + 397952 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 397952) = 236196 * k + 198976 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 198976) = 118098 * k + 99488 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 99488) = 59049 * k + 49744 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55291_mod_65536 {n : ℕ} (hn : n % 65536 = 55291) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55291 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55291) = 98304 * k + 82937 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82937) = 147456 * k + 124406 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124406) = 73728 * k + 62203 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 62203) = 110592 * k + 93305 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 93305) = 165888 * k + 139958 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 139958) = 82944 * k + 69979 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 69979) = 124416 * k + 104969 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 104969) = 186624 * k + 157454 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 157454) = 93312 * k + 78727 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 78727) = 139968 * k + 118091 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118091) = 209952 * k + 177137 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 177137) = 314928 * k + 265706 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 265706) = 157464 * k + 132853 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 132853) = 236196 * k + 199280 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 199280) = 118098 * k + 99640 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 99640) = 59049 * k + 49820 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55291) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55291)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55327_mod_65536 {n : ℕ} (hn : n % 65536 = 55327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55327) = 98304 * k + 82991 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 82991) = 147456 * k + 124487 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124487) = 221184 * k + 186731 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 186731) = 331776 * k + 280097 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 280097) = 497664 * k + 420146 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 420146) = 248832 * k + 210073 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 210073) = 373248 * k + 315110 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 315110) = 186624 * k + 157555 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 157555) = 279936 * k + 236333 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 236333) = 419904 * k + 354500 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 354500) = 209952 * k + 177250 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 177250) = 104976 * k + 88625 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88625) = 157464 * k + 132938 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 132938) = 78732 * k + 66469 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66469) = 118098 * k + 99704 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 99704) = 59049 * k + 49852 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55367_mod_65536 {n : ℕ} (hn : n % 65536 = 55367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55367) = 98304 * k + 83051 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83051) = 147456 * k + 124577 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124577) = 221184 * k + 186866 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 186866) = 110592 * k + 93433 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 93433) = 165888 * k + 140150 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 140150) = 82944 * k + 70075 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 70075) = 124416 * k + 105113 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 105113) = 186624 * k + 157670 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 157670) = 93312 * k + 78835 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 78835) = 139968 * k + 118253 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118253) = 209952 * k + 177380 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 177380) = 104976 * k + 88690 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88690) = 52488 * k + 44345 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44345) = 78732 * k + 66518 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66518) = 39366 * k + 33259 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33259) = 59049 * k + 49889 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55407_mod_65536 {n : ℕ} (hn : n % 65536 = 55407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55407) = 98304 * k + 83111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83111) = 147456 * k + 124667 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124667) = 221184 * k + 187001 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187001) = 331776 * k + 280502 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 280502) = 165888 * k + 140251 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 140251) = 248832 * k + 210377 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 210377) = 373248 * k + 315566 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 315566) = 186624 * k + 157783 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 157783) = 279936 * k + 236675 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 236675) = 419904 * k + 355013 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 355013) = 629856 * k + 532520 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 532520) = 314928 * k + 266260 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 266260) = 157464 * k + 133130 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133130) = 78732 * k + 66565 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66565) = 118098 * k + 99848 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 99848) = 59049 * k + 49924 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55423_mod_65536 {n : ℕ} (hn : n % 65536 = 55423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55423) = 98304 * k + 83135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83135) = 147456 * k + 124703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124703) = 221184 * k + 187055 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187055) = 331776 * k + 280583 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 280583) = 497664 * k + 420875 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 420875) = 746496 * k + 631313 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 631313) = 1119744 * k + 946970 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 946970) = 559872 * k + 473485 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 473485) = 839808 * k + 710228 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 710228) = 419904 * k + 355114 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 355114) = 209952 * k + 177557 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 177557) = 314928 * k + 266336 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 266336) = 157464 * k + 133168 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133168) = 78732 * k + 66584 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66584) = 39366 * k + 33292 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33292) = 19683 * k + 16646 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55519_mod_65536 {n : ℕ} (hn : n % 65536 = 55519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55519) = 98304 * k + 83279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83279) = 147456 * k + 124919 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124919) = 221184 * k + 187379 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187379) = 331776 * k + 281069 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 281069) = 497664 * k + 421604 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 421604) = 248832 * k + 210802 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 210802) = 124416 * k + 105401 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 105401) = 186624 * k + 158102 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 158102) = 93312 * k + 79051 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 79051) = 139968 * k + 118577 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118577) = 209952 * k + 177866 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 177866) = 104976 * k + 88933 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88933) = 157464 * k + 133400 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133400) = 78732 * k + 66700 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66700) = 39366 * k + 33350 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33350) = 19683 * k + 16675 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55527_mod_65536 {n : ℕ} (hn : n % 65536 = 55527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55527) = 98304 * k + 83291 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83291) = 147456 * k + 124937 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124937) = 221184 * k + 187406 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187406) = 110592 * k + 93703 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 93703) = 165888 * k + 140555 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 140555) = 248832 * k + 210833 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 210833) = 373248 * k + 316250 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 316250) = 186624 * k + 158125 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 158125) = 279936 * k + 237188 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 237188) = 139968 * k + 118594 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118594) = 69984 * k + 59297 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 59297) = 104976 * k + 88946 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 88946) = 52488 * k + 44473 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44473) = 78732 * k + 66710 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66710) = 39366 * k + 33355 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33355) = 59049 * k + 50033 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55535_mod_65536 {n : ℕ} (hn : n % 65536 = 55535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55535) = 98304 * k + 83303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83303) = 147456 * k + 124955 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 124955) = 221184 * k + 187433 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187433) = 331776 * k + 281150 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 281150) = 165888 * k + 140575 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 140575) = 248832 * k + 210863 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 210863) = 373248 * k + 316295 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 316295) = 559872 * k + 474443 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 474443) = 839808 * k + 711665 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 711665) = 1259712 * k + 1067498 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1067498) = 629856 * k + 533749 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 533749) = 944784 * k + 800624 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 800624) = 472392 * k + 400312 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 400312) = 236196 * k + 200156 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 200156) = 118098 * k + 100078 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 100078) = 59049 * k + 50039 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55579_mod_65536 {n : ℕ} (hn : n % 65536 = 55579) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55579 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55579) = 98304 * k + 83369 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83369) = 147456 * k + 125054 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125054) = 73728 * k + 62527 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 62527) = 110592 * k + 93791 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 93791) = 165888 * k + 140687 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 140687) = 248832 * k + 211031 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 211031) = 373248 * k + 316547 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 316547) = 559872 * k + 474821 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 474821) = 839808 * k + 712232 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 712232) = 419904 * k + 356116 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 356116) = 209952 * k + 178058 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 178058) = 104976 * k + 89029 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 89029) = 157464 * k + 133544 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133544) = 78732 * k + 66772 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66772) = 39366 * k + 33386 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33386) = 19683 * k + 16693 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55579) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55579)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55679_mod_65536 {n : ℕ} (hn : n % 65536 = 55679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55679) = 98304 * k + 83519 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83519) = 147456 * k + 125279 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125279) = 221184 * k + 187919 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 187919) = 331776 * k + 281879 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 281879) = 497664 * k + 422819 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 422819) = 746496 * k + 634229 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 634229) = 1119744 * k + 951344 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 951344) = 559872 * k + 475672 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 475672) = 279936 * k + 237836 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 237836) = 139968 * k + 118918 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118918) = 69984 * k + 59459 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 59459) = 104976 * k + 89189 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 89189) = 157464 * k + 133784 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133784) = 78732 * k + 66892 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66892) = 39366 * k + 33446 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33446) = 19683 * k + 16723 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55707_mod_65536 {n : ℕ} (hn : n % 65536 = 55707) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55707 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55707) = 98304 * k + 83561 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83561) = 147456 * k + 125342 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125342) = 73728 * k + 62671 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 62671) = 110592 * k + 94007 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94007) = 165888 * k + 141011 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 141011) = 248832 * k + 211517 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 211517) = 373248 * k + 317276 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 317276) = 186624 * k + 158638 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 158638) = 93312 * k + 79319 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 79319) = 139968 * k + 118979 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 118979) = 209952 * k + 178469 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 178469) = 314928 * k + 267704 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 267704) = 157464 * k + 133852 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 133852) = 78732 * k + 66926 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66926) = 39366 * k + 33463 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33463) = 59049 * k + 50195 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55707) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55707)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55759_mod_65536 {n : ℕ} (hn : n % 65536 = 55759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55759) = 98304 * k + 83639 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83639) = 147456 * k + 125459 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125459) = 221184 * k + 188189 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 188189) = 331776 * k + 282284 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 282284) = 165888 * k + 141142 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 141142) = 82944 * k + 70571 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 70571) = 124416 * k + 105857 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 105857) = 186624 * k + 158786 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 158786) = 93312 * k + 79393 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 79393) = 139968 * k + 119090 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 119090) = 69984 * k + 59545 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 59545) = 104976 * k + 89318 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 89318) = 52488 * k + 44659 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44659) = 78732 * k + 66989 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 66989) = 118098 * k + 100484 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 100484) = 59049 * k + 50242 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55899_mod_65536 {n : ℕ} (hn : n % 65536 = 55899) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55899 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55899) = 98304 * k + 83849 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83849) = 147456 * k + 125774 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125774) = 73728 * k + 62887 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 62887) = 110592 * k + 94331 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94331) = 165888 * k + 141497 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 141497) = 248832 * k + 212246 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 212246) = 124416 * k + 106123 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 106123) = 186624 * k + 159185 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 159185) = 279936 * k + 238778 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 238778) = 139968 * k + 119389 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 119389) = 209952 * k + 179084 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 179084) = 104976 * k + 89542 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 89542) = 52488 * k + 44771 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44771) = 78732 * k + 67157 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67157) = 118098 * k + 100736 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 100736) = 59049 * k + 50368 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55899) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55899)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55963_mod_65536 {n : ℕ} (hn : n % 65536 = 55963) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55963 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55963) = 98304 * k + 83945 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83945) = 147456 * k + 125918 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125918) = 73728 * k + 62959 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 62959) = 110592 * k + 94439 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94439) = 165888 * k + 141659 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 141659) = 248832 * k + 212489 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 212489) = 373248 * k + 318734 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 318734) = 186624 * k + 159367 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 159367) = 279936 * k + 239051 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 239051) = 419904 * k + 358577 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 358577) = 629856 * k + 537866 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 537866) = 314928 * k + 268933 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 268933) = 472392 * k + 403400 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 403400) = 236196 * k + 201700 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 201700) = 118098 * k + 100850 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 100850) = 59049 * k + 50425 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55963) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55963)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55967_mod_65536 {n : ℕ} (hn : n % 65536 = 55967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55967) = 98304 * k + 83951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83951) = 147456 * k + 125927 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125927) = 221184 * k + 188891 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 188891) = 331776 * k + 283337 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 283337) = 497664 * k + 425006 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 425006) = 248832 * k + 212503 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 212503) = 373248 * k + 318755 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 318755) = 559872 * k + 478133 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 478133) = 839808 * k + 717200 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 717200) = 419904 * k + 358600 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 358600) = 209952 * k + 179300 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 179300) = 104976 * k + 89650 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 89650) = 52488 * k + 44825 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 44825) = 78732 * k + 67238 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67238) = 39366 * k + 33619 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33619) = 59049 * k + 50429 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_55999_mod_65536 {n : ℕ} (hn : n % 65536 = 55999) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 55999 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 55999) = 98304 * k + 83999 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 83999) = 147456 * k + 125999 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 125999) = 221184 * k + 188999 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 188999) = 331776 * k + 283499 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 283499) = 497664 * k + 425249 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 425249) = 746496 * k + 637874 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 637874) = 373248 * k + 318937 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 318937) = 559872 * k + 478406 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 478406) = 279936 * k + 239203 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 239203) = 419904 * k + 358805 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 358805) = 629856 * k + 538208 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 538208) = 314928 * k + 269104 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 269104) = 157464 * k + 134552 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 134552) = 78732 * k + 67276 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67276) = 39366 * k + 33638 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33638) = 19683 * k + 16819 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 55999) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 55999)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56059_mod_65536 {n : ℕ} (hn : n % 65536 = 56059) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56059 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56059) = 98304 * k + 84089 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84089) = 147456 * k + 126134 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126134) = 73728 * k + 63067 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63067) = 110592 * k + 94601 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94601) = 165888 * k + 141902 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 141902) = 82944 * k + 70951 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 70951) = 124416 * k + 106427 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 106427) = 186624 * k + 159641 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 159641) = 279936 * k + 239462 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 239462) = 139968 * k + 119731 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 119731) = 209952 * k + 179597 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 179597) = 314928 * k + 269396 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 269396) = 157464 * k + 134698 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 134698) = 78732 * k + 67349 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67349) = 118098 * k + 101024 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 101024) = 59049 * k + 50512 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56059) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56059)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56127_mod_65536 {n : ℕ} (hn : n % 65536 = 56127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56127) = 98304 * k + 84191 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84191) = 147456 * k + 126287 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126287) = 221184 * k + 189431 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 189431) = 331776 * k + 284147 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 284147) = 497664 * k + 426221 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 426221) = 746496 * k + 639332 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 639332) = 373248 * k + 319666 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 319666) = 186624 * k + 159833 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 159833) = 279936 * k + 239750 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 239750) = 139968 * k + 119875 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 119875) = 209952 * k + 179813 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 179813) = 314928 * k + 269720 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 269720) = 157464 * k + 134860 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 134860) = 78732 * k + 67430 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67430) = 39366 * k + 33715 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33715) = 59049 * k + 50573 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56167_mod_65536 {n : ℕ} (hn : n % 65536 = 56167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56167) = 98304 * k + 84251 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84251) = 147456 * k + 126377 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126377) = 221184 * k + 189566 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 189566) = 110592 * k + 94783 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94783) = 165888 * k + 142175 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 142175) = 248832 * k + 213263 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 213263) = 373248 * k + 319895 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 319895) = 559872 * k + 479843 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 479843) = 839808 * k + 719765 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 719765) = 1259712 * k + 1079648 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1079648) = 629856 * k + 539824 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 539824) = 314928 * k + 269912 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 269912) = 157464 * k + 134956 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 134956) = 78732 * k + 67478 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67478) = 39366 * k + 33739 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33739) = 59049 * k + 50609 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56191_mod_65536 {n : ℕ} (hn : n % 65536 = 56191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56191) = 98304 * k + 84287 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84287) = 147456 * k + 126431 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126431) = 221184 * k + 189647 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 189647) = 331776 * k + 284471 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 284471) = 497664 * k + 426707 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 426707) = 746496 * k + 640061 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 640061) = 1119744 * k + 960092 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 960092) = 559872 * k + 480046 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 480046) = 279936 * k + 240023 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 240023) = 419904 * k + 360035 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 360035) = 629856 * k + 540053 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 540053) = 944784 * k + 810080 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 810080) = 472392 * k + 405040 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 405040) = 236196 * k + 202520 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 202520) = 118098 * k + 101260 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 101260) = 59049 * k + 50630 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56231_mod_65536 {n : ℕ} (hn : n % 65536 = 56231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56231) = 98304 * k + 84347 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84347) = 147456 * k + 126521 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126521) = 221184 * k + 189782 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 189782) = 110592 * k + 94891 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 94891) = 165888 * k + 142337 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 142337) = 248832 * k + 213506 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 213506) = 124416 * k + 106753 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 106753) = 186624 * k + 160130 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 160130) = 93312 * k + 80065 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 80065) = 139968 * k + 120098 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 120098) = 69984 * k + 60049 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 60049) = 104976 * k + 90074 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90074) = 52488 * k + 45037 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 45037) = 78732 * k + 67556 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67556) = 39366 * k + 33778 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33778) = 19683 * k + 16889 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56287_mod_65536 {n : ℕ} (hn : n % 65536 = 56287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56287) = 98304 * k + 84431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84431) = 147456 * k + 126647 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126647) = 221184 * k + 189971 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 189971) = 331776 * k + 284957 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 284957) = 497664 * k + 427436 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 427436) = 248832 * k + 213718 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 213718) = 124416 * k + 106859 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 106859) = 186624 * k + 160289 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 160289) = 279936 * k + 240434 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 240434) = 139968 * k + 120217 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 120217) = 209952 * k + 180326 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 180326) = 104976 * k + 90163 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90163) = 157464 * k + 135245 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 135245) = 236196 * k + 202868 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 202868) = 118098 * k + 101434 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 101434) = 59049 * k + 50717 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56315_mod_65536 {n : ℕ} (hn : n % 65536 = 56315) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56315 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56315) = 98304 * k + 84473 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84473) = 147456 * k + 126710 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126710) = 73728 * k + 63355 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63355) = 110592 * k + 95033 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95033) = 165888 * k + 142550 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 142550) = 82944 * k + 71275 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 71275) = 124416 * k + 106913 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 106913) = 186624 * k + 160370 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 160370) = 93312 * k + 80185 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 80185) = 139968 * k + 120278 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 120278) = 69984 * k + 60139 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 60139) = 104976 * k + 90209 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90209) = 157464 * k + 135314 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 135314) = 78732 * k + 67657 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67657) = 118098 * k + 101486 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 101486) = 59049 * k + 50743 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56315) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56315)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56347_mod_65536 {n : ℕ} (hn : n % 65536 = 56347) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56347 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56347) = 98304 * k + 84521 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84521) = 147456 * k + 126782 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126782) = 73728 * k + 63391 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63391) = 110592 * k + 95087 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95087) = 165888 * k + 142631 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 142631) = 248832 * k + 213947 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 213947) = 373248 * k + 320921 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 320921) = 559872 * k + 481382 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 481382) = 279936 * k + 240691 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 240691) = 419904 * k + 361037 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 361037) = 629856 * k + 541556 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 541556) = 314928 * k + 270778 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 270778) = 157464 * k + 135389 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 135389) = 236196 * k + 203084 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 203084) = 118098 * k + 101542 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 101542) = 59049 * k + 50771 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56347) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56347)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56383_mod_65536 {n : ℕ} (hn : n % 65536 = 56383) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56383 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56383) = 98304 * k + 84575 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84575) = 147456 * k + 126863 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126863) = 221184 * k + 190295 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 190295) = 331776 * k + 285443 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 285443) = 497664 * k + 428165 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 428165) = 746496 * k + 642248 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 642248) = 373248 * k + 321124 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 321124) = 186624 * k + 160562 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 160562) = 93312 * k + 80281 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 80281) = 139968 * k + 120422 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 120422) = 69984 * k + 60211 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 60211) = 104976 * k + 90317 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90317) = 157464 * k + 135476 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 135476) = 78732 * k + 67738 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67738) = 39366 * k + 33869 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33869) = 59049 * k + 50804 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56383) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56383)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56411_mod_65536 {n : ℕ} (hn : n % 65536 = 56411) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56411 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56411) = 98304 * k + 84617 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84617) = 147456 * k + 126926 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 126926) = 73728 * k + 63463 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63463) = 110592 * k + 95195 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95195) = 165888 * k + 142793 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 142793) = 248832 * k + 214190 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 214190) = 124416 * k + 107095 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 107095) = 186624 * k + 160643 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 160643) = 279936 * k + 240965 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 240965) = 419904 * k + 361448 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 361448) = 209952 * k + 180724 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 180724) = 104976 * k + 90362 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90362) = 52488 * k + 45181 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 45181) = 78732 * k + 67772 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67772) = 39366 * k + 33886 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33886) = 19683 * k + 16943 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56411) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56411)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56551_mod_65536 {n : ℕ} (hn : n % 65536 = 56551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56551) = 98304 * k + 84827 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84827) = 147456 * k + 127241 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 127241) = 221184 * k + 190862 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 190862) = 110592 * k + 95431 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95431) = 165888 * k + 143147 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 143147) = 248832 * k + 214721 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 214721) = 373248 * k + 322082 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 322082) = 186624 * k + 161041 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 161041) = 279936 * k + 241562 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 241562) = 139968 * k + 120781 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 120781) = 209952 * k + 181172 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 181172) = 104976 * k + 90586 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90586) = 52488 * k + 45293 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 45293) = 78732 * k + 67940 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67940) = 39366 * k + 33970 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33970) = 19683 * k + 16985 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56571_mod_65536 {n : ℕ} (hn : n % 65536 = 56571) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56571 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56571) = 98304 * k + 84857 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84857) = 147456 * k + 127286 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 127286) = 73728 * k + 63643 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63643) = 110592 * k + 95465 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95465) = 165888 * k + 143198 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 143198) = 82944 * k + 71599 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 71599) = 124416 * k + 107399 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 107399) = 186624 * k + 161099 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 161099) = 279936 * k + 241649 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 241649) = 419904 * k + 362474 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 362474) = 209952 * k + 181237 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 181237) = 314928 * k + 271856 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 271856) = 157464 * k + 135928 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 135928) = 78732 * k + 67964 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 67964) = 39366 * k + 33982 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 33982) = 19683 * k + 16991 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56571) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56571)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56603_mod_65536 {n : ℕ} (hn : n % 65536 = 56603) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56603 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56603) = 98304 * k + 84905 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84905) = 147456 * k + 127358 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 127358) = 73728 * k + 63679 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 63679) = 110592 * k + 95519 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 95519) = 165888 * k + 143279 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 143279) = 248832 * k + 214919 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 214919) = 373248 * k + 322379 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 322379) = 559872 * k + 483569 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 483569) = 839808 * k + 725354 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 725354) = 419904 * k + 362677 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 362677) = 629856 * k + 544016 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 544016) = 314928 * k + 272008 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 272008) = 157464 * k + 136004 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 136004) = 78732 * k + 68002 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68002) = 39366 * k + 34001 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34001) = 59049 * k + 51002 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56603) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56603)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56639_mod_65536 {n : ℕ} (hn : n % 65536 = 56639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56639) = 98304 * k + 84959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 84959) = 147456 * k + 127439 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 127439) = 221184 * k + 191159 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 191159) = 331776 * k + 286739 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 286739) = 497664 * k + 430109 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 430109) = 746496 * k + 645164 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 645164) = 373248 * k + 322582 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 322582) = 186624 * k + 161291 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 161291) = 279936 * k + 241937 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 241937) = 419904 * k + 362906 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 362906) = 209952 * k + 181453 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 181453) = 314928 * k + 272180 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 272180) = 157464 * k + 136090 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 136090) = 78732 * k + 68045 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68045) = 118098 * k + 102068 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 102068) = 59049 * k + 51034 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56703_mod_65536 {n : ℕ} (hn : n % 65536 = 56703) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56703 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56703) = 98304 * k + 85055 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85055) = 147456 * k + 127583 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 127583) = 221184 * k + 191375 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 191375) = 331776 * k + 287063 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 287063) = 497664 * k + 430595 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 430595) = 746496 * k + 645893 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 645893) = 1119744 * k + 968840 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 968840) = 559872 * k + 484420 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 484420) = 279936 * k + 242210 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 242210) = 139968 * k + 121105 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 121105) = 209952 * k + 181658 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 181658) = 104976 * k + 90829 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 90829) = 157464 * k + 136244 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 136244) = 78732 * k + 68122 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68122) = 39366 * k + 34061 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34061) = 59049 * k + 51092 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56703) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56703)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_56935_mod_65536 {n : ℕ} (hn : n % 65536 = 56935) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 56935 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 56935) = 98304 * k + 85403 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85403) = 147456 * k + 128105 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128105) = 221184 * k + 192158 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 192158) = 110592 * k + 96079 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 96079) = 165888 * k + 144119 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 144119) = 248832 * k + 216179 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 216179) = 373248 * k + 324269 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 324269) = 559872 * k + 486404 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 486404) = 279936 * k + 243202 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 243202) = 139968 * k + 121601 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 121601) = 209952 * k + 182402 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 182402) = 104976 * k + 91201 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 91201) = 157464 * k + 136802 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 136802) = 78732 * k + 68401 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68401) = 118098 * k + 102602 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 102602) = 59049 * k + 51301 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 56935) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 56935)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57071_mod_65536 {n : ℕ} (hn : n % 65536 = 57071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57071) = 98304 * k + 85607 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85607) = 147456 * k + 128411 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128411) = 221184 * k + 192617 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 192617) = 331776 * k + 288926 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 288926) = 165888 * k + 144463 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 144463) = 248832 * k + 216695 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 216695) = 373248 * k + 325043 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 325043) = 559872 * k + 487565 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 487565) = 839808 * k + 731348 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 731348) = 419904 * k + 365674 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 365674) = 209952 * k + 182837 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 182837) = 314928 * k + 274256 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 274256) = 157464 * k + 137128 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137128) = 78732 * k + 68564 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68564) = 39366 * k + 34282 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34282) = 19683 * k + 17141 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57179_mod_65536 {n : ℕ} (hn : n % 65536 = 57179) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57179 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57179) = 98304 * k + 85769 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85769) = 147456 * k + 128654 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128654) = 73728 * k + 64327 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 64327) = 110592 * k + 96491 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 96491) = 165888 * k + 144737 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 144737) = 248832 * k + 217106 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 217106) = 124416 * k + 108553 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 108553) = 186624 * k + 162830 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 162830) = 93312 * k + 81415 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 81415) = 139968 * k + 122123 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122123) = 209952 * k + 183185 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183185) = 314928 * k + 274778 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 274778) = 157464 * k + 137389 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137389) = 236196 * k + 206084 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 206084) = 118098 * k + 103042 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 103042) = 59049 * k + 51521 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57179) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57179)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57215_mod_65536 {n : ℕ} (hn : n % 65536 = 57215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57215) = 98304 * k + 85823 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85823) = 147456 * k + 128735 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128735) = 221184 * k + 193103 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193103) = 331776 * k + 289655 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 289655) = 497664 * k + 434483 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 434483) = 746496 * k + 651725 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 651725) = 1119744 * k + 977588 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 977588) = 559872 * k + 488794 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 488794) = 279936 * k + 244397 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 244397) = 419904 * k + 366596 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 366596) = 209952 * k + 183298 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183298) = 104976 * k + 91649 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 91649) = 157464 * k + 137474 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137474) = 78732 * k + 68737 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68737) = 118098 * k + 103106 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 103106) = 59049 * k + 51553 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57255_mod_65536 {n : ℕ} (hn : n % 65536 = 57255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57255) = 98304 * k + 85883 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85883) = 147456 * k + 128825 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128825) = 221184 * k + 193238 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193238) = 110592 * k + 96619 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 96619) = 165888 * k + 144929 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 144929) = 248832 * k + 217394 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 217394) = 124416 * k + 108697 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 108697) = 186624 * k + 163046 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 163046) = 93312 * k + 81523 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 81523) = 139968 * k + 122285 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122285) = 209952 * k + 183428 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183428) = 104976 * k + 91714 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 91714) = 52488 * k + 45857 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 45857) = 78732 * k + 68786 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68786) = 39366 * k + 34393 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34393) = 59049 * k + 51590 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57327_mod_65536 {n : ℕ} (hn : n % 65536 = 57327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57327) = 98304 * k + 85991 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 85991) = 147456 * k + 128987 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 128987) = 221184 * k + 193481 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193481) = 331776 * k + 290222 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 290222) = 165888 * k + 145111 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 145111) = 248832 * k + 217667 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 217667) = 373248 * k + 326501 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 326501) = 559872 * k + 489752 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 489752) = 279936 * k + 244876 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 244876) = 139968 * k + 122438 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122438) = 69984 * k + 61219 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 61219) = 104976 * k + 91829 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 91829) = 157464 * k + 137744 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137744) = 78732 * k + 68872 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68872) = 39366 * k + 34436 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34436) = 19683 * k + 17218 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57375_mod_65536 {n : ℕ} (hn : n % 65536 = 57375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57375) = 98304 * k + 86063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86063) = 147456 * k + 129095 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129095) = 221184 * k + 193643 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193643) = 331776 * k + 290465 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 290465) = 497664 * k + 435698 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 435698) = 248832 * k + 217849 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 217849) = 373248 * k + 326774 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 326774) = 186624 * k + 163387 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 163387) = 279936 * k + 245081 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 245081) = 419904 * k + 367622 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 367622) = 209952 * k + 183811 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183811) = 314928 * k + 275717 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 275717) = 472392 * k + 413576 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 413576) = 236196 * k + 206788 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 206788) = 118098 * k + 103394 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 103394) = 59049 * k + 51697 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57407_mod_65536 {n : ℕ} (hn : n % 65536 = 57407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57407) = 98304 * k + 86111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86111) = 147456 * k + 129167 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129167) = 221184 * k + 193751 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193751) = 331776 * k + 290627 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 290627) = 497664 * k + 435941 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 435941) = 746496 * k + 653912 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 653912) = 373248 * k + 326956 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 326956) = 186624 * k + 163478 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 163478) = 93312 * k + 81739 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 81739) = 139968 * k + 122609 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122609) = 209952 * k + 183914 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183914) = 104976 * k + 91957 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 91957) = 157464 * k + 137936 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137936) = 78732 * k + 68968 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68968) = 39366 * k + 34484 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34484) = 19683 * k + 17242 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57415_mod_65536 {n : ℕ} (hn : n % 65536 = 57415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57415) = 98304 * k + 86123 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86123) = 147456 * k + 129185 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129185) = 221184 * k + 193778 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193778) = 110592 * k + 96889 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 96889) = 165888 * k + 145334 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 145334) = 82944 * k + 72667 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 72667) = 124416 * k + 109001 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 109001) = 186624 * k + 163502 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 163502) = 93312 * k + 81751 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 81751) = 139968 * k + 122627 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122627) = 209952 * k + 183941 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 183941) = 314928 * k + 275912 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 275912) = 157464 * k + 137956 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 137956) = 78732 * k + 68978 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 68978) = 39366 * k + 34489 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34489) = 59049 * k + 51734 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57447_mod_65536 {n : ℕ} (hn : n % 65536 = 57447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57447) = 98304 * k + 86171 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86171) = 147456 * k + 129257 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129257) = 221184 * k + 193886 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 193886) = 110592 * k + 96943 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 96943) = 165888 * k + 145415 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 145415) = 248832 * k + 218123 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 218123) = 373248 * k + 327185 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 327185) = 559872 * k + 490778 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 490778) = 279936 * k + 245389 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 245389) = 419904 * k + 368084 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 368084) = 209952 * k + 184042 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 184042) = 104976 * k + 92021 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92021) = 157464 * k + 138032 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 138032) = 78732 * k + 69016 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69016) = 39366 * k + 34508 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34508) = 19683 * k + 17254 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57535_mod_65536 {n : ℕ} (hn : n % 65536 = 57535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57535) = 98304 * k + 86303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86303) = 147456 * k + 129455 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129455) = 221184 * k + 194183 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 194183) = 331776 * k + 291275 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 291275) = 497664 * k + 436913 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 436913) = 746496 * k + 655370 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 655370) = 373248 * k + 327685 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 327685) = 559872 * k + 491528 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 491528) = 279936 * k + 245764 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 245764) = 139968 * k + 122882 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 122882) = 69984 * k + 61441 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 61441) = 104976 * k + 92162 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92162) = 52488 * k + 46081 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46081) = 78732 * k + 69122 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69122) = 39366 * k + 34561 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34561) = 59049 * k + 51842 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57647_mod_65536 {n : ℕ} (hn : n % 65536 = 57647) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57647 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57647) = 98304 * k + 86471 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86471) = 147456 * k + 129707 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129707) = 221184 * k + 194561 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 194561) = 331776 * k + 291842 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 291842) = 165888 * k + 145921 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 145921) = 248832 * k + 218882 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 218882) = 124416 * k + 109441 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 109441) = 186624 * k + 164162 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 164162) = 93312 * k + 82081 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 82081) = 139968 * k + 123122 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 123122) = 69984 * k + 61561 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 61561) = 104976 * k + 92342 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92342) = 52488 * k + 46171 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46171) = 78732 * k + 69257 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69257) = 118098 * k + 103886 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 103886) = 59049 * k + 51943 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57647) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57647)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
