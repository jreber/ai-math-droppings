import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_57671_mod_65536 {n : ℕ} (hn : n % 65536 = 57671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57671) = 98304 * k + 86507 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86507) = 147456 * k + 129761 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129761) = 221184 * k + 194642 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 194642) = 110592 * k + 97321 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 97321) = 165888 * k + 145982 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 145982) = 82944 * k + 72991 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 72991) = 124416 * k + 109487 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 109487) = 186624 * k + 164231 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 164231) = 279936 * k + 246347 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 246347) = 419904 * k + 369521 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 369521) = 629856 * k + 554282 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 554282) = 314928 * k + 277141 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 277141) = 472392 * k + 415712 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 415712) = 236196 * k + 207856 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 207856) = 118098 * k + 103928 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 103928) = 59049 * k + 51964 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57755_mod_65536 {n : ℕ} (hn : n % 65536 = 57755) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57755 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57755) = 98304 * k + 86633 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86633) = 147456 * k + 129950 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129950) = 73728 * k + 64975 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 64975) = 110592 * k + 97463 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 97463) = 165888 * k + 146195 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 146195) = 248832 * k + 219293 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 219293) = 373248 * k + 328940 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 328940) = 186624 * k + 164470 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 164470) = 93312 * k + 82235 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 82235) = 139968 * k + 123353 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 123353) = 209952 * k + 185030 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 185030) = 104976 * k + 92515 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92515) = 157464 * k + 138773 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 138773) = 236196 * k + 208160 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 208160) = 118098 * k + 104080 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104080) = 59049 * k + 52040 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57755) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57755)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57759_mod_65536 {n : ℕ} (hn : n % 65536 = 57759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57759) = 98304 * k + 86639 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86639) = 147456 * k + 129959 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 129959) = 221184 * k + 194939 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 194939) = 331776 * k + 292409 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 292409) = 497664 * k + 438614 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 438614) = 248832 * k + 219307 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 219307) = 373248 * k + 328961 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 328961) = 559872 * k + 493442 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 493442) = 279936 * k + 246721 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 246721) = 419904 * k + 370082 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 370082) = 209952 * k + 185041 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 185041) = 314928 * k + 277562 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 277562) = 157464 * k + 138781 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 138781) = 236196 * k + 208172 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 208172) = 118098 * k + 104086 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104086) = 59049 * k + 52043 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57839_mod_65536 {n : ℕ} (hn : n % 65536 = 57839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57839) = 98304 * k + 86759 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86759) = 147456 * k + 130139 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130139) = 221184 * k + 195209 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 195209) = 331776 * k + 292814 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 292814) = 165888 * k + 146407 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 146407) = 248832 * k + 219611 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 219611) = 373248 * k + 329417 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 329417) = 559872 * k + 494126 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 494126) = 279936 * k + 247063 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 247063) = 419904 * k + 370595 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 370595) = 629856 * k + 555893 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 555893) = 944784 * k + 833840 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 833840) = 472392 * k + 416920 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 416920) = 236196 * k + 208460 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 208460) = 118098 * k + 104230 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104230) = 59049 * k + 52115 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57887_mod_65536 {n : ℕ} (hn : n % 65536 = 57887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57887) = 98304 * k + 86831 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86831) = 147456 * k + 130247 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130247) = 221184 * k + 195371 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 195371) = 331776 * k + 293057 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 293057) = 497664 * k + 439586 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 439586) = 248832 * k + 219793 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 219793) = 373248 * k + 329690 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 329690) = 186624 * k + 164845 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 164845) = 279936 * k + 247268 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 247268) = 139968 * k + 123634 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 123634) = 69984 * k + 61817 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 61817) = 104976 * k + 92726 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92726) = 52488 * k + 46363 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46363) = 78732 * k + 69545 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69545) = 118098 * k + 104318 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104318) = 59049 * k + 52159 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57947_mod_65536 {n : ℕ} (hn : n % 65536 = 57947) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57947 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57947) = 98304 * k + 86921 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86921) = 147456 * k + 130382 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130382) = 73728 * k + 65191 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 65191) = 110592 * k + 97787 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 97787) = 165888 * k + 146681 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 146681) = 248832 * k + 220022 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 220022) = 124416 * k + 110011 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 110011) = 186624 * k + 165017 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 165017) = 279936 * k + 247526 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 247526) = 139968 * k + 123763 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 123763) = 209952 * k + 185645 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 185645) = 314928 * k + 278468 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 278468) = 157464 * k + 139234 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 139234) = 78732 * k + 69617 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69617) = 118098 * k + 104426 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104426) = 59049 * k + 52213 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57947) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57947)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_57967_mod_65536 {n : ℕ} (hn : n % 65536 = 57967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 57967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 57967) = 98304 * k + 86951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 86951) = 147456 * k + 130427 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130427) = 221184 * k + 195641 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 195641) = 331776 * k + 293462 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 293462) = 165888 * k + 146731 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 146731) = 248832 * k + 220097 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 220097) = 373248 * k + 330146 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 330146) = 186624 * k + 165073 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 165073) = 279936 * k + 247610 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 247610) = 139968 * k + 123805 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 123805) = 209952 * k + 185708 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 185708) = 104976 * k + 92854 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 92854) = 52488 * k + 46427 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46427) = 78732 * k + 69641 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69641) = 118098 * k + 104462 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104462) = 59049 * k + 52231 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 57967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 57967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58015_mod_65536 {n : ℕ} (hn : n % 65536 = 58015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58015) = 98304 * k + 87023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87023) = 147456 * k + 130535 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130535) = 221184 * k + 195803 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 195803) = 331776 * k + 293705 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 293705) = 497664 * k + 440558 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 440558) = 248832 * k + 220279 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 220279) = 373248 * k + 330419 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 330419) = 559872 * k + 495629 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 495629) = 839808 * k + 743444 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 743444) = 419904 * k + 371722 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 371722) = 209952 * k + 185861 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 185861) = 314928 * k + 278792 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 278792) = 157464 * k + 139396 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 139396) = 78732 * k + 69698 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69698) = 39366 * k + 34849 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 34849) = 59049 * k + 52274 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58175_mod_65536 {n : ℕ} (hn : n % 65536 = 58175) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58175 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58175) = 98304 * k + 87263 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87263) = 147456 * k + 130895 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130895) = 221184 * k + 196343 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 196343) = 331776 * k + 294515 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 294515) = 497664 * k + 441773 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 441773) = 746496 * k + 662660 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 662660) = 373248 * k + 331330 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 331330) = 186624 * k + 165665 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 165665) = 279936 * k + 248498 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 248498) = 139968 * k + 124249 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 124249) = 209952 * k + 186374 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 186374) = 104976 * k + 93187 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93187) = 157464 * k + 139781 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 139781) = 236196 * k + 209672 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 209672) = 118098 * k + 104836 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104836) = 59049 * k + 52418 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58175) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58175)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58203_mod_65536 {n : ℕ} (hn : n % 65536 = 58203) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58203 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58203) = 98304 * k + 87305 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87305) = 147456 * k + 130958 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 130958) = 73728 * k + 65479 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 65479) = 110592 * k + 98219 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 98219) = 165888 * k + 147329 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 147329) = 248832 * k + 220994 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 220994) = 124416 * k + 110497 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 110497) = 186624 * k + 165746 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 165746) = 93312 * k + 82873 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 82873) = 139968 * k + 124310 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 124310) = 69984 * k + 62155 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 62155) = 104976 * k + 93233 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93233) = 157464 * k + 139850 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 139850) = 78732 * k + 69925 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 69925) = 118098 * k + 104888 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 104888) = 59049 * k + 52444 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58203) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58203)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58271_mod_65536 {n : ℕ} (hn : n % 65536 = 58271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58271) = 98304 * k + 87407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87407) = 147456 * k + 131111 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131111) = 221184 * k + 196667 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 196667) = 331776 * k + 295001 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 295001) = 497664 * k + 442502 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 442502) = 248832 * k + 221251 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 221251) = 373248 * k + 331877 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 331877) = 559872 * k + 497816 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 497816) = 279936 * k + 248908 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 248908) = 139968 * k + 124454 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 124454) = 69984 * k + 62227 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 62227) = 104976 * k + 93341 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93341) = 157464 * k + 140012 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140012) = 78732 * k + 70006 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70006) = 39366 * k + 35003 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35003) = 59049 * k + 52505 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58351_mod_65536 {n : ℕ} (hn : n % 65536 = 58351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58351) = 98304 * k + 87527 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87527) = 147456 * k + 131291 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131291) = 221184 * k + 196937 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 196937) = 331776 * k + 295406 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 295406) = 165888 * k + 147703 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 147703) = 248832 * k + 221555 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 221555) = 373248 * k + 332333 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 332333) = 559872 * k + 498500 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 498500) = 279936 * k + 249250 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 249250) = 139968 * k + 124625 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 124625) = 209952 * k + 186938 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 186938) = 104976 * k + 93469 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93469) = 157464 * k + 140204 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140204) = 78732 * k + 70102 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70102) = 39366 * k + 35051 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35051) = 59049 * k + 52577 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58459_mod_65536 {n : ℕ} (hn : n % 65536 = 58459) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58459 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58459) = 98304 * k + 87689 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87689) = 147456 * k + 131534 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131534) = 73728 * k + 65767 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 65767) = 110592 * k + 98651 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 98651) = 165888 * k + 147977 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 147977) = 248832 * k + 221966 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 221966) = 124416 * k + 110983 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 110983) = 186624 * k + 166475 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 166475) = 279936 * k + 249713 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 249713) = 419904 * k + 374570 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 374570) = 209952 * k + 187285 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 187285) = 314928 * k + 280928 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 280928) = 157464 * k + 140464 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140464) = 78732 * k + 70232 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70232) = 39366 * k + 35116 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35116) = 19683 * k + 17558 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58459) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58459)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58471_mod_65536 {n : ℕ} (hn : n % 65536 = 58471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58471) = 98304 * k + 87707 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87707) = 147456 * k + 131561 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131561) = 221184 * k + 197342 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197342) = 110592 * k + 98671 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 98671) = 165888 * k + 148007 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148007) = 248832 * k + 222011 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 222011) = 373248 * k + 333017 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333017) = 559872 * k + 499526 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 499526) = 279936 * k + 249763 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 249763) = 419904 * k + 374645 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 374645) = 629856 * k + 561968 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 561968) = 314928 * k + 280984 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 280984) = 157464 * k + 140492 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140492) = 78732 * k + 70246 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70246) = 39366 * k + 35123 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35123) = 59049 * k + 52685 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58479_mod_65536 {n : ℕ} (hn : n % 65536 = 58479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58479) = 98304 * k + 87719 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87719) = 147456 * k + 131579 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131579) = 221184 * k + 197369 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197369) = 331776 * k + 296054 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 296054) = 165888 * k + 148027 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148027) = 248832 * k + 222041 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 222041) = 373248 * k + 333062 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333062) = 186624 * k + 166531 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 166531) = 279936 * k + 249797 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 249797) = 419904 * k + 374696 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 374696) = 209952 * k + 187348 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 187348) = 104976 * k + 93674 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93674) = 52488 * k + 46837 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46837) = 78732 * k + 70256 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70256) = 39366 * k + 35128 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35128) = 19683 * k + 17564 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58495_mod_65536 {n : ℕ} (hn : n % 65536 = 58495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58495) = 98304 * k + 87743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87743) = 147456 * k + 131615 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131615) = 221184 * k + 197423 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197423) = 331776 * k + 296135 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 296135) = 497664 * k + 444203 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 444203) = 746496 * k + 666305 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 666305) = 1119744 * k + 999458 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 999458) = 559872 * k + 499729 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 499729) = 839808 * k + 749594 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 749594) = 419904 * k + 374797 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 374797) = 629856 * k + 562196 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 562196) = 314928 * k + 281098 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 281098) = 157464 * k + 140549 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140549) = 236196 * k + 210824 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 210824) = 118098 * k + 105412 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 105412) = 59049 * k + 52706 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58523_mod_65536 {n : ℕ} (hn : n % 65536 = 58523) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58523 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58523) = 98304 * k + 87785 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87785) = 147456 * k + 131678 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131678) = 73728 * k + 65839 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 65839) = 110592 * k + 98759 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 98759) = 165888 * k + 148139 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148139) = 248832 * k + 222209 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 222209) = 373248 * k + 333314 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333314) = 186624 * k + 166657 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 166657) = 279936 * k + 249986 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 249986) = 139968 * k + 124993 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 124993) = 209952 * k + 187490 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 187490) = 104976 * k + 93745 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93745) = 157464 * k + 140618 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140618) = 78732 * k + 70309 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70309) = 118098 * k + 105464 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 105464) = 59049 * k + 52732 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58523) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58523)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58527_mod_65536 {n : ℕ} (hn : n % 65536 = 58527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58527) = 98304 * k + 87791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87791) = 147456 * k + 131687 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131687) = 221184 * k + 197531 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197531) = 331776 * k + 296297 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 296297) = 497664 * k + 444446 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 444446) = 248832 * k + 222223 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 222223) = 373248 * k + 333335 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333335) = 559872 * k + 500003 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 500003) = 839808 * k + 750005 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 750005) = 1259712 * k + 1125008 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1125008) = 629856 * k + 562504 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 562504) = 314928 * k + 281252 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 281252) = 157464 * k + 140626 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140626) = 78732 * k + 70313 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70313) = 118098 * k + 105470 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 105470) = 59049 * k + 52735 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58559_mod_65536 {n : ℕ} (hn : n % 65536 = 58559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58559) = 98304 * k + 87839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87839) = 147456 * k + 131759 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131759) = 221184 * k + 197639 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197639) = 331776 * k + 296459 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 296459) = 497664 * k + 444689 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 444689) = 746496 * k + 667034 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 667034) = 373248 * k + 333517 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333517) = 559872 * k + 500276 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 500276) = 279936 * k + 250138 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 250138) = 139968 * k + 125069 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 125069) = 209952 * k + 187604 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 187604) = 104976 * k + 93802 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 93802) = 52488 * k + 46901 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 46901) = 78732 * k + 70352 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70352) = 39366 * k + 35176 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35176) = 19683 * k + 17588 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58599_mod_65536 {n : ℕ} (hn : n % 65536 = 58599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58599) = 98304 * k + 87899 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 87899) = 147456 * k + 131849 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 131849) = 221184 * k + 197774 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 197774) = 110592 * k + 98887 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 98887) = 165888 * k + 148331 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148331) = 248832 * k + 222497 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 222497) = 373248 * k + 333746 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 333746) = 186624 * k + 166873 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 166873) = 279936 * k + 250310 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 250310) = 139968 * k + 125155 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 125155) = 209952 * k + 187733 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 187733) = 314928 * k + 281600 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 281600) = 157464 * k + 140800 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 140800) = 78732 * k + 70400 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70400) = 39366 * k + 35200 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35200) = 19683 * k + 17600 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58855_mod_65536 {n : ℕ} (hn : n % 65536 = 58855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58855) = 98304 * k + 88283 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88283) = 147456 * k + 132425 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 132425) = 221184 * k + 198638 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 198638) = 110592 * k + 99319 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 99319) = 165888 * k + 148979 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148979) = 248832 * k + 223469 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 223469) = 373248 * k + 335204 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 335204) = 186624 * k + 167602 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 167602) = 93312 * k + 83801 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 83801) = 139968 * k + 125702 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 125702) = 69984 * k + 62851 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 62851) = 104976 * k + 94277 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 94277) = 157464 * k + 141416 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 141416) = 78732 * k + 70708 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70708) = 39366 * k + 35354 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35354) = 19683 * k + 17677 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58863_mod_65536 {n : ℕ} (hn : n % 65536 = 58863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58863) = 98304 * k + 88295 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88295) = 147456 * k + 132443 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 132443) = 221184 * k + 198665 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 198665) = 331776 * k + 297998 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 297998) = 165888 * k + 148999 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 148999) = 248832 * k + 223499 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 223499) = 373248 * k + 335249 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 335249) = 559872 * k + 502874 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 502874) = 279936 * k + 251437 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 251437) = 419904 * k + 377156 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 377156) = 209952 * k + 188578 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 188578) = 104976 * k + 94289 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 94289) = 157464 * k + 141434 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 141434) = 78732 * k + 70717 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70717) = 118098 * k + 106076 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 106076) = 59049 * k + 53038 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_58983_mod_65536 {n : ℕ} (hn : n % 65536 = 58983) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 58983 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 58983) = 98304 * k + 88475 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88475) = 147456 * k + 132713 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 132713) = 221184 * k + 199070 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 199070) = 110592 * k + 99535 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 99535) = 165888 * k + 149303 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 149303) = 248832 * k + 223955 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 223955) = 373248 * k + 335933 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 335933) = 559872 * k + 503900 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 503900) = 279936 * k + 251950 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 251950) = 139968 * k + 125975 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 125975) = 209952 * k + 188963 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 188963) = 314928 * k + 283445 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 283445) = 472392 * k + 425168 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 425168) = 236196 * k + 212584 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 212584) = 118098 * k + 106292 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 106292) = 59049 * k + 53146 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 58983) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 58983)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59035_mod_65536 {n : ℕ} (hn : n % 65536 = 59035) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59035 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59035) = 98304 * k + 88553 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88553) = 147456 * k + 132830 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 132830) = 73728 * k + 66415 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 66415) = 110592 * k + 99623 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 99623) = 165888 * k + 149435 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 149435) = 248832 * k + 224153 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 224153) = 373248 * k + 336230 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 336230) = 186624 * k + 168115 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 168115) = 279936 * k + 252173 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 252173) = 419904 * k + 378260 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 378260) = 209952 * k + 189130 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 189130) = 104976 * k + 94565 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 94565) = 157464 * k + 141848 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 141848) = 78732 * k + 70924 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 70924) = 39366 * k + 35462 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35462) = 19683 * k + 17731 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59035) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59035)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59247_mod_65536 {n : ℕ} (hn : n % 65536 = 59247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59247) = 98304 * k + 88871 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88871) = 147456 * k + 133307 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133307) = 221184 * k + 199961 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 199961) = 331776 * k + 299942 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 299942) = 165888 * k + 149971 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 149971) = 248832 * k + 224957 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 224957) = 373248 * k + 337436 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 337436) = 186624 * k + 168718 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 168718) = 93312 * k + 84359 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 84359) = 139968 * k + 126539 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 126539) = 209952 * k + 189809 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 189809) = 314928 * k + 284714 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 284714) = 157464 * k + 142357 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 142357) = 236196 * k + 213536 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 213536) = 118098 * k + 106768 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 106768) = 59049 * k + 53384 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59263_mod_65536 {n : ℕ} (hn : n % 65536 = 59263) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59263 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59263) = 98304 * k + 88895 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88895) = 147456 * k + 133343 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133343) = 221184 * k + 200015 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 200015) = 331776 * k + 300023 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 300023) = 497664 * k + 450035 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 450035) = 746496 * k + 675053 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 675053) = 1119744 * k + 1012580 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1012580) = 559872 * k + 506290 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 506290) = 279936 * k + 253145 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 253145) = 419904 * k + 379718 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 379718) = 209952 * k + 189859 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 189859) = 314928 * k + 284789 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 284789) = 472392 * k + 427184 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 427184) = 236196 * k + 213592 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 213592) = 118098 * k + 106796 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 106796) = 59049 * k + 53398 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59263) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59263)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59295_mod_65536 {n : ℕ} (hn : n % 65536 = 59295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59295) = 98304 * k + 88943 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88943) = 147456 * k + 133415 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133415) = 221184 * k + 200123 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 200123) = 331776 * k + 300185 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 300185) = 497664 * k + 450278 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 450278) = 248832 * k + 225139 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 225139) = 373248 * k + 337709 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 337709) = 559872 * k + 506564 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 506564) = 279936 * k + 253282 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 253282) = 139968 * k + 126641 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 126641) = 209952 * k + 189962 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 189962) = 104976 * k + 94981 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 94981) = 157464 * k + 142472 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 142472) = 78732 * k + 71236 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71236) = 39366 * k + 35618 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35618) = 19683 * k + 17809 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59303_mod_65536 {n : ℕ} (hn : n % 65536 = 59303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59303) = 98304 * k + 88955 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 88955) = 147456 * k + 133433 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133433) = 221184 * k + 200150 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 200150) = 110592 * k + 100075 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100075) = 165888 * k + 150113 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 150113) = 248832 * k + 225170 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 225170) = 124416 * k + 112585 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 112585) = 186624 * k + 168878 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 168878) = 93312 * k + 84439 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 84439) = 139968 * k + 126659 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 126659) = 209952 * k + 189989 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 189989) = 314928 * k + 284984 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 284984) = 157464 * k + 142492 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 142492) = 78732 * k + 71246 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71246) = 39366 * k + 35623 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35623) = 59049 * k + 53435 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59423_mod_65536 {n : ℕ} (hn : n % 65536 = 59423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59423) = 98304 * k + 89135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89135) = 147456 * k + 133703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133703) = 221184 * k + 200555 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 200555) = 331776 * k + 300833 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 300833) = 497664 * k + 451250 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 451250) = 248832 * k + 225625 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 225625) = 373248 * k + 338438 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 338438) = 186624 * k + 169219 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169219) = 279936 * k + 253829 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 253829) = 419904 * k + 380744 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 380744) = 209952 * k + 190372 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 190372) = 104976 * k + 95186 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95186) = 52488 * k + 47593 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 47593) = 78732 * k + 71390 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71390) = 39366 * k + 35695 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35695) = 59049 * k + 53543 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59463_mod_65536 {n : ℕ} (hn : n % 65536 = 59463) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59463 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59463) = 98304 * k + 89195 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89195) = 147456 * k + 133793 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 133793) = 221184 * k + 200690 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 200690) = 110592 * k + 100345 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100345) = 165888 * k + 150518 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 150518) = 82944 * k + 75259 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 75259) = 124416 * k + 112889 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 112889) = 186624 * k + 169334 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169334) = 93312 * k + 84667 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 84667) = 139968 * k + 127001 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 127001) = 209952 * k + 190502 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 190502) = 104976 * k + 95251 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95251) = 157464 * k + 142877 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 142877) = 236196 * k + 214316 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 214316) = 118098 * k + 107158 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107158) = 59049 * k + 53579 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59463) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59463)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59559_mod_65536 {n : ℕ} (hn : n % 65536 = 59559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59559) = 98304 * k + 89339 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89339) = 147456 * k + 134009 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134009) = 221184 * k + 201014 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 201014) = 110592 * k + 100507 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100507) = 165888 * k + 150761 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 150761) = 248832 * k + 226142 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 226142) = 124416 * k + 113071 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 113071) = 186624 * k + 169607 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169607) = 279936 * k + 254411 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 254411) = 419904 * k + 381617 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 381617) = 629856 * k + 572426 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 572426) = 314928 * k + 286213 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 286213) = 472392 * k + 429320 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 429320) = 236196 * k + 214660 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 214660) = 118098 * k + 107330 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107330) = 59049 * k + 53665 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59615_mod_65536 {n : ℕ} (hn : n % 65536 = 59615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59615) = 98304 * k + 89423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89423) = 147456 * k + 134135 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134135) = 221184 * k + 201203 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 201203) = 331776 * k + 301805 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 301805) = 497664 * k + 452708 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 452708) = 248832 * k + 226354 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 226354) = 124416 * k + 113177 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 113177) = 186624 * k + 169766 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169766) = 93312 * k + 84883 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 84883) = 139968 * k + 127325 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 127325) = 209952 * k + 190988 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 190988) = 104976 * k + 95494 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95494) = 52488 * k + 47747 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 47747) = 78732 * k + 71621 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71621) = 118098 * k + 107432 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107432) = 59049 * k + 53716 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59623_mod_65536 {n : ℕ} (hn : n % 65536 = 59623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59623) = 98304 * k + 89435 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89435) = 147456 * k + 134153 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134153) = 221184 * k + 201230 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 201230) = 110592 * k + 100615 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100615) = 165888 * k + 150923 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 150923) = 248832 * k + 226385 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 226385) = 373248 * k + 339578 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 339578) = 186624 * k + 169789 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169789) = 279936 * k + 254684 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 254684) = 139968 * k + 127342 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 127342) = 69984 * k + 63671 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 63671) = 104976 * k + 95507 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95507) = 157464 * k + 143261 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 143261) = 236196 * k + 214892 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 214892) = 118098 * k + 107446 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107446) = 59049 * k + 53723 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59643_mod_65536 {n : ℕ} (hn : n % 65536 = 59643) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59643 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59643) = 98304 * k + 89465 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89465) = 147456 * k + 134198 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134198) = 73728 * k + 67099 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 67099) = 110592 * k + 100649 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100649) = 165888 * k + 150974 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 150974) = 82944 * k + 75487 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 75487) = 124416 * k + 113231 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 113231) = 186624 * k + 169847 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 169847) = 279936 * k + 254771 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 254771) = 419904 * k + 382157 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 382157) = 629856 * k + 573236 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 573236) = 314928 * k + 286618 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 286618) = 157464 * k + 143309 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 143309) = 236196 * k + 214964 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 214964) = 118098 * k + 107482 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107482) = 59049 * k + 53741 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59643) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59643)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59647_mod_65536 {n : ℕ} (hn : n % 65536 = 59647) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59647 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59647) = 98304 * k + 89471 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89471) = 147456 * k + 134207 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134207) = 221184 * k + 201311 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 201311) = 331776 * k + 301967 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 301967) = 497664 * k + 452951 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 452951) = 746496 * k + 679427 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 679427) = 1119744 * k + 1019141 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1019141) = 1679616 * k + 1528712 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1528712) = 839808 * k + 764356 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 764356) = 419904 * k + 382178 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 382178) = 209952 * k + 191089 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 191089) = 314928 * k + 286634 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 286634) = 157464 * k + 143317 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 143317) = 236196 * k + 214976 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 214976) = 118098 * k + 107488 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107488) = 59049 * k + 53744 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59647) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59647)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59675_mod_65536 {n : ℕ} (hn : n % 65536 = 59675) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59675 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59675) = 98304 * k + 89513 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89513) = 147456 * k + 134270 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134270) = 73728 * k + 67135 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 67135) = 110592 * k + 100703 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 100703) = 165888 * k + 151055 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 151055) = 248832 * k + 226583 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 226583) = 373248 * k + 339875 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 339875) = 559872 * k + 509813 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 509813) = 839808 * k + 764720 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 764720) = 419904 * k + 382360 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 382360) = 209952 * k + 191180 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 191180) = 104976 * k + 95590 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95590) = 52488 * k + 47795 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 47795) = 78732 * k + 71693 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71693) = 118098 * k + 107540 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107540) = 59049 * k + 53770 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59675) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59675)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59775_mod_65536 {n : ℕ} (hn : n % 65536 = 59775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59775) = 98304 * k + 89663 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89663) = 147456 * k + 134495 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134495) = 221184 * k + 201743 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 201743) = 331776 * k + 302615 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 302615) = 497664 * k + 453923 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 453923) = 746496 * k + 680885 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 680885) = 1119744 * k + 1021328 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1021328) = 559872 * k + 510664 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 510664) = 279936 * k + 255332 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 255332) = 139968 * k + 127666 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 127666) = 69984 * k + 63833 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 63833) = 104976 * k + 95750 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95750) = 52488 * k + 47875 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 47875) = 78732 * k + 71813 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71813) = 118098 * k + 107720 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 107720) = 59049 * k + 53860 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_59879_mod_65536 {n : ℕ} (hn : n % 65536 = 59879) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 59879 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 59879) = 98304 * k + 89819 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 89819) = 147456 * k + 134729 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 134729) = 221184 * k + 202094 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 202094) = 110592 * k + 101047 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 101047) = 165888 * k + 151571 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 151571) = 248832 * k + 227357 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 227357) = 373248 * k + 341036 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 341036) = 186624 * k + 170518 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 170518) = 93312 * k + 85259 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 85259) = 139968 * k + 127889 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 127889) = 209952 * k + 191834 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 191834) = 104976 * k + 95917 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 95917) = 157464 * k + 143876 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 143876) = 78732 * k + 71938 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 71938) = 39366 * k + 35969 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 35969) = 59049 * k + 53954 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 59879) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 59879)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60007_mod_65536 {n : ℕ} (hn : n % 65536 = 60007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60007) = 98304 * k + 90011 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90011) = 147456 * k + 135017 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135017) = 221184 * k + 202526 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 202526) = 110592 * k + 101263 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 101263) = 165888 * k + 151895 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 151895) = 248832 * k + 227843 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 227843) = 373248 * k + 341765 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 341765) = 559872 * k + 512648 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 512648) = 279936 * k + 256324 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 256324) = 139968 * k + 128162 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 128162) = 69984 * k + 64081 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 64081) = 104976 * k + 96122 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 96122) = 52488 * k + 48061 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 48061) = 78732 * k + 72092 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72092) = 39366 * k + 36046 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36046) = 19683 * k + 18023 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60015_mod_65536 {n : ℕ} (hn : n % 65536 = 60015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60015) = 98304 * k + 90023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90023) = 147456 * k + 135035 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135035) = 221184 * k + 202553 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 202553) = 331776 * k + 303830 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 303830) = 165888 * k + 151915 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 151915) = 248832 * k + 227873 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 227873) = 373248 * k + 341810 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 341810) = 186624 * k + 170905 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 170905) = 279936 * k + 256358 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 256358) = 139968 * k + 128179 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 128179) = 209952 * k + 192269 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 192269) = 314928 * k + 288404 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 288404) = 157464 * k + 144202 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144202) = 78732 * k + 72101 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72101) = 118098 * k + 108152 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 108152) = 59049 * k + 54076 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60059_mod_65536 {n : ℕ} (hn : n % 65536 = 60059) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60059 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60059) = 98304 * k + 90089 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90089) = 147456 * k + 135134 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135134) = 73728 * k + 67567 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 67567) = 110592 * k + 101351 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 101351) = 165888 * k + 152027 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 152027) = 248832 * k + 228041 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 228041) = 373248 * k + 342062 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 342062) = 186624 * k + 171031 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 171031) = 279936 * k + 256547 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 256547) = 419904 * k + 384821 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 384821) = 629856 * k + 577232 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 577232) = 314928 * k + 288616 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 288616) = 157464 * k + 144308 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144308) = 78732 * k + 72154 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72154) = 39366 * k + 36077 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36077) = 59049 * k + 54116 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60059) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60059)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60063_mod_65536 {n : ℕ} (hn : n % 65536 = 60063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60063) = 98304 * k + 90095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90095) = 147456 * k + 135143 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135143) = 221184 * k + 202715 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 202715) = 331776 * k + 304073 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 304073) = 497664 * k + 456110 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 456110) = 248832 * k + 228055 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 228055) = 373248 * k + 342083 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 342083) = 559872 * k + 513125 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 513125) = 839808 * k + 769688 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 769688) = 419904 * k + 384844 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 384844) = 209952 * k + 192422 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 192422) = 104976 * k + 96211 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 96211) = 157464 * k + 144317 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144317) = 236196 * k + 216476 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 216476) = 118098 * k + 108238 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 108238) = 59049 * k + 54119 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60143_mod_65536 {n : ℕ} (hn : n % 65536 = 60143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60143) = 98304 * k + 90215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90215) = 147456 * k + 135323 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135323) = 221184 * k + 202985 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 202985) = 331776 * k + 304478 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 304478) = 165888 * k + 152239 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 152239) = 248832 * k + 228359 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 228359) = 373248 * k + 342539 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 342539) = 559872 * k + 513809 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 513809) = 839808 * k + 770714 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 770714) = 419904 * k + 385357 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 385357) = 629856 * k + 578036 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 578036) = 314928 * k + 289018 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 289018) = 157464 * k + 144509 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144509) = 236196 * k + 216764 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 216764) = 118098 * k + 108382 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 108382) = 59049 * k + 54191 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60231_mod_65536 {n : ℕ} (hn : n % 65536 = 60231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60231) = 98304 * k + 90347 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90347) = 147456 * k + 135521 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135521) = 221184 * k + 203282 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 203282) = 110592 * k + 101641 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 101641) = 165888 * k + 152462 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 152462) = 82944 * k + 76231 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 76231) = 124416 * k + 114347 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 114347) = 186624 * k + 171521 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 171521) = 279936 * k + 257282 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 257282) = 139968 * k + 128641 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 128641) = 209952 * k + 192962 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 192962) = 104976 * k + 96481 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 96481) = 157464 * k + 144722 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144722) = 78732 * k + 72361 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72361) = 118098 * k + 108542 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 108542) = 59049 * k + 54271 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60271_mod_65536 {n : ℕ} (hn : n % 65536 = 60271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60271) = 98304 * k + 90407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90407) = 147456 * k + 135611 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135611) = 221184 * k + 203417 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 203417) = 331776 * k + 305126 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 305126) = 165888 * k + 152563 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 152563) = 248832 * k + 228845 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 228845) = 373248 * k + 343268 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 343268) = 186624 * k + 171634 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 171634) = 93312 * k + 85817 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 85817) = 139968 * k + 128726 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 128726) = 69984 * k + 64363 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 64363) = 104976 * k + 96545 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 96545) = 157464 * k + 144818 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 144818) = 78732 * k + 72409 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72409) = 118098 * k + 108614 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 108614) = 59049 * k + 54307 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60411_mod_65536 {n : ℕ} (hn : n % 65536 = 60411) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60411 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60411) = 98304 * k + 90617 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90617) = 147456 * k + 135926 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 135926) = 73728 * k + 67963 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 67963) = 110592 * k + 101945 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 101945) = 165888 * k + 152918 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 152918) = 82944 * k + 76459 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 76459) = 124416 * k + 114689 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 114689) = 186624 * k + 172034 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 172034) = 93312 * k + 86017 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 86017) = 139968 * k + 129026 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 129026) = 69984 * k + 64513 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 64513) = 104976 * k + 96770 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 96770) = 52488 * k + 48385 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 48385) = 78732 * k + 72578 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72578) = 39366 * k + 36289 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36289) = 59049 * k + 54434 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60411) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60411)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60527_mod_65536 {n : ℕ} (hn : n % 65536 = 60527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60527) = 98304 * k + 90791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90791) = 147456 * k + 136187 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136187) = 221184 * k + 204281 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 204281) = 331776 * k + 306422 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 306422) = 165888 * k + 153211 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 153211) = 248832 * k + 229817 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 229817) = 373248 * k + 344726 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 344726) = 186624 * k + 172363 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 172363) = 279936 * k + 258545 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 258545) = 419904 * k + 387818 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 387818) = 209952 * k + 193909 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 193909) = 314928 * k + 290864 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 290864) = 157464 * k + 145432 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 145432) = 78732 * k + 72716 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72716) = 39366 * k + 36358 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36358) = 19683 * k + 18179 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60571_mod_65536 {n : ℕ} (hn : n % 65536 = 60571) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60571 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60571) = 98304 * k + 90857 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90857) = 147456 * k + 136286 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136286) = 73728 * k + 68143 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 68143) = 110592 * k + 102215 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 102215) = 165888 * k + 153323 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 153323) = 248832 * k + 229985 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 229985) = 373248 * k + 344978 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 344978) = 186624 * k + 172489 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 172489) = 279936 * k + 258734 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 258734) = 139968 * k + 129367 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 129367) = 209952 * k + 194051 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 194051) = 314928 * k + 291077 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 291077) = 472392 * k + 436616 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 436616) = 236196 * k + 218308 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 218308) = 118098 * k + 109154 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 109154) = 59049 * k + 54577 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60571) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60571)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60607_mod_65536 {n : ℕ} (hn : n % 65536 = 60607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60607) = 98304 * k + 90911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90911) = 147456 * k + 136367 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136367) = 221184 * k + 204551 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 204551) = 331776 * k + 306827 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 306827) = 497664 * k + 460241 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 460241) = 746496 * k + 690362 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 690362) = 373248 * k + 345181 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 345181) = 559872 * k + 517772 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 517772) = 279936 * k + 258886 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 258886) = 139968 * k + 129443 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 129443) = 209952 * k + 194165 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 194165) = 314928 * k + 291248 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 291248) = 157464 * k + 145624 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 145624) = 78732 * k + 72812 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72812) = 39366 * k + 36406 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36406) = 19683 * k + 18203 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60623_mod_65536 {n : ℕ} (hn : n % 65536 = 60623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60623) = 98304 * k + 90935 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 90935) = 147456 * k + 136403 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136403) = 221184 * k + 204605 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 204605) = 331776 * k + 306908 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 306908) = 165888 * k + 153454 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 153454) = 82944 * k + 76727 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 76727) = 124416 * k + 115091 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 115091) = 186624 * k + 172637 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 172637) = 279936 * k + 258956 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 258956) = 139968 * k + 129478 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 129478) = 69984 * k + 64739 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 64739) = 104976 * k + 97109 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 97109) = 157464 * k + 145664 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 145664) = 78732 * k + 72832 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72832) = 39366 * k + 36416 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36416) = 19683 * k + 18208 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60743_mod_65536 {n : ℕ} (hn : n % 65536 = 60743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60743) = 98304 * k + 91115 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91115) = 147456 * k + 136673 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136673) = 221184 * k + 205010 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 205010) = 110592 * k + 102505 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 102505) = 165888 * k + 153758 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 153758) = 82944 * k + 76879 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 76879) = 124416 * k + 115319 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 115319) = 186624 * k + 172979 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 172979) = 279936 * k + 259469 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 259469) = 419904 * k + 389204 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 389204) = 209952 * k + 194602 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 194602) = 104976 * k + 97301 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 97301) = 157464 * k + 145952 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 145952) = 78732 * k + 72976 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 72976) = 39366 * k + 36488 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36488) = 19683 * k + 18244 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60831_mod_65536 {n : ℕ} (hn : n % 65536 = 60831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60831) = 98304 * k + 91247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91247) = 147456 * k + 136871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 136871) = 221184 * k + 205307 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 205307) = 331776 * k + 307961 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 307961) = 497664 * k + 461942 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 461942) = 248832 * k + 230971 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 230971) = 373248 * k + 346457 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 346457) = 559872 * k + 519686 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 519686) = 279936 * k + 259843 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 259843) = 419904 * k + 389765 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 389765) = 629856 * k + 584648 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 584648) = 314928 * k + 292324 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 292324) = 157464 * k + 146162 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 146162) = 78732 * k + 73081 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73081) = 118098 * k + 109622 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 109622) = 59049 * k + 54811 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60911_mod_65536 {n : ℕ} (hn : n % 65536 = 60911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60911) = 98304 * k + 91367 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91367) = 147456 * k + 137051 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 137051) = 221184 * k + 205577 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 205577) = 331776 * k + 308366 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 308366) = 165888 * k + 154183 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 154183) = 248832 * k + 231275 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 231275) = 373248 * k + 346913 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 346913) = 559872 * k + 520370 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 520370) = 279936 * k + 260185 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 260185) = 419904 * k + 390278 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 390278) = 209952 * k + 195139 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 195139) = 314928 * k + 292709 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 292709) = 472392 * k + 439064 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 439064) = 236196 * k + 219532 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 219532) = 118098 * k + 109766 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 109766) = 59049 * k + 54883 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_60955_mod_65536 {n : ℕ} (hn : n % 65536 = 60955) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 60955 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 60955) = 98304 * k + 91433 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91433) = 147456 * k + 137150 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 137150) = 73728 * k + 68575 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 68575) = 110592 * k + 102863 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 102863) = 165888 * k + 154295 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 154295) = 248832 * k + 231443 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 231443) = 373248 * k + 347165 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 347165) = 559872 * k + 520748 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 520748) = 279936 * k + 260374 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 260374) = 139968 * k + 130187 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 130187) = 209952 * k + 195281 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 195281) = 314928 * k + 292922 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 292922) = 157464 * k + 146461 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 146461) = 236196 * k + 219692 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 219692) = 118098 * k + 109846 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 109846) = 59049 * k + 54923 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 60955) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 60955)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61031_mod_65536 {n : ℕ} (hn : n % 65536 = 61031) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61031 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61031) = 98304 * k + 91547 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91547) = 147456 * k + 137321 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 137321) = 221184 * k + 205982 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 205982) = 110592 * k + 102991 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 102991) = 165888 * k + 154487 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 154487) = 248832 * k + 231731 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 231731) = 373248 * k + 347597 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 347597) = 559872 * k + 521396 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 521396) = 279936 * k + 260698 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 260698) = 139968 * k + 130349 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 130349) = 209952 * k + 195524 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 195524) = 104976 * k + 97762 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 97762) = 52488 * k + 48881 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 48881) = 78732 * k + 73322 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73322) = 39366 * k + 36661 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36661) = 59049 * k + 54992 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61031) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61031)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61135_mod_65536 {n : ℕ} (hn : n % 65536 = 61135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61135) = 98304 * k + 91703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91703) = 147456 * k + 137555 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 137555) = 221184 * k + 206333 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 206333) = 331776 * k + 309500 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 309500) = 165888 * k + 154750 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 154750) = 82944 * k + 77375 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 77375) = 124416 * k + 116063 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 116063) = 186624 * k + 174095 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 174095) = 279936 * k + 261143 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 261143) = 419904 * k + 391715 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 391715) = 629856 * k + 587573 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 587573) = 944784 * k + 881360 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 881360) = 472392 * k + 440680 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 440680) = 236196 * k + 220340 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 220340) = 118098 * k + 110170 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110170) = 59049 * k + 55085 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61311_mod_65536 {n : ℕ} (hn : n % 65536 = 61311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61311) = 98304 * k + 91967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 91967) = 147456 * k + 137951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 137951) = 221184 * k + 206927 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 206927) = 331776 * k + 310391 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 310391) = 497664 * k + 465587 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 465587) = 746496 * k + 698381 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 698381) = 1119744 * k + 1047572 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1047572) = 559872 * k + 523786 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 523786) = 279936 * k + 261893 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 261893) = 419904 * k + 392840 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 392840) = 209952 * k + 196420 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 196420) = 104976 * k + 98210 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98210) = 52488 * k + 49105 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49105) = 78732 * k + 73658 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73658) = 39366 * k + 36829 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36829) = 59049 * k + 55244 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61351_mod_65536 {n : ℕ} (hn : n % 65536 = 61351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61351) = 98304 * k + 92027 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92027) = 147456 * k + 138041 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138041) = 221184 * k + 207062 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207062) = 110592 * k + 103531 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 103531) = 165888 * k + 155297 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155297) = 248832 * k + 232946 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 232946) = 124416 * k + 116473 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 116473) = 186624 * k + 174710 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 174710) = 93312 * k + 87355 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 87355) = 139968 * k + 131033 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131033) = 209952 * k + 196550 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 196550) = 104976 * k + 98275 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98275) = 157464 * k + 147413 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 147413) = 236196 * k + 221120 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 221120) = 118098 * k + 110560 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110560) = 59049 * k + 55280 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61375_mod_65536 {n : ℕ} (hn : n % 65536 = 61375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61375) = 98304 * k + 92063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92063) = 147456 * k + 138095 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138095) = 221184 * k + 207143 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207143) = 331776 * k + 310715 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 310715) = 497664 * k + 466073 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 466073) = 746496 * k + 699110 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 699110) = 373248 * k + 349555 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 349555) = 559872 * k + 524333 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 524333) = 839808 * k + 786500 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 786500) = 419904 * k + 393250 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 393250) = 209952 * k + 196625 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 196625) = 314928 * k + 294938 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 294938) = 157464 * k + 147469 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 147469) = 236196 * k + 221204 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 221204) = 118098 * k + 110602 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110602) = 59049 * k + 55301 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61423_mod_65536 {n : ℕ} (hn : n % 65536 = 61423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61423) = 98304 * k + 92135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92135) = 147456 * k + 138203 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138203) = 221184 * k + 207305 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207305) = 331776 * k + 310958 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 310958) = 165888 * k + 155479 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155479) = 248832 * k + 233219 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 233219) = 373248 * k + 349829 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 349829) = 559872 * k + 524744 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 524744) = 279936 * k + 262372 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 262372) = 139968 * k + 131186 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131186) = 69984 * k + 65593 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 65593) = 104976 * k + 98390 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98390) = 52488 * k + 49195 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49195) = 78732 * k + 73793 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73793) = 118098 * k + 110690 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110690) = 59049 * k + 55345 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61435_mod_65536 {n : ℕ} (hn : n % 65536 = 61435) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61435 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61435) = 98304 * k + 92153 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92153) = 147456 * k + 138230 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138230) = 73728 * k + 69115 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 69115) = 110592 * k + 103673 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 103673) = 165888 * k + 155510 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155510) = 82944 * k + 77755 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 77755) = 124416 * k + 116633 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 116633) = 186624 * k + 174950 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 174950) = 93312 * k + 87475 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 87475) = 139968 * k + 131213 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131213) = 209952 * k + 196820 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 196820) = 104976 * k + 98410 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98410) = 52488 * k + 49205 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49205) = 78732 * k + 73808 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73808) = 39366 * k + 36904 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36904) = 19683 * k + 18452 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61435) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61435)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61471_mod_65536 {n : ℕ} (hn : n % 65536 = 61471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61471) = 98304 * k + 92207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92207) = 147456 * k + 138311 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138311) = 221184 * k + 207467 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207467) = 331776 * k + 311201 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 311201) = 497664 * k + 466802 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 466802) = 248832 * k + 233401 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 233401) = 373248 * k + 350102 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 350102) = 186624 * k + 175051 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175051) = 279936 * k + 262577 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 262577) = 419904 * k + 393866 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 393866) = 209952 * k + 196933 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 196933) = 314928 * k + 295400 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 295400) = 157464 * k + 147700 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 147700) = 78732 * k + 73850 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73850) = 39366 * k + 36925 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 36925) = 59049 * k + 55388 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61503_mod_65536 {n : ℕ} (hn : n % 65536 = 61503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61503) = 98304 * k + 92255 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92255) = 147456 * k + 138383 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138383) = 221184 * k + 207575 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207575) = 331776 * k + 311363 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 311363) = 497664 * k + 467045 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 467045) = 746496 * k + 700568 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 700568) = 373248 * k + 350284 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 350284) = 186624 * k + 175142 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175142) = 93312 * k + 87571 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 87571) = 139968 * k + 131357 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131357) = 209952 * k + 197036 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 197036) = 104976 * k + 98518 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98518) = 52488 * k + 49259 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49259) = 78732 * k + 73889 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73889) = 118098 * k + 110834 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110834) = 59049 * k + 55417 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61531_mod_65536 {n : ℕ} (hn : n % 65536 = 61531) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61531 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61531) = 98304 * k + 92297 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92297) = 147456 * k + 138446 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138446) = 73728 * k + 69223 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 69223) = 110592 * k + 103835 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 103835) = 165888 * k + 155753 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155753) = 248832 * k + 233630 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 233630) = 124416 * k + 116815 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 116815) = 186624 * k + 175223 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175223) = 279936 * k + 262835 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 262835) = 419904 * k + 394253 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 394253) = 629856 * k + 591380 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 591380) = 314928 * k + 295690 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 295690) = 157464 * k + 147845 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 147845) = 236196 * k + 221768 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 221768) = 118098 * k + 110884 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110884) = 59049 * k + 55442 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61531) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61531)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61543_mod_65536 {n : ℕ} (hn : n % 65536 = 61543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61543) = 98304 * k + 92315 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92315) = 147456 * k + 138473 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138473) = 221184 * k + 207710 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 207710) = 110592 * k + 103855 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 103855) = 165888 * k + 155783 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155783) = 248832 * k + 233675 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 233675) = 373248 * k + 350513 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 350513) = 559872 * k + 525770 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 525770) = 279936 * k + 262885 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 262885) = 419904 * k + 394328 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 394328) = 209952 * k + 197164 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 197164) = 104976 * k + 98582 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98582) = 52488 * k + 49291 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49291) = 78732 * k + 73937 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 73937) = 118098 * k + 110906 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 110906) = 59049 * k + 55453 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61595_mod_65536 {n : ℕ} (hn : n % 65536 = 61595) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61595 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61595) = 98304 * k + 92393 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92393) = 147456 * k + 138590 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138590) = 73728 * k + 69295 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 69295) = 110592 * k + 103943 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 103943) = 165888 * k + 155915 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 155915) = 248832 * k + 233873 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 233873) = 373248 * k + 350810 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 350810) = 186624 * k + 175405 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175405) = 279936 * k + 263108 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 263108) = 139968 * k + 131554 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131554) = 69984 * k + 65777 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 65777) = 104976 * k + 98666 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98666) = 52488 * k + 49333 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49333) = 78732 * k + 74000 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74000) = 39366 * k + 37000 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37000) = 19683 * k + 18500 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61595) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61595)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61631_mod_65536 {n : ℕ} (hn : n % 65536 = 61631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61631) = 98304 * k + 92447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92447) = 147456 * k + 138671 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138671) = 221184 * k + 208007 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 208007) = 331776 * k + 312011 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 312011) = 497664 * k + 468017 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 468017) = 746496 * k + 702026 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 702026) = 373248 * k + 351013 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 351013) = 559872 * k + 526520 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 526520) = 279936 * k + 263260 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 263260) = 139968 * k + 131630 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131630) = 69984 * k + 65815 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 65815) = 104976 * k + 98723 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98723) = 157464 * k + 148085 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148085) = 236196 * k + 222128 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 222128) = 118098 * k + 111064 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 111064) = 59049 * k + 55532 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61647_mod_65536 {n : ℕ} (hn : n % 65536 = 61647) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61647 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61647) = 98304 * k + 92471 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92471) = 147456 * k + 138707 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138707) = 221184 * k + 208061 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 208061) = 331776 * k + 312092 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 312092) = 165888 * k + 156046 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 156046) = 82944 * k + 78023 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 78023) = 124416 * k + 117035 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 117035) = 186624 * k + 175553 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175553) = 279936 * k + 263330 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 263330) = 139968 * k + 131665 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131665) = 209952 * k + 197498 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 197498) = 104976 * k + 98749 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 98749) = 157464 * k + 148124 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148124) = 78732 * k + 74062 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74062) = 39366 * k + 37031 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37031) = 59049 * k + 55547 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61647) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61647)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61663_mod_65536 {n : ℕ} (hn : n % 65536 = 61663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61663) = 98304 * k + 92495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92495) = 147456 * k + 138743 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138743) = 221184 * k + 208115 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 208115) = 331776 * k + 312173 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 312173) = 497664 * k + 468260 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 468260) = 248832 * k + 234130 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 234130) = 124416 * k + 117065 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 117065) = 186624 * k + 175598 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175598) = 93312 * k + 87799 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 87799) = 139968 * k + 131699 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 131699) = 209952 * k + 197549 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 197549) = 314928 * k + 296324 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 296324) = 157464 * k + 148162 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148162) = 78732 * k + 74081 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74081) = 118098 * k + 111122 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 111122) = 59049 * k + 55561 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61723_mod_65536 {n : ℕ} (hn : n % 65536 = 61723) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61723 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61723) = 98304 * k + 92585 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92585) = 147456 * k + 138878 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138878) = 73728 * k + 69439 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 69439) = 110592 * k + 104159 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 104159) = 165888 * k + 156239 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 156239) = 248832 * k + 234359 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 234359) = 373248 * k + 351539 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 351539) = 559872 * k + 527309 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 527309) = 839808 * k + 790964 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 790964) = 419904 * k + 395482 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 395482) = 209952 * k + 197741 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 197741) = 314928 * k + 296612 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 296612) = 157464 * k + 148306 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148306) = 78732 * k + 74153 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74153) = 118098 * k + 111230 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 111230) = 59049 * k + 55615 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61723) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61723)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61767_mod_65536 {n : ℕ} (hn : n % 65536 = 61767) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61767 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61767) = 98304 * k + 92651 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92651) = 147456 * k + 138977 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 138977) = 221184 * k + 208466 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 208466) = 110592 * k + 104233 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 104233) = 165888 * k + 156350 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 156350) = 82944 * k + 78175 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 78175) = 124416 * k + 117263 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 117263) = 186624 * k + 175895 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 175895) = 279936 * k + 263843 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 263843) = 419904 * k + 395765 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 395765) = 629856 * k + 593648 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 593648) = 314928 * k + 296824 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 296824) = 157464 * k + 148412 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148412) = 78732 * k + 74206 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74206) = 39366 * k + 37103 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37103) = 59049 * k + 55655 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61767) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61767)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_61979_mod_65536 {n : ℕ} (hn : n % 65536 = 61979) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 61979 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 61979) = 98304 * k + 92969 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 92969) = 147456 * k + 139454 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 139454) = 73728 * k + 69727 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 69727) = 110592 * k + 104591 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 104591) = 165888 * k + 156887 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 156887) = 248832 * k + 235331 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 235331) = 373248 * k + 352997 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 352997) = 559872 * k + 529496 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 529496) = 279936 * k + 264748 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 264748) = 139968 * k + 132374 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 132374) = 69984 * k + 66187 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 66187) = 104976 * k + 99281 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 99281) = 157464 * k + 148922 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 148922) = 78732 * k + 74461 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74461) = 118098 * k + 111692 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 111692) = 59049 * k + 55846 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 61979) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 61979)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62119_mod_65536 {n : ℕ} (hn : n % 65536 = 62119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62119) = 98304 * k + 93179 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93179) = 147456 * k + 139769 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 139769) = 221184 * k + 209654 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 209654) = 110592 * k + 104827 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 104827) = 165888 * k + 157241 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 157241) = 248832 * k + 235862 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 235862) = 124416 * k + 117931 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 117931) = 186624 * k + 176897 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 176897) = 279936 * k + 265346 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 265346) = 139968 * k + 132673 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 132673) = 209952 * k + 199010 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 199010) = 104976 * k + 99505 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 99505) = 157464 * k + 149258 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 149258) = 78732 * k + 74629 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74629) = 118098 * k + 111944 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 111944) = 59049 * k + 55972 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62159_mod_65536 {n : ℕ} (hn : n % 65536 = 62159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62159) = 98304 * k + 93239 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93239) = 147456 * k + 139859 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 139859) = 221184 * k + 209789 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 209789) = 331776 * k + 314684 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 314684) = 165888 * k + 157342 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 157342) = 82944 * k + 78671 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 78671) = 124416 * k + 118007 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 118007) = 186624 * k + 177011 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 177011) = 279936 * k + 265517 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 265517) = 419904 * k + 398276 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 398276) = 209952 * k + 199138 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 199138) = 104976 * k + 99569 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 99569) = 157464 * k + 149354 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 149354) = 78732 * k + 74677 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74677) = 118098 * k + 112016 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 112016) = 59049 * k + 56008 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62235_mod_65536 {n : ℕ} (hn : n % 65536 = 62235) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62235 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62235) = 98304 * k + 93353 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93353) = 147456 * k + 140030 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140030) = 73728 * k + 70015 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 70015) = 110592 * k + 105023 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 105023) = 165888 * k + 157535 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 157535) = 248832 * k + 236303 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 236303) = 373248 * k + 354455 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 354455) = 559872 * k + 531683 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 531683) = 839808 * k + 797525 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 797525) = 1259712 * k + 1196288 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1196288) = 629856 * k + 598144 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 598144) = 314928 * k + 299072 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 299072) = 157464 * k + 149536 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 149536) = 78732 * k + 74768 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74768) = 39366 * k + 37384 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37384) = 19683 * k + 18692 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62235) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62235)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62239_mod_65536 {n : ℕ} (hn : n % 65536 = 62239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62239) = 98304 * k + 93359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93359) = 147456 * k + 140039 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140039) = 221184 * k + 210059 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 210059) = 331776 * k + 315089 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 315089) = 497664 * k + 472634 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 472634) = 248832 * k + 236317 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 236317) = 373248 * k + 354476 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 354476) = 186624 * k + 177238 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 177238) = 93312 * k + 88619 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 88619) = 139968 * k + 132929 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 132929) = 209952 * k + 199394 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 199394) = 104976 * k + 99697 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 99697) = 157464 * k + 149546 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 149546) = 78732 * k + 74773 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74773) = 118098 * k + 112160 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 112160) = 59049 * k + 56080 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62279_mod_65536 {n : ℕ} (hn : n % 65536 = 62279) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62279 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62279) = 98304 * k + 93419 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93419) = 147456 * k + 140129 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140129) = 221184 * k + 210194 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 210194) = 110592 * k + 105097 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 105097) = 165888 * k + 157646 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 157646) = 82944 * k + 78823 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 78823) = 124416 * k + 118235 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 118235) = 186624 * k + 177353 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 177353) = 279936 * k + 266030 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 266030) = 139968 * k + 133015 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 133015) = 209952 * k + 199523 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 199523) = 314928 * k + 299285 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 299285) = 472392 * k + 448928 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 448928) = 236196 * k + 224464 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 224464) = 118098 * k + 112232 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 112232) = 59049 * k + 56116 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62279) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62279)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62299_mod_65536 {n : ℕ} (hn : n % 65536 = 62299) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62299 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62299) = 98304 * k + 93449 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93449) = 147456 * k + 140174 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140174) = 73728 * k + 70087 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 70087) = 110592 * k + 105131 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 105131) = 165888 * k + 157697 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 157697) = 248832 * k + 236546 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 236546) = 124416 * k + 118273 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 118273) = 186624 * k + 177410 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 177410) = 93312 * k + 88705 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 88705) = 139968 * k + 133058 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 133058) = 69984 * k + 66529 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 66529) = 104976 * k + 99794 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 99794) = 52488 * k + 49897 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 49897) = 78732 * k + 74846 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 74846) = 39366 * k + 37423 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37423) = 59049 * k + 56135 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62299) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62299)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62511_mod_65536 {n : ℕ} (hn : n % 65536 = 62511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62511) = 98304 * k + 93767 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93767) = 147456 * k + 140651 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140651) = 221184 * k + 210977 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 210977) = 331776 * k + 316466 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 316466) = 165888 * k + 158233 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 158233) = 248832 * k + 237350 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 237350) = 124416 * k + 118675 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 118675) = 186624 * k + 178013 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 178013) = 279936 * k + 267020 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 267020) = 139968 * k + 133510 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 133510) = 69984 * k + 66755 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 66755) = 104976 * k + 100133 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 100133) = 157464 * k + 150200 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 150200) = 78732 * k + 75100 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75100) = 39366 * k + 37550 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37550) = 19683 * k + 18775 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62619_mod_65536 {n : ℕ} (hn : n % 65536 = 62619) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62619 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62619) = 98304 * k + 93929 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93929) = 147456 * k + 140894 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140894) = 73728 * k + 70447 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 70447) = 110592 * k + 105671 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 105671) = 165888 * k + 158507 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 158507) = 248832 * k + 237761 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 237761) = 373248 * k + 356642 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 356642) = 186624 * k + 178321 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 178321) = 279936 * k + 267482 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 267482) = 139968 * k + 133741 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 133741) = 209952 * k + 200612 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 200612) = 104976 * k + 100306 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 100306) = 52488 * k + 50153 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50153) = 78732 * k + 75230 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75230) = 39366 * k + 37615 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37615) = 59049 * k + 56423 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62619) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62619)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62631_mod_65536 {n : ℕ} (hn : n % 65536 = 62631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62631) = 98304 * k + 93947 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 93947) = 147456 * k + 140921 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 140921) = 221184 * k + 211382 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 211382) = 110592 * k + 105691 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 105691) = 165888 * k + 158537 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 158537) = 248832 * k + 237806 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 237806) = 124416 * k + 118903 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 118903) = 186624 * k + 178355 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 178355) = 279936 * k + 267533 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 267533) = 419904 * k + 401300 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 401300) = 209952 * k + 200650 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 200650) = 104976 * k + 100325 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 100325) = 157464 * k + 150488 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 150488) = 78732 * k + 75244 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75244) = 39366 * k + 37622 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37622) = 19683 * k + 18811 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62719_mod_65536 {n : ℕ} (hn : n % 65536 = 62719) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62719 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62719) = 98304 * k + 94079 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94079) = 147456 * k + 141119 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141119) = 221184 * k + 211679 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 211679) = 331776 * k + 317519 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 317519) = 497664 * k + 476279 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 476279) = 746496 * k + 714419 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 714419) = 1119744 * k + 1071629 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1071629) = 1679616 * k + 1607444 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1607444) = 839808 * k + 803722 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 803722) = 419904 * k + 401861 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 401861) = 629856 * k + 602792 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 602792) = 314928 * k + 301396 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 301396) = 157464 * k + 150698 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 150698) = 78732 * k + 75349 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75349) = 118098 * k + 113024 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 113024) = 59049 * k + 56512 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62719) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62719)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62943_mod_65536 {n : ℕ} (hn : n % 65536 = 62943) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62943 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62943) = 98304 * k + 94415 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94415) = 147456 * k + 141623 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141623) = 221184 * k + 212435 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 212435) = 331776 * k + 318653 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 318653) = 497664 * k + 477980 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 477980) = 248832 * k + 238990 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 238990) = 124416 * k + 119495 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 119495) = 186624 * k + 179243 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 179243) = 279936 * k + 268865 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 268865) = 419904 * k + 403298 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 403298) = 209952 * k + 201649 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 201649) = 314928 * k + 302474 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 302474) = 157464 * k + 151237 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 151237) = 236196 * k + 226856 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 226856) = 118098 * k + 113428 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 113428) = 59049 * k + 56714 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62943) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62943)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62951_mod_65536 {n : ℕ} (hn : n % 65536 = 62951) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62951 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62951) = 98304 * k + 94427 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94427) = 147456 * k + 141641 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141641) = 221184 * k + 212462 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 212462) = 110592 * k + 106231 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106231) = 165888 * k + 159347 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 159347) = 248832 * k + 239021 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 239021) = 373248 * k + 358532 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 358532) = 186624 * k + 179266 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 179266) = 93312 * k + 89633 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 89633) = 139968 * k + 134450 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 134450) = 69984 * k + 67225 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 67225) = 104976 * k + 100838 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 100838) = 52488 * k + 50419 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50419) = 78732 * k + 75629 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75629) = 118098 * k + 113444 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 113444) = 59049 * k + 56722 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62951) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62951)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_62959_mod_65536 {n : ℕ} (hn : n % 65536 = 62959) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 62959 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 62959) = 98304 * k + 94439 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94439) = 147456 * k + 141659 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141659) = 221184 * k + 212489 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 212489) = 331776 * k + 318734 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 318734) = 165888 * k + 159367 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 159367) = 248832 * k + 239051 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 239051) = 373248 * k + 358577 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 358577) = 559872 * k + 537866 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 537866) = 279936 * k + 268933 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 268933) = 419904 * k + 403400 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 403400) = 209952 * k + 201700 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 201700) = 104976 * k + 100850 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 100850) = 52488 * k + 50425 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50425) = 78732 * k + 75638 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75638) = 39366 * k + 37819 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37819) = 59049 * k + 56729 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 62959) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 62959)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63023_mod_65536 {n : ℕ} (hn : n % 65536 = 63023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63023) = 98304 * k + 94535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94535) = 147456 * k + 141803 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141803) = 221184 * k + 212705 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 212705) = 331776 * k + 319058 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 319058) = 165888 * k + 159529 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 159529) = 248832 * k + 239294 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 239294) = 124416 * k + 119647 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 119647) = 186624 * k + 179471 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 179471) = 279936 * k + 269207 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 269207) = 419904 * k + 403811 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 403811) = 629856 * k + 605717 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 605717) = 944784 * k + 908576 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 908576) = 472392 * k + 454288 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 454288) = 236196 * k + 227144 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 227144) = 118098 * k + 113572 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 113572) = 59049 * k + 56786 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63079_mod_65536 {n : ℕ} (hn : n % 65536 = 63079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63079) = 98304 * k + 94619 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94619) = 147456 * k + 141929 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 141929) = 221184 * k + 212894 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 212894) = 110592 * k + 106447 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106447) = 165888 * k + 159671 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 159671) = 248832 * k + 239507 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 239507) = 373248 * k + 359261 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 359261) = 559872 * k + 538892 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 538892) = 279936 * k + 269446 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 269446) = 139968 * k + 134723 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 134723) = 209952 * k + 202085 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 202085) = 314928 * k + 303128 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 303128) = 157464 * k + 151564 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 151564) = 78732 * k + 75782 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75782) = 39366 * k + 37891 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 37891) = 59049 * k + 56837 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63131_mod_65536 {n : ℕ} (hn : n % 65536 = 63131) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63131 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63131) = 98304 * k + 94697 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94697) = 147456 * k + 142046 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142046) = 73728 * k + 71023 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 71023) = 110592 * k + 106535 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106535) = 165888 * k + 159803 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 159803) = 248832 * k + 239705 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 239705) = 373248 * k + 359558 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 359558) = 186624 * k + 179779 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 179779) = 279936 * k + 269669 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 269669) = 419904 * k + 404504 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 404504) = 209952 * k + 202252 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 202252) = 104976 * k + 101126 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101126) = 52488 * k + 50563 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50563) = 78732 * k + 75845 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 75845) = 118098 * k + 113768 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 113768) = 59049 * k + 56884 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63131) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63131)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63303_mod_65536 {n : ℕ} (hn : n % 65536 = 63303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63303) = 98304 * k + 94955 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94955) = 147456 * k + 142433 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142433) = 221184 * k + 213650 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 213650) = 110592 * k + 106825 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106825) = 165888 * k + 160238 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160238) = 82944 * k + 80119 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 80119) = 124416 * k + 120179 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120179) = 186624 * k + 180269 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180269) = 279936 * k + 270404 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 270404) = 139968 * k + 135202 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135202) = 69984 * k + 67601 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 67601) = 104976 * k + 101402 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101402) = 52488 * k + 50701 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50701) = 78732 * k + 76052 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76052) = 39366 * k + 38026 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38026) = 19683 * k + 19013 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63323_mod_65536 {n : ℕ} (hn : n % 65536 = 63323) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63323 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63323) = 98304 * k + 94985 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 94985) = 147456 * k + 142478 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142478) = 73728 * k + 71239 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 71239) = 110592 * k + 106859 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106859) = 165888 * k + 160289 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160289) = 248832 * k + 240434 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 240434) = 124416 * k + 120217 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120217) = 186624 * k + 180326 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180326) = 93312 * k + 90163 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 90163) = 139968 * k + 135245 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135245) = 209952 * k + 202868 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 202868) = 104976 * k + 101434 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101434) = 52488 * k + 50717 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50717) = 78732 * k + 76076 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76076) = 39366 * k + 38038 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38038) = 19683 * k + 19019 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63323) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63323)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63335_mod_65536 {n : ℕ} (hn : n % 65536 = 63335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63335) = 98304 * k + 95003 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95003) = 147456 * k + 142505 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142505) = 221184 * k + 213758 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 213758) = 110592 * k + 106879 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 106879) = 165888 * k + 160319 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160319) = 248832 * k + 240479 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 240479) = 373248 * k + 360719 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 360719) = 559872 * k + 541079 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 541079) = 839808 * k + 811619 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 811619) = 1259712 * k + 1217429 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 1217429) = 1889568 * k + 1826144 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 1826144) = 944784 * k + 913072 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 913072) = 472392 * k + 456536 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 456536) = 236196 * k + 228268 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 228268) = 118098 * k + 114134 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114134) = 59049 * k + 57067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63359_mod_65536 {n : ℕ} (hn : n % 65536 = 63359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63359) = 98304 * k + 95039 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95039) = 147456 * k + 142559 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142559) = 221184 * k + 213839 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 213839) = 331776 * k + 320759 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 320759) = 497664 * k + 481139 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 481139) = 746496 * k + 721709 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 721709) = 1119744 * k + 1082564 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1082564) = 559872 * k + 541282 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 541282) = 279936 * k + 270641 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 270641) = 419904 * k + 405962 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 405962) = 209952 * k + 202981 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 202981) = 314928 * k + 304472 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 304472) = 157464 * k + 152236 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152236) = 78732 * k + 76118 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76118) = 39366 * k + 38059 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38059) = 59049 * k + 57089 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63391_mod_65536 {n : ℕ} (hn : n % 65536 = 63391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63391) = 98304 * k + 95087 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95087) = 147456 * k + 142631 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142631) = 221184 * k + 213947 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 213947) = 331776 * k + 320921 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 320921) = 497664 * k + 481382 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 481382) = 248832 * k + 240691 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 240691) = 373248 * k + 361037 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 361037) = 559872 * k + 541556 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 541556) = 279936 * k + 270778 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 270778) = 139968 * k + 135389 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135389) = 209952 * k + 203084 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203084) = 104976 * k + 101542 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101542) = 52488 * k + 50771 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 50771) = 78732 * k + 76157 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76157) = 118098 * k + 114236 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114236) = 59049 * k + 57118 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63455_mod_65536 {n : ℕ} (hn : n % 65536 = 63455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63455) = 98304 * k + 95183 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95183) = 147456 * k + 142775 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142775) = 221184 * k + 214163 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214163) = 331776 * k + 321245 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 321245) = 497664 * k + 481868 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 481868) = 248832 * k + 240934 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 240934) = 124416 * k + 120467 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120467) = 186624 * k + 180701 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180701) = 279936 * k + 271052 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271052) = 139968 * k + 135526 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135526) = 69984 * k + 67763 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 67763) = 104976 * k + 101645 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101645) = 157464 * k + 152468 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152468) = 78732 * k + 76234 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76234) = 39366 * k + 38117 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38117) = 59049 * k + 57176 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63483_mod_65536 {n : ℕ} (hn : n % 65536 = 63483) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63483 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63483) = 98304 * k + 95225 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95225) = 147456 * k + 142838 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142838) = 73728 * k + 71419 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 71419) = 110592 * k + 107129 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 107129) = 165888 * k + 160694 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160694) = 82944 * k + 80347 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 80347) = 124416 * k + 120521 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120521) = 186624 * k + 180782 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180782) = 93312 * k + 90391 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 90391) = 139968 * k + 135587 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135587) = 209952 * k + 203381 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203381) = 314928 * k + 305072 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 305072) = 157464 * k + 152536 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152536) = 78732 * k + 76268 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76268) = 39366 * k + 38134 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38134) = 19683 * k + 19067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63483) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63483)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63515_mod_65536 {n : ℕ} (hn : n % 65536 = 63515) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63515 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63515) = 98304 * k + 95273 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95273) = 147456 * k + 142910 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142910) = 73728 * k + 71455 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 71455) = 110592 * k + 107183 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 107183) = 165888 * k + 160775 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160775) = 248832 * k + 241163 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241163) = 373248 * k + 361745 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 361745) = 559872 * k + 542618 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 542618) = 279936 * k + 271309 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271309) = 419904 * k + 406964 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 406964) = 209952 * k + 203482 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203482) = 104976 * k + 101741 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101741) = 157464 * k + 152612 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152612) = 78732 * k + 76306 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76306) = 39366 * k + 38153 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38153) = 59049 * k + 57230 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63515) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63515)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63519_mod_65536 {n : ℕ} (hn : n % 65536 = 63519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63519) = 98304 * k + 95279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95279) = 147456 * k + 142919 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142919) = 221184 * k + 214379 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214379) = 331776 * k + 321569 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 321569) = 497664 * k + 482354 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 482354) = 248832 * k + 241177 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241177) = 373248 * k + 361766 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 361766) = 186624 * k + 180883 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180883) = 279936 * k + 271325 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271325) = 419904 * k + 406988 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 406988) = 209952 * k + 203494 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203494) = 104976 * k + 101747 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101747) = 157464 * k + 152621 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152621) = 236196 * k + 228932 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 228932) = 118098 * k + 114466 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114466) = 59049 * k + 57233 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63535_mod_65536 {n : ℕ} (hn : n % 65536 = 63535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63535) = 98304 * k + 95303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95303) = 147456 * k + 142955 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142955) = 221184 * k + 214433 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214433) = 331776 * k + 321650 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 321650) = 165888 * k + 160825 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160825) = 248832 * k + 241238 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241238) = 124416 * k + 120619 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120619) = 186624 * k + 180929 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180929) = 279936 * k + 271394 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271394) = 139968 * k + 135697 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135697) = 209952 * k + 203546 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203546) = 104976 * k + 101773 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 101773) = 157464 * k + 152660 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152660) = 78732 * k + 76330 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76330) = 39366 * k + 38165 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38165) = 59049 * k + 57248 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63551_mod_65536 {n : ℕ} (hn : n % 65536 = 63551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63551) = 98304 * k + 95327 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95327) = 147456 * k + 142991 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 142991) = 221184 * k + 214487 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214487) = 331776 * k + 321731 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 321731) = 497664 * k + 482597 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 482597) = 746496 * k + 723896 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 723896) = 373248 * k + 361948 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 361948) = 186624 * k + 180974 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 180974) = 93312 * k + 90487 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 90487) = 139968 * k + 135731 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 135731) = 209952 * k + 203597 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203597) = 314928 * k + 305396 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 305396) = 157464 * k + 152698 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152698) = 78732 * k + 76349 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76349) = 118098 * k + 114524 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114524) = 59049 * k + 57262 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63591_mod_65536 {n : ℕ} (hn : n % 65536 = 63591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63591) = 98304 * k + 95387 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95387) = 147456 * k + 143081 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 143081) = 221184 * k + 214622 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214622) = 110592 * k + 107311 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 107311) = 165888 * k + 160967 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160967) = 248832 * k + 241451 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241451) = 373248 * k + 362177 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 362177) = 559872 * k + 543266 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 543266) = 279936 * k + 271633 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271633) = 419904 * k + 407450 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 407450) = 209952 * k + 203725 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 203725) = 314928 * k + 305588 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 305588) = 157464 * k + 152794 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152794) = 78732 * k + 76397 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76397) = 118098 * k + 114596 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114596) = 59049 * k + 57298 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63599_mod_65536 {n : ℕ} (hn : n % 65536 = 63599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63599) = 98304 * k + 95399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95399) = 147456 * k + 143099 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 143099) = 221184 * k + 214649 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214649) = 331776 * k + 321974 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 321974) = 165888 * k + 160987 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 160987) = 248832 * k + 241481 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241481) = 373248 * k + 362222 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 362222) = 186624 * k + 181111 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 181111) = 279936 * k + 271667 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271667) = 419904 * k + 407501 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 407501) = 629856 * k + 611252 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 611252) = 314928 * k + 305626 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 305626) = 157464 * k + 152813 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152813) = 236196 * k + 229220 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 229220) = 118098 * k + 114610 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 114610) = 59049 * k + 57305 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63655_mod_65536 {n : ℕ} (hn : n % 65536 = 63655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63655) = 98304 * k + 95483 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95483) = 147456 * k + 143225 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 143225) = 221184 * k + 214838 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 214838) = 110592 * k + 107419 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 107419) = 165888 * k + 161129 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 161129) = 248832 * k + 241694 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 241694) = 124416 * k + 120847 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 120847) = 186624 * k + 181271 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 181271) = 279936 * k + 271907 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 271907) = 419904 * k + 407861 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 407861) = 629856 * k + 611792 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 611792) = 314928 * k + 305896 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 305896) = 157464 * k + 152948 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 152948) = 78732 * k + 76474 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76474) = 39366 * k + 38237 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38237) = 59049 * k + 57356 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_63903_mod_65536 {n : ℕ} (hn : n % 65536 = 63903) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 63903 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 63903) = 98304 * k + 95855 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 95855) = 147456 * k + 143783 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 143783) = 221184 * k + 215675 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 215675) = 331776 * k + 323513 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 323513) = 497664 * k + 485270 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 485270) = 248832 * k + 242635 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 242635) = 373248 * k + 363953 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 363953) = 559872 * k + 545930 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 545930) = 279936 * k + 272965 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 272965) = 419904 * k + 409448 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 409448) = 209952 * k + 204724 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 204724) = 104976 * k + 102362 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 102362) = 52488 * k + 51181 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 51181) = 78732 * k + 76772 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76772) = 39366 * k + 38386 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38386) = 19683 * k + 19193 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 63903) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 63903)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64047_mod_65536 {n : ℕ} (hn : n % 65536 = 64047) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64047 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64047) = 98304 * k + 96071 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96071) = 147456 * k + 144107 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144107) = 221184 * k + 216161 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 216161) = 331776 * k + 324242 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 324242) = 165888 * k + 162121 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162121) = 248832 * k + 243182 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 243182) = 124416 * k + 121591 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 121591) = 186624 * k + 182387 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 182387) = 279936 * k + 273581 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 273581) = 419904 * k + 410372 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 410372) = 209952 * k + 205186 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 205186) = 104976 * k + 102593 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 102593) = 157464 * k + 153890 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 153890) = 78732 * k + 76945 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 76945) = 118098 * k + 115418 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 115418) = 59049 * k + 57709 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64047) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64047)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64167_mod_65536 {n : ℕ} (hn : n % 65536 = 64167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64167) = 98304 * k + 96251 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96251) = 147456 * k + 144377 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144377) = 221184 * k + 216566 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 216566) = 110592 * k + 108283 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 108283) = 165888 * k + 162425 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162425) = 248832 * k + 243638 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 243638) = 124416 * k + 121819 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 121819) = 186624 * k + 182729 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 182729) = 279936 * k + 274094 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 274094) = 139968 * k + 137047 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137047) = 209952 * k + 205571 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 205571) = 314928 * k + 308357 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 308357) = 472392 * k + 462536 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 462536) = 236196 * k + 231268 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 231268) = 118098 * k + 115634 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 115634) = 59049 * k + 57817 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64207_mod_65536 {n : ℕ} (hn : n % 65536 = 64207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64207) = 98304 * k + 96311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96311) = 147456 * k + 144467 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144467) = 221184 * k + 216701 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 216701) = 331776 * k + 325052 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 325052) = 165888 * k + 162526 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162526) = 82944 * k + 81263 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 81263) = 124416 * k + 121895 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 121895) = 186624 * k + 182843 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 182843) = 279936 * k + 274265 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 274265) = 419904 * k + 411398 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 411398) = 209952 * k + 205699 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 205699) = 314928 * k + 308549 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 308549) = 472392 * k + 462824 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 462824) = 236196 * k + 231412 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 231412) = 118098 * k + 115706 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 115706) = 59049 * k + 57853 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64251_mod_65536 {n : ℕ} (hn : n % 65536 = 64251) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64251 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64251) = 98304 * k + 96377 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96377) = 147456 * k + 144566 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144566) = 73728 * k + 72283 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 72283) = 110592 * k + 108425 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 108425) = 165888 * k + 162638 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162638) = 82944 * k + 81319 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 81319) = 124416 * k + 121979 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 121979) = 186624 * k + 182969 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 182969) = 279936 * k + 274454 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 274454) = 139968 * k + 137227 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137227) = 209952 * k + 205841 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 205841) = 314928 * k + 308762 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 308762) = 157464 * k + 154381 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 154381) = 236196 * k + 231572 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 231572) = 118098 * k + 115786 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 115786) = 59049 * k + 57893 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64251) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64251)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64287_mod_65536 {n : ℕ} (hn : n % 65536 = 64287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64287) = 98304 * k + 96431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96431) = 147456 * k + 144647 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144647) = 221184 * k + 216971 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 216971) = 331776 * k + 325457 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 325457) = 497664 * k + 488186 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 488186) = 248832 * k + 244093 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 244093) = 373248 * k + 366140 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 366140) = 186624 * k + 183070 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 183070) = 93312 * k + 91535 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 91535) = 139968 * k + 137303 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137303) = 209952 * k + 205955 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 205955) = 314928 * k + 308933 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 308933) = 472392 * k + 463400 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 463400) = 236196 * k + 231700 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 231700) = 118098 * k + 115850 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 115850) = 59049 * k + 57925 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64327_mod_65536 {n : ℕ} (hn : n % 65536 = 64327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64327) = 98304 * k + 96491 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96491) = 147456 * k + 144737 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144737) = 221184 * k + 217106 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 217106) = 110592 * k + 108553 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 108553) = 165888 * k + 162830 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162830) = 82944 * k + 81415 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 81415) = 124416 * k + 122123 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 122123) = 186624 * k + 183185 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 183185) = 279936 * k + 274778 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 274778) = 139968 * k + 137389 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137389) = 209952 * k + 206084 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 206084) = 104976 * k + 103042 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103042) = 52488 * k + 51521 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 51521) = 78732 * k + 77282 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77282) = 39366 * k + 38641 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38641) = 59049 * k + 57962 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64367_mod_65536 {n : ℕ} (hn : n % 65536 = 64367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64367) = 98304 * k + 96551 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96551) = 147456 * k + 144827 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 144827) = 221184 * k + 217241 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 217241) = 331776 * k + 325862 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 325862) = 165888 * k + 162931 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 162931) = 248832 * k + 244397 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 244397) = 373248 * k + 366596 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 366596) = 186624 * k + 183298 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 183298) = 93312 * k + 91649 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 91649) = 139968 * k + 137474 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137474) = 69984 * k + 68737 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 68737) = 104976 * k + 103106 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103106) = 52488 * k + 51553 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 51553) = 78732 * k + 77330 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77330) = 39366 * k + 38665 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38665) = 59049 * k + 57998 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64447_mod_65536 {n : ℕ} (hn : n % 65536 = 64447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64447) = 98304 * k + 96671 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96671) = 147456 * k + 145007 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145007) = 221184 * k + 217511 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 217511) = 331776 * k + 326267 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 326267) = 497664 * k + 489401 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 489401) = 746496 * k + 734102 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 734102) = 373248 * k + 367051 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 367051) = 559872 * k + 550577 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 550577) = 839808 * k + 825866 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 825866) = 419904 * k + 412933 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 412933) = 629856 * k + 619400 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 619400) = 314928 * k + 309700 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 309700) = 157464 * k + 154850 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 154850) = 78732 * k + 77425 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77425) = 118098 * k + 116138 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116138) = 59049 * k + 58069 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64479_mod_65536 {n : ℕ} (hn : n % 65536 = 64479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64479) = 98304 * k + 96719 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96719) = 147456 * k + 145079 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145079) = 221184 * k + 217619 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 217619) = 331776 * k + 326429 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 326429) = 497664 * k + 489644 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 489644) = 248832 * k + 244822 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 244822) = 124416 * k + 122411 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 122411) = 186624 * k + 183617 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 183617) = 279936 * k + 275426 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 275426) = 139968 * k + 137713 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137713) = 209952 * k + 206570 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 206570) = 104976 * k + 103285 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103285) = 157464 * k + 154928 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 154928) = 78732 * k + 77464 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77464) = 39366 * k + 38732 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38732) = 19683 * k + 19366 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64507_mod_65536 {n : ℕ} (hn : n % 65536 = 64507) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64507 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64507) = 98304 * k + 96761 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96761) = 147456 * k + 145142 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145142) = 73728 * k + 72571 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 72571) = 110592 * k + 108857 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 108857) = 165888 * k + 163286 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 163286) = 82944 * k + 81643 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 81643) = 124416 * k + 122465 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 122465) = 186624 * k + 183698 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 183698) = 93312 * k + 91849 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 91849) = 139968 * k + 137774 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 137774) = 69984 * k + 68887 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 68887) = 104976 * k + 103331 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103331) = 157464 * k + 154997 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 154997) = 236196 * k + 232496 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 232496) = 118098 * k + 116248 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116248) = 59049 * k + 58124 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64507) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64507)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64539_mod_65536 {n : ℕ} (hn : n % 65536 = 64539) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64539 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64539) = 98304 * k + 96809 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 96809) = 147456 * k + 145214 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145214) = 73728 * k + 72607 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 72607) = 110592 * k + 108911 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 108911) = 165888 * k + 163367 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 163367) = 248832 * k + 245051 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 245051) = 373248 * k + 367577 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 367577) = 559872 * k + 551366 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 551366) = 279936 * k + 275683 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 275683) = 419904 * k + 413525 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 413525) = 629856 * k + 620288 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 620288) = 314928 * k + 310144 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 310144) = 157464 * k + 155072 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 155072) = 78732 * k + 77536 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77536) = 39366 * k + 38768 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38768) = 19683 * k + 19384 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64539) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64539)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64667_mod_65536 {n : ℕ} (hn : n % 65536 = 64667) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64667 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64667) = 98304 * k + 97001 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97001) = 147456 * k + 145502 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145502) = 73728 * k + 72751 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 72751) = 110592 * k + 109127 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109127) = 165888 * k + 163691 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 163691) = 248832 * k + 245537 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 245537) = 373248 * k + 368306 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 368306) = 186624 * k + 184153 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 184153) = 279936 * k + 276230 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 276230) = 139968 * k + 138115 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 138115) = 209952 * k + 207173 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 207173) = 314928 * k + 310760 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 310760) = 157464 * k + 155380 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 155380) = 78732 * k + 77690 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77690) = 39366 * k + 38845 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38845) = 59049 * k + 58268 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64667) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64667)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64719_mod_65536 {n : ℕ} (hn : n % 65536 = 64719) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64719 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64719) = 98304 * k + 97079 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97079) = 147456 * k + 145619 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145619) = 221184 * k + 218429 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 218429) = 331776 * k + 327644 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 327644) = 165888 * k + 163822 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 163822) = 82944 * k + 81911 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 81911) = 124416 * k + 122867 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 122867) = 186624 * k + 184301 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 184301) = 279936 * k + 276452 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 276452) = 139968 * k + 138226 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 138226) = 69984 * k + 69113 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69113) = 104976 * k + 103670 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103670) = 52488 * k + 51835 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 51835) = 78732 * k + 77753 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77753) = 118098 * k + 116630 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116630) = 59049 * k + 58315 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64719) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64719)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64831_mod_65536 {n : ℕ} (hn : n % 65536 = 64831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64831) = 98304 * k + 97247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97247) = 147456 * k + 145871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145871) = 221184 * k + 218807 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 218807) = 331776 * k + 328211 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 328211) = 497664 * k + 492317 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 492317) = 746496 * k + 738476 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 738476) = 373248 * k + 369238 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 369238) = 186624 * k + 184619 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 184619) = 279936 * k + 276929 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 276929) = 419904 * k + 415394 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 415394) = 209952 * k + 207697 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 207697) = 314928 * k + 311546 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 311546) = 157464 * k + 155773 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 155773) = 236196 * k + 233660 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 233660) = 118098 * k + 116830 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116830) = 59049 * k + 58415 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64839_mod_65536 {n : ℕ} (hn : n % 65536 = 64839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64839) = 98304 * k + 97259 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97259) = 147456 * k + 145889 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145889) = 221184 * k + 218834 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 218834) = 110592 * k + 109417 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109417) = 165888 * k + 164126 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164126) = 82944 * k + 82063 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 82063) = 124416 * k + 123095 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 123095) = 186624 * k + 184643 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 184643) = 279936 * k + 276965 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 276965) = 419904 * k + 415448 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 415448) = 209952 * k + 207724 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 207724) = 104976 * k + 103862 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103862) = 52488 * k + 51931 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 51931) = 78732 * k + 77897 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77897) = 118098 * k + 116846 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116846) = 59049 * k + 58423 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64871_mod_65536 {n : ℕ} (hn : n % 65536 = 64871) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64871 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64871) = 98304 * k + 97307 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97307) = 147456 * k + 145961 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 145961) = 221184 * k + 218942 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 218942) = 110592 * k + 109471 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109471) = 165888 * k + 164207 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164207) = 248832 * k + 246311 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 246311) = 373248 * k + 369467 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 369467) = 559872 * k + 554201 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 554201) = 839808 * k + 831302 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 831302) = 419904 * k + 415651 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 415651) = 629856 * k + 623477 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 623477) = 944784 * k + 935216 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 935216) = 472392 * k + 467608 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 467608) = 236196 * k + 233804 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 233804) = 118098 * k + 116902 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 116902) = 59049 * k + 58451 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64871) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64871)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_64923_mod_65536 {n : ℕ} (hn : n % 65536 = 64923) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 64923 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 64923) = 98304 * k + 97385 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97385) = 147456 * k + 146078 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146078) = 73728 * k + 73039 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 73039) = 110592 * k + 109559 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109559) = 165888 * k + 164339 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164339) = 248832 * k + 246509 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 246509) = 373248 * k + 369764 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 369764) = 186624 * k + 184882 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 184882) = 93312 * k + 92441 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 92441) = 139968 * k + 138662 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 138662) = 69984 * k + 69331 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69331) = 104976 * k + 103997 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 103997) = 157464 * k + 155996 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 155996) = 78732 * k + 77998 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 77998) = 39366 * k + 38999 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 38999) = 59049 * k + 58499 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 64923) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 64923)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65007_mod_65536 {n : ℕ} (hn : n % 65536 = 65007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65007) = 98304 * k + 97511 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97511) = 147456 * k + 146267 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146267) = 221184 * k + 219401 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 219401) = 331776 * k + 329102 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 329102) = 165888 * k + 164551 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164551) = 248832 * k + 246827 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 246827) = 373248 * k + 370241 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 370241) = 559872 * k + 555362 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 555362) = 279936 * k + 277681 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 277681) = 419904 * k + 416522 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 416522) = 209952 * k + 208261 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 208261) = 314928 * k + 312392 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 312392) = 157464 * k + 156196 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 156196) = 78732 * k + 78098 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78098) = 39366 * k + 39049 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39049) = 59049 * k + 58574 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65127_mod_65536 {n : ℕ} (hn : n % 65536 = 65127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65127) = 98304 * k + 97691 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97691) = 147456 * k + 146537 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146537) = 221184 * k + 219806 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 219806) = 110592 * k + 109903 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109903) = 165888 * k + 164855 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164855) = 248832 * k + 247283 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 247283) = 373248 * k + 370925 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 370925) = 559872 * k + 556388 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 556388) = 279936 * k + 278194 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 278194) = 139968 * k + 139097 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139097) = 209952 * k + 208646 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 208646) = 104976 * k + 104323 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104323) = 157464 * k + 156485 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 156485) = 236196 * k + 234728 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 234728) = 118098 * k + 117364 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117364) = 59049 * k + 58682 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65179_mod_65536 {n : ℕ} (hn : n % 65536 = 65179) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65179 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65179) = 98304 * k + 97769 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97769) = 147456 * k + 146654 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146654) = 73728 * k + 73327 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 73327) = 110592 * k + 109991 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 109991) = 165888 * k + 164987 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 164987) = 248832 * k + 247481 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 247481) = 373248 * k + 371222 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 371222) = 186624 * k + 185611 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 185611) = 279936 * k + 278417 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 278417) = 419904 * k + 417626 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 417626) = 209952 * k + 208813 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 208813) = 314928 * k + 313220 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 313220) = 157464 * k + 156610 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 156610) = 78732 * k + 78305 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78305) = 118098 * k + 117458 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117458) = 59049 * k + 58729 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65179) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65179)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65183_mod_65536 {n : ℕ} (hn : n % 65536 = 65183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65183) = 98304 * k + 97775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97775) = 147456 * k + 146663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146663) = 221184 * k + 219995 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 219995) = 331776 * k + 329993 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 329993) = 497664 * k + 494990 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 494990) = 248832 * k + 247495 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 247495) = 373248 * k + 371243 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 371243) = 559872 * k + 556865 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 556865) = 839808 * k + 835298 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 835298) = 419904 * k + 417649 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 417649) = 629856 * k + 626474 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 626474) = 314928 * k + 313237 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 313237) = 472392 * k + 469856 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 469856) = 236196 * k + 234928 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 234928) = 118098 * k + 117464 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117464) = 59049 * k + 58732 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65191_mod_65536 {n : ℕ} (hn : n % 65536 = 65191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65191) = 98304 * k + 97787 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97787) = 147456 * k + 146681 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146681) = 221184 * k + 220022 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220022) = 110592 * k + 110011 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 110011) = 165888 * k + 165017 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 165017) = 248832 * k + 247526 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 247526) = 124416 * k + 123763 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 123763) = 186624 * k + 185645 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 185645) = 279936 * k + 278468 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 278468) = 139968 * k + 139234 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139234) = 69984 * k + 69617 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69617) = 104976 * k + 104426 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104426) = 52488 * k + 52213 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 52213) = 78732 * k + 78320 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78320) = 39366 * k + 39160 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39160) = 19683 * k + 19580 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65275_mod_65536 {n : ℕ} (hn : n % 65536 = 65275) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65275 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65275) = 98304 * k + 97913 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97913) = 147456 * k + 146870 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146870) = 73728 * k + 73435 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 73435) = 110592 * k + 110153 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 110153) = 165888 * k + 165230 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 165230) = 82944 * k + 82615 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 82615) = 124416 * k + 123923 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 123923) = 186624 * k + 185885 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 185885) = 279936 * k + 278828 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 278828) = 139968 * k + 139414 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139414) = 69984 * k + 69707 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69707) = 104976 * k + 104561 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104561) = 157464 * k + 156842 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 156842) = 78732 * k + 78421 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78421) = 118098 * k + 117632 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117632) = 59049 * k + 58816 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65275) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65275)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65311_mod_65536 {n : ℕ} (hn : n % 65536 = 65311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65311) = 98304 * k + 97967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 97967) = 147456 * k + 146951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 146951) = 221184 * k + 220427 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220427) = 331776 * k + 330641 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 330641) = 497664 * k + 495962 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 495962) = 248832 * k + 247981 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 247981) = 373248 * k + 371972 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 371972) = 186624 * k + 185986 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 185986) = 93312 * k + 92993 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 92993) = 139968 * k + 139490 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139490) = 69984 * k + 69745 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69745) = 104976 * k + 104618 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104618) = 52488 * k + 52309 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 52309) = 78732 * k + 78464 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78464) = 39366 * k + 39232 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39232) = 19683 * k + 19616 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65343_mod_65536 {n : ℕ} (hn : n % 65536 = 65343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65343) = 98304 * k + 98015 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 98015) = 147456 * k + 147023 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 147023) = 221184 * k + 220535 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220535) = 331776 * k + 330803 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 330803) = 497664 * k + 496205 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 496205) = 746496 * k + 744308 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 744308) = 373248 * k + 372154 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 372154) = 186624 * k + 186077 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 186077) = 279936 * k + 279116 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 279116) = 139968 * k + 139558 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139558) = 69984 * k + 69779 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 69779) = 104976 * k + 104669 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104669) = 157464 * k + 157004 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 157004) = 78732 * k + 78502 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78502) = 39366 * k + 39251 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39251) = 59049 * k + 58877 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65371_mod_65536 {n : ℕ} (hn : n % 65536 = 65371) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65371 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65371) = 98304 * k + 98057 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 98057) = 147456 * k + 147086 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 147086) = 73728 * k + 73543 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 73543) = 110592 * k + 110315 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 110315) = 165888 * k + 165473 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 165473) = 248832 * k + 248210 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 248210) = 124416 * k + 124105 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 124105) = 186624 * k + 186158 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 186158) = 93312 * k + 93079 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 93079) = 139968 * k + 139619 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139619) = 209952 * k + 209429 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 209429) = 314928 * k + 314144 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 314144) = 157464 * k + 157072 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 157072) = 78732 * k + 78536 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78536) = 39366 * k + 39268 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39268) = 19683 * k + 19634 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65371) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65371)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65391_mod_65536 {n : ℕ} (hn : n % 65536 = 65391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65391) = 98304 * k + 98087 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 98087) = 147456 * k + 147131 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 147131) = 221184 * k + 220697 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220697) = 331776 * k + 331046 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 331046) = 165888 * k + 165523 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 165523) = 248832 * k + 248285 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 248285) = 373248 * k + 372428 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 372428) = 186624 * k + 186214 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 186214) = 93312 * k + 93107 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 93107) = 139968 * k + 139661 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139661) = 209952 * k + 209492 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 209492) = 104976 * k + 104746 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104746) = 52488 * k + 52373 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 52373) = 78732 * k + 78560 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78560) = 39366 * k + 39280 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 39280) = 19683 * k + 19640 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65407_mod_65536 {n : ℕ} (hn : n % 65536 = 65407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65407) = 98304 * k + 98111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 98111) = 147456 * k + 147167 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 147167) = 221184 * k + 220751 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220751) = 331776 * k + 331127 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 331127) = 497664 * k + 496691 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 496691) = 746496 * k + 745037 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 745037) = 1119744 * k + 1117556 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 1117556) = 559872 * k + 558778 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 558778) = 279936 * k + 279389 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 279389) = 419904 * k + 419084 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 419084) = 209952 * k + 209542 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 209542) = 104976 * k + 104771 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 104771) = 157464 * k + 157157 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 157157) = 236196 * k + 235736 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 235736) = 118098 * k + 117868 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117868) = 59049 * k + 58934 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_65439_mod_65536 {n : ℕ} (hn : n % 65536 = 65439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 65439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 65439) = 98304 * k + 98159 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 98159) = 147456 * k + 147239 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 147239) = 221184 * k + 220859 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 220859) = 331776 * k + 331289 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 331289) = 497664 * k + 496934 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 496934) = 248832 * k + 248467 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 248467) = 373248 * k + 372701 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 372701) = 559872 * k + 559052 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 559052) = 279936 * k + 279526 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 279526) = 139968 * k + 139763 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 139763) = 209952 * k + 209645 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 209645) = 314928 * k + 314468 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 314468) = 157464 * k + 157234 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 157234) = 78732 * k + 78617 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 78617) = 118098 * k + 117926 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 117926) = 59049 * k + 58963 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 65439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 65439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
