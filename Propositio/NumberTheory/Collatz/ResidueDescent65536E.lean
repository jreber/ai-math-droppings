import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_33087_mod_65536 {n : ℕ} (hn : n % 65536 = 33087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33087) = 98304 * k + 49631 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49631) = 147456 * k + 74447 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74447) = 221184 * k + 111671 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111671) = 331776 * k + 167507 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 167507) = 497664 * k + 251261 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 251261) = 746496 * k + 376892 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 376892) = 373248 * k + 188446 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 188446) = 186624 * k + 94223 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 94223) = 279936 * k + 141335 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 141335) = 419904 * k + 212003 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 212003) = 629856 * k + 318005 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 318005) = 944784 * k + 477008 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 477008) = 472392 * k + 238504 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 238504) = 236196 * k + 119252 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 119252) = 118098 * k + 59626 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59626) = 59049 * k + 29813 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33179_mod_65536 {n : ℕ} (hn : n % 65536 = 33179) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33179 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33179) = 98304 * k + 49769 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49769) = 147456 * k + 74654 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74654) = 73728 * k + 37327 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 37327) = 110592 * k + 55991 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 55991) = 165888 * k + 83987 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 83987) = 248832 * k + 125981 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 125981) = 373248 * k + 188972 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 188972) = 186624 * k + 94486 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 94486) = 93312 * k + 47243 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 47243) = 139968 * k + 70865 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 70865) = 209952 * k + 106298 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 106298) = 104976 * k + 53149 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53149) = 157464 * k + 79724 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79724) = 78732 * k + 39862 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39862) = 39366 * k + 19931 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19931) = 59049 * k + 29897 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33179) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33179)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33183_mod_65536 {n : ℕ} (hn : n % 65536 = 33183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33183) = 98304 * k + 49775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49775) = 147456 * k + 74663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74663) = 221184 * k + 111995 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 111995) = 331776 * k + 167993 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 167993) = 497664 * k + 251990 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 251990) = 248832 * k + 125995 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 125995) = 373248 * k + 188993 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 188993) = 559872 * k + 283490 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 283490) = 279936 * k + 141745 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 141745) = 419904 * k + 212618 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 212618) = 209952 * k + 106309 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 106309) = 314928 * k + 159464 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 159464) = 157464 * k + 79732 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79732) = 78732 * k + 39866 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39866) = 39366 * k + 19933 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 19933) = 59049 * k + 29900 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33255_mod_65536 {n : ℕ} (hn : n % 65536 = 33255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33255) = 98304 * k + 49883 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49883) = 147456 * k + 74825 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74825) = 221184 * k + 112238 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 112238) = 110592 * k + 56119 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 56119) = 165888 * k + 84179 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 84179) = 248832 * k + 126269 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 126269) = 373248 * k + 189404 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 189404) = 186624 * k + 94702 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 94702) = 93312 * k + 47351 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 47351) = 139968 * k + 71027 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71027) = 209952 * k + 106541 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 106541) = 314928 * k + 159812 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 159812) = 157464 * k + 79906 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 79906) = 78732 * k + 39953 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 39953) = 118098 * k + 59930 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 59930) = 59049 * k + 29965 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33307_mod_65536 {n : ℕ} (hn : n % 65536 = 33307) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33307 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33307) = 98304 * k + 49961 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 49961) = 147456 * k + 74942 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 74942) = 73728 * k + 37471 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 37471) = 110592 * k + 56207 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 56207) = 165888 * k + 84311 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 84311) = 248832 * k + 126467 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 126467) = 373248 * k + 189701 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 189701) = 559872 * k + 284552 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 284552) = 279936 * k + 142276 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 142276) = 139968 * k + 71138 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71138) = 69984 * k + 35569 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 35569) = 104976 * k + 53354 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53354) = 52488 * k + 26677 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26677) = 78732 * k + 40016 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40016) = 39366 * k + 20008 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20008) = 19683 * k + 10004 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33307) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33307)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33447_mod_65536 {n : ℕ} (hn : n % 65536 = 33447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33447) = 98304 * k + 50171 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50171) = 147456 * k + 75257 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75257) = 221184 * k + 112886 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 112886) = 110592 * k + 56443 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 56443) = 165888 * k + 84665 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 84665) = 248832 * k + 126998 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 126998) = 124416 * k + 63499 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 63499) = 186624 * k + 95249 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95249) = 279936 * k + 142874 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 142874) = 139968 * k + 71437 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71437) = 209952 * k + 107156 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107156) = 104976 * k + 53578 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53578) = 52488 * k + 26789 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26789) = 78732 * k + 40184 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40184) = 39366 * k + 20092 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20092) = 19683 * k + 10046 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33487_mod_65536 {n : ℕ} (hn : n % 65536 = 33487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33487) = 98304 * k + 50231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50231) = 147456 * k + 75347 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75347) = 221184 * k + 113021 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 113021) = 331776 * k + 169532 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 169532) = 165888 * k + 84766 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 84766) = 82944 * k + 42383 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 42383) = 124416 * k + 63575 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 63575) = 186624 * k + 95363 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95363) = 279936 * k + 143045 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 143045) = 419904 * k + 214568 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 214568) = 209952 * k + 107284 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107284) = 104976 * k + 53642 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53642) = 52488 * k + 26821 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26821) = 78732 * k + 40232 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40232) = 39366 * k + 20116 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20116) = 19683 * k + 10058 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33531_mod_65536 {n : ℕ} (hn : n % 65536 = 33531) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33531 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33531) = 98304 * k + 50297 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50297) = 147456 * k + 75446 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75446) = 73728 * k + 37723 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 37723) = 110592 * k + 56585 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 56585) = 165888 * k + 84878 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 84878) = 82944 * k + 42439 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 42439) = 124416 * k + 63659 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 63659) = 186624 * k + 95489 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95489) = 279936 * k + 143234 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 143234) = 139968 * k + 71617 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71617) = 209952 * k + 107426 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107426) = 104976 * k + 53713 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53713) = 157464 * k + 80570 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 80570) = 78732 * k + 40285 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40285) = 118098 * k + 60428 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 60428) = 59049 * k + 30214 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33531) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33531)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33567_mod_65536 {n : ℕ} (hn : n % 65536 = 33567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33567) = 98304 * k + 50351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50351) = 147456 * k + 75527 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75527) = 221184 * k + 113291 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 113291) = 331776 * k + 169937 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 169937) = 497664 * k + 254906 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 254906) = 248832 * k + 127453 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 127453) = 373248 * k + 191180 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 191180) = 186624 * k + 95590 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95590) = 93312 * k + 47795 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 47795) = 139968 * k + 71693 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71693) = 209952 * k + 107540 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107540) = 104976 * k + 53770 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53770) = 52488 * k + 26885 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 26885) = 78732 * k + 40328 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40328) = 39366 * k + 20164 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20164) = 19683 * k + 10082 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33599_mod_65536 {n : ℕ} (hn : n % 65536 = 33599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33599) = 98304 * k + 50399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50399) = 147456 * k + 75599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75599) = 221184 * k + 113399 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 113399) = 331776 * k + 170099 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 170099) = 497664 * k + 255149 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 255149) = 746496 * k + 382724 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 382724) = 373248 * k + 191362 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 191362) = 186624 * k + 95681 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95681) = 279936 * k + 143522 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 143522) = 139968 * k + 71761 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71761) = 209952 * k + 107642 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107642) = 104976 * k + 53821 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 53821) = 157464 * k + 80732 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 80732) = 78732 * k + 40366 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40366) = 39366 * k + 20183 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20183) = 59049 * k + 30275 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33607_mod_65536 {n : ℕ} (hn : n % 65536 = 33607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33607) = 98304 * k + 50411 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50411) = 147456 * k + 75617 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75617) = 221184 * k + 113426 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 113426) = 110592 * k + 56713 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 56713) = 165888 * k + 85070 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 85070) = 82944 * k + 42535 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 42535) = 124416 * k + 63803 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 63803) = 186624 * k + 95705 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 95705) = 279936 * k + 143558 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 143558) = 139968 * k + 71779 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 71779) = 209952 * k + 107669 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 107669) = 314928 * k + 161504 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 161504) = 157464 * k + 80752 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 80752) = 78732 * k + 40376 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40376) = 39366 * k + 20188 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20188) = 19683 * k + 10094 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33663_mod_65536 {n : ℕ} (hn : n % 65536 = 33663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33663) = 98304 * k + 50495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50495) = 147456 * k + 75743 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 75743) = 221184 * k + 113615 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 113615) = 331776 * k + 170423 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 170423) = 497664 * k + 255635 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 255635) = 746496 * k + 383453 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 383453) = 1119744 * k + 575180 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 575180) = 559872 * k + 287590 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 287590) = 279936 * k + 143795 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 143795) = 419904 * k + 215693 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 215693) = 629856 * k + 323540 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 323540) = 314928 * k + 161770 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 161770) = 157464 * k + 80885 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 80885) = 236196 * k + 121328 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 121328) = 118098 * k + 60664 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 60664) = 59049 * k + 30332 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33863_mod_65536 {n : ℕ} (hn : n % 65536 = 33863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33863) = 98304 * k + 50795 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50795) = 147456 * k + 76193 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 76193) = 221184 * k + 114290 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 114290) = 110592 * k + 57145 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 57145) = 165888 * k + 85718 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 85718) = 82944 * k + 42859 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 42859) = 124416 * k + 64289 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 64289) = 186624 * k + 96434 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 96434) = 93312 * k + 48217 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 48217) = 139968 * k + 72326 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 72326) = 69984 * k + 36163 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 36163) = 104976 * k + 54245 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 54245) = 157464 * k + 81368 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 81368) = 78732 * k + 40684 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40684) = 39366 * k + 20342 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20342) = 19683 * k + 10171 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_33919_mod_65536 {n : ℕ} (hn : n % 65536 = 33919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 33919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 33919) = 98304 * k + 50879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 50879) = 147456 * k + 76319 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 76319) = 221184 * k + 114479 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 114479) = 331776 * k + 171719 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 171719) = 497664 * k + 257579 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 257579) = 746496 * k + 386369 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 386369) = 1119744 * k + 579554 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 579554) = 559872 * k + 289777 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 289777) = 839808 * k + 434666 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 434666) = 419904 * k + 217333 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 217333) = 629856 * k + 326000 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 326000) = 314928 * k + 163000 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 163000) = 157464 * k + 81500 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 81500) = 78732 * k + 40750 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40750) = 39366 * k + 20375 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20375) = 59049 * k + 30563 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 33919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 33919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34043_mod_65536 {n : ℕ} (hn : n % 65536 = 34043) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34043 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34043) = 98304 * k + 51065 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51065) = 147456 * k + 76598 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 76598) = 73728 * k + 38299 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 38299) = 110592 * k + 57449 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 57449) = 165888 * k + 86174 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 86174) = 82944 * k + 43087 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 43087) = 124416 * k + 64631 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 64631) = 186624 * k + 96947 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 96947) = 279936 * k + 145421 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 145421) = 419904 * k + 218132 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 218132) = 209952 * k + 109066 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 109066) = 104976 * k + 54533 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 54533) = 157464 * k + 81800 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 81800) = 78732 * k + 40900 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40900) = 39366 * k + 20450 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20450) = 19683 * k + 10225 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34043) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34043)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34111_mod_65536 {n : ℕ} (hn : n % 65536 = 34111) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34111 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34111) = 98304 * k + 51167 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51167) = 147456 * k + 76751 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 76751) = 221184 * k + 115127 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 115127) = 331776 * k + 172691 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 172691) = 497664 * k + 259037 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 259037) = 746496 * k + 388556 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 388556) = 373248 * k + 194278 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 194278) = 186624 * k + 97139 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 97139) = 279936 * k + 145709 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 145709) = 419904 * k + 218564 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 218564) = 209952 * k + 109282 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 109282) = 104976 * k + 54641 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 54641) = 157464 * k + 81962 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 81962) = 78732 * k + 40981 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 40981) = 118098 * k + 61472 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 61472) = 59049 * k + 30736 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34111) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34111)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34151_mod_65536 {n : ℕ} (hn : n % 65536 = 34151) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34151 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34151) = 98304 * k + 51227 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51227) = 147456 * k + 76841 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 76841) = 221184 * k + 115262 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 115262) = 110592 * k + 57631 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 57631) = 165888 * k + 86447 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 86447) = 248832 * k + 129671 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 129671) = 373248 * k + 194507 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 194507) = 559872 * k + 291761 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 291761) = 839808 * k + 437642 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 437642) = 419904 * k + 218821 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 218821) = 629856 * k + 328232 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 328232) = 314928 * k + 164116 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 164116) = 157464 * k + 82058 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 82058) = 78732 * k + 41029 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41029) = 118098 * k + 61544 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 61544) = 59049 * k + 30772 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34151) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34151)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34255_mod_65536 {n : ℕ} (hn : n % 65536 = 34255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34255) = 98304 * k + 51383 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51383) = 147456 * k + 77075 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77075) = 221184 * k + 115613 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 115613) = 331776 * k + 173420 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 173420) = 165888 * k + 86710 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 86710) = 82944 * k + 43355 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 43355) = 124416 * k + 65033 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 65033) = 186624 * k + 97550 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 97550) = 93312 * k + 48775 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 48775) = 139968 * k + 73163 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 73163) = 209952 * k + 109745 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 109745) = 314928 * k + 164618 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 164618) = 157464 * k + 82309 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 82309) = 236196 * k + 123464 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 123464) = 118098 * k + 61732 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 61732) = 59049 * k + 30866 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34271_mod_65536 {n : ℕ} (hn : n % 65536 = 34271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34271) = 98304 * k + 51407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51407) = 147456 * k + 77111 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77111) = 221184 * k + 115667 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 115667) = 331776 * k + 173501 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 173501) = 497664 * k + 260252 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 260252) = 248832 * k + 130126 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 130126) = 124416 * k + 65063 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 65063) = 186624 * k + 97595 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 97595) = 279936 * k + 146393 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 146393) = 419904 * k + 219590 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 219590) = 209952 * k + 109795 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 109795) = 314928 * k + 164693 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 164693) = 472392 * k + 247040 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 247040) = 236196 * k + 123520 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 123520) = 118098 * k + 61760 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 61760) = 59049 * k + 30880 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34331_mod_65536 {n : ℕ} (hn : n % 65536 = 34331) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34331 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34331) = 98304 * k + 51497 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51497) = 147456 * k + 77246 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77246) = 73728 * k + 38623 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 38623) = 110592 * k + 57935 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 57935) = 165888 * k + 86903 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 86903) = 248832 * k + 130355 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 130355) = 373248 * k + 195533 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 195533) = 559872 * k + 293300 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 293300) = 279936 * k + 146650 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 146650) = 139968 * k + 73325 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 73325) = 209952 * k + 109988 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 109988) = 104976 * k + 54994 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 54994) = 52488 * k + 27497 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 27497) = 78732 * k + 41246 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41246) = 39366 * k + 20623 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20623) = 59049 * k + 30935 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34331) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34331)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34535_mod_65536 {n : ℕ} (hn : n % 65536 = 34535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34535) = 98304 * k + 51803 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51803) = 147456 * k + 77705 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77705) = 221184 * k + 116558 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 116558) = 110592 * k + 58279 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 58279) = 165888 * k + 87419 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 87419) = 248832 * k + 131129 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 131129) = 373248 * k + 196694 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 196694) = 186624 * k + 98347 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 98347) = 279936 * k + 147521 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 147521) = 419904 * k + 221282 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 221282) = 209952 * k + 110641 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 110641) = 314928 * k + 165962 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 165962) = 157464 * k + 82981 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 82981) = 236196 * k + 124472 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 124472) = 118098 * k + 62236 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62236) = 59049 * k + 31118 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34543_mod_65536 {n : ℕ} (hn : n % 65536 = 34543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34543) = 98304 * k + 51815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51815) = 147456 * k + 77723 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77723) = 221184 * k + 116585 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 116585) = 331776 * k + 174878 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 174878) = 165888 * k + 87439 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 87439) = 248832 * k + 131159 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 131159) = 373248 * k + 196739 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 196739) = 559872 * k + 295109 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 295109) = 839808 * k + 442664 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 442664) = 419904 * k + 221332 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 221332) = 209952 * k + 110666 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 110666) = 104976 * k + 55333 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55333) = 157464 * k + 83000 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 83000) = 78732 * k + 41500 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41500) = 39366 * k + 20750 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20750) = 19683 * k + 10375 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34631_mod_65536 {n : ℕ} (hn : n % 65536 = 34631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34631) = 98304 * k + 51947 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51947) = 147456 * k + 77921 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77921) = 221184 * k + 116882 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 116882) = 110592 * k + 58441 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 58441) = 165888 * k + 87662 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 87662) = 82944 * k + 43831 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 43831) = 124416 * k + 65747 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 65747) = 186624 * k + 98621 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 98621) = 279936 * k + 147932 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 147932) = 139968 * k + 73966 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 73966) = 69984 * k + 36983 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 36983) = 104976 * k + 55475 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55475) = 157464 * k + 83213 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 83213) = 236196 * k + 124820 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 124820) = 118098 * k + 62410 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62410) = 59049 * k + 31205 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34651_mod_65536 {n : ℕ} (hn : n % 65536 = 34651) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34651 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34651) = 98304 * k + 51977 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 51977) = 147456 * k + 77966 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 77966) = 73728 * k + 38983 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 38983) = 110592 * k + 58475 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 58475) = 165888 * k + 87713 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 87713) = 248832 * k + 131570 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 131570) = 124416 * k + 65785 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 65785) = 186624 * k + 98678 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 98678) = 93312 * k + 49339 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 49339) = 139968 * k + 74009 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74009) = 209952 * k + 111014 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111014) = 104976 * k + 55507 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55507) = 157464 * k + 83261 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 83261) = 236196 * k + 124892 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 124892) = 118098 * k + 62446 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62446) = 59049 * k + 31223 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34651) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34651)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34671_mod_65536 {n : ℕ} (hn : n % 65536 = 34671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34671) = 98304 * k + 52007 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52007) = 147456 * k + 78011 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78011) = 221184 * k + 117017 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117017) = 331776 * k + 175526 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 175526) = 165888 * k + 87763 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 87763) = 248832 * k + 131645 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 131645) = 373248 * k + 197468 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 197468) = 186624 * k + 98734 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 98734) = 93312 * k + 49367 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 49367) = 139968 * k + 74051 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74051) = 209952 * k + 111077 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111077) = 314928 * k + 166616 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 166616) = 157464 * k + 83308 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 83308) = 78732 * k + 41654 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41654) = 39366 * k + 20827 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20827) = 59049 * k + 31241 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34751_mod_65536 {n : ℕ} (hn : n % 65536 = 34751) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34751 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34751) = 98304 * k + 52127 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52127) = 147456 * k + 78191 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78191) = 221184 * k + 117287 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117287) = 331776 * k + 175931 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 175931) = 497664 * k + 263897 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 263897) = 746496 * k + 395846 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 395846) = 373248 * k + 197923 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 197923) = 559872 * k + 296885 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 296885) = 839808 * k + 445328 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 445328) = 419904 * k + 222664 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 222664) = 209952 * k + 111332 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111332) = 104976 * k + 55666 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55666) = 52488 * k + 27833 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 27833) = 78732 * k + 41750 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41750) = 39366 * k + 20875 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20875) = 59049 * k + 31313 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34751) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34751)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34783_mod_65536 {n : ℕ} (hn : n % 65536 = 34783) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34783 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34783) = 98304 * k + 52175 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52175) = 147456 * k + 78263 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78263) = 221184 * k + 117395 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117395) = 331776 * k + 176093 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 176093) = 497664 * k + 264140 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 264140) = 248832 * k + 132070 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 132070) = 124416 * k + 66035 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66035) = 186624 * k + 99053 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99053) = 279936 * k + 148580 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 148580) = 139968 * k + 74290 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74290) = 69984 * k + 37145 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 37145) = 104976 * k + 55718 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55718) = 52488 * k + 27859 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 27859) = 78732 * k + 41789 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41789) = 118098 * k + 62684 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62684) = 59049 * k + 31342 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34783) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34783)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34843_mod_65536 {n : ℕ} (hn : n % 65536 = 34843) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34843 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34843) = 98304 * k + 52265 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52265) = 147456 * k + 78398 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78398) = 73728 * k + 39199 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 39199) = 110592 * k + 58799 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 58799) = 165888 * k + 88199 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88199) = 248832 * k + 132299 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 132299) = 373248 * k + 198449 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 198449) = 559872 * k + 297674 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 297674) = 279936 * k + 148837 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 148837) = 419904 * k + 223256 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 223256) = 209952 * k + 111628 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111628) = 104976 * k + 55814 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55814) = 52488 * k + 27907 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 27907) = 78732 * k + 41861 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41861) = 118098 * k + 62792 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62792) = 59049 * k + 31396 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34843) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34843)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34863_mod_65536 {n : ℕ} (hn : n % 65536 = 34863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34863) = 98304 * k + 52295 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52295) = 147456 * k + 78443 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78443) = 221184 * k + 117665 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117665) = 331776 * k + 176498 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 176498) = 165888 * k + 88249 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88249) = 248832 * k + 132374 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 132374) = 124416 * k + 66187 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66187) = 186624 * k + 99281 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99281) = 279936 * k + 148922 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 148922) = 139968 * k + 74461 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74461) = 209952 * k + 111692 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111692) = 104976 * k + 55846 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55846) = 52488 * k + 27923 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 27923) = 78732 * k + 41885 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41885) = 118098 * k + 62828 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62828) = 59049 * k + 31414 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34887_mod_65536 {n : ℕ} (hn : n % 65536 = 34887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34887) = 98304 * k + 52331 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52331) = 147456 * k + 78497 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78497) = 221184 * k + 117746 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117746) = 110592 * k + 58873 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 58873) = 165888 * k + 88310 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88310) = 82944 * k + 44155 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 44155) = 124416 * k + 66233 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66233) = 186624 * k + 99350 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99350) = 93312 * k + 49675 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 49675) = 139968 * k + 74513 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74513) = 209952 * k + 111770 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 111770) = 104976 * k + 55885 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 55885) = 157464 * k + 83828 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 83828) = 78732 * k + 41914 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 41914) = 39366 * k + 20957 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 20957) = 59049 * k + 31436 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_34927_mod_65536 {n : ℕ} (hn : n % 65536 = 34927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 34927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 34927) = 98304 * k + 52391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52391) = 147456 * k + 78587 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78587) = 221184 * k + 117881 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 117881) = 331776 * k + 176822 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 176822) = 165888 * k + 88411 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88411) = 248832 * k + 132617 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 132617) = 373248 * k + 198926 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 198926) = 186624 * k + 99463 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99463) = 279936 * k + 149195 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 149195) = 419904 * k + 223793 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 223793) = 629856 * k + 335690 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 335690) = 314928 * k + 167845 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 167845) = 472392 * k + 251768 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 251768) = 236196 * k + 125884 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 125884) = 118098 * k + 62942 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 62942) = 59049 * k + 31471 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 34927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 34927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35023_mod_65536 {n : ℕ} (hn : n % 65536 = 35023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35023) = 98304 * k + 52535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52535) = 147456 * k + 78803 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78803) = 221184 * k + 118205 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 118205) = 331776 * k + 177308 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 177308) = 165888 * k + 88654 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88654) = 82944 * k + 44327 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 44327) = 124416 * k + 66491 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66491) = 186624 * k + 99737 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99737) = 279936 * k + 149606 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 149606) = 139968 * k + 74803 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74803) = 209952 * k + 112205 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 112205) = 314928 * k + 168308 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 168308) = 157464 * k + 84154 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84154) = 78732 * k + 42077 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42077) = 118098 * k + 63116 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 63116) = 59049 * k + 31558 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35047_mod_65536 {n : ℕ} (hn : n % 65536 = 35047) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35047 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35047) = 98304 * k + 52571 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52571) = 147456 * k + 78857 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78857) = 221184 * k + 118286 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 118286) = 110592 * k + 59143 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 59143) = 165888 * k + 88715 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88715) = 248832 * k + 133073 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 133073) = 373248 * k + 199610 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 199610) = 186624 * k + 99805 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99805) = 279936 * k + 149708 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 149708) = 139968 * k + 74854 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 74854) = 69984 * k + 37427 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 37427) = 104976 * k + 56141 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56141) = 157464 * k + 84212 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84212) = 78732 * k + 42106 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42106) = 39366 * k + 21053 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21053) = 59049 * k + 31580 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35047) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35047)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35067_mod_65536 {n : ℕ} (hn : n % 65536 = 35067) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35067 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35067) = 98304 * k + 52601 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52601) = 147456 * k + 78902 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78902) = 73728 * k + 39451 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 39451) = 110592 * k + 59177 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 59177) = 165888 * k + 88766 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 88766) = 82944 * k + 44383 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 44383) = 124416 * k + 66575 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66575) = 186624 * k + 99863 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 99863) = 279936 * k + 149795 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 149795) = 419904 * k + 224693 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 224693) = 629856 * k + 337040 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 337040) = 314928 * k + 168520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 168520) = 157464 * k + 84260 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84260) = 78732 * k + 42130 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42130) = 39366 * k + 21065 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21065) = 59049 * k + 31598 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35067) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35067)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35071_mod_65536 {n : ℕ} (hn : n % 65536 = 35071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35071) = 98304 * k + 52607 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52607) = 147456 * k + 78911 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 78911) = 221184 * k + 118367 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 118367) = 331776 * k + 177551 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 177551) = 497664 * k + 266327 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 266327) = 746496 * k + 399491 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 399491) = 1119744 * k + 599237 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 599237) = 1679616 * k + 898856 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 898856) = 839808 * k + 449428 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 449428) = 419904 * k + 224714 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 224714) = 209952 * k + 112357 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 112357) = 314928 * k + 168536 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 168536) = 157464 * k + 84268 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84268) = 78732 * k + 42134 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42134) = 39366 * k + 21067 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21067) = 59049 * k + 31601 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35231_mod_65536 {n : ℕ} (hn : n % 65536 = 35231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35231) = 98304 * k + 52847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52847) = 147456 * k + 79271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79271) = 221184 * k + 118907 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 118907) = 331776 * k + 178361 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 178361) = 497664 * k + 267542 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 267542) = 248832 * k + 133771 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 133771) = 373248 * k + 200657 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 200657) = 559872 * k + 300986 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 300986) = 279936 * k + 150493 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 150493) = 419904 * k + 225740 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 225740) = 209952 * k + 112870 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 112870) = 104976 * k + 56435 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56435) = 157464 * k + 84653 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84653) = 236196 * k + 126980 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 126980) = 118098 * k + 63490 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 63490) = 59049 * k + 31745 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35279_mod_65536 {n : ℕ} (hn : n % 65536 = 35279) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35279 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35279) = 98304 * k + 52919 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52919) = 147456 * k + 79379 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79379) = 221184 * k + 119069 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119069) = 331776 * k + 178604 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 178604) = 165888 * k + 89302 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89302) = 82944 * k + 44651 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 44651) = 124416 * k + 66977 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 66977) = 186624 * k + 100466 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 100466) = 93312 * k + 50233 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 50233) = 139968 * k + 75350 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 75350) = 69984 * k + 37675 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 37675) = 104976 * k + 56513 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56513) = 157464 * k + 84770 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84770) = 78732 * k + 42385 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42385) = 118098 * k + 63578 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 63578) = 59049 * k + 31789 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35279) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35279)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35311_mod_65536 {n : ℕ} (hn : n % 65536 = 35311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35311) = 98304 * k + 52967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 52967) = 147456 * k + 79451 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79451) = 221184 * k + 119177 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119177) = 331776 * k + 178766 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 178766) = 165888 * k + 89383 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89383) = 248832 * k + 134075 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 134075) = 373248 * k + 201113 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 201113) = 559872 * k + 301670 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 301670) = 279936 * k + 150835 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 150835) = 419904 * k + 226253 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 226253) = 629856 * k + 339380 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 339380) = 314928 * k + 169690 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 169690) = 157464 * k + 84845 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 84845) = 236196 * k + 127268 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 127268) = 118098 * k + 63634 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 63634) = 59049 * k + 31817 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35375_mod_65536 {n : ℕ} (hn : n % 65536 = 35375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35375) = 98304 * k + 53063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53063) = 147456 * k + 79595 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79595) = 221184 * k + 119393 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119393) = 331776 * k + 179090 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 179090) = 165888 * k + 89545 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89545) = 248832 * k + 134318 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 134318) = 124416 * k + 67159 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67159) = 186624 * k + 100739 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 100739) = 279936 * k + 151109 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 151109) = 419904 * k + 226664 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 226664) = 209952 * k + 113332 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113332) = 104976 * k + 56666 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56666) = 52488 * k + 28333 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 28333) = 78732 * k + 42500 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42500) = 39366 * k + 21250 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21250) = 19683 * k + 10625 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35419_mod_65536 {n : ℕ} (hn : n % 65536 = 35419) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35419 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35419) = 98304 * k + 53129 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53129) = 147456 * k + 79694 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79694) = 73728 * k + 39847 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 39847) = 110592 * k + 59771 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 59771) = 165888 * k + 89657 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89657) = 248832 * k + 134486 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 134486) = 124416 * k + 67243 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67243) = 186624 * k + 100865 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 100865) = 279936 * k + 151298 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 151298) = 139968 * k + 75649 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 75649) = 209952 * k + 113474 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113474) = 104976 * k + 56737 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56737) = 157464 * k + 85106 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85106) = 78732 * k + 42553 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42553) = 118098 * k + 63830 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 63830) = 59049 * k + 31915 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35419) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35419)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35487_mod_65536 {n : ℕ} (hn : n % 65536 = 35487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35487) = 98304 * k + 53231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53231) = 147456 * k + 79847 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79847) = 221184 * k + 119771 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119771) = 331776 * k + 179657 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 179657) = 497664 * k + 269486 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 269486) = 248832 * k + 134743 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 134743) = 373248 * k + 202115 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 202115) = 559872 * k + 303173 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 303173) = 839808 * k + 454760 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 454760) = 419904 * k + 227380 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 227380) = 209952 * k + 113690 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113690) = 104976 * k + 56845 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 56845) = 157464 * k + 85268 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85268) = 78732 * k + 42634 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42634) = 39366 * k + 21317 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21317) = 59049 * k + 31976 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35495_mod_65536 {n : ℕ} (hn : n % 65536 = 35495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35495) = 98304 * k + 53243 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53243) = 147456 * k + 79865 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79865) = 221184 * k + 119798 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119798) = 110592 * k + 59899 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 59899) = 165888 * k + 89849 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89849) = 248832 * k + 134774 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 134774) = 124416 * k + 67387 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67387) = 186624 * k + 101081 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 101081) = 279936 * k + 151622 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 151622) = 139968 * k + 75811 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 75811) = 209952 * k + 113717 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113717) = 314928 * k + 170576 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 170576) = 157464 * k + 85288 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85288) = 78732 * k + 42644 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42644) = 39366 * k + 21322 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21322) = 19683 * k + 10661 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35535_mod_65536 {n : ℕ} (hn : n % 65536 = 35535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35535) = 98304 * k + 53303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53303) = 147456 * k + 79955 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 79955) = 221184 * k + 119933 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 119933) = 331776 * k + 179900 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 179900) = 165888 * k + 89950 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 89950) = 82944 * k + 44975 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 44975) = 124416 * k + 67463 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67463) = 186624 * k + 101195 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 101195) = 279936 * k + 151793 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 151793) = 419904 * k + 227690 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 227690) = 209952 * k + 113845 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113845) = 314928 * k + 170768 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 170768) = 157464 * k + 85384 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85384) = 78732 * k + 42692 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42692) = 39366 * k + 21346 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21346) = 19683 * k + 10673 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35567_mod_65536 {n : ℕ} (hn : n % 65536 = 35567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35567) = 98304 * k + 53351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53351) = 147456 * k + 80027 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80027) = 221184 * k + 120041 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 120041) = 331776 * k + 180062 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 180062) = 165888 * k + 90031 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 90031) = 248832 * k + 135047 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 135047) = 373248 * k + 202571 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 202571) = 559872 * k + 303857 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 303857) = 839808 * k + 455786 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 455786) = 419904 * k + 227893 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 227893) = 629856 * k + 341840 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 341840) = 314928 * k + 170920 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 170920) = 157464 * k + 85460 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85460) = 78732 * k + 42730 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42730) = 39366 * k + 21365 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21365) = 59049 * k + 32048 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35579_mod_65536 {n : ℕ} (hn : n % 65536 = 35579) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35579 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35579) = 98304 * k + 53369 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53369) = 147456 * k + 80054 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80054) = 73728 * k + 40027 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 40027) = 110592 * k + 60041 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 60041) = 165888 * k + 90062 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 90062) = 82944 * k + 45031 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 45031) = 124416 * k + 67547 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67547) = 186624 * k + 101321 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 101321) = 279936 * k + 151982 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 151982) = 139968 * k + 75991 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 75991) = 209952 * k + 113987 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 113987) = 314928 * k + 170981 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 170981) = 472392 * k + 256472 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 256472) = 236196 * k + 128236 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 128236) = 118098 * k + 64118 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 64118) = 59049 * k + 32059 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35579) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35579)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35583_mod_65536 {n : ℕ} (hn : n % 65536 = 35583) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35583 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35583) = 98304 * k + 53375 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53375) = 147456 * k + 80063 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80063) = 221184 * k + 120095 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 120095) = 331776 * k + 180143 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 180143) = 497664 * k + 270215 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 270215) = 746496 * k + 405323 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 405323) = 1119744 * k + 607985 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 607985) = 1679616 * k + 911978 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 911978) = 839808 * k + 455989 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 455989) = 1259712 * k + 683984 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 683984) = 629856 * k + 341992 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 341992) = 314928 * k + 170996 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 170996) = 157464 * k + 85498 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85498) = 78732 * k + 42749 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42749) = 118098 * k + 64124 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 64124) = 59049 * k + 32062 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35583) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35583)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35615_mod_65536 {n : ℕ} (hn : n % 65536 = 35615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35615) = 98304 * k + 53423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53423) = 147456 * k + 80135 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80135) = 221184 * k + 120203 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 120203) = 331776 * k + 180305 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 180305) = 497664 * k + 270458 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 270458) = 248832 * k + 135229 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 135229) = 373248 * k + 202844 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 202844) = 186624 * k + 101422 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 101422) = 93312 * k + 50711 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 50711) = 139968 * k + 76067 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 76067) = 209952 * k + 114101 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 114101) = 314928 * k + 171152 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 171152) = 157464 * k + 85576 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85576) = 78732 * k + 42788 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42788) = 39366 * k + 21394 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21394) = 19683 * k + 10697 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35751_mod_65536 {n : ℕ} (hn : n % 65536 = 35751) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35751 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35751) = 98304 * k + 53627 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53627) = 147456 * k + 80441 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80441) = 221184 * k + 120662 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 120662) = 110592 * k + 60331 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 60331) = 165888 * k + 90497 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 90497) = 248832 * k + 135746 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 135746) = 124416 * k + 67873 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 67873) = 186624 * k + 101810 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 101810) = 93312 * k + 50905 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 50905) = 139968 * k + 76358 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 76358) = 69984 * k + 38179 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 38179) = 104976 * k + 57269 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 57269) = 157464 * k + 85904 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 85904) = 78732 * k + 42952 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 42952) = 39366 * k + 21476 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21476) = 19683 * k + 10738 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35751) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35751)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_35931_mod_65536 {n : ℕ} (hn : n % 65536 = 35931) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 35931 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 35931) = 98304 * k + 53897 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 53897) = 147456 * k + 80846 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 80846) = 73728 * k + 40423 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 40423) = 110592 * k + 60635 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 60635) = 165888 * k + 90953 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 90953) = 248832 * k + 136430 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 136430) = 124416 * k + 68215 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 68215) = 186624 * k + 102323 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 102323) = 279936 * k + 153485 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 153485) = 419904 * k + 230228 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 230228) = 209952 * k + 115114 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 115114) = 104976 * k + 57557 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 57557) = 157464 * k + 86336 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 86336) = 78732 * k + 43168 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43168) = 39366 * k + 21584 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21584) = 19683 * k + 10792 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 35931) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 35931)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36071_mod_65536 {n : ℕ} (hn : n % 65536 = 36071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36071) = 98304 * k + 54107 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54107) = 147456 * k + 81161 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81161) = 221184 * k + 121742 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 121742) = 110592 * k + 60871 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 60871) = 165888 * k + 91307 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 91307) = 248832 * k + 136961 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 136961) = 373248 * k + 205442 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 205442) = 186624 * k + 102721 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 102721) = 279936 * k + 154082 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 154082) = 139968 * k + 77041 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77041) = 209952 * k + 115562 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 115562) = 104976 * k + 57781 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 57781) = 157464 * k + 86672 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 86672) = 78732 * k + 43336 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43336) = 39366 * k + 21668 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21668) = 19683 * k + 10834 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36143_mod_65536 {n : ℕ} (hn : n % 65536 = 36143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36143) = 98304 * k + 54215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54215) = 147456 * k + 81323 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81323) = 221184 * k + 121985 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 121985) = 331776 * k + 182978 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 182978) = 165888 * k + 91489 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 91489) = 248832 * k + 137234 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 137234) = 124416 * k + 68617 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 68617) = 186624 * k + 102926 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 102926) = 93312 * k + 51463 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 51463) = 139968 * k + 77195 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77195) = 209952 * k + 115793 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 115793) = 314928 * k + 173690 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 173690) = 157464 * k + 86845 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 86845) = 236196 * k + 130268 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 130268) = 118098 * k + 65134 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65134) = 59049 * k + 32567 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36159_mod_65536 {n : ℕ} (hn : n % 65536 = 36159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36159) = 98304 * k + 54239 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54239) = 147456 * k + 81359 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81359) = 221184 * k + 122039 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 122039) = 331776 * k + 183059 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 183059) = 497664 * k + 274589 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 274589) = 746496 * k + 411884 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 411884) = 373248 * k + 205942 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 205942) = 186624 * k + 102971 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 102971) = 279936 * k + 154457 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 154457) = 419904 * k + 231686 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 231686) = 209952 * k + 115843 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 115843) = 314928 * k + 173765 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 173765) = 472392 * k + 260648 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 260648) = 236196 * k + 130324 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 130324) = 118098 * k + 65162 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65162) = 59049 * k + 32581 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36251_mod_65536 {n : ℕ} (hn : n % 65536 = 36251) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36251 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36251) = 98304 * k + 54377 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54377) = 147456 * k + 81566 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81566) = 73728 * k + 40783 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 40783) = 110592 * k + 61175 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 61175) = 165888 * k + 91763 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 91763) = 248832 * k + 137645 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 137645) = 373248 * k + 206468 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 206468) = 186624 * k + 103234 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 103234) = 93312 * k + 51617 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 51617) = 139968 * k + 77426 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77426) = 69984 * k + 38713 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 38713) = 104976 * k + 58070 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58070) = 52488 * k + 29035 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29035) = 78732 * k + 43553 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43553) = 118098 * k + 65330 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65330) = 59049 * k + 32665 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36251) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36251)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36319_mod_65536 {n : ℕ} (hn : n % 65536 = 36319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36319) = 98304 * k + 54479 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54479) = 147456 * k + 81719 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81719) = 221184 * k + 122579 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 122579) = 331776 * k + 183869 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 183869) = 497664 * k + 275804 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 275804) = 248832 * k + 137902 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 137902) = 124416 * k + 68951 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 68951) = 186624 * k + 103427 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 103427) = 279936 * k + 155141 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 155141) = 419904 * k + 232712 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 232712) = 209952 * k + 116356 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 116356) = 104976 * k + 58178 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58178) = 52488 * k + 29089 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29089) = 78732 * k + 43634 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43634) = 39366 * k + 21817 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21817) = 59049 * k + 32726 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36379_mod_65536 {n : ℕ} (hn : n % 65536 = 36379) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36379 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36379) = 98304 * k + 54569 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54569) = 147456 * k + 81854 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81854) = 73728 * k + 40927 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 40927) = 110592 * k + 61391 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 61391) = 165888 * k + 92087 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 92087) = 248832 * k + 138131 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 138131) = 373248 * k + 207197 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 207197) = 559872 * k + 310796 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 310796) = 279936 * k + 155398 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 155398) = 139968 * k + 77699 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77699) = 209952 * k + 116549 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 116549) = 314928 * k + 174824 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 174824) = 157464 * k + 87412 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 87412) = 78732 * k + 43706 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43706) = 39366 * k + 21853 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21853) = 59049 * k + 32780 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36379) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36379)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36383_mod_65536 {n : ℕ} (hn : n % 65536 = 36383) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36383 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36383) = 98304 * k + 54575 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54575) = 147456 * k + 81863 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 81863) = 221184 * k + 122795 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 122795) = 331776 * k + 184193 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 184193) = 497664 * k + 276290 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 276290) = 248832 * k + 138145 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 138145) = 373248 * k + 207218 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 207218) = 186624 * k + 103609 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 103609) = 279936 * k + 155414 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 155414) = 139968 * k + 77707 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77707) = 209952 * k + 116561 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 116561) = 314928 * k + 174842 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 174842) = 157464 * k + 87421 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 87421) = 236196 * k + 131132 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 131132) = 118098 * k + 65566 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65566) = 59049 * k + 32783 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36383) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36383)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36511_mod_65536 {n : ℕ} (hn : n % 65536 = 36511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36511) = 98304 * k + 54767 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54767) = 147456 * k + 82151 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82151) = 221184 * k + 123227 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123227) = 331776 * k + 184841 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 184841) = 497664 * k + 277262 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 277262) = 248832 * k + 138631 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 138631) = 373248 * k + 207947 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 207947) = 559872 * k + 311921 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 311921) = 839808 * k + 467882 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 467882) = 419904 * k + 233941 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 233941) = 629856 * k + 350912 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 350912) = 314928 * k + 175456 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 175456) = 157464 * k + 87728 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 87728) = 78732 * k + 43864 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43864) = 39366 * k + 21932 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21932) = 19683 * k + 10966 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36519_mod_65536 {n : ℕ} (hn : n % 65536 = 36519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36519) = 98304 * k + 54779 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54779) = 147456 * k + 82169 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82169) = 221184 * k + 123254 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123254) = 110592 * k + 61627 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 61627) = 165888 * k + 92441 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 92441) = 248832 * k + 138662 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 138662) = 124416 * k + 69331 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 69331) = 186624 * k + 103997 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 103997) = 279936 * k + 155996 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 155996) = 139968 * k + 77998 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 77998) = 69984 * k + 38999 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 38999) = 104976 * k + 58499 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58499) = 157464 * k + 87749 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 87749) = 236196 * k + 131624 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 131624) = 118098 * k + 65812 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65812) = 59049 * k + 32906 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36543_mod_65536 {n : ℕ} (hn : n % 65536 = 36543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36543) = 98304 * k + 54815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54815) = 147456 * k + 82223 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82223) = 221184 * k + 123335 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123335) = 331776 * k + 185003 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 185003) = 497664 * k + 277505 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 277505) = 746496 * k + 416258 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 416258) = 373248 * k + 208129 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 208129) = 559872 * k + 312194 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 312194) = 279936 * k + 156097 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 156097) = 419904 * k + 234146 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 234146) = 209952 * k + 117073 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 117073) = 314928 * k + 175610 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 175610) = 157464 * k + 87805 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 87805) = 236196 * k + 131708 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 131708) = 118098 * k + 65854 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 65854) = 59049 * k + 32927 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36603_mod_65536 {n : ℕ} (hn : n % 65536 = 36603) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36603 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36603) = 98304 * k + 54905 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54905) = 147456 * k + 82358 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82358) = 73728 * k + 41179 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 41179) = 110592 * k + 61769 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 61769) = 165888 * k + 92654 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 92654) = 82944 * k + 46327 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 46327) = 124416 * k + 69491 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 69491) = 186624 * k + 104237 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 104237) = 279936 * k + 156356 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 156356) = 139968 * k + 78178 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78178) = 69984 * k + 39089 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39089) = 104976 * k + 58634 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58634) = 52488 * k + 29317 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29317) = 78732 * k + 43976 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 43976) = 39366 * k + 21988 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 21988) = 19683 * k + 10994 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36603) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36603)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36635_mod_65536 {n : ℕ} (hn : n % 65536 = 36635) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36635 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36635) = 98304 * k + 54953 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54953) = 147456 * k + 82430 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82430) = 73728 * k + 41215 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 41215) = 110592 * k + 61823 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 61823) = 165888 * k + 92735 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 92735) = 248832 * k + 139103 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 139103) = 373248 * k + 208655 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 208655) = 559872 * k + 312983 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 312983) = 839808 * k + 469475 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 469475) = 1259712 * k + 704213 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 704213) = 1889568 * k + 1056320 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 1056320) = 944784 * k + 528160 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 528160) = 472392 * k + 264080 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 264080) = 236196 * k + 132040 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 132040) = 118098 * k + 66020 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66020) = 59049 * k + 33010 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36635) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36635)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36639_mod_65536 {n : ℕ} (hn : n % 65536 = 36639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36639) = 98304 * k + 54959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 54959) = 147456 * k + 82439 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82439) = 221184 * k + 123659 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123659) = 331776 * k + 185489 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 185489) = 497664 * k + 278234 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 278234) = 248832 * k + 139117 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 139117) = 373248 * k + 208676 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 208676) = 186624 * k + 104338 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 104338) = 93312 * k + 52169 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 52169) = 139968 * k + 78254 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78254) = 69984 * k + 39127 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39127) = 104976 * k + 58691 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58691) = 157464 * k + 88037 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88037) = 236196 * k + 132056 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 132056) = 118098 * k + 66028 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66028) = 59049 * k + 33014 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36671_mod_65536 {n : ℕ} (hn : n % 65536 = 36671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36671) = 98304 * k + 55007 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55007) = 147456 * k + 82511 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82511) = 221184 * k + 123767 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123767) = 331776 * k + 185651 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 185651) = 497664 * k + 278477 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 278477) = 746496 * k + 417716 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 417716) = 373248 * k + 208858 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 208858) = 186624 * k + 104429 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 104429) = 279936 * k + 156644 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 156644) = 139968 * k + 78322 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78322) = 69984 * k + 39161 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39161) = 104976 * k + 58742 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58742) = 52488 * k + 29371 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29371) = 78732 * k + 44057 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44057) = 118098 * k + 66086 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66086) = 59049 * k + 33043 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36719_mod_65536 {n : ℕ} (hn : n % 65536 = 36719) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36719 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36719) = 98304 * k + 55079 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55079) = 147456 * k + 82619 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82619) = 221184 * k + 123929 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 123929) = 331776 * k + 185894 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 185894) = 165888 * k + 92947 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 92947) = 248832 * k + 139421 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 139421) = 373248 * k + 209132 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 209132) = 186624 * k + 104566 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 104566) = 93312 * k + 52283 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 52283) = 139968 * k + 78425 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78425) = 209952 * k + 117638 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 117638) = 104976 * k + 58819 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58819) = 157464 * k + 88229 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88229) = 236196 * k + 132344 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 132344) = 118098 * k + 66172 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66172) = 59049 * k + 33086 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36719) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36719)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36775_mod_65536 {n : ℕ} (hn : n % 65536 = 36775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36775) = 98304 * k + 55163 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55163) = 147456 * k + 82745 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82745) = 221184 * k + 124118 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 124118) = 110592 * k + 62059 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 62059) = 165888 * k + 93089 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 93089) = 248832 * k + 139634 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 139634) = 124416 * k + 69817 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 69817) = 186624 * k + 104726 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 104726) = 93312 * k + 52363 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 52363) = 139968 * k + 78545 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78545) = 209952 * k + 117818 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 117818) = 104976 * k + 58909 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 58909) = 157464 * k + 88364 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88364) = 78732 * k + 44182 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44182) = 39366 * k + 22091 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22091) = 59049 * k + 33137 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36799_mod_65536 {n : ℕ} (hn : n % 65536 = 36799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36799) = 98304 * k + 55199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55199) = 147456 * k + 82799 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 82799) = 221184 * k + 124199 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 124199) = 331776 * k + 186299 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 186299) = 497664 * k + 279449 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 279449) = 746496 * k + 419174 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 419174) = 373248 * k + 209587 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 209587) = 559872 * k + 314381 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 314381) = 839808 * k + 471572 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 471572) = 419904 * k + 235786 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 235786) = 209952 * k + 117893 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 117893) = 314928 * k + 176840 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 176840) = 157464 * k + 88420 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88420) = 78732 * k + 44210 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44210) = 39366 * k + 22105 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22105) = 59049 * k + 33158 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36891_mod_65536 {n : ℕ} (hn : n % 65536 = 36891) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36891 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36891) = 98304 * k + 55337 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55337) = 147456 * k + 83006 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83006) = 73728 * k + 41503 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 41503) = 110592 * k + 62255 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 62255) = 165888 * k + 93383 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 93383) = 248832 * k + 140075 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 140075) = 373248 * k + 210113 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 210113) = 559872 * k + 315170 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 315170) = 279936 * k + 157585 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 157585) = 419904 * k + 236378 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 236378) = 209952 * k + 118189 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 118189) = 314928 * k + 177284 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 177284) = 157464 * k + 88642 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88642) = 78732 * k + 44321 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44321) = 118098 * k + 66482 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66482) = 59049 * k + 33241 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36891) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36891)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36911_mod_65536 {n : ℕ} (hn : n % 65536 = 36911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36911) = 98304 * k + 55367 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55367) = 147456 * k + 83051 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83051) = 221184 * k + 124577 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 124577) = 331776 * k + 186866 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 186866) = 165888 * k + 93433 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 93433) = 248832 * k + 140150 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 140150) = 124416 * k + 70075 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 70075) = 186624 * k + 105113 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 105113) = 279936 * k + 157670 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 157670) = 139968 * k + 78835 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 78835) = 209952 * k + 118253 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 118253) = 314928 * k + 177380 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 177380) = 157464 * k + 88690 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88690) = 78732 * k + 44345 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44345) = 118098 * k + 66518 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66518) = 59049 * k + 33259 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36955_mod_65536 {n : ℕ} (hn : n % 65536 = 36955) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36955 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36955) = 98304 * k + 55433 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55433) = 147456 * k + 83150 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83150) = 73728 * k + 41575 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 41575) = 110592 * k + 62363 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 62363) = 165888 * k + 93545 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 93545) = 248832 * k + 140318 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 140318) = 124416 * k + 70159 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 70159) = 186624 * k + 105239 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 105239) = 279936 * k + 157859 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 157859) = 419904 * k + 236789 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 236789) = 629856 * k + 355184 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 355184) = 314928 * k + 177592 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 177592) = 157464 * k + 88796 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 88796) = 78732 * k + 44398 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44398) = 39366 * k + 22199 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22199) = 59049 * k + 33299 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36955) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36955)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_36991_mod_65536 {n : ℕ} (hn : n % 65536 = 36991) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 36991 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 36991) = 98304 * k + 55487 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55487) = 147456 * k + 83231 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83231) = 221184 * k + 124847 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 124847) = 331776 * k + 187271 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 187271) = 497664 * k + 280907 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 280907) = 746496 * k + 421361 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 421361) = 1119744 * k + 632042 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 632042) = 559872 * k + 316021 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 316021) = 839808 * k + 474032 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 474032) = 419904 * k + 237016 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 237016) = 209952 * k + 118508 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 118508) = 104976 * k + 59254 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59254) = 52488 * k + 29627 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29627) = 78732 * k + 44441 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44441) = 118098 * k + 66662 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66662) = 59049 * k + 33331 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 36991) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 36991)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37055_mod_65536 {n : ℕ} (hn : n % 65536 = 37055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37055) = 98304 * k + 55583 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55583) = 147456 * k + 83375 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83375) = 221184 * k + 125063 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 125063) = 331776 * k + 187595 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 187595) = 497664 * k + 281393 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 281393) = 746496 * k + 422090 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 422090) = 373248 * k + 211045 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 211045) = 559872 * k + 316568 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 316568) = 279936 * k + 158284 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 158284) = 139968 * k + 79142 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 79142) = 69984 * k + 39571 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39571) = 104976 * k + 59357 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59357) = 157464 * k + 89036 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89036) = 78732 * k + 44518 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44518) = 39366 * k + 22259 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22259) = 59049 * k + 33389 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37119_mod_65536 {n : ℕ} (hn : n % 65536 = 37119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37119) = 98304 * k + 55679 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55679) = 147456 * k + 83519 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83519) = 221184 * k + 125279 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 125279) = 331776 * k + 187919 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 187919) = 497664 * k + 281879 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 281879) = 746496 * k + 422819 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 422819) = 1119744 * k + 634229 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 634229) = 1679616 * k + 951344 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 951344) = 839808 * k + 475672 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 475672) = 419904 * k + 237836 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 237836) = 209952 * k + 118918 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 118918) = 104976 * k + 59459 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59459) = 157464 * k + 89189 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89189) = 236196 * k + 133784 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 133784) = 118098 * k + 66892 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66892) = 59049 * k + 33446 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37167_mod_65536 {n : ℕ} (hn : n % 65536 = 37167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37167) = 98304 * k + 55751 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55751) = 147456 * k + 83627 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83627) = 221184 * k + 125441 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 125441) = 331776 * k + 188162 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 188162) = 165888 * k + 94081 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 94081) = 248832 * k + 141122 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 141122) = 124416 * k + 70561 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 70561) = 186624 * k + 105842 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 105842) = 93312 * k + 52921 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 52921) = 139968 * k + 79382 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 79382) = 69984 * k + 39691 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39691) = 104976 * k + 59537 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59537) = 157464 * k + 89306 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89306) = 78732 * k + 44653 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44653) = 118098 * k + 66980 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 66980) = 59049 * k + 33490 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37223_mod_65536 {n : ℕ} (hn : n % 65536 = 37223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37223) = 98304 * k + 55835 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55835) = 147456 * k + 83753 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83753) = 221184 * k + 125630 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 125630) = 110592 * k + 62815 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 62815) = 165888 * k + 94223 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 94223) = 248832 * k + 141335 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 141335) = 373248 * k + 212003 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 212003) = 559872 * k + 318005 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 318005) = 839808 * k + 477008 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 477008) = 419904 * k + 238504 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 238504) = 209952 * k + 119252 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 119252) = 104976 * k + 59626 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59626) = 52488 * k + 29813 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 29813) = 78732 * k + 44720 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44720) = 39366 * k + 22360 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22360) = 19683 * k + 11180 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37311_mod_65536 {n : ℕ} (hn : n % 65536 = 37311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37311) = 98304 * k + 55967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 55967) = 147456 * k + 83951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 83951) = 221184 * k + 125927 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 125927) = 331776 * k + 188891 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 188891) = 497664 * k + 283337 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 283337) = 746496 * k + 425006 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 425006) = 373248 * k + 212503 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 212503) = 559872 * k + 318755 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 318755) = 839808 * k + 478133 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 478133) = 1259712 * k + 717200 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 717200) = 629856 * k + 358600 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 358600) = 314928 * k + 179300 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 179300) = 157464 * k + 89650 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89650) = 78732 * k + 44825 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44825) = 118098 * k + 67238 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 67238) = 59049 * k + 33619 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37407_mod_65536 {n : ℕ} (hn : n % 65536 = 37407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37407) = 98304 * k + 56111 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56111) = 147456 * k + 84167 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84167) = 221184 * k + 126251 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 126251) = 331776 * k + 189377 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 189377) = 497664 * k + 284066 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 284066) = 248832 * k + 142033 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 142033) = 373248 * k + 213050 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 213050) = 186624 * k + 106525 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 106525) = 279936 * k + 159788 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 159788) = 139968 * k + 79894 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 79894) = 69984 * k + 39947 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 39947) = 104976 * k + 59921 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 59921) = 157464 * k + 89882 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89882) = 78732 * k + 44941 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44941) = 118098 * k + 67412 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 67412) = 59049 * k + 33706 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37423_mod_65536 {n : ℕ} (hn : n % 65536 = 37423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37423) = 98304 * k + 56135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56135) = 147456 * k + 84203 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84203) = 221184 * k + 126305 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 126305) = 331776 * k + 189458 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 189458) = 165888 * k + 94729 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 94729) = 248832 * k + 142094 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 142094) = 124416 * k + 71047 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 71047) = 186624 * k + 106571 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 106571) = 279936 * k + 159857 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 159857) = 419904 * k + 239786 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 239786) = 209952 * k + 119893 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 119893) = 314928 * k + 179840 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 179840) = 157464 * k + 89920 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 89920) = 78732 * k + 44960 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 44960) = 39366 * k + 22480 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22480) = 19683 * k + 11240 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37467_mod_65536 {n : ℕ} (hn : n % 65536 = 37467) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37467 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37467) = 98304 * k + 56201 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56201) = 147456 * k + 84302 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84302) = 73728 * k + 42151 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 42151) = 110592 * k + 63227 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 63227) = 165888 * k + 94841 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 94841) = 248832 * k + 142262 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 142262) = 124416 * k + 71131 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 71131) = 186624 * k + 106697 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 106697) = 279936 * k + 160046 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 160046) = 139968 * k + 80023 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 80023) = 209952 * k + 120035 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 120035) = 314928 * k + 180053 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 180053) = 472392 * k + 270080 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 270080) = 236196 * k + 135040 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 135040) = 118098 * k + 67520 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 67520) = 59049 * k + 33760 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37467) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37467)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37487_mod_65536 {n : ℕ} (hn : n % 65536 = 37487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37487) = 98304 * k + 56231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56231) = 147456 * k + 84347 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84347) = 221184 * k + 126521 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 126521) = 331776 * k + 189782 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 189782) = 165888 * k + 94891 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 94891) = 248832 * k + 142337 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 142337) = 373248 * k + 213506 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 213506) = 186624 * k + 106753 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 106753) = 279936 * k + 160130 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 160130) = 139968 * k + 80065 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 80065) = 209952 * k + 120098 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 120098) = 104976 * k + 60049 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 60049) = 157464 * k + 90074 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 90074) = 78732 * k + 45037 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45037) = 118098 * k + 67556 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 67556) = 59049 * k + 33778 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37607_mod_65536 {n : ℕ} (hn : n % 65536 = 37607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37607) = 98304 * k + 56411 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56411) = 147456 * k + 84617 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84617) = 221184 * k + 126926 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 126926) = 110592 * k + 63463 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 63463) = 165888 * k + 95195 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 95195) = 248832 * k + 142793 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 142793) = 373248 * k + 214190 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 214190) = 186624 * k + 107095 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 107095) = 279936 * k + 160643 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 160643) = 419904 * k + 240965 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 240965) = 629856 * k + 361448 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 361448) = 314928 * k + 180724 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 180724) = 157464 * k + 90362 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 90362) = 78732 * k + 45181 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45181) = 118098 * k + 67772 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 67772) = 59049 * k + 33886 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37627_mod_65536 {n : ℕ} (hn : n % 65536 = 37627) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37627 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37627) = 98304 * k + 56441 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56441) = 147456 * k + 84662 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84662) = 73728 * k + 42331 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 42331) = 110592 * k + 63497 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 63497) = 165888 * k + 95246 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 95246) = 82944 * k + 47623 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 47623) = 124416 * k + 71435 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 71435) = 186624 * k + 107153 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 107153) = 279936 * k + 160730 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 160730) = 139968 * k + 80365 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 80365) = 209952 * k + 120548 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 120548) = 104976 * k + 60274 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 60274) = 52488 * k + 30137 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30137) = 78732 * k + 45206 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45206) = 39366 * k + 22603 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22603) = 59049 * k + 33905 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37627) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37627)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37735_mod_65536 {n : ℕ} (hn : n % 65536 = 37735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37735) = 98304 * k + 56603 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56603) = 147456 * k + 84905 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 84905) = 221184 * k + 127358 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 127358) = 110592 * k + 63679 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 63679) = 165888 * k + 95519 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 95519) = 248832 * k + 143279 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 143279) = 373248 * k + 214919 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 214919) = 559872 * k + 322379 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 322379) = 839808 * k + 483569 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 483569) = 1259712 * k + 725354 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 725354) = 629856 * k + 362677 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 362677) = 944784 * k + 544016 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 544016) = 472392 * k + 272008 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 272008) = 236196 * k + 136004 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 136004) = 118098 * k + 68002 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68002) = 59049 * k + 34001 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37959_mod_65536 {n : ℕ} (hn : n % 65536 = 37959) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37959 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37959) = 98304 * k + 56939 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56939) = 147456 * k + 85409 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85409) = 221184 * k + 128114 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 128114) = 110592 * k + 64057 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 64057) = 165888 * k + 96086 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 96086) = 82944 * k + 48043 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 48043) = 124416 * k + 72065 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 72065) = 186624 * k + 108098 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 108098) = 93312 * k + 54049 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 54049) = 139968 * k + 81074 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 81074) = 69984 * k + 40537 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 40537) = 104976 * k + 60806 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 60806) = 52488 * k + 30403 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30403) = 78732 * k + 45605 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45605) = 118098 * k + 68408 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68408) = 59049 * k + 34204 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37959) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37959)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_37999_mod_65536 {n : ℕ} (hn : n % 65536 = 37999) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 37999 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 37999) = 98304 * k + 56999 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 56999) = 147456 * k + 85499 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85499) = 221184 * k + 128249 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 128249) = 331776 * k + 192374 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 192374) = 165888 * k + 96187 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 96187) = 248832 * k + 144281 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 144281) = 373248 * k + 216422 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 216422) = 186624 * k + 108211 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 108211) = 279936 * k + 162317 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 162317) = 419904 * k + 243476 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 243476) = 209952 * k + 121738 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 121738) = 104976 * k + 60869 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 60869) = 157464 * k + 91304 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 91304) = 78732 * k + 45652 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45652) = 39366 * k + 22826 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22826) = 19683 * k + 11413 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 37999) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 37999)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38047_mod_65536 {n : ℕ} (hn : n % 65536 = 38047) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38047 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38047) = 98304 * k + 57071 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57071) = 147456 * k + 85607 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85607) = 221184 * k + 128411 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 128411) = 331776 * k + 192617 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 192617) = 497664 * k + 288926 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 288926) = 248832 * k + 144463 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 144463) = 373248 * k + 216695 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 216695) = 559872 * k + 325043 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 325043) = 839808 * k + 487565 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 487565) = 1259712 * k + 731348 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 731348) = 629856 * k + 365674 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 365674) = 314928 * k + 182837 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 182837) = 472392 * k + 274256 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 274256) = 236196 * k + 137128 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 137128) = 118098 * k + 68564 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68564) = 59049 * k + 34282 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38047) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38047)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38079_mod_65536 {n : ℕ} (hn : n % 65536 = 38079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38079) = 98304 * k + 57119 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57119) = 147456 * k + 85679 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85679) = 221184 * k + 128519 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 128519) = 331776 * k + 192779 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 192779) = 497664 * k + 289169 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 289169) = 746496 * k + 433754 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 433754) = 373248 * k + 216877 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 216877) = 559872 * k + 325316 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 325316) = 279936 * k + 162658 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 162658) = 139968 * k + 81329 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 81329) = 209952 * k + 121994 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 121994) = 104976 * k + 60997 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 60997) = 157464 * k + 91496 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 91496) = 78732 * k + 45748 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45748) = 39366 * k + 22874 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22874) = 19683 * k + 11437 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38139_mod_65536 {n : ℕ} (hn : n % 65536 = 38139) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38139 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38139) = 98304 * k + 57209 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57209) = 147456 * k + 85814 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85814) = 73728 * k + 42907 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 42907) = 110592 * k + 64361 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 64361) = 165888 * k + 96542 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 96542) = 82944 * k + 48271 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 48271) = 124416 * k + 72407 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 72407) = 186624 * k + 108611 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 108611) = 279936 * k + 162917 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 162917) = 419904 * k + 244376 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 244376) = 209952 * k + 122188 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 122188) = 104976 * k + 61094 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 61094) = 52488 * k + 30547 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30547) = 78732 * k + 45821 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45821) = 118098 * k + 68732 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68732) = 59049 * k + 34366 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38139) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38139)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38171_mod_65536 {n : ℕ} (hn : n % 65536 = 38171) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38171 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38171) = 98304 * k + 57257 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57257) = 147456 * k + 85886 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85886) = 73728 * k + 42943 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 42943) = 110592 * k + 64415 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 64415) = 165888 * k + 96623 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 96623) = 248832 * k + 144935 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 144935) = 373248 * k + 217403 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 217403) = 559872 * k + 326105 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 326105) = 839808 * k + 489158 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 489158) = 419904 * k + 244579 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 244579) = 629856 * k + 366869 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 366869) = 944784 * k + 550304 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 550304) = 472392 * k + 275152 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 275152) = 236196 * k + 137576 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 137576) = 118098 * k + 68788 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68788) = 59049 * k + 34394 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38171) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38171)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38207_mod_65536 {n : ℕ} (hn : n % 65536 = 38207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38207) = 98304 * k + 57311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57311) = 147456 * k + 85967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 85967) = 221184 * k + 128951 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 128951) = 331776 * k + 193427 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 193427) = 497664 * k + 290141 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 290141) = 746496 * k + 435212 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 435212) = 373248 * k + 217606 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 217606) = 186624 * k + 108803 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 108803) = 279936 * k + 163205 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 163205) = 419904 * k + 244808 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 244808) = 209952 * k + 122404 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 122404) = 104976 * k + 61202 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 61202) = 52488 * k + 30601 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30601) = 78732 * k + 45902 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 45902) = 39366 * k + 22951 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 22951) = 59049 * k + 34427 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38271_mod_65536 {n : ℕ} (hn : n % 65536 = 38271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38271) = 98304 * k + 57407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57407) = 147456 * k + 86111 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86111) = 221184 * k + 129167 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 129167) = 331776 * k + 193751 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 193751) = 497664 * k + 290627 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 290627) = 746496 * k + 435941 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 435941) = 1119744 * k + 653912 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 653912) = 559872 * k + 326956 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 326956) = 279936 * k + 163478 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 163478) = 139968 * k + 81739 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 81739) = 209952 * k + 122609 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 122609) = 314928 * k + 183914 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 183914) = 157464 * k + 91957 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 91957) = 236196 * k + 137936 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 137936) = 118098 * k + 68968 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 68968) = 59049 * k + 34484 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38367_mod_65536 {n : ℕ} (hn : n % 65536 = 38367) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38367 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38367) = 98304 * k + 57551 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57551) = 147456 * k + 86327 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86327) = 221184 * k + 129491 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 129491) = 331776 * k + 194237 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 194237) = 497664 * k + 291356 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 291356) = 248832 * k + 145678 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 145678) = 124416 * k + 72839 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 72839) = 186624 * k + 109259 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 109259) = 279936 * k + 163889 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 163889) = 419904 * k + 245834 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 245834) = 209952 * k + 122917 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 122917) = 314928 * k + 184376 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 184376) = 157464 * k + 92188 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 92188) = 78732 * k + 46094 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46094) = 39366 * k + 23047 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23047) = 59049 * k + 34571 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38367) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38367)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38399_mod_65536 {n : ℕ} (hn : n % 65536 = 38399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38399) = 98304 * k + 57599 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57599) = 147456 * k + 86399 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86399) = 221184 * k + 129599 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 129599) = 331776 * k + 194399 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 194399) = 497664 * k + 291599 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 291599) = 746496 * k + 437399 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 437399) = 1119744 * k + 656099 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 656099) = 1679616 * k + 984149 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 984149) = 2519424 * k + 1476224 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 1476224) = 1259712 * k + 738112 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 738112) = 629856 * k + 369056 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 369056) = 314928 * k + 184528 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 184528) = 157464 * k + 92264 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 92264) = 78732 * k + 46132 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46132) = 39366 * k + 23066 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23066) = 19683 * k + 11533 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38427_mod_65536 {n : ℕ} (hn : n % 65536 = 38427) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38427 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38427) = 98304 * k + 57641 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57641) = 147456 * k + 86462 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86462) = 73728 * k + 43231 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 43231) = 110592 * k + 64847 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 64847) = 165888 * k + 97271 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 97271) = 248832 * k + 145907 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 145907) = 373248 * k + 218861 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 218861) = 559872 * k + 328292 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 328292) = 279936 * k + 164146 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 164146) = 139968 * k + 82073 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 82073) = 209952 * k + 123110 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 123110) = 104976 * k + 61555 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 61555) = 157464 * k + 92333 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 92333) = 236196 * k + 138500 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 138500) = 118098 * k + 69250 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 69250) = 59049 * k + 34625 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38427) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38427)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38491_mod_65536 {n : ℕ} (hn : n % 65536 = 38491) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38491 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38491) = 98304 * k + 57737 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57737) = 147456 * k + 86606 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86606) = 73728 * k + 43303 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 43303) = 110592 * k + 64955 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 64955) = 165888 * k + 97433 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 97433) = 248832 * k + 146150 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 146150) = 124416 * k + 73075 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 73075) = 186624 * k + 109613 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 109613) = 279936 * k + 164420 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 164420) = 139968 * k + 82210 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 82210) = 69984 * k + 41105 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 41105) = 104976 * k + 61658 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 61658) = 52488 * k + 30829 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30829) = 78732 * k + 46244 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46244) = 39366 * k + 23122 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23122) = 19683 * k + 11561 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38491) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38491)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38607_mod_65536 {n : ℕ} (hn : n % 65536 = 38607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38607) = 98304 * k + 57911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57911) = 147456 * k + 86867 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86867) = 221184 * k + 130301 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 130301) = 331776 * k + 195452 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 195452) = 165888 * k + 97726 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 97726) = 82944 * k + 48863 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 48863) = 124416 * k + 73295 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 73295) = 186624 * k + 109943 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 109943) = 279936 * k + 164915 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 164915) = 419904 * k + 247373 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 247373) = 629856 * k + 371060 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 371060) = 314928 * k + 185530 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 185530) = 157464 * k + 92765 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 92765) = 236196 * k + 139148 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 139148) = 118098 * k + 69574 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 69574) = 59049 * k + 34787 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38639_mod_65536 {n : ℕ} (hn : n % 65536 = 38639) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38639 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38639) = 98304 * k + 57959 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 57959) = 147456 * k + 86939 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 86939) = 221184 * k + 130409 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 130409) = 331776 * k + 195614 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 195614) = 165888 * k + 97807 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 97807) = 248832 * k + 146711 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 146711) = 373248 * k + 220067 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 220067) = 559872 * k + 330101 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 330101) = 839808 * k + 495152 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 495152) = 419904 * k + 247576 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 247576) = 209952 * k + 123788 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 123788) = 104976 * k + 61894 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 61894) = 52488 * k + 30947 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 30947) = 78732 * k + 46421 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46421) = 118098 * k + 69632 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 69632) = 59049 * k + 34816 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38639) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38639)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38847_mod_65536 {n : ℕ} (hn : n % 65536 = 38847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38847) = 98304 * k + 58271 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58271) = 147456 * k + 87407 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 87407) = 221184 * k + 131111 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 131111) = 331776 * k + 196667 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 196667) = 497664 * k + 295001 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 295001) = 746496 * k + 442502 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 442502) = 373248 * k + 221251 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 221251) = 559872 * k + 331877 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 331877) = 839808 * k + 497816 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 497816) = 419904 * k + 248908 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 248908) = 209952 * k + 124454 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 124454) = 104976 * k + 62227 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 62227) = 157464 * k + 93341 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 93341) = 236196 * k + 140012 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 140012) = 118098 * k + 70006 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 70006) = 59049 * k + 35003 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_38943_mod_65536 {n : ℕ} (hn : n % 65536 = 38943) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 38943 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 38943) = 98304 * k + 58415 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58415) = 147456 * k + 87623 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 87623) = 221184 * k + 131435 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 131435) = 331776 * k + 197153 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 197153) = 497664 * k + 295730 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 295730) = 248832 * k + 147865 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 147865) = 373248 * k + 221798 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 221798) = 186624 * k + 110899 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 110899) = 279936 * k + 166349 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 166349) = 419904 * k + 249524 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 249524) = 209952 * k + 124762 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 124762) = 104976 * k + 62381 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 62381) = 157464 * k + 93572 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 93572) = 78732 * k + 46786 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46786) = 39366 * k + 23393 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23393) = 59049 * k + 35090 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 38943) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 38943)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39023_mod_65536 {n : ℕ} (hn : n % 65536 = 39023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39023) = 98304 * k + 58535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58535) = 147456 * k + 87803 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 87803) = 221184 * k + 131705 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 131705) = 331776 * k + 197558 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 197558) = 165888 * k + 98779 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 98779) = 248832 * k + 148169 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 148169) = 373248 * k + 222254 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 222254) = 186624 * k + 111127 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 111127) = 279936 * k + 166691 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 166691) = 419904 * k + 250037 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 250037) = 629856 * k + 375056 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 375056) = 314928 * k + 187528 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 187528) = 157464 * k + 93764 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 93764) = 78732 * k + 46882 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46882) = 39366 * k + 23441 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23441) = 59049 * k + 35162 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39039_mod_65536 {n : ℕ} (hn : n % 65536 = 39039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39039) = 98304 * k + 58559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58559) = 147456 * k + 87839 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 87839) = 221184 * k + 131759 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 131759) = 331776 * k + 197639 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 197639) = 497664 * k + 296459 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 296459) = 746496 * k + 444689 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 444689) = 1119744 * k + 667034 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 667034) = 559872 * k + 333517 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 333517) = 839808 * k + 500276 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 500276) = 419904 * k + 250138 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 250138) = 209952 * k + 125069 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 125069) = 314928 * k + 187604 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 187604) = 157464 * k + 93802 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 93802) = 78732 * k + 46901 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 46901) = 118098 * k + 70352 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 70352) = 59049 * k + 35176 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39135_mod_65536 {n : ℕ} (hn : n % 65536 = 39135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39135) = 98304 * k + 58703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58703) = 147456 * k + 88055 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88055) = 221184 * k + 132083 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 132083) = 331776 * k + 198125 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 198125) = 497664 * k + 297188 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 297188) = 248832 * k + 148594 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 148594) = 124416 * k + 74297 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 74297) = 186624 * k + 111446 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 111446) = 93312 * k + 55723 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 55723) = 139968 * k + 83585 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 83585) = 209952 * k + 125378 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 125378) = 104976 * k + 62689 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 62689) = 157464 * k + 94034 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 94034) = 78732 * k + 47017 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47017) = 118098 * k + 70526 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 70526) = 59049 * k + 35263 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39195_mod_65536 {n : ℕ} (hn : n % 65536 = 39195) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39195 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39195) = 98304 * k + 58793 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58793) = 147456 * k + 88190 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88190) = 73728 * k + 44095 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 44095) = 110592 * k + 66143 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 66143) = 165888 * k + 99215 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 99215) = 248832 * k + 148823 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 148823) = 373248 * k + 223235 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 223235) = 559872 * k + 334853 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 334853) = 839808 * k + 502280 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 502280) = 419904 * k + 251140 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 251140) = 209952 * k + 125570 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 125570) = 104976 * k + 62785 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 62785) = 157464 * k + 94178 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 94178) = 78732 * k + 47089 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47089) = 118098 * k + 70634 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 70634) = 59049 * k + 35317 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39195) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39195)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39271_mod_65536 {n : ℕ} (hn : n % 65536 = 39271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39271) = 98304 * k + 58907 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58907) = 147456 * k + 88361 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88361) = 221184 * k + 132542 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 132542) = 110592 * k + 66271 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 66271) = 165888 * k + 99407 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 99407) = 248832 * k + 149111 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 149111) = 373248 * k + 223667 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 223667) = 559872 * k + 335501 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 335501) = 839808 * k + 503252 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 503252) = 419904 * k + 251626 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 251626) = 209952 * k + 125813 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 125813) = 314928 * k + 188720 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 188720) = 157464 * k + 94360 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 94360) = 78732 * k + 47180 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47180) = 39366 * k + 23590 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23590) = 19683 * k + 11795 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39295_mod_65536 {n : ℕ} (hn : n % 65536 = 39295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39295) = 98304 * k + 58943 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 58943) = 147456 * k + 88415 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88415) = 221184 * k + 132623 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 132623) = 331776 * k + 198935 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 198935) = 497664 * k + 298403 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 298403) = 746496 * k + 447605 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 447605) = 1119744 * k + 671408 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 671408) = 559872 * k + 335704 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 335704) = 279936 * k + 167852 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 167852) = 139968 * k + 83926 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 83926) = 69984 * k + 41963 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 41963) = 104976 * k + 62945 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 62945) = 157464 * k + 94418 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 94418) = 78732 * k + 47209 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47209) = 118098 * k + 70814 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 70814) = 59049 * k + 35407 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39375_mod_65536 {n : ℕ} (hn : n % 65536 = 39375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39375) = 98304 * k + 59063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59063) = 147456 * k + 88595 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88595) = 221184 * k + 132893 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 132893) = 331776 * k + 199340 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 199340) = 165888 * k + 99670 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 99670) = 82944 * k + 49835 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 49835) = 124416 * k + 74753 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 74753) = 186624 * k + 112130 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 112130) = 93312 * k + 56065 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 56065) = 139968 * k + 84098 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 84098) = 69984 * k + 42049 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 42049) = 104976 * k + 63074 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 63074) = 52488 * k + 31537 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 31537) = 78732 * k + 47306 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47306) = 39366 * k + 23653 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23653) = 59049 * k + 35480 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39515_mod_65536 {n : ℕ} (hn : n % 65536 = 39515) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39515 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39515) = 98304 * k + 59273 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59273) = 147456 * k + 88910 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88910) = 73728 * k + 44455 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 44455) = 110592 * k + 66683 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 66683) = 165888 * k + 100025 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 100025) = 248832 * k + 150038 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 150038) = 124416 * k + 75019 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 75019) = 186624 * k + 112529 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 112529) = 279936 * k + 168794 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 168794) = 139968 * k + 84397 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 84397) = 209952 * k + 126596 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 126596) = 104976 * k + 63298 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 63298) = 52488 * k + 31649 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 31649) = 78732 * k + 47474 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47474) = 39366 * k + 23737 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23737) = 59049 * k + 35606 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39515) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39515)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39527_mod_65536 {n : ℕ} (hn : n % 65536 = 39527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39527) = 98304 * k + 59291 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59291) = 147456 * k + 88937 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88937) = 221184 * k + 133406 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 133406) = 110592 * k + 66703 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 66703) = 165888 * k + 100055 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 100055) = 248832 * k + 150083 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 150083) = 373248 * k + 225125 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 225125) = 559872 * k + 337688 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 337688) = 279936 * k + 168844 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 168844) = 139968 * k + 84422 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 84422) = 69984 * k + 42211 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 42211) = 104976 * k + 63317 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 63317) = 157464 * k + 94976 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 94976) = 78732 * k + 47488 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47488) = 39366 * k + 23744 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23744) = 19683 * k + 11872 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39535_mod_65536 {n : ℕ} (hn : n % 65536 = 39535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39535) = 98304 * k + 59303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59303) = 147456 * k + 88955 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88955) = 221184 * k + 133433 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 133433) = 331776 * k + 200150 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 200150) = 165888 * k + 100075 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 100075) = 248832 * k + 150113 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 150113) = 373248 * k + 225170 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 225170) = 186624 * k + 112585 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 112585) = 279936 * k + 168878 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 168878) = 139968 * k + 84439 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 84439) = 209952 * k + 126659 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 126659) = 314928 * k + 189989 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 189989) = 472392 * k + 284984 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 284984) = 236196 * k + 142492 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 142492) = 118098 * k + 71246 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 71246) = 59049 * k + 35623 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39551_mod_65536 {n : ℕ} (hn : n % 65536 = 39551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39551) = 98304 * k + 59327 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59327) = 147456 * k + 88991 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 88991) = 221184 * k + 133487 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 133487) = 331776 * k + 200231 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 200231) = 497664 * k + 300347 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 300347) = 746496 * k + 450521 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 450521) = 1119744 * k + 675782 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 675782) = 559872 * k + 337891 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 337891) = 839808 * k + 506837 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 506837) = 1259712 * k + 760256 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 760256) = 629856 * k + 380128 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 380128) = 314928 * k + 190064 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 190064) = 157464 * k + 95032 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 95032) = 78732 * k + 47516 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47516) = 39366 * k + 23758 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23758) = 19683 * k + 11879 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39615_mod_65536 {n : ℕ} (hn : n % 65536 = 39615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39615) = 98304 * k + 59423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59423) = 147456 * k + 89135 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89135) = 221184 * k + 133703 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 133703) = 331776 * k + 200555 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 200555) = 497664 * k + 300833 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 300833) = 746496 * k + 451250 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 451250) = 373248 * k + 225625 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 225625) = 559872 * k + 338438 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 338438) = 279936 * k + 169219 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 169219) = 419904 * k + 253829 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 253829) = 629856 * k + 380744 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 380744) = 314928 * k + 190372 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 190372) = 157464 * k + 95186 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 95186) = 78732 * k + 47593 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47593) = 118098 * k + 71390 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 71390) = 59049 * k + 35695 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39675_mod_65536 {n : ℕ} (hn : n % 65536 = 39675) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39675 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39675) = 98304 * k + 59513 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59513) = 147456 * k + 89270 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89270) = 73728 * k + 44635 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 44635) = 110592 * k + 66953 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 66953) = 165888 * k + 100430 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 100430) = 82944 * k + 50215 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 50215) = 124416 * k + 75323 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 75323) = 186624 * k + 112985 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 112985) = 279936 * k + 169478 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 169478) = 139968 * k + 84739 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 84739) = 209952 * k + 127109 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 127109) = 314928 * k + 190664 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 190664) = 157464 * k + 95332 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 95332) = 78732 * k + 47666 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47666) = 39366 * k + 23833 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23833) = 59049 * k + 35750 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39675) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39675)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39847_mod_65536 {n : ℕ} (hn : n % 65536 = 39847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39847) = 98304 * k + 59771 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59771) = 147456 * k + 89657 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89657) = 221184 * k + 134486 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 134486) = 110592 * k + 67243 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67243) = 165888 * k + 100865 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 100865) = 248832 * k + 151298 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 151298) = 124416 * k + 75649 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 75649) = 186624 * k + 113474 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 113474) = 93312 * k + 56737 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 56737) = 139968 * k + 85106 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 85106) = 69984 * k + 42553 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 42553) = 104976 * k + 63830 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 63830) = 52488 * k + 31915 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 31915) = 78732 * k + 47873 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47873) = 118098 * k + 71810 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 71810) = 59049 * k + 35905 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39919_mod_65536 {n : ℕ} (hn : n % 65536 = 39919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39919) = 98304 * k + 59879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59879) = 147456 * k + 89819 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89819) = 221184 * k + 134729 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 134729) = 331776 * k + 202094 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 202094) = 165888 * k + 101047 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101047) = 248832 * k + 151571 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 151571) = 373248 * k + 227357 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 227357) = 559872 * k + 341036 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 341036) = 279936 * k + 170518 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 170518) = 139968 * k + 85259 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 85259) = 209952 * k + 127889 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 127889) = 314928 * k + 191834 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 191834) = 157464 * k + 95917 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 95917) = 236196 * k + 143876 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 143876) = 118098 * k + 71938 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 71938) = 59049 * k + 35969 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39931_mod_65536 {n : ℕ} (hn : n % 65536 = 39931) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39931 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39931) = 98304 * k + 59897 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59897) = 147456 * k + 89846 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89846) = 73728 * k + 44923 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 44923) = 110592 * k + 67385 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67385) = 165888 * k + 101078 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101078) = 82944 * k + 50539 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 50539) = 124416 * k + 75809 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 75809) = 186624 * k + 113714 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 113714) = 93312 * k + 56857 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 56857) = 139968 * k + 85286 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 85286) = 69984 * k + 42643 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 42643) = 104976 * k + 63965 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 63965) = 157464 * k + 95948 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 95948) = 78732 * k + 47974 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 47974) = 39366 * k + 23987 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 23987) = 59049 * k + 35981 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39931) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39931)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_39967_mod_65536 {n : ℕ} (hn : n % 65536 = 39967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 39967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 39967) = 98304 * k + 59951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 59951) = 147456 * k + 89927 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 89927) = 221184 * k + 134891 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 134891) = 331776 * k + 202337 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 202337) = 497664 * k + 303506 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 303506) = 248832 * k + 151753 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 151753) = 373248 * k + 227630 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 227630) = 186624 * k + 113815 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 113815) = 279936 * k + 170723 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 170723) = 419904 * k + 256085 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 256085) = 629856 * k + 384128 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 384128) = 314928 * k + 192064 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 192064) = 157464 * k + 96032 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 96032) = 78732 * k + 48016 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48016) = 39366 * k + 24008 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24008) = 19683 * k + 12004 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 39967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 39967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40027_mod_65536 {n : ℕ} (hn : n % 65536 = 40027) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40027 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40027) = 98304 * k + 60041 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60041) = 147456 * k + 90062 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90062) = 73728 * k + 45031 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 45031) = 110592 * k + 67547 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67547) = 165888 * k + 101321 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101321) = 248832 * k + 151982 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 151982) = 124416 * k + 75991 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 75991) = 186624 * k + 113987 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 113987) = 279936 * k + 170981 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 170981) = 419904 * k + 256472 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 256472) = 209952 * k + 128236 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 128236) = 104976 * k + 64118 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64118) = 52488 * k + 32059 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 32059) = 78732 * k + 48089 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48089) = 118098 * k + 72134 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72134) = 59049 * k + 36067 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40027) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40027)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40039_mod_65536 {n : ℕ} (hn : n % 65536 = 40039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40039) = 98304 * k + 60059 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60059) = 147456 * k + 90089 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90089) = 221184 * k + 135134 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 135134) = 110592 * k + 67567 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67567) = 165888 * k + 101351 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101351) = 248832 * k + 152027 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 152027) = 373248 * k + 228041 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 228041) = 559872 * k + 342062 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 342062) = 279936 * k + 171031 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 171031) = 419904 * k + 256547 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 256547) = 629856 * k + 384821 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 384821) = 944784 * k + 577232 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 577232) = 472392 * k + 288616 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 288616) = 236196 * k + 144308 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 144308) = 118098 * k + 72154 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72154) = 59049 * k + 36077 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40167_mod_65536 {n : ℕ} (hn : n % 65536 = 40167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40167) = 98304 * k + 60251 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60251) = 147456 * k + 90377 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90377) = 221184 * k + 135566 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 135566) = 110592 * k + 67783 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67783) = 165888 * k + 101675 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101675) = 248832 * k + 152513 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 152513) = 373248 * k + 228770 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 228770) = 186624 * k + 114385 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 114385) = 279936 * k + 171578 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 171578) = 139968 * k + 85789 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 85789) = 209952 * k + 128684 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 128684) = 104976 * k + 64342 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64342) = 52488 * k + 32171 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 32171) = 78732 * k + 48257 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48257) = 118098 * k + 72386 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72386) = 59049 * k + 36193 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40187_mod_65536 {n : ℕ} (hn : n % 65536 = 40187) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40187 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40187) = 98304 * k + 60281 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60281) = 147456 * k + 90422 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90422) = 73728 * k + 45211 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 45211) = 110592 * k + 67817 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 67817) = 165888 * k + 101726 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 101726) = 82944 * k + 50863 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 50863) = 124416 * k + 76295 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 76295) = 186624 * k + 114443 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 114443) = 279936 * k + 171665 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 171665) = 419904 * k + 257498 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 257498) = 209952 * k + 128749 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 128749) = 314928 * k + 193124 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 193124) = 157464 * k + 96562 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 96562) = 78732 * k + 48281 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48281) = 118098 * k + 72422 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72422) = 59049 * k + 36211 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40187) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40187)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40255_mod_65536 {n : ℕ} (hn : n % 65536 = 40255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40255) = 98304 * k + 60383 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60383) = 147456 * k + 90575 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90575) = 221184 * k + 135863 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 135863) = 331776 * k + 203795 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 203795) = 497664 * k + 305693 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 305693) = 746496 * k + 458540 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 458540) = 373248 * k + 229270 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 229270) = 186624 * k + 114635 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 114635) = 279936 * k + 171953 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 171953) = 419904 * k + 257930 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 257930) = 209952 * k + 128965 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 128965) = 314928 * k + 193448 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 193448) = 157464 * k + 96724 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 96724) = 78732 * k + 48362 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48362) = 39366 * k + 24181 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24181) = 59049 * k + 36272 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40351_mod_65536 {n : ℕ} (hn : n % 65536 = 40351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40351) = 98304 * k + 60527 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60527) = 147456 * k + 90791 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90791) = 221184 * k + 136187 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136187) = 331776 * k + 204281 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 204281) = 497664 * k + 306422 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 306422) = 248832 * k + 153211 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 153211) = 373248 * k + 229817 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 229817) = 559872 * k + 344726 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 344726) = 279936 * k + 172363 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 172363) = 419904 * k + 258545 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 258545) = 629856 * k + 387818 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 387818) = 314928 * k + 193909 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 193909) = 472392 * k + 290864 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 290864) = 236196 * k + 145432 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 145432) = 118098 * k + 72716 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72716) = 59049 * k + 36358 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40399_mod_65536 {n : ℕ} (hn : n % 65536 = 40399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40399) = 98304 * k + 60599 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60599) = 147456 * k + 90899 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90899) = 221184 * k + 136349 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136349) = 331776 * k + 204524 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 204524) = 165888 * k + 102262 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102262) = 82944 * k + 51131 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 51131) = 124416 * k + 76697 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 76697) = 186624 * k + 115046 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 115046) = 93312 * k + 57523 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 57523) = 139968 * k + 86285 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 86285) = 209952 * k + 129428 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 129428) = 104976 * k + 64714 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64714) = 52488 * k + 32357 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 32357) = 78732 * k + 48536 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48536) = 39366 * k + 24268 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24268) = 19683 * k + 12134 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40415_mod_65536 {n : ℕ} (hn : n % 65536 = 40415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40415) = 98304 * k + 60623 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60623) = 147456 * k + 90935 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 90935) = 221184 * k + 136403 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136403) = 331776 * k + 204605 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 204605) = 497664 * k + 306908 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 306908) = 248832 * k + 153454 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 153454) = 124416 * k + 76727 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 76727) = 186624 * k + 115091 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 115091) = 279936 * k + 172637 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 172637) = 419904 * k + 258956 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 258956) = 209952 * k + 129478 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 129478) = 104976 * k + 64739 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64739) = 157464 * k + 97109 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 97109) = 236196 * k + 145664 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 145664) = 118098 * k + 72832 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72832) = 59049 * k + 36416 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40495_mod_65536 {n : ℕ} (hn : n % 65536 = 40495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40495) = 98304 * k + 60743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60743) = 147456 * k + 91115 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91115) = 221184 * k + 136673 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136673) = 331776 * k + 205010 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 205010) = 165888 * k + 102505 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102505) = 248832 * k + 153758 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 153758) = 124416 * k + 76879 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 76879) = 186624 * k + 115319 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 115319) = 279936 * k + 172979 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 172979) = 419904 * k + 259469 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 259469) = 629856 * k + 389204 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 389204) = 314928 * k + 194602 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 194602) = 157464 * k + 97301 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 97301) = 236196 * k + 145952 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 145952) = 118098 * k + 72976 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 72976) = 59049 * k + 36488 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40551_mod_65536 {n : ℕ} (hn : n % 65536 = 40551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40551) = 98304 * k + 60827 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60827) = 147456 * k + 91241 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91241) = 221184 * k + 136862 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136862) = 110592 * k + 68431 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 68431) = 165888 * k + 102647 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102647) = 248832 * k + 153971 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 153971) = 373248 * k + 230957 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 230957) = 559872 * k + 346436 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 346436) = 279936 * k + 173218 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 173218) = 139968 * k + 86609 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 86609) = 209952 * k + 129914 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 129914) = 104976 * k + 64957 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64957) = 157464 * k + 97436 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 97436) = 78732 * k + 48718 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48718) = 39366 * k + 24359 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24359) = 59049 * k + 36539 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40559_mod_65536 {n : ℕ} (hn : n % 65536 = 40559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40559) = 98304 * k + 60839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 60839) = 147456 * k + 91259 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91259) = 221184 * k + 136889 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 136889) = 331776 * k + 205334 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 205334) = 165888 * k + 102667 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102667) = 248832 * k + 154001 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 154001) = 373248 * k + 231002 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 231002) = 186624 * k + 115501 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 115501) = 279936 * k + 173252 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 173252) = 139968 * k + 86626 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 86626) = 69984 * k + 43313 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 43313) = 104976 * k + 64970 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 64970) = 52488 * k + 32485 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 32485) = 78732 * k + 48728 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48728) = 39366 * k + 24364 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24364) = 19683 * k + 12182 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40679_mod_65536 {n : ℕ} (hn : n % 65536 = 40679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40679) = 98304 * k + 61019 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61019) = 147456 * k + 91529 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91529) = 221184 * k + 137294 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 137294) = 110592 * k + 68647 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 68647) = 165888 * k + 102971 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102971) = 248832 * k + 154457 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 154457) = 373248 * k + 231686 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 231686) = 186624 * k + 115843 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 115843) = 279936 * k + 173765 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 173765) = 419904 * k + 260648 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 260648) = 209952 * k + 130324 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 130324) = 104976 * k + 65162 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65162) = 52488 * k + 32581 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 32581) = 78732 * k + 48872 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48872) = 39366 * k + 24436 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24436) = 19683 * k + 12218 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40687_mod_65536 {n : ℕ} (hn : n % 65536 = 40687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40687) = 98304 * k + 61031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61031) = 147456 * k + 91547 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91547) = 221184 * k + 137321 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 137321) = 331776 * k + 205982 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 205982) = 165888 * k + 102991 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 102991) = 248832 * k + 154487 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 154487) = 373248 * k + 231731 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 231731) = 559872 * k + 347597 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 347597) = 839808 * k + 521396 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 521396) = 419904 * k + 260698 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 260698) = 209952 * k + 130349 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 130349) = 314928 * k + 195524 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 195524) = 157464 * k + 97762 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 97762) = 78732 * k + 48881 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 48881) = 118098 * k + 73322 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 73322) = 59049 * k + 36661 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40831_mod_65536 {n : ℕ} (hn : n % 65536 = 40831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40831) = 98304 * k + 61247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61247) = 147456 * k + 91871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 91871) = 221184 * k + 137807 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 137807) = 331776 * k + 206711 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 206711) = 497664 * k + 310067 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 310067) = 746496 * k + 465101 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 465101) = 1119744 * k + 697652 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 697652) = 559872 * k + 348826 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 348826) = 279936 * k + 174413 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 174413) = 419904 * k + 261620 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 261620) = 209952 * k + 130810 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 130810) = 104976 * k + 65405 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65405) = 157464 * k + 98108 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98108) = 78732 * k + 49054 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49054) = 39366 * k + 24527 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24527) = 59049 * k + 36791 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40943_mod_65536 {n : ℕ} (hn : n % 65536 = 40943) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40943 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40943) = 98304 * k + 61415 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61415) = 147456 * k + 92123 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92123) = 221184 * k + 138185 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 138185) = 331776 * k + 207278 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 207278) = 165888 * k + 103639 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 103639) = 248832 * k + 155459 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 155459) = 373248 * k + 233189 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 233189) = 559872 * k + 349784 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 349784) = 279936 * k + 174892 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 174892) = 139968 * k + 87446 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 87446) = 69984 * k + 43723 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 43723) = 104976 * k + 65585 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65585) = 157464 * k + 98378 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98378) = 78732 * k + 49189 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49189) = 118098 * k + 73784 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 73784) = 59049 * k + 36892 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40943) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40943)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_40955_mod_65536 {n : ℕ} (hn : n % 65536 = 40955) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 40955 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 40955) = 98304 * k + 61433 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61433) = 147456 * k + 92150 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92150) = 73728 * k + 46075 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46075) = 110592 * k + 69113 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 69113) = 165888 * k + 103670 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 103670) = 82944 * k + 51835 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 51835) = 124416 * k + 77753 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 77753) = 186624 * k + 116630 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 116630) = 93312 * k + 58315 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 58315) = 139968 * k + 87473 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 87473) = 209952 * k + 131210 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 131210) = 104976 * k + 65605 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65605) = 157464 * k + 98408 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98408) = 78732 * k + 49204 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49204) = 39366 * k + 24602 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24602) = 19683 * k + 12301 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 40955) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 40955)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41023_mod_65536 {n : ℕ} (hn : n % 65536 = 41023) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41023 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41023) = 98304 * k + 61535 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61535) = 147456 * k + 92303 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92303) = 221184 * k + 138455 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 138455) = 331776 * k + 207683 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 207683) = 497664 * k + 311525 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 311525) = 746496 * k + 467288 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 467288) = 373248 * k + 233644 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 233644) = 186624 * k + 116822 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 116822) = 93312 * k + 58411 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 58411) = 139968 * k + 87617 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 87617) = 209952 * k + 131426 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 131426) = 104976 * k + 65713 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65713) = 157464 * k + 98570 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98570) = 78732 * k + 49285 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49285) = 118098 * k + 73928 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 73928) = 59049 * k + 36964 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41023) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41023)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41063_mod_65536 {n : ℕ} (hn : n % 65536 = 41063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41063) = 98304 * k + 61595 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61595) = 147456 * k + 92393 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92393) = 221184 * k + 138590 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 138590) = 110592 * k + 69295 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 69295) = 165888 * k + 103943 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 103943) = 248832 * k + 155915 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 155915) = 373248 * k + 233873 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 233873) = 559872 * k + 350810 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 350810) = 279936 * k + 175405 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 175405) = 419904 * k + 263108 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 263108) = 209952 * k + 131554 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 131554) = 104976 * k + 65777 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65777) = 157464 * k + 98666 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98666) = 78732 * k + 49333 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49333) = 118098 * k + 74000 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 74000) = 59049 * k + 37000 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41115_mod_65536 {n : ℕ} (hn : n % 65536 = 41115) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41115 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41115) = 98304 * k + 61673 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61673) = 147456 * k + 92510 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92510) = 73728 * k + 46255 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46255) = 110592 * k + 69383 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 69383) = 165888 * k + 104075 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 104075) = 248832 * k + 156113 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 156113) = 373248 * k + 234170 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 234170) = 186624 * k + 117085 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 117085) = 279936 * k + 175628 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 175628) = 139968 * k + 87814 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 87814) = 69984 * k + 43907 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 43907) = 104976 * k + 65861 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 65861) = 157464 * k + 98792 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98792) = 78732 * k + 49396 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49396) = 39366 * k + 24698 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24698) = 19683 * k + 12349 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41115) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41115)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41183_mod_65536 {n : ℕ} (hn : n % 65536 = 41183) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41183 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41183) = 98304 * k + 61775 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61775) = 147456 * k + 92663 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92663) = 221184 * k + 138995 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 138995) = 331776 * k + 208493 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 208493) = 497664 * k + 312740 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 312740) = 248832 * k + 156370 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 156370) = 124416 * k + 78185 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 78185) = 186624 * k + 117278 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 117278) = 93312 * k + 58639 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 58639) = 139968 * k + 87959 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 87959) = 209952 * k + 131939 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 131939) = 314928 * k + 197909 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 197909) = 472392 * k + 296864 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 296864) = 236196 * k + 148432 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 148432) = 118098 * k + 74216 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 74216) = 59049 * k + 37108 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41183) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41183)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
