import Propositio.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_41199_mod_65536 {n : ℕ} (hn : n % 65536 = 41199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41199) = 98304 * k + 61799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61799) = 147456 * k + 92699 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92699) = 221184 * k + 139049 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 139049) = 331776 * k + 208574 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 208574) = 165888 * k + 104287 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 104287) = 248832 * k + 156431 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 156431) = 373248 * k + 234647 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 234647) = 559872 * k + 351971 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 351971) = 839808 * k + 527957 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 527957) = 1259712 * k + 791936 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 791936) = 629856 * k + 395968 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 395968) = 314928 * k + 197984 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 197984) = 157464 * k + 98992 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 98992) = 78732 * k + 49496 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49496) = 39366 * k + 24748 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24748) = 19683 * k + 12374 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41243_mod_65536 {n : ℕ} (hn : n % 65536 = 41243) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41243 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41243) = 98304 * k + 61865 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61865) = 147456 * k + 92798 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92798) = 73728 * k + 46399 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46399) = 110592 * k + 69599 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 69599) = 165888 * k + 104399 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 104399) = 248832 * k + 156599 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 156599) = 373248 * k + 234899 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 234899) = 559872 * k + 352349 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 352349) = 839808 * k + 528524 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 528524) = 419904 * k + 264262 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 264262) = 209952 * k + 132131 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 132131) = 314928 * k + 198197 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 198197) = 472392 * k + 297296 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 297296) = 236196 * k + 148648 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 148648) = 118098 * k + 74324 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 74324) = 59049 * k + 37162 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41243) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41243)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41263_mod_65536 {n : ℕ} (hn : n % 65536 = 41263) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41263 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41263) = 98304 * k + 61895 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 61895) = 147456 * k + 92843 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 92843) = 221184 * k + 139265 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 139265) = 331776 * k + 208898 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 208898) = 165888 * k + 104449 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 104449) = 248832 * k + 156674 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 156674) = 124416 * k + 78337 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 78337) = 186624 * k + 117506 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 117506) = 93312 * k + 58753 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 58753) = 139968 * k + 88130 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 88130) = 69984 * k + 44065 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 44065) = 104976 * k + 66098 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 66098) = 52488 * k + 33049 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33049) = 78732 * k + 49574 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49574) = 39366 * k + 24787 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24787) = 59049 * k + 37181 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41263) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41263)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41447_mod_65536 {n : ℕ} (hn : n % 65536 = 41447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41447) = 98304 * k + 62171 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62171) = 147456 * k + 93257 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93257) = 221184 * k + 139886 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 139886) = 110592 * k + 69943 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 69943) = 165888 * k + 104915 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 104915) = 248832 * k + 157373 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 157373) = 373248 * k + 236060 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 236060) = 186624 * k + 118030 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118030) = 93312 * k + 59015 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 59015) = 139968 * k + 88523 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 88523) = 209952 * k + 132785 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 132785) = 314928 * k + 199178 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 199178) = 157464 * k + 99589 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 99589) = 236196 * k + 149384 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 149384) = 118098 * k + 74692 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 74692) = 59049 * k + 37346 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41503_mod_65536 {n : ℕ} (hn : n % 65536 = 41503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41503) = 98304 * k + 62255 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62255) = 147456 * k + 93383 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93383) = 221184 * k + 140075 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 140075) = 331776 * k + 210113 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 210113) = 497664 * k + 315170 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 315170) = 248832 * k + 157585 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 157585) = 373248 * k + 236378 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 236378) = 186624 * k + 118189 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118189) = 279936 * k + 177284 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 177284) = 139968 * k + 88642 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 88642) = 69984 * k + 44321 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 44321) = 104976 * k + 66482 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 66482) = 52488 * k + 33241 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33241) = 78732 * k + 49862 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49862) = 39366 * k + 24931 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24931) = 59049 * k + 37397 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41563_mod_65536 {n : ℕ} (hn : n % 65536 = 41563) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41563 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41563) = 98304 * k + 62345 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62345) = 147456 * k + 93518 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93518) = 73728 * k + 46759 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46759) = 110592 * k + 70139 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 70139) = 165888 * k + 105209 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 105209) = 248832 * k + 157814 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 157814) = 124416 * k + 78907 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 78907) = 186624 * k + 118361 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118361) = 279936 * k + 177542 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 177542) = 139968 * k + 88771 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 88771) = 209952 * k + 133157 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 133157) = 314928 * k + 199736 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 199736) = 157464 * k + 99868 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 99868) = 78732 * k + 49934 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49934) = 39366 * k + 24967 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24967) = 59049 * k + 37451 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41563) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41563)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41583_mod_65536 {n : ℕ} (hn : n % 65536 = 41583) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41583 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41583) = 98304 * k + 62375 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62375) = 147456 * k + 93563 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93563) = 221184 * k + 140345 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 140345) = 331776 * k + 210518 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 210518) = 165888 * k + 105259 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 105259) = 248832 * k + 157889 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 157889) = 373248 * k + 236834 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 236834) = 186624 * k + 118417 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118417) = 279936 * k + 177626 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 177626) = 139968 * k + 88813 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 88813) = 209952 * k + 133220 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 133220) = 104976 * k + 66610 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 66610) = 52488 * k + 33305 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33305) = 78732 * k + 49958 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 49958) = 39366 * k + 24979 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 24979) = 59049 * k + 37469 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41583) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41583)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41627_mod_65536 {n : ℕ} (hn : n % 65536 = 41627) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41627 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41627) = 98304 * k + 62441 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62441) = 147456 * k + 93662 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93662) = 73728 * k + 46831 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46831) = 110592 * k + 70247 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 70247) = 165888 * k + 105371 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 105371) = 248832 * k + 158057 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 158057) = 373248 * k + 237086 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 237086) = 186624 * k + 118543 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118543) = 279936 * k + 177815 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 177815) = 419904 * k + 266723 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 266723) = 629856 * k + 400085 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 400085) = 944784 * k + 600128 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 600128) = 472392 * k + 300064 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 300064) = 236196 * k + 150032 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 150032) = 118098 * k + 75016 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 75016) = 59049 * k + 37508 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41627) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41627)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41723_mod_65536 {n : ℕ} (hn : n % 65536 = 41723) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41723 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41723) = 98304 * k + 62585 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62585) = 147456 * k + 93878 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 93878) = 73728 * k + 46939 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 46939) = 110592 * k + 70409 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 70409) = 165888 * k + 105614 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 105614) = 82944 * k + 52807 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 52807) = 124416 * k + 79211 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 79211) = 186624 * k + 118817 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 118817) = 279936 * k + 178226 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 178226) = 139968 * k + 89113 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 89113) = 209952 * k + 133670 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 133670) = 104976 * k + 66835 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 66835) = 157464 * k + 100253 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 100253) = 236196 * k + 150380 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 150380) = 118098 * k + 75190 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 75190) = 59049 * k + 37595 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41723) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41723)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41819_mod_65536 {n : ℕ} (hn : n % 65536 = 41819) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41819 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41819) = 98304 * k + 62729 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62729) = 147456 * k + 94094 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94094) = 73728 * k + 47047 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 47047) = 110592 * k + 70571 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 70571) = 165888 * k + 105857 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 105857) = 248832 * k + 158786 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 158786) = 124416 * k + 79393 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 79393) = 186624 * k + 119090 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 119090) = 93312 * k + 59545 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 59545) = 139968 * k + 89318 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 89318) = 69984 * k + 44659 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 44659) = 104976 * k + 66989 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 66989) = 157464 * k + 100484 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 100484) = 78732 * k + 50242 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50242) = 39366 * k + 25121 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25121) = 59049 * k + 37682 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41819) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41819)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_41855_mod_65536 {n : ℕ} (hn : n % 65536 = 41855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 41855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 41855) = 98304 * k + 62783 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 62783) = 147456 * k + 94175 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94175) = 221184 * k + 141263 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 141263) = 331776 * k + 211895 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 211895) = 497664 * k + 317843 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 317843) = 746496 * k + 476765 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 476765) = 1119744 * k + 715148 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 715148) = 559872 * k + 357574 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 357574) = 279936 * k + 178787 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 178787) = 419904 * k + 268181 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 268181) = 629856 * k + 402272 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 402272) = 314928 * k + 201136 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 201136) = 157464 * k + 100568 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 100568) = 78732 * k + 50284 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50284) = 39366 * k + 25142 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25142) = 19683 * k + 12571 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 41855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 41855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42075_mod_65536 {n : ℕ} (hn : n % 65536 = 42075) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42075 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42075) = 98304 * k + 63113 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63113) = 147456 * k + 94670 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94670) = 73728 * k + 47335 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 47335) = 110592 * k + 71003 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71003) = 165888 * k + 106505 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 106505) = 248832 * k + 159758 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 159758) = 124416 * k + 79879 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 79879) = 186624 * k + 119819 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 119819) = 279936 * k + 179729 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 179729) = 419904 * k + 269594 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 269594) = 209952 * k + 134797 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 134797) = 314928 * k + 202196 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 202196) = 157464 * k + 101098 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101098) = 78732 * k + 50549 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50549) = 118098 * k + 75824 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 75824) = 59049 * k + 37912 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42075) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42075)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42095_mod_65536 {n : ℕ} (hn : n % 65536 = 42095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42095) = 98304 * k + 63143 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63143) = 147456 * k + 94715 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94715) = 221184 * k + 142073 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142073) = 331776 * k + 213110 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 213110) = 165888 * k + 106555 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 106555) = 248832 * k + 159833 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 159833) = 373248 * k + 239750 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 239750) = 186624 * k + 119875 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 119875) = 279936 * k + 179813 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 179813) = 419904 * k + 269720 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 269720) = 209952 * k + 134860 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 134860) = 104976 * k + 67430 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67430) = 52488 * k + 33715 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33715) = 78732 * k + 50573 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50573) = 118098 * k + 75860 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 75860) = 59049 * k + 37930 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42139_mod_65536 {n : ℕ} (hn : n % 65536 = 42139) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42139 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42139) = 98304 * k + 63209 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63209) = 147456 * k + 94814 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94814) = 73728 * k + 47407 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 47407) = 110592 * k + 71111 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71111) = 165888 * k + 106667 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 106667) = 248832 * k + 160001 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160001) = 373248 * k + 240002 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 240002) = 186624 * k + 120001 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120001) = 279936 * k + 180002 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 180002) = 139968 * k + 90001 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90001) = 209952 * k + 135002 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135002) = 104976 * k + 67501 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67501) = 157464 * k + 101252 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101252) = 78732 * k + 50626 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50626) = 39366 * k + 25313 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25313) = 59049 * k + 37970 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42139) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42139)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42143_mod_65536 {n : ℕ} (hn : n % 65536 = 42143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42143) = 98304 * k + 63215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63215) = 147456 * k + 94823 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94823) = 221184 * k + 142235 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142235) = 331776 * k + 213353 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 213353) = 497664 * k + 320030 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 320030) = 248832 * k + 160015 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160015) = 373248 * k + 240023 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 240023) = 559872 * k + 360035 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 360035) = 839808 * k + 540053 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 540053) = 1259712 * k + 810080 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 810080) = 629856 * k + 405040 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 405040) = 314928 * k + 202520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 202520) = 157464 * k + 101260 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101260) = 78732 * k + 50630 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50630) = 39366 * k + 25315 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25315) = 59049 * k + 37973 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42175_mod_65536 {n : ℕ} (hn : n % 65536 = 42175) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42175 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42175) = 98304 * k + 63263 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63263) = 147456 * k + 94895 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94895) = 221184 * k + 142343 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142343) = 331776 * k + 213515 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 213515) = 497664 * k + 320273 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 320273) = 746496 * k + 480410 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 480410) = 373248 * k + 240205 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 240205) = 559872 * k + 360308 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 360308) = 279936 * k + 180154 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 180154) = 139968 * k + 90077 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90077) = 209952 * k + 135116 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135116) = 104976 * k + 67558 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67558) = 52488 * k + 33779 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33779) = 78732 * k + 50669 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50669) = 118098 * k + 76004 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76004) = 59049 * k + 38002 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42175) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42175)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42207_mod_65536 {n : ℕ} (hn : n % 65536 = 42207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42207) = 98304 * k + 63311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63311) = 147456 * k + 94967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94967) = 221184 * k + 142451 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142451) = 331776 * k + 213677 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 213677) = 497664 * k + 320516 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 320516) = 248832 * k + 160258 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160258) = 124416 * k + 80129 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 80129) = 186624 * k + 120194 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120194) = 93312 * k + 60097 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 60097) = 139968 * k + 90146 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90146) = 69984 * k + 45073 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 45073) = 104976 * k + 67610 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67610) = 52488 * k + 33805 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33805) = 78732 * k + 50708 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50708) = 39366 * k + 25354 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25354) = 19683 * k + 12677 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42215_mod_65536 {n : ℕ} (hn : n % 65536 = 42215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42215) = 98304 * k + 63323 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63323) = 147456 * k + 94985 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 94985) = 221184 * k + 142478 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142478) = 110592 * k + 71239 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71239) = 165888 * k + 106859 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 106859) = 248832 * k + 160289 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160289) = 373248 * k + 240434 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 240434) = 186624 * k + 120217 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120217) = 279936 * k + 180326 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 180326) = 139968 * k + 90163 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90163) = 209952 * k + 135245 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135245) = 314928 * k + 202868 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 202868) = 157464 * k + 101434 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101434) = 78732 * k + 50717 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50717) = 118098 * k + 76076 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76076) = 59049 * k + 38038 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42239_mod_65536 {n : ℕ} (hn : n % 65536 = 42239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42239) = 98304 * k + 63359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63359) = 147456 * k + 95039 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95039) = 221184 * k + 142559 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142559) = 331776 * k + 213839 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 213839) = 497664 * k + 320759 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 320759) = 746496 * k + 481139 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 481139) = 1119744 * k + 721709 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 721709) = 1679616 * k + 1082564 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1082564) = 839808 * k + 541282 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 541282) = 419904 * k + 270641 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 270641) = 629856 * k + 405962 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 405962) = 314928 * k + 202981 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 202981) = 472392 * k + 304472 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 304472) = 236196 * k + 152236 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 152236) = 118098 * k + 76118 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76118) = 59049 * k + 38059 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42287_mod_65536 {n : ℕ} (hn : n % 65536 = 42287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42287) = 98304 * k + 63431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63431) = 147456 * k + 95147 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95147) = 221184 * k + 142721 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142721) = 331776 * k + 214082 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 214082) = 165888 * k + 107041 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107041) = 248832 * k + 160562 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160562) = 124416 * k + 80281 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 80281) = 186624 * k + 120422 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120422) = 93312 * k + 60211 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 60211) = 139968 * k + 90317 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90317) = 209952 * k + 135476 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135476) = 104976 * k + 67738 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67738) = 52488 * k + 33869 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 33869) = 78732 * k + 50804 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50804) = 39366 * k + 25402 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25402) = 19683 * k + 12701 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42303_mod_65536 {n : ℕ} (hn : n % 65536 = 42303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42303) = 98304 * k + 63455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63455) = 147456 * k + 95183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95183) = 221184 * k + 142775 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142775) = 331776 * k + 214163 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 214163) = 497664 * k + 321245 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 321245) = 746496 * k + 481868 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 481868) = 373248 * k + 240934 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 240934) = 186624 * k + 120467 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120467) = 279936 * k + 180701 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 180701) = 419904 * k + 271052 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 271052) = 209952 * k + 135526 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135526) = 104976 * k + 67763 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 67763) = 157464 * k + 101645 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101645) = 236196 * k + 152468 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 152468) = 118098 * k + 76234 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76234) = 59049 * k + 38117 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42343_mod_65536 {n : ℕ} (hn : n % 65536 = 42343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42343) = 98304 * k + 63515 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63515) = 147456 * k + 95273 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95273) = 221184 * k + 142910 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 142910) = 110592 * k + 71455 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71455) = 165888 * k + 107183 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107183) = 248832 * k + 160775 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 160775) = 373248 * k + 241163 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 241163) = 559872 * k + 361745 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 361745) = 839808 * k + 542618 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 542618) = 419904 * k + 271309 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 271309) = 629856 * k + 406964 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 406964) = 314928 * k + 203482 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 203482) = 157464 * k + 101741 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101741) = 236196 * k + 152612 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 152612) = 118098 * k + 76306 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76306) = 59049 * k + 38153 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42447_mod_65536 {n : ℕ} (hn : n % 65536 = 42447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42447) = 98304 * k + 63671 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63671) = 147456 * k + 95507 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95507) = 221184 * k + 143261 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 143261) = 331776 * k + 214892 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 214892) = 165888 * k + 107446 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107446) = 82944 * k + 53723 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 53723) = 124416 * k + 80585 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 80585) = 186624 * k + 120878 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120878) = 93312 * k + 60439 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 60439) = 139968 * k + 90659 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90659) = 209952 * k + 135989 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 135989) = 314928 * k + 203984 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 203984) = 157464 * k + 101992 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 101992) = 78732 * k + 50996 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 50996) = 39366 * k + 25498 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25498) = 19683 * k + 12749 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42471_mod_65536 {n : ℕ} (hn : n % 65536 = 42471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42471) = 98304 * k + 63707 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63707) = 147456 * k + 95561 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95561) = 221184 * k + 143342 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 143342) = 110592 * k + 71671 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71671) = 165888 * k + 107507 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107507) = 248832 * k + 161261 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 161261) = 373248 * k + 241892 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 241892) = 186624 * k + 120946 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 120946) = 93312 * k + 60473 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 60473) = 139968 * k + 90710 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90710) = 69984 * k + 45355 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 45355) = 104976 * k + 68033 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68033) = 157464 * k + 102050 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102050) = 78732 * k + 51025 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51025) = 118098 * k + 76538 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76538) = 59049 * k + 38269 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42479_mod_65536 {n : ℕ} (hn : n % 65536 = 42479) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42479 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42479) = 98304 * k + 63719 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63719) = 147456 * k + 95579 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95579) = 221184 * k + 143369 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 143369) = 331776 * k + 215054 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 215054) = 165888 * k + 107527 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107527) = 248832 * k + 161291 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 161291) = 373248 * k + 241937 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 241937) = 559872 * k + 362906 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 362906) = 279936 * k + 181453 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 181453) = 419904 * k + 272180 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 272180) = 209952 * k + 136090 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 136090) = 104976 * k + 68045 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68045) = 157464 * k + 102068 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102068) = 78732 * k + 51034 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51034) = 39366 * k + 25517 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25517) = 59049 * k + 38276 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42479) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42479)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42527_mod_65536 {n : ℕ} (hn : n % 65536 = 42527) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42527 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42527) = 98304 * k + 63791 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63791) = 147456 * k + 95687 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95687) = 221184 * k + 143531 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 143531) = 331776 * k + 215297 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 215297) = 497664 * k + 322946 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 322946) = 248832 * k + 161473 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 161473) = 373248 * k + 242210 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 242210) = 186624 * k + 121105 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 121105) = 279936 * k + 181658 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 181658) = 139968 * k + 90829 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 90829) = 209952 * k + 136244 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 136244) = 104976 * k + 68122 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68122) = 52488 * k + 34061 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34061) = 78732 * k + 51092 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51092) = 39366 * k + 25546 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25546) = 19683 * k + 12773 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42527) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42527)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42651_mod_65536 {n : ℕ} (hn : n % 65536 = 42651) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42651 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42651) = 98304 * k + 63977 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 63977) = 147456 * k + 95966 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 95966) = 73728 * k + 47983 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 47983) = 110592 * k + 71975 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 71975) = 165888 * k + 107963 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 107963) = 248832 * k + 161945 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 161945) = 373248 * k + 242918 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 242918) = 186624 * k + 121459 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 121459) = 279936 * k + 182189 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 182189) = 419904 * k + 273284 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 273284) = 209952 * k + 136642 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 136642) = 104976 * k + 68321 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68321) = 157464 * k + 102482 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102482) = 78732 * k + 51241 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51241) = 118098 * k + 76862 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 76862) = 59049 * k + 38431 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42651) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42651)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42687_mod_65536 {n : ℕ} (hn : n % 65536 = 42687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42687) = 98304 * k + 64031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64031) = 147456 * k + 96047 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96047) = 221184 * k + 144071 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 144071) = 331776 * k + 216107 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 216107) = 497664 * k + 324161 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 324161) = 746496 * k + 486242 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 486242) = 373248 * k + 243121 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 243121) = 559872 * k + 364682 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 364682) = 279936 * k + 182341 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 182341) = 419904 * k + 273512 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 273512) = 209952 * k + 136756 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 136756) = 104976 * k + 68378 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68378) = 52488 * k + 34189 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34189) = 78732 * k + 51284 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51284) = 39366 * k + 25642 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25642) = 19683 * k + 12821 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42727_mod_65536 {n : ℕ} (hn : n % 65536 = 42727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42727) = 98304 * k + 64091 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64091) = 147456 * k + 96137 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96137) = 221184 * k + 144206 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 144206) = 110592 * k + 72103 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 72103) = 165888 * k + 108155 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 108155) = 248832 * k + 162233 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 162233) = 373248 * k + 243350 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 243350) = 186624 * k + 121675 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 121675) = 279936 * k + 182513 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 182513) = 419904 * k + 273770 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 273770) = 209952 * k + 136885 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 136885) = 314928 * k + 205328 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 205328) = 157464 * k + 102664 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102664) = 78732 * k + 51332 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51332) = 39366 * k + 25666 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25666) = 19683 * k + 12833 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42823_mod_65536 {n : ℕ} (hn : n % 65536 = 42823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42823) = 98304 * k + 64235 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64235) = 147456 * k + 96353 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96353) = 221184 * k + 144530 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 144530) = 110592 * k + 72265 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 72265) = 165888 * k + 108398 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 108398) = 82944 * k + 54199 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 54199) = 124416 * k + 81299 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 81299) = 186624 * k + 121949 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 121949) = 279936 * k + 182924 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 182924) = 139968 * k + 91462 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 91462) = 69984 * k + 45731 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 45731) = 104976 * k + 68597 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68597) = 157464 * k + 102896 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102896) = 78732 * k + 51448 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51448) = 39366 * k + 25724 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25724) = 19683 * k + 12862 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42843_mod_65536 {n : ℕ} (hn : n % 65536 = 42843) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42843 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42843) = 98304 * k + 64265 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64265) = 147456 * k + 96398 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96398) = 73728 * k + 48199 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 48199) = 110592 * k + 72299 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 72299) = 165888 * k + 108449 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 108449) = 248832 * k + 162674 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 162674) = 124416 * k + 81337 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 81337) = 186624 * k + 122006 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 122006) = 93312 * k + 61003 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 61003) = 139968 * k + 91505 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 91505) = 209952 * k + 137258 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 137258) = 104976 * k + 68629 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68629) = 157464 * k + 102944 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 102944) = 78732 * k + 51472 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51472) = 39366 * k + 25736 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25736) = 19683 * k + 12868 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42843) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42843)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_42911_mod_65536 {n : ℕ} (hn : n % 65536 = 42911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 42911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 42911) = 98304 * k + 64367 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64367) = 147456 * k + 96551 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96551) = 221184 * k + 144827 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 144827) = 331776 * k + 217241 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 217241) = 497664 * k + 325862 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 325862) = 248832 * k + 162931 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 162931) = 373248 * k + 244397 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 244397) = 559872 * k + 366596 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 366596) = 279936 * k + 183298 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 183298) = 139968 * k + 91649 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 91649) = 209952 * k + 137474 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 137474) = 104976 * k + 68737 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 68737) = 157464 * k + 103106 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 103106) = 78732 * k + 51553 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51553) = 118098 * k + 77330 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 77330) = 59049 * k + 38665 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 42911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 42911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43071_mod_65536 {n : ℕ} (hn : n % 65536 = 43071) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43071 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43071) = 98304 * k + 64607 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64607) = 147456 * k + 96911 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 96911) = 221184 * k + 145367 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 145367) = 331776 * k + 218051 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 218051) = 497664 * k + 327077 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 327077) = 746496 * k + 490616 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 490616) = 373248 * k + 245308 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 245308) = 186624 * k + 122654 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 122654) = 93312 * k + 61327 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 61327) = 139968 * k + 91991 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 91991) = 209952 * k + 137987 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 137987) = 314928 * k + 206981 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 206981) = 472392 * k + 310472 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 310472) = 236196 * k + 155236 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 155236) = 118098 * k + 77618 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 77618) = 59049 * k + 38809 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43071) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43071)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43111_mod_65536 {n : ℕ} (hn : n % 65536 = 43111) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43111 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43111) = 98304 * k + 64667 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64667) = 147456 * k + 97001 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97001) = 221184 * k + 145502 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 145502) = 110592 * k + 72751 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 72751) = 165888 * k + 109127 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 109127) = 248832 * k + 163691 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 163691) = 373248 * k + 245537 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 245537) = 559872 * k + 368306 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 368306) = 279936 * k + 184153 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 184153) = 419904 * k + 276230 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 276230) = 209952 * k + 138115 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 138115) = 314928 * k + 207173 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 207173) = 472392 * k + 310760 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 310760) = 236196 * k + 155380 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 155380) = 118098 * k + 77690 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 77690) = 59049 * k + 38845 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43111) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43111)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43215_mod_65536 {n : ℕ} (hn : n % 65536 = 43215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43215) = 98304 * k + 64823 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64823) = 147456 * k + 97235 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97235) = 221184 * k + 145853 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 145853) = 331776 * k + 218780 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 218780) = 165888 * k + 109390 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 109390) = 82944 * k + 54695 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 54695) = 124416 * k + 82043 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 82043) = 186624 * k + 123065 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 123065) = 279936 * k + 184598 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 184598) = 139968 * k + 92299 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 92299) = 209952 * k + 138449 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 138449) = 314928 * k + 207674 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 207674) = 157464 * k + 103837 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 103837) = 236196 * k + 155756 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 155756) = 118098 * k + 77878 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 77878) = 59049 * k + 38939 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43231_mod_65536 {n : ℕ} (hn : n % 65536 = 43231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43231) = 98304 * k + 64847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64847) = 147456 * k + 97271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97271) = 221184 * k + 145907 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 145907) = 331776 * k + 218861 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 218861) = 497664 * k + 328292 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 328292) = 248832 * k + 164146 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 164146) = 124416 * k + 82073 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 82073) = 186624 * k + 123110 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 123110) = 93312 * k + 61555 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 61555) = 139968 * k + 92333 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 92333) = 209952 * k + 138500 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 138500) = 104976 * k + 69250 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69250) = 52488 * k + 34625 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34625) = 78732 * k + 51938 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 51938) = 39366 * k + 25969 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 25969) = 59049 * k + 38954 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43291_mod_65536 {n : ℕ} (hn : n % 65536 = 43291) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43291 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43291) = 98304 * k + 64937 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 64937) = 147456 * k + 97406 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97406) = 73728 * k + 48703 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 48703) = 110592 * k + 73055 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 73055) = 165888 * k + 109583 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 109583) = 248832 * k + 164375 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 164375) = 373248 * k + 246563 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 246563) = 559872 * k + 369845 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 369845) = 839808 * k + 554768 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 554768) = 419904 * k + 277384 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 277384) = 209952 * k + 138692 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 138692) = 104976 * k + 69346 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69346) = 52488 * k + 34673 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34673) = 78732 * k + 52010 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52010) = 39366 * k + 26005 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26005) = 59049 * k + 39008 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43291) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43291)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43335_mod_65536 {n : ℕ} (hn : n % 65536 = 43335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43335) = 98304 * k + 65003 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65003) = 147456 * k + 97505 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97505) = 221184 * k + 146258 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 146258) = 110592 * k + 73129 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 73129) = 165888 * k + 109694 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 109694) = 82944 * k + 54847 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 54847) = 124416 * k + 82271 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 82271) = 186624 * k + 123407 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 123407) = 279936 * k + 185111 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 185111) = 419904 * k + 277667 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 277667) = 629856 * k + 416501 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 416501) = 944784 * k + 624752 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 624752) = 472392 * k + 312376 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 312376) = 236196 * k + 156188 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 156188) = 118098 * k + 78094 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 78094) = 59049 * k + 39047 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43391_mod_65536 {n : ℕ} (hn : n % 65536 = 43391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43391) = 98304 * k + 65087 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65087) = 147456 * k + 97631 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97631) = 221184 * k + 146447 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 146447) = 331776 * k + 219671 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 219671) = 497664 * k + 329507 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 329507) = 746496 * k + 494261 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 494261) = 1119744 * k + 741392 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 741392) = 559872 * k + 370696 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 370696) = 279936 * k + 185348 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 185348) = 139968 * k + 92674 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 92674) = 69984 * k + 46337 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 46337) = 104976 * k + 69506 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69506) = 52488 * k + 34753 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34753) = 78732 * k + 52130 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52130) = 39366 * k + 26065 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26065) = 59049 * k + 39098 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43423_mod_65536 {n : ℕ} (hn : n % 65536 = 43423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43423) = 98304 * k + 65135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65135) = 147456 * k + 97703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97703) = 221184 * k + 146555 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 146555) = 331776 * k + 219833 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 219833) = 497664 * k + 329750 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 329750) = 248832 * k + 164875 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 164875) = 373248 * k + 247313 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 247313) = 559872 * k + 370970 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 370970) = 279936 * k + 185485 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 185485) = 419904 * k + 278228 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 278228) = 209952 * k + 139114 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 139114) = 104976 * k + 69557 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69557) = 157464 * k + 104336 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 104336) = 78732 * k + 52168 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52168) = 39366 * k + 26084 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26084) = 19683 * k + 13042 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43471_mod_65536 {n : ℕ} (hn : n % 65536 = 43471) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43471 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43471) = 98304 * k + 65207 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65207) = 147456 * k + 97811 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97811) = 221184 * k + 146717 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 146717) = 331776 * k + 220076 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 220076) = 165888 * k + 110038 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110038) = 82944 * k + 55019 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 55019) = 124416 * k + 82529 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 82529) = 186624 * k + 123794 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 123794) = 93312 * k + 61897 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 61897) = 139968 * k + 92846 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 92846) = 69984 * k + 46423 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 46423) = 104976 * k + 69635 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69635) = 157464 * k + 104453 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 104453) = 236196 * k + 156680 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 156680) = 118098 * k + 78340 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 78340) = 59049 * k + 39170 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43471) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43471)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43503_mod_65536 {n : ℕ} (hn : n % 65536 = 43503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43503) = 98304 * k + 65255 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65255) = 147456 * k + 97883 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 97883) = 221184 * k + 146825 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 146825) = 331776 * k + 220238 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 220238) = 165888 * k + 110119 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110119) = 248832 * k + 165179 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 165179) = 373248 * k + 247769 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 247769) = 559872 * k + 371654 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 371654) = 279936 * k + 185827 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 185827) = 419904 * k + 278741 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 278741) = 629856 * k + 418112 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 418112) = 314928 * k + 209056 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 209056) = 157464 * k + 104528 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 104528) = 78732 * k + 52264 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52264) = 39366 * k + 26132 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26132) = 19683 * k + 13066 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43611_mod_65536 {n : ℕ} (hn : n % 65536 = 43611) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43611 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43611) = 98304 * k + 65417 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65417) = 147456 * k + 98126 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98126) = 73728 * k + 49063 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 49063) = 110592 * k + 73595 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 73595) = 165888 * k + 110393 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110393) = 248832 * k + 165590 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 165590) = 124416 * k + 82795 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 82795) = 186624 * k + 124193 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 124193) = 279936 * k + 186290 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 186290) = 139968 * k + 93145 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 93145) = 209952 * k + 139718 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 139718) = 104976 * k + 69859 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69859) = 157464 * k + 104789 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 104789) = 236196 * k + 157184 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 157184) = 118098 * k + 78592 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 78592) = 59049 * k + 39296 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43611) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43611)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43623_mod_65536 {n : ℕ} (hn : n % 65536 = 43623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43623) = 98304 * k + 65435 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65435) = 147456 * k + 98153 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98153) = 221184 * k + 147230 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 147230) = 110592 * k + 73615 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 73615) = 165888 * k + 110423 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110423) = 248832 * k + 165635 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 165635) = 373248 * k + 248453 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 248453) = 559872 * k + 372680 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 372680) = 279936 * k + 186340 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 186340) = 139968 * k + 93170 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 93170) = 69984 * k + 46585 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 46585) = 104976 * k + 69878 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 69878) = 52488 * k + 34939 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 34939) = 78732 * k + 52409 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52409) = 118098 * k + 78614 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 78614) = 59049 * k + 39307 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43631_mod_65536 {n : ℕ} (hn : n % 65536 = 43631) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43631 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43631) = 98304 * k + 65447 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65447) = 147456 * k + 98171 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98171) = 221184 * k + 147257 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 147257) = 331776 * k + 220886 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 220886) = 165888 * k + 110443 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110443) = 248832 * k + 165665 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 165665) = 373248 * k + 248498 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 248498) = 186624 * k + 124249 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 124249) = 279936 * k + 186374 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 186374) = 139968 * k + 93187 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 93187) = 209952 * k + 139781 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 139781) = 314928 * k + 209672 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 209672) = 157464 * k + 104836 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 104836) = 78732 * k + 52418 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52418) = 39366 * k + 26209 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26209) = 59049 * k + 39314 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43631) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43631)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43775_mod_65536 {n : ℕ} (hn : n % 65536 = 43775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43775) = 98304 * k + 65663 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65663) = 147456 * k + 98495 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98495) = 221184 * k + 147743 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 147743) = 331776 * k + 221615 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 221615) = 497664 * k + 332423 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 332423) = 746496 * k + 498635 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 498635) = 1119744 * k + 747953 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 747953) = 1679616 * k + 1121930 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1121930) = 839808 * k + 560965 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 560965) = 1259712 * k + 841448 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 841448) = 629856 * k + 420724 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 420724) = 314928 * k + 210362 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 210362) = 157464 * k + 105181 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 105181) = 236196 * k + 157772 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 157772) = 118098 * k + 78886 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 78886) = 59049 * k + 39443 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43847_mod_65536 {n : ℕ} (hn : n % 65536 = 43847) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43847 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43847) = 98304 * k + 65771 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65771) = 147456 * k + 98657 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98657) = 221184 * k + 147986 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 147986) = 110592 * k + 73993 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 73993) = 165888 * k + 110990 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 110990) = 82944 * k + 55495 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 55495) = 124416 * k + 83243 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 83243) = 186624 * k + 124865 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 124865) = 279936 * k + 187298 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 187298) = 139968 * k + 93649 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 93649) = 209952 * k + 140474 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 140474) = 104976 * k + 70237 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 70237) = 157464 * k + 105356 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 105356) = 78732 * k + 52678 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52678) = 39366 * k + 26339 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26339) = 59049 * k + 39509 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43847) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43847)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43887_mod_65536 {n : ℕ} (hn : n % 65536 = 43887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43887) = 98304 * k + 65831 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65831) = 147456 * k + 98747 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98747) = 221184 * k + 148121 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 148121) = 331776 * k + 222182 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 222182) = 165888 * k + 111091 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 111091) = 248832 * k + 166637 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 166637) = 373248 * k + 249956 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 249956) = 186624 * k + 124978 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 124978) = 93312 * k + 62489 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 62489) = 139968 * k + 93734 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 93734) = 69984 * k + 46867 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 46867) = 104976 * k + 70301 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 70301) = 157464 * k + 105452 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 105452) = 78732 * k + 52726 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52726) = 39366 * k + 26363 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26363) = 59049 * k + 39545 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_43967_mod_65536 {n : ℕ} (hn : n % 65536 = 43967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 43967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 43967) = 98304 * k + 65951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 65951) = 147456 * k + 98927 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 98927) = 221184 * k + 148391 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 148391) = 331776 * k + 222587 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 222587) = 497664 * k + 333881 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 333881) = 746496 * k + 500822 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 500822) = 373248 * k + 250411 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 250411) = 559872 * k + 375617 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 375617) = 839808 * k + 563426 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 563426) = 419904 * k + 281713 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 281713) = 629856 * k + 422570 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 422570) = 314928 * k + 211285 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 211285) = 472392 * k + 316928 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 316928) = 236196 * k + 158464 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 158464) = 118098 * k + 79232 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 79232) = 59049 * k + 39616 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 43967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 43967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44095_mod_65536 {n : ℕ} (hn : n % 65536 = 44095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44095) = 98304 * k + 66143 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66143) = 147456 * k + 99215 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99215) = 221184 * k + 148823 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 148823) = 331776 * k + 223235 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 223235) = 497664 * k + 334853 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 334853) = 746496 * k + 502280 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 502280) = 373248 * k + 251140 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 251140) = 186624 * k + 125570 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 125570) = 93312 * k + 62785 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 62785) = 139968 * k + 94178 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 94178) = 69984 * k + 47089 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 47089) = 104976 * k + 70634 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 70634) = 52488 * k + 35317 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 35317) = 78732 * k + 52976 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 52976) = 39366 * k + 26488 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26488) = 19683 * k + 13244 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44143_mod_65536 {n : ℕ} (hn : n % 65536 = 44143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44143) = 98304 * k + 66215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66215) = 147456 * k + 99323 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99323) = 221184 * k + 148985 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 148985) = 331776 * k + 223478 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 223478) = 165888 * k + 111739 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 111739) = 248832 * k + 167609 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 167609) = 373248 * k + 251414 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 251414) = 186624 * k + 125707 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 125707) = 279936 * k + 188561 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 188561) = 419904 * k + 282842 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 282842) = 209952 * k + 141421 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 141421) = 314928 * k + 212132 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 212132) = 157464 * k + 106066 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106066) = 78732 * k + 53033 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53033) = 118098 * k + 79550 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 79550) = 59049 * k + 39775 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44223_mod_65536 {n : ℕ} (hn : n % 65536 = 44223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44223) = 98304 * k + 66335 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66335) = 147456 * k + 99503 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99503) = 221184 * k + 149255 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 149255) = 331776 * k + 223883 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 223883) = 497664 * k + 335825 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 335825) = 746496 * k + 503738 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 503738) = 373248 * k + 251869 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 251869) = 559872 * k + 377804 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 377804) = 279936 * k + 188902 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 188902) = 139968 * k + 94451 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 94451) = 209952 * k + 141677 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 141677) = 314928 * k + 212516 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 212516) = 157464 * k + 106258 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106258) = 78732 * k + 53129 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53129) = 118098 * k + 79694 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 79694) = 59049 * k + 39847 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44239_mod_65536 {n : ℕ} (hn : n % 65536 = 44239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44239) = 98304 * k + 66359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66359) = 147456 * k + 99539 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99539) = 221184 * k + 149309 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 149309) = 331776 * k + 223964 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 223964) = 165888 * k + 111982 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 111982) = 82944 * k + 55991 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 55991) = 124416 * k + 83987 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 83987) = 186624 * k + 125981 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 125981) = 279936 * k + 188972 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 188972) = 139968 * k + 94486 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 94486) = 69984 * k + 47243 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 47243) = 104976 * k + 70865 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 70865) = 157464 * k + 106298 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106298) = 78732 * k + 53149 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53149) = 118098 * k + 79724 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 79724) = 59049 * k + 39862 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44335_mod_65536 {n : ℕ} (hn : n % 65536 = 44335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44335) = 98304 * k + 66503 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66503) = 147456 * k + 99755 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99755) = 221184 * k + 149633 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 149633) = 331776 * k + 224450 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 224450) = 165888 * k + 112225 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 112225) = 248832 * k + 168338 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 168338) = 124416 * k + 84169 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 84169) = 186624 * k + 126254 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 126254) = 93312 * k + 63127 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 63127) = 139968 * k + 94691 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 94691) = 209952 * k + 142037 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 142037) = 314928 * k + 213056 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 213056) = 157464 * k + 106528 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106528) = 78732 * k + 53264 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53264) = 39366 * k + 26632 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26632) = 19683 * k + 13316 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44359_mod_65536 {n : ℕ} (hn : n % 65536 = 44359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44359) = 98304 * k + 66539 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66539) = 147456 * k + 99809 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99809) = 221184 * k + 149714 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 149714) = 110592 * k + 74857 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 74857) = 165888 * k + 112286 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 112286) = 82944 * k + 56143 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 56143) = 124416 * k + 84215 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 84215) = 186624 * k + 126323 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 126323) = 279936 * k + 189485 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 189485) = 419904 * k + 284228 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 284228) = 209952 * k + 142114 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 142114) = 104976 * k + 71057 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 71057) = 157464 * k + 106586 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106586) = 78732 * k + 53293 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53293) = 118098 * k + 79940 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 79940) = 59049 * k + 39970 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44415_mod_65536 {n : ℕ} (hn : n % 65536 = 44415) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44415 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44415) = 98304 * k + 66623 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66623) = 147456 * k + 99935 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 99935) = 221184 * k + 149903 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 149903) = 331776 * k + 224855 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 224855) = 497664 * k + 337283 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 337283) = 746496 * k + 505925 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 505925) = 1119744 * k + 758888 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 758888) = 559872 * k + 379444 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 379444) = 279936 * k + 189722 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 189722) = 139968 * k + 94861 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 94861) = 209952 * k + 142292 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 142292) = 104976 * k + 71146 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 71146) = 52488 * k + 35573 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 35573) = 78732 * k + 53360 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53360) = 39366 * k + 26680 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26680) = 19683 * k + 13340 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44415) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44415)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44447_mod_65536 {n : ℕ} (hn : n % 65536 = 44447) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44447 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44447) = 98304 * k + 66671 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66671) = 147456 * k + 100007 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100007) = 221184 * k + 150011 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 150011) = 331776 * k + 225017 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 225017) = 497664 * k + 337526 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 337526) = 248832 * k + 168763 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 168763) = 373248 * k + 253145 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 253145) = 559872 * k + 379718 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 379718) = 279936 * k + 189859 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 189859) = 419904 * k + 284789 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 284789) = 629856 * k + 427184 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 427184) = 314928 * k + 213592 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 213592) = 157464 * k + 106796 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 106796) = 78732 * k + 53398 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53398) = 39366 * k + 26699 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26699) = 59049 * k + 40049 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44447) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44447)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44575_mod_65536 {n : ℕ} (hn : n % 65536 = 44575) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44575 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44575) = 98304 * k + 66863 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 66863) = 147456 * k + 100295 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100295) = 221184 * k + 150443 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 150443) = 331776 * k + 225665 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 225665) = 497664 * k + 338498 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 338498) = 248832 * k + 169249 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 169249) = 373248 * k + 253874 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 253874) = 186624 * k + 126937 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 126937) = 279936 * k + 190406 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 190406) = 139968 * k + 95203 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 95203) = 209952 * k + 142805 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 142805) = 314928 * k + 214208 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 214208) = 157464 * k + 107104 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 107104) = 78732 * k + 53552 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53552) = 39366 * k + 26776 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26776) = 19683 * k + 13388 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44575) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44575)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44699_mod_65536 {n : ℕ} (hn : n % 65536 = 44699) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44699 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44699) = 98304 * k + 67049 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67049) = 147456 * k + 100574 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100574) = 73728 * k + 50287 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 50287) = 110592 * k + 75431 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 75431) = 165888 * k + 113147 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 113147) = 248832 * k + 169721 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 169721) = 373248 * k + 254582 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 254582) = 186624 * k + 127291 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 127291) = 279936 * k + 190937 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 190937) = 419904 * k + 286406 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 286406) = 209952 * k + 143203 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 143203) = 314928 * k + 214805 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 214805) = 472392 * k + 322208 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 322208) = 236196 * k + 161104 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 161104) = 118098 * k + 80552 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 80552) = 59049 * k + 40276 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44699) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44699)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44711_mod_65536 {n : ℕ} (hn : n % 65536 = 44711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44711) = 98304 * k + 67067 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67067) = 147456 * k + 100601 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100601) = 221184 * k + 150902 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 150902) = 110592 * k + 75451 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 75451) = 165888 * k + 113177 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 113177) = 248832 * k + 169766 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 169766) = 124416 * k + 84883 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 84883) = 186624 * k + 127325 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 127325) = 279936 * k + 190988 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 190988) = 139968 * k + 95494 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 95494) = 69984 * k + 47747 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 47747) = 104976 * k + 71621 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 71621) = 157464 * k + 107432 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 107432) = 78732 * k + 53716 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53716) = 39366 * k + 26858 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26858) = 19683 * k + 13429 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44735_mod_65536 {n : ℕ} (hn : n % 65536 = 44735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44735) = 98304 * k + 67103 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67103) = 147456 * k + 100655 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100655) = 221184 * k + 150983 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 150983) = 331776 * k + 226475 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 226475) = 497664 * k + 339713 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 339713) = 746496 * k + 509570 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 509570) = 373248 * k + 254785 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 254785) = 559872 * k + 382178 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 382178) = 279936 * k + 191089 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 191089) = 419904 * k + 286634 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 286634) = 209952 * k + 143317 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 143317) = 314928 * k + 214976 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 214976) = 157464 * k + 107488 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 107488) = 78732 * k + 53744 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53744) = 39366 * k + 26872 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26872) = 19683 * k + 13436 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44831_mod_65536 {n : ℕ} (hn : n % 65536 = 44831) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44831 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44831) = 98304 * k + 67247 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67247) = 147456 * k + 100871 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 100871) = 221184 * k + 151307 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 151307) = 331776 * k + 226961 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 226961) = 497664 * k + 340442 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 340442) = 248832 * k + 170221 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 170221) = 373248 * k + 255332 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 255332) = 186624 * k + 127666 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 127666) = 93312 * k + 63833 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 63833) = 139968 * k + 95750 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 95750) = 69984 * k + 47875 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 47875) = 104976 * k + 71813 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 71813) = 157464 * k + 107720 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 107720) = 78732 * k + 53860 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53860) = 39366 * k + 26930 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26930) = 19683 * k + 13465 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44831) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44831)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44911_mod_65536 {n : ℕ} (hn : n % 65536 = 44911) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44911 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44911) = 98304 * k + 67367 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67367) = 147456 * k + 101051 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101051) = 221184 * k + 151577 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 151577) = 331776 * k + 227366 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 227366) = 165888 * k + 113683 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 113683) = 248832 * k + 170525 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 170525) = 373248 * k + 255788 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 255788) = 186624 * k + 127894 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 127894) = 93312 * k + 63947 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 63947) = 139968 * k + 95921 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 95921) = 209952 * k + 143882 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 143882) = 104976 * k + 71941 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 71941) = 157464 * k + 107912 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 107912) = 78732 * k + 53956 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 53956) = 39366 * k + 26978 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 26978) = 19683 * k + 13489 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44911) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44911)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_44959_mod_65536 {n : ℕ} (hn : n % 65536 = 44959) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 44959 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 44959) = 98304 * k + 67439 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67439) = 147456 * k + 101159 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101159) = 221184 * k + 151739 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 151739) = 331776 * k + 227609 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 227609) = 497664 * k + 341414 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 341414) = 248832 * k + 170707 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 170707) = 373248 * k + 256061 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 256061) = 559872 * k + 384092 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 384092) = 279936 * k + 192046 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 192046) = 139968 * k + 96023 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96023) = 209952 * k + 144035 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144035) = 314928 * k + 216053 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 216053) = 472392 * k + 324080 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 324080) = 236196 * k + 162040 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 162040) = 118098 * k + 81020 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81020) = 59049 * k + 40510 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 44959) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 44959)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45039_mod_65536 {n : ℕ} (hn : n % 65536 = 45039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45039) = 98304 * k + 67559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67559) = 147456 * k + 101339 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101339) = 221184 * k + 152009 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152009) = 331776 * k + 228014 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 228014) = 165888 * k + 114007 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114007) = 248832 * k + 171011 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171011) = 373248 * k + 256517 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 256517) = 559872 * k + 384776 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 384776) = 279936 * k + 192388 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 192388) = 139968 * k + 96194 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96194) = 69984 * k + 48097 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 48097) = 104976 * k + 72146 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72146) = 52488 * k + 36073 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36073) = 78732 * k + 54110 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54110) = 39366 * k + 27055 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27055) = 59049 * k + 40583 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45051_mod_65536 {n : ℕ} (hn : n % 65536 = 45051) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45051 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45051) = 98304 * k + 67577 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67577) = 147456 * k + 101366 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101366) = 73728 * k + 50683 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 50683) = 110592 * k + 76025 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76025) = 165888 * k + 114038 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114038) = 82944 * k + 57019 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 57019) = 124416 * k + 85529 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 85529) = 186624 * k + 128294 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128294) = 93312 * k + 64147 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 64147) = 139968 * k + 96221 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96221) = 209952 * k + 144332 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144332) = 104976 * k + 72166 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72166) = 52488 * k + 36083 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36083) = 78732 * k + 54125 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54125) = 118098 * k + 81188 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81188) = 59049 * k + 40594 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45051) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45051)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45083_mod_65536 {n : ℕ} (hn : n % 65536 = 45083) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45083 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45083) = 98304 * k + 67625 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67625) = 147456 * k + 101438 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101438) = 73728 * k + 50719 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 50719) = 110592 * k + 76079 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76079) = 165888 * k + 114119 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114119) = 248832 * k + 171179 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171179) = 373248 * k + 256769 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 256769) = 559872 * k + 385154 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 385154) = 279936 * k + 192577 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 192577) = 419904 * k + 288866 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 288866) = 209952 * k + 144433 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144433) = 314928 * k + 216650 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 216650) = 157464 * k + 108325 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108325) = 236196 * k + 162488 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 162488) = 118098 * k + 81244 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81244) = 59049 * k + 40622 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45083) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45083)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45103_mod_65536 {n : ℕ} (hn : n % 65536 = 45103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45103) = 98304 * k + 67655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67655) = 147456 * k + 101483 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101483) = 221184 * k + 152225 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152225) = 331776 * k + 228338 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 228338) = 165888 * k + 114169 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114169) = 248832 * k + 171254 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171254) = 124416 * k + 85627 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 85627) = 186624 * k + 128441 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128441) = 279936 * k + 192662 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 192662) = 139968 * k + 96331 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96331) = 209952 * k + 144497 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144497) = 314928 * k + 216746 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 216746) = 157464 * k + 108373 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108373) = 236196 * k + 162560 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 162560) = 118098 * k + 81280 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81280) = 59049 * k + 40640 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45119_mod_65536 {n : ℕ} (hn : n % 65536 = 45119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45119) = 98304 * k + 67679 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67679) = 147456 * k + 101519 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101519) = 221184 * k + 152279 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152279) = 331776 * k + 228419 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 228419) = 497664 * k + 342629 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 342629) = 746496 * k + 513944 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 513944) = 373248 * k + 256972 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 256972) = 186624 * k + 128486 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128486) = 93312 * k + 64243 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 64243) = 139968 * k + 96365 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96365) = 209952 * k + 144548 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144548) = 104976 * k + 72274 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72274) = 52488 * k + 36137 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36137) = 78732 * k + 54206 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54206) = 39366 * k + 27103 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27103) = 59049 * k + 40655 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45159_mod_65536 {n : ℕ} (hn : n % 65536 = 45159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45159) = 98304 * k + 67739 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67739) = 147456 * k + 101609 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101609) = 221184 * k + 152414 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152414) = 110592 * k + 76207 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76207) = 165888 * k + 114311 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114311) = 248832 * k + 171467 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171467) = 373248 * k + 257201 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 257201) = 559872 * k + 385802 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 385802) = 279936 * k + 192901 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 192901) = 419904 * k + 289352 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 289352) = 209952 * k + 144676 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 144676) = 104976 * k + 72338 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72338) = 52488 * k + 36169 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36169) = 78732 * k + 54254 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54254) = 39366 * k + 27127 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27127) = 59049 * k + 40691 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45211_mod_65536 {n : ℕ} (hn : n % 65536 = 45211) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45211 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45211) = 98304 * k + 67817 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67817) = 147456 * k + 101726 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101726) = 73728 * k + 50863 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 50863) = 110592 * k + 76295 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76295) = 165888 * k + 114443 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114443) = 248832 * k + 171665 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171665) = 373248 * k + 257498 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 257498) = 186624 * k + 128749 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128749) = 279936 * k + 193124 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 193124) = 139968 * k + 96562 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96562) = 69984 * k + 48281 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 48281) = 104976 * k + 72422 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72422) = 52488 * k + 36211 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36211) = 78732 * k + 54317 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54317) = 118098 * k + 81476 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81476) = 59049 * k + 40738 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45211) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45211)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45223_mod_65536 {n : ℕ} (hn : n % 65536 = 45223) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45223 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45223) = 98304 * k + 67835 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67835) = 147456 * k + 101753 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101753) = 221184 * k + 152630 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152630) = 110592 * k + 76315 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76315) = 165888 * k + 114473 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114473) = 248832 * k + 171710 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171710) = 124416 * k + 85855 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 85855) = 186624 * k + 128783 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128783) = 279936 * k + 193175 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 193175) = 419904 * k + 289763 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 289763) = 629856 * k + 434645 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 434645) = 944784 * k + 651968 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 651968) = 472392 * k + 325984 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 325984) = 236196 * k + 162992 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 162992) = 118098 * k + 81496 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81496) = 59049 * k + 40748 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45223) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45223)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45279_mod_65536 {n : ℕ} (hn : n % 65536 = 45279) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45279 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45279) = 98304 * k + 67919 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67919) = 147456 * k + 101879 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101879) = 221184 * k + 152819 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152819) = 331776 * k + 229229 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 229229) = 497664 * k + 343844 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 343844) = 248832 * k + 171922 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 171922) = 124416 * k + 85961 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 85961) = 186624 * k + 128942 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 128942) = 93312 * k + 64471 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 64471) = 139968 * k + 96707 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96707) = 209952 * k + 145061 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 145061) = 314928 * k + 217592 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 217592) = 157464 * k + 108796 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108796) = 78732 * k + 54398 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54398) = 39366 * k + 27199 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27199) = 59049 * k + 40799 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45279) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45279)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45311_mod_65536 {n : ℕ} (hn : n % 65536 = 45311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45311) = 98304 * k + 67967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 67967) = 147456 * k + 101951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 101951) = 221184 * k + 152927 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 152927) = 331776 * k + 229391 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 229391) = 497664 * k + 344087 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 344087) = 746496 * k + 516131 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 516131) = 1119744 * k + 774197 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 774197) = 1679616 * k + 1161296 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1161296) = 839808 * k + 580648 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 580648) = 419904 * k + 290324 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 290324) = 209952 * k + 145162 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 145162) = 104976 * k + 72581 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72581) = 157464 * k + 108872 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108872) = 78732 * k + 54436 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54436) = 39366 * k + 27218 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27218) = 19683 * k + 13609 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45339_mod_65536 {n : ℕ} (hn : n % 65536 = 45339) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45339 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45339) = 98304 * k + 68009 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68009) = 147456 * k + 102014 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102014) = 73728 * k + 51007 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 51007) = 110592 * k + 76511 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76511) = 165888 * k + 114767 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114767) = 248832 * k + 172151 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 172151) = 373248 * k + 258227 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 258227) = 559872 * k + 387341 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 387341) = 839808 * k + 581012 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 581012) = 419904 * k + 290506 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 290506) = 209952 * k + 145253 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 145253) = 314928 * k + 217880 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 217880) = 157464 * k + 108940 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108940) = 78732 * k + 54470 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54470) = 39366 * k + 27235 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27235) = 59049 * k + 40853 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45339) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45339)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45359_mod_65536 {n : ℕ} (hn : n % 65536 = 45359) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45359 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45359) = 98304 * k + 68039 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68039) = 147456 * k + 102059 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102059) = 221184 * k + 153089 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 153089) = 331776 * k + 229634 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 229634) = 165888 * k + 114817 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 114817) = 248832 * k + 172226 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 172226) = 124416 * k + 86113 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 86113) = 186624 * k + 129170 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 129170) = 93312 * k + 64585 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 64585) = 139968 * k + 96878 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 96878) = 69984 * k + 48439 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 48439) = 104976 * k + 72659 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 72659) = 157464 * k + 108989 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 108989) = 236196 * k + 163484 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 163484) = 118098 * k + 81742 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 81742) = 59049 * k + 40871 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45359) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45359)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45503_mod_65536 {n : ℕ} (hn : n % 65536 = 45503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45503) = 98304 * k + 68255 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68255) = 147456 * k + 102383 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102383) = 221184 * k + 153575 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 153575) = 331776 * k + 230363 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 230363) = 497664 * k + 345545 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 345545) = 746496 * k + 518318 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 518318) = 373248 * k + 259159 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 259159) = 559872 * k + 388739 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 388739) = 839808 * k + 583109 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 583109) = 1259712 * k + 874664 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 874664) = 629856 * k + 437332 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 437332) = 314928 * k + 218666 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 218666) = 157464 * k + 109333 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109333) = 236196 * k + 164000 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 164000) = 118098 * k + 82000 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82000) = 59049 * k + 41000 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45535_mod_65536 {n : ℕ} (hn : n % 65536 = 45535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45535) = 98304 * k + 68303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68303) = 147456 * k + 102455 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102455) = 221184 * k + 153683 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 153683) = 331776 * k + 230525 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 230525) = 497664 * k + 345788 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 345788) = 248832 * k + 172894 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 172894) = 124416 * k + 86447 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 86447) = 186624 * k + 129671 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 129671) = 279936 * k + 194507 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 194507) = 419904 * k + 291761 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 291761) = 629856 * k + 437642 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 437642) = 314928 * k + 218821 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 218821) = 472392 * k + 328232 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 328232) = 236196 * k + 164116 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 164116) = 118098 * k + 82058 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82058) = 59049 * k + 41029 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45595_mod_65536 {n : ℕ} (hn : n % 65536 = 45595) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45595 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45595) = 98304 * k + 68393 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68393) = 147456 * k + 102590 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102590) = 73728 * k + 51295 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 51295) = 110592 * k + 76943 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 76943) = 165888 * k + 115415 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 115415) = 248832 * k + 173123 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 173123) = 373248 * k + 259685 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 259685) = 559872 * k + 389528 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 389528) = 279936 * k + 194764 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 194764) = 139968 * k + 97382 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 97382) = 69984 * k + 48691 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 48691) = 104976 * k + 73037 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73037) = 157464 * k + 109556 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109556) = 78732 * k + 54778 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54778) = 39366 * k + 27389 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27389) = 59049 * k + 41084 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45595) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45595)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45599_mod_65536 {n : ℕ} (hn : n % 65536 = 45599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45599) = 98304 * k + 68399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68399) = 147456 * k + 102599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102599) = 221184 * k + 153899 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 153899) = 331776 * k + 230849 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 230849) = 497664 * k + 346274 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 346274) = 248832 * k + 173137 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 173137) = 373248 * k + 259706 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 259706) = 186624 * k + 129853 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 129853) = 279936 * k + 194780 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 194780) = 139968 * k + 97390 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 97390) = 69984 * k + 48695 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 48695) = 104976 * k + 73043 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73043) = 157464 * k + 109565 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109565) = 236196 * k + 164348 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 164348) = 118098 * k + 82174 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82174) = 59049 * k + 41087 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45679_mod_65536 {n : ℕ} (hn : n % 65536 = 45679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45679) = 98304 * k + 68519 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68519) = 147456 * k + 102779 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102779) = 221184 * k + 154169 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 154169) = 331776 * k + 231254 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 231254) = 165888 * k + 115627 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 115627) = 248832 * k + 173441 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 173441) = 373248 * k + 260162 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 260162) = 186624 * k + 130081 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 130081) = 279936 * k + 195122 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 195122) = 139968 * k + 97561 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 97561) = 209952 * k + 146342 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 146342) = 104976 * k + 73171 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73171) = 157464 * k + 109757 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109757) = 236196 * k + 164636 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 164636) = 118098 * k + 82318 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82318) = 59049 * k + 41159 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45735_mod_65536 {n : ℕ} (hn : n % 65536 = 45735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45735) = 98304 * k + 68603 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68603) = 147456 * k + 102905 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102905) = 221184 * k + 154358 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 154358) = 110592 * k + 77179 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 77179) = 165888 * k + 115769 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 115769) = 248832 * k + 173654 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 173654) = 124416 * k + 86827 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 86827) = 186624 * k + 130241 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 130241) = 279936 * k + 195362 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 195362) = 139968 * k + 97681 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 97681) = 209952 * k + 146522 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 146522) = 104976 * k + 73261 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73261) = 157464 * k + 109892 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109892) = 78732 * k + 54946 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54946) = 39366 * k + 27473 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27473) = 59049 * k + 41210 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45775_mod_65536 {n : ℕ} (hn : n % 65536 = 45775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45775) = 98304 * k + 68663 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68663) = 147456 * k + 102995 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 102995) = 221184 * k + 154493 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 154493) = 331776 * k + 231740 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 231740) = 165888 * k + 115870 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 115870) = 82944 * k + 57935 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 57935) = 124416 * k + 86903 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 86903) = 186624 * k + 130355 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 130355) = 279936 * k + 195533 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 195533) = 419904 * k + 293300 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 293300) = 209952 * k + 146650 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 146650) = 104976 * k + 73325 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73325) = 157464 * k + 109988 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 109988) = 78732 * k + 54994 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 54994) = 39366 * k + 27497 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27497) = 59049 * k + 41246 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45799_mod_65536 {n : ℕ} (hn : n % 65536 = 45799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45799) = 98304 * k + 68699 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68699) = 147456 * k + 103049 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103049) = 221184 * k + 154574 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 154574) = 110592 * k + 77287 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 77287) = 165888 * k + 115931 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 115931) = 248832 * k + 173897 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 173897) = 373248 * k + 260846 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 260846) = 186624 * k + 130423 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 130423) = 279936 * k + 195635 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 195635) = 419904 * k + 293453 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 293453) = 629856 * k + 440180 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 440180) = 314928 * k + 220090 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 220090) = 157464 * k + 110045 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 110045) = 236196 * k + 165068 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 165068) = 118098 * k + 82534 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82534) = 59049 * k + 41267 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45851_mod_65536 {n : ℕ} (hn : n % 65536 = 45851) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45851 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45851) = 98304 * k + 68777 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68777) = 147456 * k + 103166 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103166) = 73728 * k + 51583 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 51583) = 110592 * k + 77375 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 77375) = 165888 * k + 116063 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 116063) = 248832 * k + 174095 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 174095) = 373248 * k + 261143 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 261143) = 559872 * k + 391715 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 391715) = 839808 * k + 587573 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 587573) = 1259712 * k + 881360 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 881360) = 629856 * k + 440680 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 440680) = 314928 * k + 220340 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 220340) = 157464 * k + 110170 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 110170) = 78732 * k + 55085 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55085) = 118098 * k + 82628 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 82628) = 59049 * k + 41314 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45851) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45851)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45855_mod_65536 {n : ℕ} (hn : n % 65536 = 45855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45855) = 98304 * k + 68783 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68783) = 147456 * k + 103175 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103175) = 221184 * k + 154763 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 154763) = 331776 * k + 232145 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 232145) = 497664 * k + 348218 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 348218) = 248832 * k + 174109 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 174109) = 373248 * k + 261164 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 261164) = 186624 * k + 130582 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 130582) = 93312 * k + 65291 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 65291) = 139968 * k + 97937 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 97937) = 209952 * k + 146906 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 146906) = 104976 * k + 73453 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73453) = 157464 * k + 110180 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 110180) = 78732 * k + 55090 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55090) = 39366 * k + 27545 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27545) = 59049 * k + 41318 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_45983_mod_65536 {n : ℕ} (hn : n % 65536 = 45983) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 45983 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 45983) = 98304 * k + 68975 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 68975) = 147456 * k + 103463 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103463) = 221184 * k + 155195 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 155195) = 331776 * k + 232793 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 232793) = 497664 * k + 349190 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 349190) = 248832 * k + 174595 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 174595) = 373248 * k + 261893 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 261893) = 559872 * k + 392840 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 392840) = 279936 * k + 196420 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 196420) = 139968 * k + 98210 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 98210) = 69984 * k + 49105 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 49105) = 104976 * k + 73658 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73658) = 52488 * k + 36829 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36829) = 78732 * k + 55244 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55244) = 39366 * k + 27622 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27622) = 19683 * k + 13811 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 45983) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 45983)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46063_mod_65536 {n : ℕ} (hn : n % 65536 = 46063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46063) = 98304 * k + 69095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69095) = 147456 * k + 103643 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103643) = 221184 * k + 155465 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 155465) = 331776 * k + 233198 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 233198) = 165888 * k + 116599 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 116599) = 248832 * k + 174899 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 174899) = 373248 * k + 262349 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 262349) = 559872 * k + 393524 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 393524) = 279936 * k + 196762 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 196762) = 139968 * k + 98381 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 98381) = 209952 * k + 147572 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 147572) = 104976 * k + 73786 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73786) = 52488 * k + 36893 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 36893) = 78732 * k + 55340 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55340) = 39366 * k + 27670 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27670) = 19683 * k + 13835 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46127_mod_65536 {n : ℕ} (hn : n % 65536 = 46127) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46127 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46127) = 98304 * k + 69191 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69191) = 147456 * k + 103787 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 103787) = 221184 * k + 155681 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 155681) = 331776 * k + 233522 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 233522) = 165888 * k + 116761 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 116761) = 248832 * k + 175142 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 175142) = 124416 * k + 87571 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 87571) = 186624 * k + 131357 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 131357) = 279936 * k + 197036 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 197036) = 139968 * k + 98518 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 98518) = 69984 * k + 49259 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 49259) = 104976 * k + 73889 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 73889) = 157464 * k + 110834 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 110834) = 78732 * k + 55417 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55417) = 118098 * k + 83126 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 83126) = 59049 * k + 41563 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46127) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46127)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46247_mod_65536 {n : ℕ} (hn : n % 65536 = 46247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46247) = 98304 * k + 69371 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69371) = 147456 * k + 104057 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104057) = 221184 * k + 156086 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 156086) = 110592 * k + 78043 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 78043) = 165888 * k + 117065 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 117065) = 248832 * k + 175598 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 175598) = 124416 * k + 87799 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 87799) = 186624 * k + 131699 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 131699) = 279936 * k + 197549 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 197549) = 419904 * k + 296324 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 296324) = 209952 * k + 148162 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 148162) = 104976 * k + 74081 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 74081) = 157464 * k + 111122 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 111122) = 78732 * k + 55561 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55561) = 118098 * k + 83342 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 83342) = 59049 * k + 41671 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46335_mod_65536 {n : ℕ} (hn : n % 65536 = 46335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46335) = 98304 * k + 69503 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69503) = 147456 * k + 104255 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104255) = 221184 * k + 156383 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 156383) = 331776 * k + 234575 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 234575) = 497664 * k + 351863 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 351863) = 746496 * k + 527795 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 527795) = 1119744 * k + 791693 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 791693) = 1679616 * k + 1187540 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 1187540) = 839808 * k + 593770 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 593770) = 419904 * k + 296885 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 296885) = 629856 * k + 445328 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 445328) = 314928 * k + 222664 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 222664) = 157464 * k + 111332 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 111332) = 78732 * k + 55666 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55666) = 39366 * k + 27833 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27833) = 59049 * k + 41750 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46407_mod_65536 {n : ℕ} (hn : n % 65536 = 46407) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46407 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46407) = 98304 * k + 69611 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69611) = 147456 * k + 104417 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104417) = 221184 * k + 156626 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 156626) = 110592 * k + 78313 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 78313) = 165888 * k + 117470 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 117470) = 82944 * k + 58735 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 58735) = 124416 * k + 88103 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 88103) = 186624 * k + 132155 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 132155) = 279936 * k + 198233 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 198233) = 419904 * k + 297350 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 297350) = 209952 * k + 148675 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 148675) = 314928 * k + 223013 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 223013) = 472392 * k + 334520 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 334520) = 236196 * k + 167260 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 167260) = 118098 * k + 83630 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 83630) = 59049 * k + 41815 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46407) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46407)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46463_mod_65536 {n : ℕ} (hn : n % 65536 = 46463) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46463 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46463) = 98304 * k + 69695 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69695) = 147456 * k + 104543 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104543) = 221184 * k + 156815 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 156815) = 331776 * k + 235223 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 235223) = 497664 * k + 352835 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 352835) = 746496 * k + 529253 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 529253) = 1119744 * k + 793880 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 793880) = 559872 * k + 396940 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 396940) = 279936 * k + 198470 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 198470) = 139968 * k + 99235 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 99235) = 209952 * k + 148853 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 148853) = 314928 * k + 223280 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 223280) = 157464 * k + 111640 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 111640) = 78732 * k + 55820 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55820) = 39366 * k + 27910 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27910) = 19683 * k + 13955 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46463) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46463)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46567_mod_65536 {n : ℕ} (hn : n % 65536 = 46567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46567) = 98304 * k + 69851 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69851) = 147456 * k + 104777 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104777) = 221184 * k + 157166 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 157166) = 110592 * k + 78583 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 78583) = 165888 * k + 117875 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 117875) = 248832 * k + 176813 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 176813) = 373248 * k + 265220 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 265220) = 186624 * k + 132610 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 132610) = 93312 * k + 66305 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 66305) = 139968 * k + 99458 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 99458) = 69984 * k + 49729 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 49729) = 104976 * k + 74594 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 74594) = 52488 * k + 37297 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 37297) = 78732 * k + 55946 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 55946) = 39366 * k + 27973 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 27973) = 59049 * k + 41960 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46619_mod_65536 {n : ℕ} (hn : n % 65536 = 46619) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46619 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46619) = 98304 * k + 69929 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 69929) = 147456 * k + 104894 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 104894) = 73728 * k + 52447 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 52447) = 110592 * k + 78671 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 78671) = 165888 * k + 118007 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 118007) = 248832 * k + 177011 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 177011) = 373248 * k + 265517 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 265517) = 559872 * k + 398276 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 398276) = 279936 * k + 199138 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 199138) = 139968 * k + 99569 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 99569) = 209952 * k + 149354 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 149354) = 104976 * k + 74677 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 74677) = 157464 * k + 112016 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 112016) = 78732 * k + 56008 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56008) = 39366 * k + 28004 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28004) = 19683 * k + 14002 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46619) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46619)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46747_mod_65536 {n : ℕ} (hn : n % 65536 = 46747) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46747 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46747) = 98304 * k + 70121 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70121) = 147456 * k + 105182 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105182) = 73728 * k + 52591 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 52591) = 110592 * k + 78887 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 78887) = 165888 * k + 118331 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 118331) = 248832 * k + 177497 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 177497) = 373248 * k + 266246 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 266246) = 186624 * k + 133123 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 133123) = 279936 * k + 199685 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 199685) = 419904 * k + 299528 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 299528) = 209952 * k + 149764 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 149764) = 104976 * k + 74882 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 74882) = 52488 * k + 37441 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 37441) = 78732 * k + 56162 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56162) = 39366 * k + 28081 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28081) = 59049 * k + 42122 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46747) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46747)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46799_mod_65536 {n : ℕ} (hn : n % 65536 = 46799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46799) = 98304 * k + 70199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70199) = 147456 * k + 105299 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105299) = 221184 * k + 157949 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 157949) = 331776 * k + 236924 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 236924) = 165888 * k + 118462 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 118462) = 82944 * k + 59231 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 59231) = 124416 * k + 88847 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 88847) = 186624 * k + 133271 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 133271) = 279936 * k + 199907 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 199907) = 419904 * k + 299861 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 299861) = 629856 * k + 449792 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 449792) = 314928 * k + 224896 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 224896) = 157464 * k + 112448 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 112448) = 78732 * k + 56224 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56224) = 39366 * k + 28112 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28112) = 19683 * k + 14056 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46919_mod_65536 {n : ℕ} (hn : n % 65536 = 46919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46919) = 98304 * k + 70379 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70379) = 147456 * k + 105569 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105569) = 221184 * k + 158354 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 158354) = 110592 * k + 79177 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 79177) = 165888 * k + 118766 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 118766) = 82944 * k + 59383 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 59383) = 124416 * k + 89075 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 89075) = 186624 * k + 133613 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 133613) = 279936 * k + 200420 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 200420) = 139968 * k + 100210 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 100210) = 69984 * k + 50105 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 50105) = 104976 * k + 75158 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75158) = 52488 * k + 37579 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 37579) = 78732 * k + 56369 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56369) = 118098 * k + 84554 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 84554) = 59049 * k + 42277 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_46939_mod_65536 {n : ℕ} (hn : n % 65536 = 46939) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 46939 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 46939) = 98304 * k + 70409 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70409) = 147456 * k + 105614 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105614) = 73728 * k + 52807 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 52807) = 110592 * k + 79211 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 79211) = 165888 * k + 118817 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 118817) = 248832 * k + 178226 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 178226) = 124416 * k + 89113 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 89113) = 186624 * k + 133670 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 133670) = 93312 * k + 66835 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 66835) = 139968 * k + 100253 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 100253) = 209952 * k + 150380 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 150380) = 104976 * k + 75190 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75190) = 52488 * k + 37595 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 37595) = 78732 * k + 56393 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56393) = 118098 * k + 84590 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 84590) = 59049 * k + 42295 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 46939) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 46939)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47007_mod_65536 {n : ℕ} (hn : n % 65536 = 47007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47007) = 98304 * k + 70511 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70511) = 147456 * k + 105767 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105767) = 221184 * k + 158651 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 158651) = 331776 * k + 237977 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 237977) = 497664 * k + 356966 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 356966) = 248832 * k + 178483 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 178483) = 373248 * k + 267725 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 267725) = 559872 * k + 401588 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 401588) = 279936 * k + 200794 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 200794) = 139968 * k + 100397 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 100397) = 209952 * k + 150596 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 150596) = 104976 * k + 75298 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75298) = 52488 * k + 37649 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 37649) = 78732 * k + 56474 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56474) = 39366 * k + 28237 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28237) = 59049 * k + 42356 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47039_mod_65536 {n : ℕ} (hn : n % 65536 = 47039) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47039 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47039) = 98304 * k + 70559 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70559) = 147456 * k + 105839 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105839) = 221184 * k + 158759 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 158759) = 331776 * k + 238139 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 238139) = 497664 * k + 357209 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 357209) = 746496 * k + 535814 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 535814) = 373248 * k + 267907 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 267907) = 559872 * k + 401861 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 401861) = 839808 * k + 602792 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 602792) = 419904 * k + 301396 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 301396) = 209952 * k + 150698 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 150698) = 104976 * k + 75349 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75349) = 157464 * k + 113024 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113024) = 78732 * k + 56512 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56512) = 39366 * k + 28256 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28256) = 19683 * k + 14128 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47039) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47039)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47099_mod_65536 {n : ℕ} (hn : n % 65536 = 47099) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47099 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47099) = 98304 * k + 70649 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70649) = 147456 * k + 105974 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 105974) = 73728 * k + 52987 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 52987) = 110592 * k + 79481 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 79481) = 165888 * k + 119222 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 119222) = 82944 * k + 59611 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 59611) = 124416 * k + 89417 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 89417) = 186624 * k + 134126 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 134126) = 93312 * k + 67063 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 67063) = 139968 * k + 100595 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 100595) = 209952 * k + 150893 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 150893) = 314928 * k + 226340 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 226340) = 157464 * k + 113170 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113170) = 78732 * k + 56585 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56585) = 118098 * k + 84878 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 84878) = 59049 * k + 42439 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47099) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47099)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47167_mod_65536 {n : ℕ} (hn : n % 65536 = 47167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47167) = 98304 * k + 70751 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70751) = 147456 * k + 106127 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106127) = 221184 * k + 159191 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 159191) = 331776 * k + 238787 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 238787) = 497664 * k + 358181 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 358181) = 746496 * k + 537272 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 537272) = 373248 * k + 268636 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 268636) = 186624 * k + 134318 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 134318) = 93312 * k + 67159 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 67159) = 139968 * k + 100739 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 100739) = 209952 * k + 151109 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 151109) = 314928 * k + 226664 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 226664) = 157464 * k + 113332 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113332) = 78732 * k + 56666 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56666) = 39366 * k + 28333 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28333) = 59049 * k + 42500 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47207_mod_65536 {n : ℕ} (hn : n % 65536 = 47207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47207) = 98304 * k + 70811 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70811) = 147456 * k + 106217 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106217) = 221184 * k + 159326 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 159326) = 110592 * k + 79663 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 79663) = 165888 * k + 119495 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 119495) = 248832 * k + 179243 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 179243) = 373248 * k + 268865 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 268865) = 559872 * k + 403298 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 403298) = 279936 * k + 201649 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 201649) = 419904 * k + 302474 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 302474) = 209952 * k + 151237 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 151237) = 314928 * k + 226856 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 226856) = 157464 * k + 113428 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113428) = 78732 * k + 56714 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 56714) = 39366 * k + 28357 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28357) = 59049 * k + 42536 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47231_mod_65536 {n : ℕ} (hn : n % 65536 = 47231) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47231 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47231) = 98304 * k + 70847 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70847) = 147456 * k + 106271 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106271) = 221184 * k + 159407 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 159407) = 331776 * k + 239111 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 239111) = 497664 * k + 358667 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 358667) = 746496 * k + 538001 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 538001) = 1119744 * k + 807002 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 807002) = 559872 * k + 403501 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 403501) = 839808 * k + 605252 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 605252) = 419904 * k + 302626 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 302626) = 209952 * k + 151313 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 151313) = 314928 * k + 226970 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 226970) = 157464 * k + 113485 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113485) = 236196 * k + 170228 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 170228) = 118098 * k + 85114 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85114) = 59049 * k + 42557 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47231) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47231)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47327_mod_65536 {n : ℕ} (hn : n % 65536 = 47327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47327) = 98304 * k + 70991 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 70991) = 147456 * k + 106487 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106487) = 221184 * k + 159731 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 159731) = 331776 * k + 239597 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 239597) = 497664 * k + 359396 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 359396) = 248832 * k + 179698 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 179698) = 124416 * k + 89849 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 89849) = 186624 * k + 134774 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 134774) = 93312 * k + 67387 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 67387) = 139968 * k + 101081 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 101081) = 209952 * k + 151622 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 151622) = 104976 * k + 75811 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75811) = 157464 * k + 113717 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113717) = 236196 * k + 170576 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 170576) = 118098 * k + 85288 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85288) = 59049 * k + 42644 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47387_mod_65536 {n : ℕ} (hn : n % 65536 = 47387) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47387 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47387) = 98304 * k + 71081 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71081) = 147456 * k + 106622 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106622) = 73728 * k + 53311 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 53311) = 110592 * k + 79967 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 79967) = 165888 * k + 119951 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 119951) = 248832 * k + 179927 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 179927) = 373248 * k + 269891 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 269891) = 559872 * k + 404837 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 404837) = 839808 * k + 607256 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 607256) = 419904 * k + 303628 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 303628) = 209952 * k + 151814 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 151814) = 104976 * k + 75907 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 75907) = 157464 * k + 113861 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 113861) = 236196 * k + 170792 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 170792) = 118098 * k + 85396 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85396) = 59049 * k + 42698 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47387) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47387)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47423_mod_65536 {n : ℕ} (hn : n % 65536 = 47423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47423) = 98304 * k + 71135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71135) = 147456 * k + 106703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106703) = 221184 * k + 160055 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 160055) = 331776 * k + 240083 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 240083) = 497664 * k + 360125 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 360125) = 746496 * k + 540188 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 540188) = 373248 * k + 270094 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 270094) = 186624 * k + 135047 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 135047) = 279936 * k + 202571 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 202571) = 419904 * k + 303857 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 303857) = 629856 * k + 455786 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 455786) = 314928 * k + 227893 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 227893) = 472392 * k + 341840 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 341840) = 236196 * k + 170920 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 170920) = 118098 * k + 85460 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85460) = 59049 * k + 42730 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47487_mod_65536 {n : ℕ} (hn : n % 65536 = 47487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47487) = 98304 * k + 71231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71231) = 147456 * k + 106847 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106847) = 221184 * k + 160271 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 160271) = 331776 * k + 240407 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 240407) = 497664 * k + 360611 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 360611) = 746496 * k + 540917 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 540917) = 1119744 * k + 811376 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 811376) = 559872 * k + 405688 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 405688) = 279936 * k + 202844 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 202844) = 139968 * k + 101422 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 101422) = 69984 * k + 50711 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 50711) = 104976 * k + 76067 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 76067) = 157464 * k + 114101 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 114101) = 236196 * k + 171152 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 171152) = 118098 * k + 85576 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85576) = 59049 * k + 42788 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47519_mod_65536 {n : ℕ} (hn : n % 65536 = 47519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47519) = 98304 * k + 71279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71279) = 147456 * k + 106919 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 106919) = 221184 * k + 160379 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 160379) = 331776 * k + 240569 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 240569) = 497664 * k + 360854 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 360854) = 248832 * k + 180427 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 180427) = 373248 * k + 270641 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 270641) = 559872 * k + 405962 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 405962) = 279936 * k + 202981 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 202981) = 419904 * k + 304472 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 304472) = 209952 * k + 152236 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 152236) = 104976 * k + 76118 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 76118) = 52488 * k + 38059 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 38059) = 78732 * k + 57089 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57089) = 118098 * k + 85634 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 85634) = 59049 * k + 42817 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47591_mod_65536 {n : ℕ} (hn : n % 65536 = 47591) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47591 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47591) = 98304 * k + 71387 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71387) = 147456 * k + 107081 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 107081) = 221184 * k + 160622 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 160622) = 110592 * k + 80311 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 80311) = 165888 * k + 120467 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 120467) = 248832 * k + 180701 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 180701) = 373248 * k + 271052 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 271052) = 186624 * k + 135526 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 135526) = 93312 * k + 67763 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 67763) = 139968 * k + 101645 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 101645) = 209952 * k + 152468 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 152468) = 104976 * k + 76234 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 76234) = 52488 * k + 38117 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 38117) = 78732 * k + 57176 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57176) = 39366 * k + 28588 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28588) = 19683 * k + 14294 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47591) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47591)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47663_mod_65536 {n : ℕ} (hn : n % 65536 = 47663) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47663 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47663) = 98304 * k + 71495 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71495) = 147456 * k + 107243 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 107243) = 221184 * k + 160865 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 160865) = 331776 * k + 241298 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 241298) = 165888 * k + 120649 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 120649) = 248832 * k + 180974 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 180974) = 124416 * k + 90487 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 90487) = 186624 * k + 135731 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 135731) = 279936 * k + 203597 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 203597) = 419904 * k + 305396 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 305396) = 209952 * k + 152698 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 152698) = 104976 * k + 76349 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 76349) = 157464 * k + 114524 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 114524) = 78732 * k + 57262 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57262) = 39366 * k + 28631 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28631) = 59049 * k + 42947 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47663) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47663)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_47807_mod_65536 {n : ℕ} (hn : n % 65536 = 47807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 47807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 47807) = 98304 * k + 71711 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 71711) = 147456 * k + 107567 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 107567) = 221184 * k + 161351 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 161351) = 331776 * k + 242027 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 242027) = 497664 * k + 363041 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 363041) = 746496 * k + 544562 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 544562) = 373248 * k + 272281 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 272281) = 559872 * k + 408422 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 408422) = 279936 * k + 204211 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 204211) = 419904 * k + 306317 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 306317) = 629856 * k + 459476 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 459476) = 314928 * k + 229738 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 229738) = 157464 * k + 114869 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 114869) = 236196 * k + 172304 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 172304) = 118098 * k + 86152 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 86152) = 59049 * k + 43076 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 47807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 47807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48063_mod_65536 {n : ℕ} (hn : n % 65536 = 48063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48063) = 98304 * k + 72095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72095) = 147456 * k + 108143 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108143) = 221184 * k + 162215 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 162215) = 331776 * k + 243323 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 243323) = 497664 * k + 364985 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 364985) = 746496 * k + 547478 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 547478) = 373248 * k + 273739 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 273739) = 559872 * k + 410609 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 410609) = 839808 * k + 615914 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 615914) = 419904 * k + 307957 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 307957) = 629856 * k + 461936 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 461936) = 314928 * k + 230968 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 230968) = 157464 * k + 115484 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 115484) = 78732 * k + 57742 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57742) = 39366 * k + 28871 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28871) = 59049 * k + 43307 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48095_mod_65536 {n : ℕ} (hn : n % 65536 = 48095) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48095 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48095) = 98304 * k + 72143 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72143) = 147456 * k + 108215 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108215) = 221184 * k + 162323 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 162323) = 331776 * k + 243485 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 243485) = 497664 * k + 365228 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 365228) = 248832 * k + 182614 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 182614) = 124416 * k + 91307 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 91307) = 186624 * k + 136961 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 136961) = 279936 * k + 205442 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 205442) = 139968 * k + 102721 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 102721) = 209952 * k + 154082 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 154082) = 104976 * k + 77041 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 77041) = 157464 * k + 115562 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 115562) = 78732 * k + 57781 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57781) = 118098 * k + 86672 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 86672) = 59049 * k + 43336 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48095) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48095)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48111_mod_65536 {n : ℕ} (hn : n % 65536 = 48111) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48111 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48111) = 98304 * k + 72167 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72167) = 147456 * k + 108251 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108251) = 221184 * k + 162377 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 162377) = 331776 * k + 243566 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 243566) = 165888 * k + 121783 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 121783) = 248832 * k + 182675 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 182675) = 373248 * k + 274013 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 274013) = 559872 * k + 411020 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 411020) = 279936 * k + 205510 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 205510) = 139968 * k + 102755 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 102755) = 209952 * k + 154133 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 154133) = 314928 * k + 231200 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 231200) = 157464 * k + 115600 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 115600) = 78732 * k + 57800 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57800) = 39366 * k + 28900 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 28900) = 19683 * k + 14450 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48111) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48111)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48155_mod_65536 {n : ℕ} (hn : n % 65536 = 48155) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48155 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48155) = 98304 * k + 72233 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72233) = 147456 * k + 108350 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108350) = 73728 * k + 54175 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 54175) = 110592 * k + 81263 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 81263) = 165888 * k + 121895 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 121895) = 248832 * k + 182843 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 182843) = 373248 * k + 274265 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 274265) = 559872 * k + 411398 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 411398) = 279936 * k + 205699 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 205699) = 419904 * k + 308549 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 308549) = 629856 * k + 462824 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 462824) = 314928 * k + 231412 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 231412) = 157464 * k + 115706 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 115706) = 78732 * k + 57853 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 57853) = 118098 * k + 86780 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 86780) = 59049 * k + 43390 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48155) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48155)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48295_mod_65536 {n : ℕ} (hn : n % 65536 = 48295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48295) = 98304 * k + 72443 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72443) = 147456 * k + 108665 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108665) = 221184 * k + 162998 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 162998) = 110592 * k + 81499 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 81499) = 165888 * k + 122249 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 122249) = 248832 * k + 183374 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 183374) = 124416 * k + 91687 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 91687) = 186624 * k + 137531 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 137531) = 279936 * k + 206297 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 206297) = 419904 * k + 309446 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 309446) = 209952 * k + 154723 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 154723) = 314928 * k + 232085 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 232085) = 472392 * k + 348128 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 348128) = 236196 * k + 174064 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 174064) = 118098 * k + 87032 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 87032) = 59049 * k + 43516 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48335_mod_65536 {n : ℕ} (hn : n % 65536 = 48335) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48335 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48335) = 98304 * k + 72503 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72503) = 147456 * k + 108755 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108755) = 221184 * k + 163133 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 163133) = 331776 * k + 244700 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 244700) = 165888 * k + 122350 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 122350) = 82944 * k + 61175 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 61175) = 124416 * k + 91763 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 91763) = 186624 * k + 137645 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 137645) = 279936 * k + 206468 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 206468) = 139968 * k + 103234 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 103234) = 69984 * k + 51617 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 51617) = 104976 * k + 77426 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 77426) = 52488 * k + 38713 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 38713) = 78732 * k + 58070 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58070) = 39366 * k + 29035 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29035) = 59049 * k + 43553 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48335) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48335)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48379_mod_65536 {n : ℕ} (hn : n % 65536 = 48379) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48379 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48379) = 98304 * k + 72569 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72569) = 147456 * k + 108854 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 108854) = 73728 * k + 54427 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 54427) = 110592 * k + 81641 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 81641) = 165888 * k + 122462 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 122462) = 82944 * k + 61231 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 61231) = 124416 * k + 91847 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 91847) = 186624 * k + 137771 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 137771) = 279936 * k + 206657 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 206657) = 419904 * k + 309986 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 309986) = 209952 * k + 154993 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 154993) = 314928 * k + 232490 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 232490) = 157464 * k + 116245 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 116245) = 236196 * k + 174368 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 174368) = 118098 * k + 87184 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 87184) = 59049 * k + 43592 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48379) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48379)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48455_mod_65536 {n : ℕ} (hn : n % 65536 = 48455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48455) = 98304 * k + 72683 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72683) = 147456 * k + 109025 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109025) = 221184 * k + 163538 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 163538) = 110592 * k + 81769 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 81769) = 165888 * k + 122654 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 122654) = 82944 * k + 61327 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 61327) = 124416 * k + 91991 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 91991) = 186624 * k + 137987 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 137987) = 279936 * k + 206981 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 206981) = 419904 * k + 310472 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 310472) = 209952 * k + 155236 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 155236) = 104976 * k + 77618 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 77618) = 52488 * k + 38809 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 38809) = 78732 * k + 58214 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58214) = 39366 * k + 29107 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29107) = 59049 * k + 43661 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48607_mod_65536 {n : ℕ} (hn : n % 65536 = 48607) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48607 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48607) = 98304 * k + 72911 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 72911) = 147456 * k + 109367 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109367) = 221184 * k + 164051 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 164051) = 331776 * k + 246077 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 246077) = 497664 * k + 369116 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 369116) = 248832 * k + 184558 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 184558) = 124416 * k + 92279 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 92279) = 186624 * k + 138419 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 138419) = 279936 * k + 207629 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 207629) = 419904 * k + 311444 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 311444) = 209952 * k + 155722 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 155722) = 104976 * k + 77861 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 77861) = 157464 * k + 116792 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 116792) = 78732 * k + 58396 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58396) = 39366 * k + 29198 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29198) = 19683 * k + 14599 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48607) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48607)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48687_mod_65536 {n : ℕ} (hn : n % 65536 = 48687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48687) = 98304 * k + 73031 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73031) = 147456 * k + 109547 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109547) = 221184 * k + 164321 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 164321) = 331776 * k + 246482 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 246482) = 165888 * k + 123241 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 123241) = 248832 * k + 184862 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 184862) = 124416 * k + 92431 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 92431) = 186624 * k + 138647 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 138647) = 279936 * k + 207971 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 207971) = 419904 * k + 311957 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 311957) = 629856 * k + 467936 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 467936) = 314928 * k + 233968 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 233968) = 157464 * k + 116984 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 116984) = 78732 * k + 58492 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58492) = 39366 * k + 29246 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29246) = 19683 * k + 14623 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48795_mod_65536 {n : ℕ} (hn : n % 65536 = 48795) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48795 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48795) = 98304 * k + 73193 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73193) = 147456 * k + 109790 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109790) = 73728 * k + 54895 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 54895) = 110592 * k + 82343 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 82343) = 165888 * k + 123515 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 123515) = 248832 * k + 185273 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 185273) = 373248 * k + 277910 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 277910) = 186624 * k + 138955 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 138955) = 279936 * k + 208433 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 208433) = 419904 * k + 312650 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 312650) = 209952 * k + 156325 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 156325) = 314928 * k + 234488 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 234488) = 157464 * k + 117244 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 117244) = 78732 * k + 58622 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58622) = 39366 * k + 29311 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29311) = 59049 * k + 43967 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48795) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48795)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48807_mod_65536 {n : ℕ} (hn : n % 65536 = 48807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48807) = 98304 * k + 73211 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73211) = 147456 * k + 109817 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109817) = 221184 * k + 164726 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 164726) = 110592 * k + 82363 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 82363) = 165888 * k + 123545 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 123545) = 248832 * k + 185318 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 185318) = 124416 * k + 92659 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 92659) = 186624 * k + 138989 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 138989) = 279936 * k + 208484 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 208484) = 139968 * k + 104242 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104242) = 69984 * k + 52121 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 52121) = 104976 * k + 78182 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78182) = 52488 * k + 39091 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 39091) = 78732 * k + 58637 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58637) = 118098 * k + 87956 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 87956) = 59049 * k + 43978 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48879_mod_65536 {n : ℕ} (hn : n % 65536 = 48879) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48879 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48879) = 98304 * k + 73319 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73319) = 147456 * k + 109979 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 109979) = 221184 * k + 164969 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 164969) = 331776 * k + 247454 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 247454) = 165888 * k + 123727 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 123727) = 248832 * k + 185591 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 185591) = 373248 * k + 278387 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 278387) = 559872 * k + 417581 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 417581) = 839808 * k + 626372 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 626372) = 419904 * k + 313186 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 313186) = 209952 * k + 156593 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 156593) = 314928 * k + 234890 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 234890) = 157464 * k + 117445 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 117445) = 236196 * k + 176168 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 176168) = 118098 * k + 88084 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88084) = 59049 * k + 44042 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48879) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48879)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48891_mod_65536 {n : ℕ} (hn : n % 65536 = 48891) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48891 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48891) = 98304 * k + 73337 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73337) = 147456 * k + 110006 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110006) = 73728 * k + 55003 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 55003) = 110592 * k + 82505 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 82505) = 165888 * k + 123758 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 123758) = 82944 * k + 61879 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 61879) = 124416 * k + 92819 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 92819) = 186624 * k + 139229 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 139229) = 279936 * k + 208844 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 208844) = 139968 * k + 104422 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104422) = 69984 * k + 52211 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 52211) = 104976 * k + 78317 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78317) = 157464 * k + 117476 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 117476) = 78732 * k + 58738 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58738) = 39366 * k + 29369 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29369) = 59049 * k + 44054 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48891) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48891)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48927_mod_65536 {n : ℕ} (hn : n % 65536 = 48927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48927) = 98304 * k + 73391 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73391) = 147456 * k + 110087 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110087) = 221184 * k + 165131 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 165131) = 331776 * k + 247697 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 247697) = 497664 * k + 371546 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 371546) = 248832 * k + 185773 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 185773) = 373248 * k + 278660 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 278660) = 186624 * k + 139330 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 139330) = 93312 * k + 69665 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 69665) = 139968 * k + 104498 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104498) = 69984 * k + 52249 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 52249) = 104976 * k + 78374 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78374) = 52488 * k + 39187 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 39187) = 78732 * k + 58781 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58781) = 118098 * k + 88172 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88172) = 59049 * k + 44086 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_48987_mod_65536 {n : ℕ} (hn : n % 65536 = 48987) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 48987 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 48987) = 98304 * k + 73481 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73481) = 147456 * k + 110222 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110222) = 73728 * k + 55111 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 55111) = 110592 * k + 82667 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 82667) = 165888 * k + 124001 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 124001) = 248832 * k + 186002 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 186002) = 124416 * k + 93001 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 93001) = 186624 * k + 139502 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 139502) = 93312 * k + 69751 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 69751) = 139968 * k + 104627 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104627) = 209952 * k + 156941 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 156941) = 314928 * k + 235412 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 235412) = 157464 * k + 117706 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 117706) = 78732 * k + 58853 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58853) = 118098 * k + 88280 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88280) = 59049 * k + 44140 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 48987) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 48987)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49007_mod_65536 {n : ℕ} (hn : n % 65536 = 49007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49007) = 98304 * k + 73511 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73511) = 147456 * k + 110267 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110267) = 221184 * k + 165401 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 165401) = 331776 * k + 248102 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 248102) = 165888 * k + 124051 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 124051) = 248832 * k + 186077 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 186077) = 373248 * k + 279116 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 279116) = 186624 * k + 139558 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 139558) = 93312 * k + 69779 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 69779) = 139968 * k + 104669 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104669) = 209952 * k + 157004 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 157004) = 104976 * k + 78502 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78502) = 52488 * k + 39251 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 39251) = 78732 * k + 58877 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58877) = 118098 * k + 88316 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88316) = 59049 * k + 44158 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49055_mod_65536 {n : ℕ} (hn : n % 65536 = 49055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49055) = 98304 * k + 73583 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73583) = 147456 * k + 110375 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110375) = 221184 * k + 165563 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 165563) = 331776 * k + 248345 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 248345) = 497664 * k + 372518 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 372518) = 248832 * k + 186259 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 186259) = 373248 * k + 279389 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 279389) = 559872 * k + 419084 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 419084) = 279936 * k + 209542 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 209542) = 139968 * k + 104771 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104771) = 209952 * k + 157157 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 157157) = 314928 * k + 235736 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 235736) = 157464 * k + 117868 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 117868) = 78732 * k + 58934 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 58934) = 39366 * k + 29467 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 29467) = 59049 * k + 44201 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49135_mod_65536 {n : ℕ} (hn : n % 65536 = 49135) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49135 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49135) = 98304 * k + 73703 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73703) = 147456 * k + 110555 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110555) = 221184 * k + 165833 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 165833) = 331776 * k + 248750 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 248750) = 165888 * k + 124375 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 124375) = 248832 * k + 186563 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 186563) = 373248 * k + 279845 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 279845) = 559872 * k + 419768 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 419768) = 279936 * k + 209884 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 209884) = 139968 * k + 104942 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 104942) = 69984 * k + 52471 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 52471) = 104976 * k + 78707 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78707) = 157464 * k + 118061 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 118061) = 236196 * k + 177092 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 177092) = 118098 * k + 88546 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88546) = 59049 * k + 44273 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49135) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49135)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49215_mod_65536 {n : ℕ} (hn : n % 65536 = 49215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49215) = 98304 * k + 73823 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73823) = 147456 * k + 110735 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110735) = 221184 * k + 166103 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 166103) = 331776 * k + 249155 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 249155) = 497664 * k + 373733 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 373733) = 746496 * k + 560600 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 560600) = 373248 * k + 280300 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 280300) = 186624 * k + 140150 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 140150) = 93312 * k + 70075 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 70075) = 139968 * k + 105113 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 105113) = 209952 * k + 157670 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 157670) = 104976 * k + 78835 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78835) = 157464 * k + 118253 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 118253) = 236196 * k + 177380 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 177380) = 118098 * k + 88690 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88690) = 59049 * k + 44345 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49255_mod_65536 {n : ℕ} (hn : n % 65536 = 49255) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49255 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49255) = 98304 * k + 73883 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73883) = 147456 * k + 110825 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110825) = 221184 * k + 166238 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 166238) = 110592 * k + 83119 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 83119) = 165888 * k + 124679 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 124679) = 248832 * k + 187019 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 187019) = 373248 * k + 280529 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 280529) = 559872 * k + 420794 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 420794) = 279936 * k + 210397 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 210397) = 419904 * k + 315596 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 315596) = 209952 * k + 157798 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 157798) = 104976 * k + 78899 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 78899) = 157464 * k + 118349 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 118349) = 236196 * k + 177524 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 177524) = 118098 * k + 88762 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88762) = 59049 * k + 44381 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49255) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49255)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_49311_mod_65536 {n : ℕ} (hn : n % 65536 = 49311) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 49311 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 49311) = 98304 * k + 73967 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 73967) = 147456 * k + 110951 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 110951) = 221184 * k + 166427 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 166427) = 331776 * k + 249641 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 249641) = 497664 * k + 374462 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 374462) = 248832 * k + 187231 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 187231) = 373248 * k + 280847 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 280847) = 559872 * k + 421271 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 421271) = 839808 * k + 631907 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 631907) = 1259712 * k + 947861 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 947861) = 1889568 * k + 1421792 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 1421792) = 944784 * k + 710896 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 710896) = 472392 * k + 355448 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 355448) = 236196 * k + 177724 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 177724) = 118098 * k + 88862 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 88862) = 59049 * k + 44431 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 49311) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 49311)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
