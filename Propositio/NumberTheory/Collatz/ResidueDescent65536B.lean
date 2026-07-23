import Propositio.NumberTheory.Collatz.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace CollatzResidueDescent65536

open TerrasDensity

theorem descent_8383_mod_65536 {n : ℕ} (hn : n % 65536 = 8383) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8383 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8383) = 98304 * k + 12575 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12575) = 147456 * k + 18863 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18863) = 221184 * k + 28295 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 28295) = 331776 * k + 42443 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 42443) = 497664 * k + 63665 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 63665) = 746496 * k + 95498 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 95498) = 373248 * k + 47749 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 47749) = 559872 * k + 71624 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 71624) = 279936 * k + 35812 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 35812) = 139968 * k + 17906 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 17906) = 69984 * k + 8953 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 8953) = 104976 * k + 13430 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13430) = 52488 * k + 6715 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6715) = 78732 * k + 10073 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10073) = 118098 * k + 15110 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 15110) = 59049 * k + 7555 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8383) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8383)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8431_mod_65536 {n : ℕ} (hn : n % 65536 = 8431) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8431 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8431) = 98304 * k + 12647 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12647) = 147456 * k + 18971 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 18971) = 221184 * k + 28457 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 28457) = 331776 * k + 42686 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 42686) = 165888 * k + 21343 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 21343) = 248832 * k + 32015 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 32015) = 373248 * k + 48023 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 48023) = 559872 * k + 72035 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 72035) = 839808 * k + 108053 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 108053) = 1259712 * k + 162080 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 162080) = 629856 * k + 81040 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 81040) = 314928 * k + 40520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 40520) = 157464 * k + 20260 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 20260) = 78732 * k + 10130 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10130) = 39366 * k + 5065 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5065) = 59049 * k + 7598 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8431) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8431)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8495_mod_65536 {n : ℕ} (hn : n % 65536 = 8495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8495) = 98304 * k + 12743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12743) = 147456 * k + 19115 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19115) = 221184 * k + 28673 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 28673) = 331776 * k + 43010 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 43010) = 165888 * k + 21505 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 21505) = 248832 * k + 32258 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 32258) = 124416 * k + 16129 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 16129) = 186624 * k + 24194 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 24194) = 93312 * k + 12097 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 12097) = 139968 * k + 18146 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 18146) = 69984 * k + 9073 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 9073) = 104976 * k + 13610 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13610) = 52488 * k + 6805 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6805) = 78732 * k + 10208 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10208) = 39366 * k + 5104 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5104) = 19683 * k + 2552 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8551_mod_65536 {n : ℕ} (hn : n % 65536 = 8551) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8551 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8551) = 98304 * k + 12827 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 12827) = 147456 * k + 19241 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19241) = 221184 * k + 28862 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 28862) = 110592 * k + 14431 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 14431) = 165888 * k + 21647 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 21647) = 248832 * k + 32471 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 32471) = 373248 * k + 48707 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 48707) = 559872 * k + 73061 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 73061) = 839808 * k + 109592 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 109592) = 419904 * k + 54796 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 54796) = 209952 * k + 27398 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 27398) = 104976 * k + 13699 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13699) = 157464 * k + 20549 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 20549) = 236196 * k + 30824 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 30824) = 118098 * k + 15412 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 15412) = 59049 * k + 7706 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8551) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8551)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8671_mod_65536 {n : ℕ} (hn : n % 65536 = 8671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8671) = 98304 * k + 13007 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13007) = 147456 * k + 19511 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19511) = 221184 * k + 29267 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 29267) = 331776 * k + 43901 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 43901) = 497664 * k + 65852 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 65852) = 248832 * k + 32926 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 32926) = 124416 * k + 16463 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 16463) = 186624 * k + 24695 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 24695) = 279936 * k + 37043 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 37043) = 419904 * k + 55565 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 55565) = 629856 * k + 83348 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 83348) = 314928 * k + 41674 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 41674) = 157464 * k + 20837 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 20837) = 236196 * k + 31256 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 31256) = 118098 * k + 15628 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 15628) = 59049 * k + 7814 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8735_mod_65536 {n : ℕ} (hn : n % 65536 = 8735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8735) = 98304 * k + 13103 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13103) = 147456 * k + 19655 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19655) = 221184 * k + 29483 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 29483) = 331776 * k + 44225 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 44225) = 497664 * k + 66338 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 66338) = 248832 * k + 33169 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 33169) = 373248 * k + 49754 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 49754) = 186624 * k + 24877 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 24877) = 279936 * k + 37316 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 37316) = 139968 * k + 18658 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 18658) = 69984 * k + 9329 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 9329) = 104976 * k + 13994 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 13994) = 52488 * k + 6997 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 6997) = 78732 * k + 10496 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10496) = 39366 * k + 5248 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5248) = 19683 * k + 2624 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8795_mod_65536 {n : ℕ} (hn : n % 65536 = 8795) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8795 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8795) = 98304 * k + 13193 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13193) = 147456 * k + 19790 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19790) = 73728 * k + 9895 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 9895) = 110592 * k + 14843 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 14843) = 165888 * k + 22265 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 22265) = 248832 * k + 33398 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 33398) = 124416 * k + 16699 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 16699) = 186624 * k + 25049 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 25049) = 279936 * k + 37574 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 37574) = 139968 * k + 18787 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 18787) = 209952 * k + 28181 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 28181) = 314928 * k + 42272 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 42272) = 157464 * k + 21136 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 21136) = 78732 * k + 10568 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10568) = 39366 * k + 5284 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5284) = 19683 * k + 2642 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8795) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8795)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8815_mod_65536 {n : ℕ} (hn : n % 65536 = 8815) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8815 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8815) = 98304 * k + 13223 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13223) = 147456 * k + 19835 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19835) = 221184 * k + 29753 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 29753) = 331776 * k + 44630 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 44630) = 165888 * k + 22315 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 22315) = 248832 * k + 33473 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 33473) = 373248 * k + 50210 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 50210) = 186624 * k + 25105 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 25105) = 279936 * k + 37658 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 37658) = 139968 * k + 18829 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 18829) = 209952 * k + 28244 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 28244) = 104976 * k + 14122 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 14122) = 52488 * k + 7061 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 7061) = 78732 * k + 10592 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10592) = 39366 * k + 5296 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5296) = 19683 * k + 2648 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8815) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8815)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_8863_mod_65536 {n : ℕ} (hn : n % 65536 = 8863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 8863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 8863) = 98304 * k + 13295 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13295) = 147456 * k + 19943 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 19943) = 221184 * k + 29915 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 29915) = 331776 * k + 44873 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 44873) = 497664 * k + 67310 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 67310) = 248832 * k + 33655 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 33655) = 373248 * k + 50483 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 50483) = 559872 * k + 75725 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 75725) = 839808 * k + 113588 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 113588) = 419904 * k + 56794 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 56794) = 209952 * k + 28397 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 28397) = 314928 * k + 42596 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 42596) = 157464 * k + 21298 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 21298) = 78732 * k + 10649 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10649) = 118098 * k + 15974 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 15974) = 59049 * k + 7987 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 8863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 8863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9051_mod_65536 {n : ℕ} (hn : n % 65536 = 9051) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9051 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9051) = 98304 * k + 13577 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13577) = 147456 * k + 20366 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 20366) = 73728 * k + 10183 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 10183) = 110592 * k + 15275 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 15275) = 165888 * k + 22913 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 22913) = 248832 * k + 34370 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 34370) = 124416 * k + 17185 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 17185) = 186624 * k + 25778 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 25778) = 93312 * k + 12889 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 12889) = 139968 * k + 19334 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 19334) = 69984 * k + 9667 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 9667) = 104976 * k + 14501 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 14501) = 157464 * k + 21752 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 21752) = 78732 * k + 10876 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10876) = 39366 * k + 5438 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5438) = 19683 * k + 2719 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9051) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9051)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9087_mod_65536 {n : ℕ} (hn : n % 65536 = 9087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9087) = 98304 * k + 13631 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13631) = 147456 * k + 20447 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 20447) = 221184 * k + 30671 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 30671) = 331776 * k + 46007 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 46007) = 497664 * k + 69011 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 69011) = 746496 * k + 103517 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 103517) = 1119744 * k + 155276 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 155276) = 559872 * k + 77638 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 77638) = 279936 * k + 38819 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 38819) = 419904 * k + 58229 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 58229) = 629856 * k + 87344 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 87344) = 314928 * k + 43672 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 43672) = 157464 * k + 21836 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 21836) = 78732 * k + 10918 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10918) = 39366 * k + 5459 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5459) = 59049 * k + 8189 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9119_mod_65536 {n : ℕ} (hn : n % 65536 = 9119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9119) = 98304 * k + 13679 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13679) = 147456 * k + 20519 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 20519) = 221184 * k + 30779 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 30779) = 331776 * k + 46169 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 46169) = 497664 * k + 69254 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 69254) = 248832 * k + 34627 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 34627) = 373248 * k + 51941 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 51941) = 559872 * k + 77912 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 77912) = 279936 * k + 38956 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 38956) = 139968 * k + 19478 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 19478) = 69984 * k + 9739 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 9739) = 104976 * k + 14609 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 14609) = 157464 * k + 21914 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 21914) = 78732 * k + 10957 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 10957) = 118098 * k + 16436 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 16436) = 59049 * k + 8218 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9199_mod_65536 {n : ℕ} (hn : n % 65536 = 9199) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9199 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9199) = 98304 * k + 13799 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13799) = 147456 * k + 20699 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 20699) = 221184 * k + 31049 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 31049) = 331776 * k + 46574 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 46574) = 165888 * k + 23287 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 23287) = 248832 * k + 34931 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 34931) = 373248 * k + 52397 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 52397) = 559872 * k + 78596 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 78596) = 279936 * k + 39298 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 39298) = 139968 * k + 19649 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 19649) = 209952 * k + 29474 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 29474) = 104976 * k + 14737 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 14737) = 157464 * k + 22106 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 22106) = 78732 * k + 11053 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11053) = 118098 * k + 16580 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 16580) = 59049 * k + 8290 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9199) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9199)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9319_mod_65536 {n : ℕ} (hn : n % 65536 = 9319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9319) = 98304 * k + 13979 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 13979) = 147456 * k + 20969 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 20969) = 221184 * k + 31454 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 31454) = 110592 * k + 15727 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 15727) = 165888 * k + 23591 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 23591) = 248832 * k + 35387 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 35387) = 373248 * k + 53081 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 53081) = 559872 * k + 79622 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 79622) = 279936 * k + 39811 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 39811) = 419904 * k + 59717 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 59717) = 629856 * k + 89576 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 89576) = 314928 * k + 44788 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 44788) = 157464 * k + 22394 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 22394) = 78732 * k + 11197 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11197) = 118098 * k + 16796 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 16796) = 59049 * k + 8398 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9371_mod_65536 {n : ℕ} (hn : n % 65536 = 9371) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9371 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9371) = 98304 * k + 14057 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14057) = 147456 * k + 21086 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21086) = 73728 * k + 10543 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 10543) = 110592 * k + 15815 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 15815) = 165888 * k + 23723 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 23723) = 248832 * k + 35585 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 35585) = 373248 * k + 53378 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 53378) = 186624 * k + 26689 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 26689) = 279936 * k + 40034 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 40034) = 139968 * k + 20017 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20017) = 209952 * k + 30026 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 30026) = 104976 * k + 15013 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15013) = 157464 * k + 22520 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 22520) = 78732 * k + 11260 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11260) = 39366 * k + 5630 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5630) = 19683 * k + 2815 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9371) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9371)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9375_mod_65536 {n : ℕ} (hn : n % 65536 = 9375) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9375 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9375) = 98304 * k + 14063 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14063) = 147456 * k + 21095 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21095) = 221184 * k + 31643 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 31643) = 331776 * k + 47465 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 47465) = 497664 * k + 71198 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 71198) = 248832 * k + 35599 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 35599) = 373248 * k + 53399 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 53399) = 559872 * k + 80099 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 80099) = 839808 * k + 120149 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 120149) = 1259712 * k + 180224 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 180224) = 629856 * k + 90112 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 90112) = 314928 * k + 45056 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 45056) = 157464 * k + 22528 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 22528) = 78732 * k + 11264 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11264) = 39366 * k + 5632 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5632) = 19683 * k + 2816 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9375) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9375)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9439_mod_65536 {n : ℕ} (hn : n % 65536 = 9439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9439) = 98304 * k + 14159 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14159) = 147456 * k + 21239 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21239) = 221184 * k + 31859 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 31859) = 331776 * k + 47789 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 47789) = 497664 * k + 71684 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 71684) = 248832 * k + 35842 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 35842) = 124416 * k + 17921 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 17921) = 186624 * k + 26882 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 26882) = 93312 * k + 13441 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 13441) = 139968 * k + 20162 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20162) = 69984 * k + 10081 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 10081) = 104976 * k + 15122 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15122) = 52488 * k + 7561 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 7561) = 78732 * k + 11342 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11342) = 39366 * k + 5671 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5671) = 59049 * k + 8507 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9519_mod_65536 {n : ℕ} (hn : n % 65536 = 9519) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9519 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9519) = 98304 * k + 14279 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14279) = 147456 * k + 21419 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21419) = 221184 * k + 32129 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32129) = 331776 * k + 48194 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 48194) = 165888 * k + 24097 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 24097) = 248832 * k + 36146 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 36146) = 124416 * k + 18073 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 18073) = 186624 * k + 27110 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 27110) = 93312 * k + 13555 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 13555) = 139968 * k + 20333 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20333) = 209952 * k + 30500 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 30500) = 104976 * k + 15250 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15250) = 52488 * k + 7625 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 7625) = 78732 * k + 11438 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11438) = 39366 * k + 5719 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5719) = 59049 * k + 8579 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9519) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9519)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9543_mod_65536 {n : ℕ} (hn : n % 65536 = 9543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9543) = 98304 * k + 14315 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14315) = 147456 * k + 21473 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21473) = 221184 * k + 32210 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32210) = 110592 * k + 16105 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 16105) = 165888 * k + 24158 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 24158) = 82944 * k + 12079 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 12079) = 124416 * k + 18119 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 18119) = 186624 * k + 27179 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 27179) = 279936 * k + 40769 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 40769) = 419904 * k + 61154 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 61154) = 209952 * k + 30577 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 30577) = 314928 * k + 45866 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 45866) = 157464 * k + 22933 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 22933) = 236196 * k + 34400 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 34400) = 118098 * k + 17200 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 17200) = 59049 * k + 8600 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9599_mod_65536 {n : ℕ} (hn : n % 65536 = 9599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9599) = 98304 * k + 14399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14399) = 147456 * k + 21599 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21599) = 221184 * k + 32399 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32399) = 331776 * k + 48599 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 48599) = 497664 * k + 72899 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 72899) = 746496 * k + 109349 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 109349) = 1119744 * k + 164024 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 164024) = 559872 * k + 82012 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 82012) = 279936 * k + 41006 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 41006) = 139968 * k + 20503 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20503) = 209952 * k + 30755 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 30755) = 314928 * k + 46133 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 46133) = 472392 * k + 69200 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 69200) = 236196 * k + 34600 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 34600) = 118098 * k + 17300 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 17300) = 59049 * k + 8650 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9679_mod_65536 {n : ℕ} (hn : n % 65536 = 9679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9679) = 98304 * k + 14519 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14519) = 147456 * k + 21779 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21779) = 221184 * k + 32669 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32669) = 331776 * k + 49004 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 49004) = 165888 * k + 24502 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 24502) = 82944 * k + 12251 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 12251) = 124416 * k + 18377 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 18377) = 186624 * k + 27566 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 27566) = 93312 * k + 13783 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 13783) = 139968 * k + 20675 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20675) = 209952 * k + 31013 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 31013) = 314928 * k + 46520 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 46520) = 157464 * k + 23260 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 23260) = 78732 * k + 11630 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11630) = 39366 * k + 5815 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5815) = 59049 * k + 8723 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9711_mod_65536 {n : ℕ} (hn : n % 65536 = 9711) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9711 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9711) = 98304 * k + 14567 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14567) = 147456 * k + 21851 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21851) = 221184 * k + 32777 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32777) = 331776 * k + 49166 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 49166) = 165888 * k + 24583 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 24583) = 248832 * k + 36875 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 36875) = 373248 * k + 55313 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 55313) = 559872 * k + 82970 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 82970) = 279936 * k + 41485 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 41485) = 419904 * k + 62228 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 62228) = 209952 * k + 31114 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 31114) = 104976 * k + 15557 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15557) = 157464 * k + 23336 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 23336) = 78732 * k + 11668 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11668) = 39366 * k + 5834 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5834) = 19683 * k + 2917 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9711) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9711)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9759_mod_65536 {n : ℕ} (hn : n % 65536 = 9759) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9759 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9759) = 98304 * k + 14639 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14639) = 147456 * k + 21959 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 21959) = 221184 * k + 32939 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 32939) = 331776 * k + 49409 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 49409) = 497664 * k + 74114 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 74114) = 248832 * k + 37057 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 37057) = 373248 * k + 55586 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 55586) = 186624 * k + 27793 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 27793) = 279936 * k + 41690 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 41690) = 139968 * k + 20845 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20845) = 209952 * k + 31268 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 31268) = 104976 * k + 15634 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15634) = 52488 * k + 7817 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 7817) = 78732 * k + 11726 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11726) = 39366 * k + 5863 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5863) = 59049 * k + 8795 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9759) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9759)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9819_mod_65536 {n : ℕ} (hn : n % 65536 = 9819) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9819 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9819) = 98304 * k + 14729 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14729) = 147456 * k + 22094 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22094) = 73728 * k + 11047 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 11047) = 110592 * k + 16571 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 16571) = 165888 * k + 24857 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 24857) = 248832 * k + 37286 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 37286) = 124416 * k + 18643 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 18643) = 186624 * k + 27965 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 27965) = 279936 * k + 41948 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 41948) = 139968 * k + 20974 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 20974) = 69984 * k + 10487 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 10487) = 104976 * k + 15731 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15731) = 157464 * k + 23597 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 23597) = 236196 * k + 35396 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 35396) = 118098 * k + 17698 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 17698) = 59049 * k + 8849 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9819) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9819)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9919_mod_65536 {n : ℕ} (hn : n % 65536 = 9919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9919) = 98304 * k + 14879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14879) = 147456 * k + 22319 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22319) = 221184 * k + 33479 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 33479) = 331776 * k + 50219 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 50219) = 497664 * k + 75329 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 75329) = 746496 * k + 112994 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 112994) = 373248 * k + 56497 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 56497) = 559872 * k + 84746 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 84746) = 279936 * k + 42373 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 42373) = 419904 * k + 63560 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 63560) = 209952 * k + 31780 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 31780) = 104976 * k + 15890 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 15890) = 52488 * k + 7945 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 7945) = 78732 * k + 11918 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11918) = 39366 * k + 5959 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5959) = 59049 * k + 8939 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9935_mod_65536 {n : ℕ} (hn : n % 65536 = 9935) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9935 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9935) = 98304 * k + 14903 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14903) = 147456 * k + 22355 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22355) = 221184 * k + 33533 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 33533) = 331776 * k + 50300 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 50300) = 165888 * k + 25150 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 25150) = 82944 * k + 12575 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 12575) = 124416 * k + 18863 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 18863) = 186624 * k + 28295 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 28295) = 279936 * k + 42443 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 42443) = 419904 * k + 63665 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 63665) = 629856 * k + 95498 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 95498) = 314928 * k + 47749 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 47749) = 472392 * k + 71624 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 71624) = 236196 * k + 35812 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 35812) = 118098 * k + 17906 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 17906) = 59049 * k + 8953 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9935) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9935)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_9959_mod_65536 {n : ℕ} (hn : n % 65536 = 9959) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 9959 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 9959) = 98304 * k + 14939 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 14939) = 147456 * k + 22409 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22409) = 221184 * k + 33614 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 33614) = 110592 * k + 16807 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 16807) = 165888 * k + 25211 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 25211) = 248832 * k + 37817 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 37817) = 373248 * k + 56726 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 56726) = 186624 * k + 28363 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 28363) = 279936 * k + 42545 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 42545) = 419904 * k + 63818 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 63818) = 209952 * k + 31909 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 31909) = 314928 * k + 47864 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 47864) = 157464 * k + 23932 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 23932) = 78732 * k + 11966 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 11966) = 39366 * k + 5983 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 5983) = 59049 * k + 8975 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 9959) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 9959)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10055_mod_65536 {n : ℕ} (hn : n % 65536 = 10055) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10055 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10055) = 98304 * k + 15083 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15083) = 147456 * k + 22625 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22625) = 221184 * k + 33938 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 33938) = 110592 * k + 16969 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 16969) = 165888 * k + 25454 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 25454) = 82944 * k + 12727 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 12727) = 124416 * k + 19091 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 19091) = 186624 * k + 28637 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 28637) = 279936 * k + 42956 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 42956) = 139968 * k + 21478 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 21478) = 69984 * k + 10739 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 10739) = 104976 * k + 16109 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 16109) = 157464 * k + 24164 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 24164) = 78732 * k + 12082 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12082) = 39366 * k + 6041 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6041) = 59049 * k + 9062 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10055) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10055)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10075_mod_65536 {n : ℕ} (hn : n % 65536 = 10075) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10075 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10075) = 98304 * k + 15113 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15113) = 147456 * k + 22670 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22670) = 73728 * k + 11335 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 11335) = 110592 * k + 17003 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 17003) = 165888 * k + 25505 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 25505) = 248832 * k + 38258 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 38258) = 124416 * k + 19129 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 19129) = 186624 * k + 28694 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 28694) = 93312 * k + 14347 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 14347) = 139968 * k + 21521 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 21521) = 209952 * k + 32282 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 32282) = 104976 * k + 16141 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 16141) = 157464 * k + 24212 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 24212) = 78732 * k + 12106 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12106) = 39366 * k + 6053 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6053) = 59049 * k + 9080 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10075) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10075)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10151_mod_65536 {n : ℕ} (hn : n % 65536 = 10151) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10151 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10151) = 98304 * k + 15227 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15227) = 147456 * k + 22841 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 22841) = 221184 * k + 34262 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 34262) = 110592 * k + 17131 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 17131) = 165888 * k + 25697 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 25697) = 248832 * k + 38546 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 38546) = 124416 * k + 19273 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 19273) = 186624 * k + 28910 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 28910) = 93312 * k + 14455 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 14455) = 139968 * k + 21683 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 21683) = 209952 * k + 32525 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 32525) = 314928 * k + 48788 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 48788) = 157464 * k + 24394 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 24394) = 78732 * k + 12197 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12197) = 118098 * k + 18296 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 18296) = 59049 * k + 9148 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10151) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10151)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10271_mod_65536 {n : ℕ} (hn : n % 65536 = 10271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10271) = 98304 * k + 15407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15407) = 147456 * k + 23111 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23111) = 221184 * k + 34667 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 34667) = 331776 * k + 52001 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 52001) = 497664 * k + 78002 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 78002) = 248832 * k + 39001 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 39001) = 373248 * k + 58502 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 58502) = 186624 * k + 29251 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 29251) = 279936 * k + 43877 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 43877) = 419904 * k + 65816 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 65816) = 209952 * k + 32908 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 32908) = 104976 * k + 16454 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 16454) = 52488 * k + 8227 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 8227) = 78732 * k + 12341 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12341) = 118098 * k + 18512 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 18512) = 59049 * k + 9256 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10463_mod_65536 {n : ℕ} (hn : n % 65536 = 10463) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10463 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10463) = 98304 * k + 15695 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15695) = 147456 * k + 23543 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23543) = 221184 * k + 35315 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 35315) = 331776 * k + 52973 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 52973) = 497664 * k + 79460 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 79460) = 248832 * k + 39730 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 39730) = 124416 * k + 19865 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 19865) = 186624 * k + 29798 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 29798) = 93312 * k + 14899 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 14899) = 139968 * k + 22349 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 22349) = 209952 * k + 33524 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 33524) = 104976 * k + 16762 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 16762) = 52488 * k + 8381 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 8381) = 78732 * k + 12572 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12572) = 39366 * k + 6286 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6286) = 19683 * k + 3143 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10463) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10463)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10523_mod_65536 {n : ℕ} (hn : n % 65536 = 10523) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10523 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10523) = 98304 * k + 15785 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15785) = 147456 * k + 23678 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23678) = 73728 * k + 11839 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 11839) = 110592 * k + 17759 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 17759) = 165888 * k + 26639 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 26639) = 248832 * k + 39959 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 39959) = 373248 * k + 59939 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 59939) = 559872 * k + 89909 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 89909) = 839808 * k + 134864 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 134864) = 419904 * k + 67432 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 67432) = 209952 * k + 33716 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 33716) = 104976 * k + 16858 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 16858) = 52488 * k + 8429 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 8429) = 78732 * k + 12644 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12644) = 39366 * k + 6322 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6322) = 19683 * k + 3161 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10523) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10523)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10559_mod_65536 {n : ℕ} (hn : n % 65536 = 10559) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10559 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10559) = 98304 * k + 15839 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15839) = 147456 * k + 23759 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23759) = 221184 * k + 35639 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 35639) = 331776 * k + 53459 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 53459) = 497664 * k + 80189 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 80189) = 746496 * k + 120284 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 120284) = 373248 * k + 60142 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 60142) = 186624 * k + 30071 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 30071) = 279936 * k + 45107 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 45107) = 419904 * k + 67661 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 67661) = 629856 * k + 101492 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 101492) = 314928 * k + 50746 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 50746) = 157464 * k + 25373 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 25373) = 236196 * k + 38060 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 38060) = 118098 * k + 19030 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 19030) = 59049 * k + 9515 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10559) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10559)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10623_mod_65536 {n : ℕ} (hn : n % 65536 = 10623) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10623 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10623) = 98304 * k + 15935 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15935) = 147456 * k + 23903 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23903) = 221184 * k + 35855 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 35855) = 331776 * k + 53783 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 53783) = 497664 * k + 80675 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 80675) = 746496 * k + 121013 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 121013) = 1119744 * k + 181520 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 181520) = 559872 * k + 90760 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 90760) = 279936 * k + 45380 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 45380) = 139968 * k + 22690 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 22690) = 69984 * k + 11345 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 11345) = 104976 * k + 17018 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 17018) = 52488 * k + 8509 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 8509) = 78732 * k + 12764 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12764) = 39366 * k + 6382 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6382) = 19683 * k + 3191 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10623) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10623)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10655_mod_65536 {n : ℕ} (hn : n % 65536 = 10655) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10655 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10655) = 98304 * k + 15983 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 15983) = 147456 * k + 23975 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 23975) = 221184 * k + 35963 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 35963) = 331776 * k + 53945 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 53945) = 497664 * k + 80918 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 80918) = 248832 * k + 40459 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 40459) = 373248 * k + 60689 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 60689) = 559872 * k + 91034 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 91034) = 279936 * k + 45517 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 45517) = 419904 * k + 68276 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 68276) = 209952 * k + 34138 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 34138) = 104976 * k + 17069 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 17069) = 157464 * k + 25604 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 25604) = 78732 * k + 12802 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12802) = 39366 * k + 6401 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6401) = 59049 * k + 9602 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10655) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10655)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10727_mod_65536 {n : ℕ} (hn : n % 65536 = 10727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10727) = 98304 * k + 16091 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16091) = 147456 * k + 24137 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24137) = 221184 * k + 36206 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 36206) = 110592 * k + 18103 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 18103) = 165888 * k + 27155 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 27155) = 248832 * k + 40733 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 40733) = 373248 * k + 61100 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 61100) = 186624 * k + 30550 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 30550) = 93312 * k + 15275 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 15275) = 139968 * k + 22913 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 22913) = 209952 * k + 34370 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 34370) = 104976 * k + 17185 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 17185) = 157464 * k + 25778 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 25778) = 78732 * k + 12889 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12889) = 118098 * k + 19334 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 19334) = 59049 * k + 9667 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10735_mod_65536 {n : ℕ} (hn : n % 65536 = 10735) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10735 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10735) = 98304 * k + 16103 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16103) = 147456 * k + 24155 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24155) = 221184 * k + 36233 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 36233) = 331776 * k + 54350 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 54350) = 165888 * k + 27175 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 27175) = 248832 * k + 40763 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 40763) = 373248 * k + 61145 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 61145) = 559872 * k + 91718 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 91718) = 279936 * k + 45859 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 45859) = 419904 * k + 68789 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 68789) = 629856 * k + 103184 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 103184) = 314928 * k + 51592 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 51592) = 157464 * k + 25796 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 25796) = 78732 * k + 12898 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 12898) = 39366 * k + 6449 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6449) = 59049 * k + 9674 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10735) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10735)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10863_mod_65536 {n : ℕ} (hn : n % 65536 = 10863) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10863 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10863) = 98304 * k + 16295 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16295) = 147456 * k + 24443 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24443) = 221184 * k + 36665 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 36665) = 331776 * k + 54998 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 54998) = 165888 * k + 27499 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 27499) = 248832 * k + 41249 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 41249) = 373248 * k + 61874 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 61874) = 186624 * k + 30937 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 30937) = 279936 * k + 46406 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 46406) = 139968 * k + 23203 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 23203) = 209952 * k + 34805 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 34805) = 314928 * k + 52208 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 52208) = 157464 * k + 26104 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 26104) = 78732 * k + 13052 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13052) = 39366 * k + 6526 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6526) = 19683 * k + 3263 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10863) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10863)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_10907_mod_65536 {n : ℕ} (hn : n % 65536 = 10907) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 10907 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 10907) = 98304 * k + 16361 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16361) = 147456 * k + 24542 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24542) = 73728 * k + 12271 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 12271) = 110592 * k + 18407 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 18407) = 165888 * k + 27611 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 27611) = 248832 * k + 41417 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 41417) = 373248 * k + 62126 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 62126) = 186624 * k + 31063 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 31063) = 279936 * k + 46595 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 46595) = 419904 * k + 69893 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 69893) = 629856 * k + 104840 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 104840) = 314928 * k + 52420 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 52420) = 157464 * k + 26210 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 26210) = 78732 * k + 13105 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13105) = 118098 * k + 19658 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 19658) = 59049 * k + 9829 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 10907) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 10907)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11035_mod_65536 {n : ℕ} (hn : n % 65536 = 11035) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11035 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11035) = 98304 * k + 16553 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16553) = 147456 * k + 24830 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24830) = 73728 * k + 12415 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 12415) = 110592 * k + 18623 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 18623) = 165888 * k + 27935 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 27935) = 248832 * k + 41903 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 41903) = 373248 * k + 62855 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 62855) = 559872 * k + 94283 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 94283) = 839808 * k + 141425 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 141425) = 1259712 * k + 212138 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 212138) = 629856 * k + 106069 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 106069) = 944784 * k + 159104 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 159104) = 472392 * k + 79552 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 79552) = 236196 * k + 39776 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 39776) = 118098 * k + 19888 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 19888) = 59049 * k + 9944 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11035) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11035)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11079_mod_65536 {n : ℕ} (hn : n % 65536 = 11079) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11079 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11079) = 98304 * k + 16619 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16619) = 147456 * k + 24929 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 24929) = 221184 * k + 37394 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 37394) = 110592 * k + 18697 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 18697) = 165888 * k + 28046 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 28046) = 82944 * k + 14023 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 14023) = 124416 * k + 21035 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 21035) = 186624 * k + 31553 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 31553) = 279936 * k + 47330 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 47330) = 139968 * k + 23665 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 23665) = 209952 * k + 35498 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 35498) = 104976 * k + 17749 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 17749) = 157464 * k + 26624 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 26624) = 78732 * k + 13312 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13312) = 39366 * k + 6656 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6656) = 19683 * k + 3328 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11079) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11079)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11119_mod_65536 {n : ℕ} (hn : n % 65536 = 11119) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11119 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11119) = 98304 * k + 16679 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16679) = 147456 * k + 25019 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 25019) = 221184 * k + 37529 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 37529) = 331776 * k + 56294 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 56294) = 165888 * k + 28147 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 28147) = 248832 * k + 42221 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 42221) = 373248 * k + 63332 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 63332) = 186624 * k + 31666 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 31666) = 93312 * k + 15833 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 15833) = 139968 * k + 23750 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 23750) = 69984 * k + 11875 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 11875) = 104976 * k + 17813 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 17813) = 157464 * k + 26720 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 26720) = 78732 * k + 13360 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13360) = 39366 * k + 6680 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6680) = 19683 * k + 3340 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11119) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11119)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11247_mod_65536 {n : ℕ} (hn : n % 65536 = 11247) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11247 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11247) = 98304 * k + 16871 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16871) = 147456 * k + 25307 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 25307) = 221184 * k + 37961 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 37961) = 331776 * k + 56942 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 56942) = 165888 * k + 28471 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 28471) = 248832 * k + 42707 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 42707) = 373248 * k + 64061 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 64061) = 559872 * k + 96092 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 96092) = 279936 * k + 48046 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 48046) = 139968 * k + 24023 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 24023) = 209952 * k + 36035 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 36035) = 314928 * k + 54053 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 54053) = 472392 * k + 81080 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 81080) = 236196 * k + 40540 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 40540) = 118098 * k + 20270 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 20270) = 59049 * k + 10135 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11247) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11247)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11259_mod_65536 {n : ℕ} (hn : n % 65536 = 11259) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11259 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11259) = 98304 * k + 16889 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16889) = 147456 * k + 25334 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 25334) = 73728 * k + 12667 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 12667) = 110592 * k + 19001 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 19001) = 165888 * k + 28502 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 28502) = 82944 * k + 14251 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 14251) = 124416 * k + 21377 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 21377) = 186624 * k + 32066 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 32066) = 93312 * k + 16033 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 16033) = 139968 * k + 24050 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 24050) = 69984 * k + 12025 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 12025) = 104976 * k + 18038 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 18038) = 52488 * k + 9019 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9019) = 78732 * k + 13529 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13529) = 118098 * k + 20294 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 20294) = 59049 * k + 10147 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11259) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11259)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11327_mod_65536 {n : ℕ} (hn : n % 65536 = 11327) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11327 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11327) = 98304 * k + 16991 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 16991) = 147456 * k + 25487 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 25487) = 221184 * k + 38231 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 38231) = 331776 * k + 57347 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 57347) = 497664 * k + 86021 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 86021) = 746496 * k + 129032 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 129032) = 373248 * k + 64516 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 64516) = 186624 * k + 32258 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 32258) = 93312 * k + 16129 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 16129) = 139968 * k + 24194 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 24194) = 69984 * k + 12097 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 12097) = 104976 * k + 18146 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 18146) = 52488 * k + 9073 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9073) = 78732 * k + 13610 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13610) = 39366 * k + 6805 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6805) = 59049 * k + 10208 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11327) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11327)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11431_mod_65536 {n : ℕ} (hn : n % 65536 = 11431) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11431 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11431) = 98304 * k + 17147 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17147) = 147456 * k + 25721 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 25721) = 221184 * k + 38582 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 38582) = 110592 * k + 19291 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 19291) = 165888 * k + 28937 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 28937) = 248832 * k + 43406 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 43406) = 124416 * k + 21703 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 21703) = 186624 * k + 32555 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 32555) = 279936 * k + 48833 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 48833) = 419904 * k + 73250 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 73250) = 209952 * k + 36625 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 36625) = 314928 * k + 54938 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 54938) = 157464 * k + 27469 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 27469) = 236196 * k + 41204 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 41204) = 118098 * k + 20602 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 20602) = 59049 * k + 10301 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11431) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11431)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11567_mod_65536 {n : ℕ} (hn : n % 65536 = 11567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11567) = 98304 * k + 17351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17351) = 147456 * k + 26027 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26027) = 221184 * k + 39041 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39041) = 331776 * k + 58562 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 58562) = 165888 * k + 29281 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 29281) = 248832 * k + 43922 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 43922) = 124416 * k + 21961 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 21961) = 186624 * k + 32942 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 32942) = 93312 * k + 16471 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 16471) = 139968 * k + 24707 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 24707) = 209952 * k + 37061 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 37061) = 314928 * k + 55592 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 55592) = 157464 * k + 27796 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 27796) = 78732 * k + 13898 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13898) = 39366 * k + 6949 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6949) = 59049 * k + 10424 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11647_mod_65536 {n : ℕ} (hn : n % 65536 = 11647) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11647 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11647) = 98304 * k + 17471 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17471) = 147456 * k + 26207 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26207) = 221184 * k + 39311 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39311) = 331776 * k + 58967 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 58967) = 497664 * k + 88451 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 88451) = 746496 * k + 132677 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 132677) = 1119744 * k + 199016 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 199016) = 559872 * k + 99508 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 99508) = 279936 * k + 49754 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 49754) = 139968 * k + 24877 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 24877) = 209952 * k + 37316 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 37316) = 104976 * k + 18658 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 18658) = 52488 * k + 9329 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9329) = 78732 * k + 13994 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 13994) = 39366 * k + 6997 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 6997) = 59049 * k + 10496 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11647) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11647)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11679_mod_65536 {n : ℕ} (hn : n % 65536 = 11679) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11679 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11679) = 98304 * k + 17519 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17519) = 147456 * k + 26279 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26279) = 221184 * k + 39419 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39419) = 331776 * k + 59129 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 59129) = 497664 * k + 88694 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 88694) = 248832 * k + 44347 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 44347) = 373248 * k + 66521 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 66521) = 559872 * k + 99782 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 99782) = 279936 * k + 49891 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 49891) = 419904 * k + 74837 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 74837) = 629856 * k + 112256 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 112256) = 314928 * k + 56128 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 56128) = 157464 * k + 28064 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28064) = 78732 * k + 14032 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14032) = 39366 * k + 7016 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7016) = 19683 * k + 3508 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11679) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11679)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11727_mod_65536 {n : ℕ} (hn : n % 65536 = 11727) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11727 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11727) = 98304 * k + 17591 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17591) = 147456 * k + 26387 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26387) = 221184 * k + 39581 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39581) = 331776 * k + 59372 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 59372) = 165888 * k + 29686 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 29686) = 82944 * k + 14843 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 14843) = 124416 * k + 22265 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 22265) = 186624 * k + 33398 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 33398) = 93312 * k + 16699 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 16699) = 139968 * k + 25049 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25049) = 209952 * k + 37574 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 37574) = 104976 * k + 18787 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 18787) = 157464 * k + 28181 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28181) = 236196 * k + 42272 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 42272) = 118098 * k + 21136 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21136) = 59049 * k + 10568 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11727) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11727)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11807_mod_65536 {n : ℕ} (hn : n % 65536 = 11807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11807) = 98304 * k + 17711 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17711) = 147456 * k + 26567 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26567) = 221184 * k + 39851 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39851) = 331776 * k + 59777 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 59777) = 497664 * k + 89666 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 89666) = 248832 * k + 44833 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 44833) = 373248 * k + 67250 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 67250) = 186624 * k + 33625 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 33625) = 279936 * k + 50438 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 50438) = 139968 * k + 25219 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25219) = 209952 * k + 37829 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 37829) = 314928 * k + 56744 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 56744) = 157464 * k + 28372 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28372) = 78732 * k + 14186 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14186) = 39366 * k + 7093 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7093) = 59049 * k + 10640 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11823_mod_65536 {n : ℕ} (hn : n % 65536 = 11823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11823) = 98304 * k + 17735 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17735) = 147456 * k + 26603 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26603) = 221184 * k + 39905 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 39905) = 331776 * k + 59858 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 59858) = 165888 * k + 29929 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 29929) = 248832 * k + 44894 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 44894) = 124416 * k + 22447 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 22447) = 186624 * k + 33671 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 33671) = 279936 * k + 50507 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 50507) = 419904 * k + 75761 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 75761) = 629856 * k + 113642 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 113642) = 314928 * k + 56821 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 56821) = 472392 * k + 85232 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 85232) = 236196 * k + 42616 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 42616) = 118098 * k + 21308 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21308) = 59049 * k + 10654 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11879_mod_65536 {n : ℕ} (hn : n % 65536 = 11879) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11879 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11879) = 98304 * k + 17819 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17819) = 147456 * k + 26729 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26729) = 221184 * k + 40094 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40094) = 110592 * k + 20047 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 20047) = 165888 * k + 30071 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 30071) = 248832 * k + 45107 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 45107) = 373248 * k + 67661 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 67661) = 559872 * k + 101492 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 101492) = 279936 * k + 50746 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 50746) = 139968 * k + 25373 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25373) = 209952 * k + 38060 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 38060) = 104976 * k + 19030 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19030) = 52488 * k + 9515 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9515) = 78732 * k + 14273 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14273) = 118098 * k + 21410 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21410) = 59049 * k + 10705 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11879) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11879)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11887_mod_65536 {n : ℕ} (hn : n % 65536 = 11887) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11887 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11887) = 98304 * k + 17831 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17831) = 147456 * k + 26747 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26747) = 221184 * k + 40121 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40121) = 331776 * k + 60182 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 60182) = 165888 * k + 30091 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 30091) = 248832 * k + 45137 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 45137) = 373248 * k + 67706 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 67706) = 186624 * k + 33853 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 33853) = 279936 * k + 50780 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 50780) = 139968 * k + 25390 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25390) = 69984 * k + 12695 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 12695) = 104976 * k + 19043 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19043) = 157464 * k + 28565 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28565) = 236196 * k + 42848 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 42848) = 118098 * k + 21424 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21424) = 59049 * k + 10712 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11887) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11887)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11943_mod_65536 {n : ℕ} (hn : n % 65536 = 11943) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11943 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11943) = 98304 * k + 17915 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17915) = 147456 * k + 26873 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26873) = 221184 * k + 40310 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40310) = 110592 * k + 20155 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 20155) = 165888 * k + 30233 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 30233) = 248832 * k + 45350 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 45350) = 124416 * k + 22675 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 22675) = 186624 * k + 34013 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 34013) = 279936 * k + 51020 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 51020) = 139968 * k + 25510 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25510) = 69984 * k + 12755 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 12755) = 104976 * k + 19133 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19133) = 157464 * k + 28700 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28700) = 78732 * k + 14350 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14350) = 39366 * k + 7175 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7175) = 59049 * k + 10763 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11943) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11943)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_11967_mod_65536 {n : ℕ} (hn : n % 65536 = 11967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 11967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 11967) = 98304 * k + 17951 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 17951) = 147456 * k + 26927 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 26927) = 221184 * k + 40391 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40391) = 331776 * k + 60587 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 60587) = 497664 * k + 90881 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 90881) = 746496 * k + 136322 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 136322) = 373248 * k + 68161 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 68161) = 559872 * k + 102242 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 102242) = 279936 * k + 51121 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 51121) = 419904 * k + 76682 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 76682) = 209952 * k + 38341 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 38341) = 314928 * k + 57512 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 57512) = 157464 * k + 28756 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28756) = 78732 * k + 14378 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14378) = 39366 * k + 7189 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7189) = 59049 * k + 10784 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 11967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 11967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12007_mod_65536 {n : ℕ} (hn : n % 65536 = 12007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12007) = 98304 * k + 18011 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18011) = 147456 * k + 27017 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27017) = 221184 * k + 40526 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40526) = 110592 * k + 20263 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 20263) = 165888 * k + 30395 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 30395) = 248832 * k + 45593 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 45593) = 373248 * k + 68390 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 68390) = 186624 * k + 34195 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 34195) = 279936 * k + 51293 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 51293) = 419904 * k + 76940 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 76940) = 209952 * k + 38470 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 38470) = 104976 * k + 19235 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19235) = 157464 * k + 28853 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28853) = 236196 * k + 43280 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 43280) = 118098 * k + 21640 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21640) = 59049 * k + 10820 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12063_mod_65536 {n : ℕ} (hn : n % 65536 = 12063) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12063 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12063) = 98304 * k + 18095 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18095) = 147456 * k + 27143 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27143) = 221184 * k + 40715 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40715) = 331776 * k + 61073 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 61073) = 497664 * k + 91610 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 91610) = 248832 * k + 45805 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 45805) = 373248 * k + 68708 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 68708) = 186624 * k + 34354 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 34354) = 93312 * k + 17177 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 17177) = 139968 * k + 25766 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25766) = 69984 * k + 12883 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 12883) = 104976 * k + 19325 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19325) = 157464 * k + 28988 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 28988) = 78732 * k + 14494 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14494) = 39366 * k + 7247 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7247) = 59049 * k + 10871 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12063) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12063)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12143_mod_65536 {n : ℕ} (hn : n % 65536 = 12143) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12143 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12143) = 98304 * k + 18215 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18215) = 147456 * k + 27323 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27323) = 221184 * k + 40985 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 40985) = 331776 * k + 61478 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 61478) = 165888 * k + 30739 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 30739) = 248832 * k + 46109 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 46109) = 373248 * k + 69164 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 69164) = 186624 * k + 34582 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 34582) = 93312 * k + 17291 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 17291) = 139968 * k + 25937 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 25937) = 209952 * k + 38906 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 38906) = 104976 * k + 19453 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19453) = 157464 * k + 29180 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 29180) = 78732 * k + 14590 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14590) = 39366 * k + 7295 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7295) = 59049 * k + 10943 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12143) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12143)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12159_mod_65536 {n : ℕ} (hn : n % 65536 = 12159) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12159 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12159) = 98304 * k + 18239 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18239) = 147456 * k + 27359 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27359) = 221184 * k + 41039 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 41039) = 331776 * k + 61559 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 61559) = 497664 * k + 92339 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 92339) = 746496 * k + 138509 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 138509) = 1119744 * k + 207764 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 207764) = 559872 * k + 103882 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 103882) = 279936 * k + 51941 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 51941) = 419904 * k + 77912 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 77912) = 209952 * k + 38956 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 38956) = 104976 * k + 19478 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19478) = 52488 * k + 9739 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9739) = 78732 * k + 14609 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14609) = 118098 * k + 21914 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 21914) = 59049 * k + 10957 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12159) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12159)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12271_mod_65536 {n : ℕ} (hn : n % 65536 = 12271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12271) = 98304 * k + 18407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18407) = 147456 * k + 27611 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27611) = 221184 * k + 41417 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 41417) = 331776 * k + 62126 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 62126) = 165888 * k + 31063 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 31063) = 248832 * k + 46595 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 46595) = 373248 * k + 69893 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 69893) = 559872 * k + 104840 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 104840) = 279936 * k + 52420 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 52420) = 139968 * k + 26210 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 26210) = 69984 * k + 13105 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 13105) = 104976 * k + 19658 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19658) = 52488 * k + 9829 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9829) = 78732 * k + 14744 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14744) = 39366 * k + 7372 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7372) = 19683 * k + 3686 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12319_mod_65536 {n : ℕ} (hn : n % 65536 = 12319) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12319 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12319) = 98304 * k + 18479 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18479) = 147456 * k + 27719 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27719) = 221184 * k + 41579 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 41579) = 331776 * k + 62369 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 62369) = 497664 * k + 93554 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 93554) = 248832 * k + 46777 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 46777) = 373248 * k + 70166 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 70166) = 186624 * k + 35083 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 35083) = 279936 * k + 52625 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 52625) = 419904 * k + 78938 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 78938) = 209952 * k + 39469 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 39469) = 314928 * k + 59204 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 59204) = 157464 * k + 29602 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 29602) = 78732 * k + 14801 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14801) = 118098 * k + 22202 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 22202) = 59049 * k + 11101 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12319) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12319)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12351_mod_65536 {n : ℕ} (hn : n % 65536 = 12351) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12351 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12351) = 98304 * k + 18527 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18527) = 147456 * k + 27791 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27791) = 221184 * k + 41687 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 41687) = 331776 * k + 62531 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 62531) = 497664 * k + 93797 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 93797) = 746496 * k + 140696 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 140696) = 373248 * k + 70348 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 70348) = 186624 * k + 35174 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 35174) = 93312 * k + 17587 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 17587) = 139968 * k + 26381 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 26381) = 209952 * k + 39572 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 39572) = 104976 * k + 19786 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19786) = 52488 * k + 9893 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9893) = 78732 * k + 14840 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14840) = 39366 * k + 7420 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7420) = 19683 * k + 3710 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12351) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12351)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12391_mod_65536 {n : ℕ} (hn : n % 65536 = 12391) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12391 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12391) = 98304 * k + 18587 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18587) = 147456 * k + 27881 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 27881) = 221184 * k + 41822 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 41822) = 110592 * k + 20911 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 20911) = 165888 * k + 31367 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 31367) = 248832 * k + 47051 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 47051) = 373248 * k + 70577 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 70577) = 559872 * k + 105866 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 105866) = 279936 * k + 52933 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 52933) = 419904 * k + 79400 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 79400) = 209952 * k + 39700 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 39700) = 104976 * k + 19850 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 19850) = 52488 * k + 9925 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 9925) = 78732 * k + 14888 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 14888) = 39366 * k + 7444 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7444) = 19683 * k + 3722 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12391) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12391)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12495_mod_65536 {n : ℕ} (hn : n % 65536 = 12495) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12495 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12495) = 98304 * k + 18743 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18743) = 147456 * k + 28115 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28115) = 221184 * k + 42173 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 42173) = 331776 * k + 63260 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 63260) = 165888 * k + 31630 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 31630) = 82944 * k + 15815 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 15815) = 124416 * k + 23723 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 23723) = 186624 * k + 35585 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 35585) = 279936 * k + 53378 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 53378) = 139968 * k + 26689 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 26689) = 209952 * k + 40034 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 40034) = 104976 * k + 20017 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20017) = 157464 * k + 30026 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30026) = 78732 * k + 15013 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15013) = 118098 * k + 22520 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 22520) = 59049 * k + 11260 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12495) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12495)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12511_mod_65536 {n : ℕ} (hn : n % 65536 = 12511) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12511 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12511) = 98304 * k + 18767 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18767) = 147456 * k + 28151 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28151) = 221184 * k + 42227 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 42227) = 331776 * k + 63341 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 63341) = 497664 * k + 95012 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 95012) = 248832 * k + 47506 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 47506) = 124416 * k + 23753 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 23753) = 186624 * k + 35630 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 35630) = 93312 * k + 17815 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 17815) = 139968 * k + 26723 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 26723) = 209952 * k + 40085 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 40085) = 314928 * k + 60128 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 60128) = 157464 * k + 30064 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30064) = 78732 * k + 15032 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15032) = 39366 * k + 7516 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7516) = 19683 * k + 3758 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12511) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12511)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12543_mod_65536 {n : ℕ} (hn : n % 65536 = 12543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12543) = 98304 * k + 18815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18815) = 147456 * k + 28223 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28223) = 221184 * k + 42335 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 42335) = 331776 * k + 63503 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 63503) = 497664 * k + 95255 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 95255) = 746496 * k + 142883 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 142883) = 1119744 * k + 214325 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 214325) = 1679616 * k + 321488 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 321488) = 839808 * k + 160744 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 160744) = 419904 * k + 80372 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 80372) = 209952 * k + 40186 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 40186) = 104976 * k + 20093 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20093) = 157464 * k + 30140 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30140) = 78732 * k + 15070 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15070) = 39366 * k + 7535 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7535) = 59049 * k + 11303 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12571_mod_65536 {n : ℕ} (hn : n % 65536 = 12571) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12571 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12571) = 98304 * k + 18857 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18857) = 147456 * k + 28286 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28286) = 73728 * k + 14143 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 14143) = 110592 * k + 21215 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 21215) = 165888 * k + 31823 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 31823) = 248832 * k + 47735 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 47735) = 373248 * k + 71603 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 71603) = 559872 * k + 107405 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 107405) = 839808 * k + 161108 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 161108) = 419904 * k + 80554 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 80554) = 209952 * k + 40277 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 40277) = 314928 * k + 60416 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 60416) = 157464 * k + 30208 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30208) = 78732 * k + 15104 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15104) = 39366 * k + 7552 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7552) = 19683 * k + 3776 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12571) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12571)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12615_mod_65536 {n : ℕ} (hn : n % 65536 = 12615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12615) = 98304 * k + 18923 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 18923) = 147456 * k + 28385 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28385) = 221184 * k + 42578 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 42578) = 110592 * k + 21289 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 21289) = 165888 * k + 31934 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 31934) = 82944 * k + 15967 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 15967) = 124416 * k + 23951 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 23951) = 186624 * k + 35927 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 35927) = 279936 * k + 53891 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 53891) = 419904 * k + 80837 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 80837) = 629856 * k + 121256 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 121256) = 314928 * k + 60628 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 60628) = 157464 * k + 30314 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30314) = 78732 * k + 15157 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15157) = 118098 * k + 22736 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 22736) = 59049 * k + 11368 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12775_mod_65536 {n : ℕ} (hn : n % 65536 = 12775) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12775 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12775) = 98304 * k + 19163 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19163) = 147456 * k + 28745 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28745) = 221184 * k + 43118 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 43118) = 110592 * k + 21559 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 21559) = 165888 * k + 32339 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 32339) = 248832 * k + 48509 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 48509) = 373248 * k + 72764 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 72764) = 186624 * k + 36382 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 36382) = 93312 * k + 18191 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 18191) = 139968 * k + 27287 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 27287) = 209952 * k + 40931 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 40931) = 314928 * k + 61397 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 61397) = 472392 * k + 92096 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 92096) = 236196 * k + 46048 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 46048) = 118098 * k + 23024 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 23024) = 59049 * k + 11512 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12775) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12775)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12799_mod_65536 {n : ℕ} (hn : n % 65536 = 12799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12799) = 98304 * k + 19199 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19199) = 147456 * k + 28799 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28799) = 221184 * k + 43199 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 43199) = 331776 * k + 64799 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 64799) = 497664 * k + 97199 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 97199) = 746496 * k + 145799 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 145799) = 1119744 * k + 218699 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 218699) = 1679616 * k + 328049 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 328049) = 2519424 * k + 492074 := by unfold T; split <;> omega
  have h10 : T (2519424 * k + 492074) = 1259712 * k + 246037 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 246037) = 1889568 * k + 369056 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 369056) = 944784 * k + 184528 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 184528) = 472392 * k + 92264 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 92264) = 236196 * k + 46132 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 46132) = 118098 * k + 23066 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 23066) = 59049 * k + 11533 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12827_mod_65536 {n : ℕ} (hn : n % 65536 = 12827) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12827 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12827) = 98304 * k + 19241 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19241) = 147456 * k + 28862 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 28862) = 73728 * k + 14431 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 14431) = 110592 * k + 21647 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 21647) = 165888 * k + 32471 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 32471) = 248832 * k + 48707 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 48707) = 373248 * k + 73061 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 73061) = 559872 * k + 109592 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 109592) = 279936 * k + 54796 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 54796) = 139968 * k + 27398 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 27398) = 69984 * k + 13699 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 13699) = 104976 * k + 20549 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20549) = 157464 * k + 30824 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 30824) = 78732 * k + 15412 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15412) = 39366 * k + 7706 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7706) = 19683 * k + 3853 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12827) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12827)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_12967_mod_65536 {n : ℕ} (hn : n % 65536 = 12967) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 12967 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 12967) = 98304 * k + 19451 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19451) = 147456 * k + 29177 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29177) = 221184 * k + 43766 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 43766) = 110592 * k + 21883 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 21883) = 165888 * k + 32825 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 32825) = 248832 * k + 49238 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 49238) = 124416 * k + 24619 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 24619) = 186624 * k + 36929 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 36929) = 279936 * k + 55394 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 55394) = 139968 * k + 27697 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 27697) = 209952 * k + 41546 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 41546) = 104976 * k + 20773 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20773) = 157464 * k + 31160 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 31160) = 78732 * k + 15580 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15580) = 39366 * k + 7790 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7790) = 19683 * k + 3895 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 12967) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 12967)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13007_mod_65536 {n : ℕ} (hn : n % 65536 = 13007) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13007 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13007) = 98304 * k + 19511 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19511) = 147456 * k + 29267 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29267) = 221184 * k + 43901 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 43901) = 331776 * k + 65852 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 65852) = 165888 * k + 32926 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 32926) = 82944 * k + 16463 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 16463) = 124416 * k + 24695 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 24695) = 186624 * k + 37043 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 37043) = 279936 * k + 55565 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 55565) = 419904 * k + 83348 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 83348) = 209952 * k + 41674 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 41674) = 104976 * k + 20837 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20837) = 157464 * k + 31256 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 31256) = 78732 * k + 15628 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15628) = 39366 * k + 7814 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7814) = 19683 * k + 3907 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13007) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13007)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13087_mod_65536 {n : ℕ} (hn : n % 65536 = 13087) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13087 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13087) = 98304 * k + 19631 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19631) = 147456 * k + 29447 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29447) = 221184 * k + 44171 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 44171) = 331776 * k + 66257 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 66257) = 497664 * k + 99386 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 99386) = 248832 * k + 49693 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 49693) = 373248 * k + 74540 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 74540) = 186624 * k + 37270 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 37270) = 93312 * k + 18635 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 18635) = 139968 * k + 27953 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 27953) = 209952 * k + 41930 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 41930) = 104976 * k + 20965 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 20965) = 157464 * k + 31448 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 31448) = 78732 * k + 15724 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15724) = 39366 * k + 7862 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7862) = 19683 * k + 3931 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13087) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13087)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13147_mod_65536 {n : ℕ} (hn : n % 65536 = 13147) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13147 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13147) = 98304 * k + 19721 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19721) = 147456 * k + 29582 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29582) = 73728 * k + 14791 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 14791) = 110592 * k + 22187 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 22187) = 165888 * k + 33281 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 33281) = 248832 * k + 49922 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 49922) = 124416 * k + 24961 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 24961) = 186624 * k + 37442 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 37442) = 93312 * k + 18721 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 18721) = 139968 * k + 28082 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28082) = 69984 * k + 14041 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 14041) = 104976 * k + 21062 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21062) = 52488 * k + 10531 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 10531) = 78732 * k + 15797 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15797) = 118098 * k + 23696 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 23696) = 59049 * k + 11848 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13147) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13147)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13215_mod_65536 {n : ℕ} (hn : n % 65536 = 13215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13215) = 98304 * k + 19823 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19823) = 147456 * k + 29735 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29735) = 221184 * k + 44603 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 44603) = 331776 * k + 66905 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 66905) = 497664 * k + 100358 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 100358) = 248832 * k + 50179 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 50179) = 373248 * k + 75269 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 75269) = 559872 * k + 112904 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 112904) = 279936 * k + 56452 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 56452) = 139968 * k + 28226 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28226) = 69984 * k + 14113 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 14113) = 104976 * k + 21170 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21170) = 52488 * k + 10585 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 10585) = 78732 * k + 15878 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15878) = 39366 * k + 7939 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7939) = 59049 * k + 11909 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13279_mod_65536 {n : ℕ} (hn : n % 65536 = 13279) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13279 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13279) = 98304 * k + 19919 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19919) = 147456 * k + 29879 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29879) = 221184 * k + 44819 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 44819) = 331776 * k + 67229 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 67229) = 497664 * k + 100844 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 100844) = 248832 * k + 50422 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 50422) = 124416 * k + 25211 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 25211) = 186624 * k + 37817 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 37817) = 279936 * k + 56726 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 56726) = 139968 * k + 28363 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28363) = 209952 * k + 42545 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 42545) = 314928 * k + 63818 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 63818) = 157464 * k + 31909 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 31909) = 236196 * k + 47864 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 47864) = 118098 * k + 23932 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 23932) = 59049 * k + 11966 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13279) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13279)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13295_mod_65536 {n : ℕ} (hn : n % 65536 = 13295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13295) = 98304 * k + 19943 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 19943) = 147456 * k + 29915 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 29915) = 221184 * k + 44873 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 44873) = 331776 * k + 67310 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 67310) = 165888 * k + 33655 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 33655) = 248832 * k + 50483 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 50483) = 373248 * k + 75725 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 75725) = 559872 * k + 113588 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 113588) = 279936 * k + 56794 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 56794) = 139968 * k + 28397 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28397) = 209952 * k + 42596 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 42596) = 104976 * k + 21298 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21298) = 52488 * k + 10649 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 10649) = 78732 * k + 15974 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 15974) = 39366 * k + 7987 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 7987) = 59049 * k + 11981 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13339_mod_65536 {n : ℕ} (hn : n % 65536 = 13339) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13339 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13339) = 98304 * k + 20009 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20009) = 147456 * k + 30014 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30014) = 73728 * k + 15007 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 15007) = 110592 * k + 22511 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 22511) = 165888 * k + 33767 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 33767) = 248832 * k + 50651 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 50651) = 373248 * k + 75977 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 75977) = 559872 * k + 113966 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 113966) = 279936 * k + 56983 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 56983) = 419904 * k + 85475 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 85475) = 629856 * k + 128213 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 128213) = 944784 * k + 192320 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 192320) = 472392 * k + 96160 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 96160) = 236196 * k + 48080 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 48080) = 118098 * k + 24040 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24040) = 59049 * k + 12020 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13339) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13339)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13467_mod_65536 {n : ℕ} (hn : n % 65536 = 13467) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13467 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13467) = 98304 * k + 20201 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20201) = 147456 * k + 30302 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30302) = 73728 * k + 15151 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 15151) = 110592 * k + 22727 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 22727) = 165888 * k + 34091 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 34091) = 248832 * k + 51137 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 51137) = 373248 * k + 76706 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 76706) = 186624 * k + 38353 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 38353) = 279936 * k + 57530 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 57530) = 139968 * k + 28765 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28765) = 209952 * k + 43148 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 43148) = 104976 * k + 21574 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21574) = 52488 * k + 10787 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 10787) = 78732 * k + 16181 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16181) = 118098 * k + 24272 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24272) = 59049 * k + 12136 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13467) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13467)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13535_mod_65536 {n : ℕ} (hn : n % 65536 = 13535) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13535 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13535) = 98304 * k + 20303 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20303) = 147456 * k + 30455 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30455) = 221184 * k + 45683 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 45683) = 331776 * k + 68525 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 68525) = 497664 * k + 102788 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 102788) = 248832 * k + 51394 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 51394) = 124416 * k + 25697 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 25697) = 186624 * k + 38546 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 38546) = 93312 * k + 19273 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 19273) = 139968 * k + 28910 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 28910) = 69984 * k + 14455 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 14455) = 104976 * k + 21683 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21683) = 157464 * k + 32525 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 32525) = 236196 * k + 48788 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 48788) = 118098 * k + 24394 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24394) = 59049 * k + 12197 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13535) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13535)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13567_mod_65536 {n : ℕ} (hn : n % 65536 = 13567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13567) = 98304 * k + 20351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20351) = 147456 * k + 30527 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30527) = 221184 * k + 45791 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 45791) = 331776 * k + 68687 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 68687) = 497664 * k + 103031 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 103031) = 746496 * k + 154547 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 154547) = 1119744 * k + 231821 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 231821) = 1679616 * k + 347732 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 347732) = 839808 * k + 173866 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 173866) = 419904 * k + 86933 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 86933) = 629856 * k + 130400 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 130400) = 314928 * k + 65200 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 65200) = 157464 * k + 32600 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 32600) = 78732 * k + 16300 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16300) = 39366 * k + 8150 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8150) = 19683 * k + 4075 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13615_mod_65536 {n : ℕ} (hn : n % 65536 = 13615) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13615 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13615) = 98304 * k + 20423 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20423) = 147456 * k + 30635 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30635) = 221184 * k + 45953 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 45953) = 331776 * k + 68930 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 68930) = 165888 * k + 34465 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 34465) = 248832 * k + 51698 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 51698) = 124416 * k + 25849 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 25849) = 186624 * k + 38774 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 38774) = 93312 * k + 19387 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 19387) = 139968 * k + 29081 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29081) = 209952 * k + 43622 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 43622) = 104976 * k + 21811 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 21811) = 157464 * k + 32717 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 32717) = 236196 * k + 49076 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 49076) = 118098 * k + 24538 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24538) = 59049 * k + 12269 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13615) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13615)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13671_mod_65536 {n : ℕ} (hn : n % 65536 = 13671) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13671 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13671) = 98304 * k + 20507 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20507) = 147456 * k + 30761 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30761) = 221184 * k + 46142 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 46142) = 110592 * k + 23071 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 23071) = 165888 * k + 34607 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 34607) = 248832 * k + 51911 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 51911) = 373248 * k + 77867 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 77867) = 559872 * k + 116801 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 116801) = 839808 * k + 175202 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 175202) = 419904 * k + 87601 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 87601) = 629856 * k + 131402 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 131402) = 314928 * k + 65701 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 65701) = 472392 * k + 98552 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 98552) = 236196 * k + 49276 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 49276) = 118098 * k + 24638 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24638) = 59049 * k + 12319 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13671) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13671)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13695_mod_65536 {n : ℕ} (hn : n % 65536 = 13695) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13695 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13695) = 98304 * k + 20543 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20543) = 147456 * k + 30815 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 30815) = 221184 * k + 46223 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 46223) = 331776 * k + 69335 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 69335) = 497664 * k + 104003 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 104003) = 746496 * k + 156005 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 156005) = 1119744 * k + 234008 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 234008) = 559872 * k + 117004 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 117004) = 279936 * k + 58502 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 58502) = 139968 * k + 29251 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29251) = 209952 * k + 43877 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 43877) = 314928 * k + 65816 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 65816) = 157464 * k + 32908 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 32908) = 78732 * k + 16454 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16454) = 39366 * k + 8227 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8227) = 59049 * k + 12341 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13695) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13695)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13799_mod_65536 {n : ℕ} (hn : n % 65536 = 13799) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13799 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13799) = 98304 * k + 20699 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20699) = 147456 * k + 31049 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31049) = 221184 * k + 46574 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 46574) = 110592 * k + 23287 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 23287) = 165888 * k + 34931 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 34931) = 248832 * k + 52397 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 52397) = 373248 * k + 78596 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 78596) = 186624 * k + 39298 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 39298) = 93312 * k + 19649 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 19649) = 139968 * k + 29474 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29474) = 69984 * k + 14737 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 14737) = 104976 * k + 22106 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22106) = 52488 * k + 11053 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 11053) = 78732 * k + 16580 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16580) = 39366 * k + 8290 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8290) = 19683 * k + 4145 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13799) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13799)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13807_mod_65536 {n : ℕ} (hn : n % 65536 = 13807) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13807 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13807) = 98304 * k + 20711 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20711) = 147456 * k + 31067 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31067) = 221184 * k + 46601 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 46601) = 331776 * k + 69902 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 69902) = 165888 * k + 34951 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 34951) = 248832 * k + 52427 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 52427) = 373248 * k + 78641 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 78641) = 559872 * k + 117962 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 117962) = 279936 * k + 58981 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 58981) = 419904 * k + 88472 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 88472) = 209952 * k + 44236 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44236) = 104976 * k + 22118 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22118) = 52488 * k + 11059 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 11059) = 78732 * k + 16589 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16589) = 118098 * k + 24884 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24884) = 59049 * k + 12442 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13807) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13807)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13851_mod_65536 {n : ℕ} (hn : n % 65536 = 13851) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13851 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13851) = 98304 * k + 20777 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20777) = 147456 * k + 31166 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31166) = 73728 * k + 15583 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 15583) = 110592 * k + 23375 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 23375) = 165888 * k + 35063 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 35063) = 248832 * k + 52595 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 52595) = 373248 * k + 78893 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 78893) = 559872 * k + 118340 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 118340) = 279936 * k + 59170 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59170) = 139968 * k + 29585 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29585) = 209952 * k + 44378 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44378) = 104976 * k + 22189 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22189) = 157464 * k + 33284 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 33284) = 78732 * k + 16642 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16642) = 39366 * k + 8321 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8321) = 59049 * k + 12482 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13851) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13851)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13855_mod_65536 {n : ℕ} (hn : n % 65536 = 13855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13855) = 98304 * k + 20783 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20783) = 147456 * k + 31175 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31175) = 221184 * k + 46763 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 46763) = 331776 * k + 70145 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 70145) = 497664 * k + 105218 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 105218) = 248832 * k + 52609 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 52609) = 373248 * k + 78914 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 78914) = 186624 * k + 39457 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 39457) = 279936 * k + 59186 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59186) = 139968 * k + 29593 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29593) = 209952 * k + 44390 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44390) = 104976 * k + 22195 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22195) = 157464 * k + 33293 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 33293) = 236196 * k + 49940 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 49940) = 118098 * k + 24970 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 24970) = 59049 * k + 12485 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13927_mod_65536 {n : ℕ} (hn : n % 65536 = 13927) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13927 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13927) = 98304 * k + 20891 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20891) = 147456 * k + 31337 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31337) = 221184 * k + 47006 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 47006) = 110592 * k + 23503 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 23503) = 165888 * k + 35255 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 35255) = 248832 * k + 52883 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 52883) = 373248 * k + 79325 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 79325) = 559872 * k + 118988 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 118988) = 279936 * k + 59494 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59494) = 139968 * k + 29747 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 29747) = 209952 * k + 44621 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44621) = 314928 * k + 66932 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 66932) = 157464 * k + 33466 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 33466) = 78732 * k + 16733 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16733) = 118098 * k + 25100 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25100) = 59049 * k + 12550 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13927) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13927)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13951_mod_65536 {n : ℕ} (hn : n % 65536 = 13951) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13951 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13951) = 98304 * k + 20927 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20927) = 147456 * k + 31391 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31391) = 221184 * k + 47087 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 47087) = 331776 * k + 70631 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 70631) = 497664 * k + 105947 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 105947) = 746496 * k + 158921 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 158921) = 1119744 * k + 238382 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 238382) = 559872 * k + 119191 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 119191) = 839808 * k + 178787 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 178787) = 1259712 * k + 268181 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 268181) = 1889568 * k + 402272 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 402272) = 944784 * k + 201136 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 201136) = 472392 * k + 100568 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 100568) = 236196 * k + 50284 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 50284) = 118098 * k + 25142 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25142) = 59049 * k + 12571 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13951) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13951)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_13979_mod_65536 {n : ℕ} (hn : n % 65536 = 13979) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 13979 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 13979) = 98304 * k + 20969 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 20969) = 147456 * k + 31454 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31454) = 73728 * k + 15727 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 15727) = 110592 * k + 23591 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 23591) = 165888 * k + 35387 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 35387) = 248832 * k + 53081 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 53081) = 373248 * k + 79622 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 79622) = 186624 * k + 39811 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 39811) = 279936 * k + 59717 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59717) = 419904 * k + 89576 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 89576) = 209952 * k + 44788 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44788) = 104976 * k + 22394 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22394) = 52488 * k + 11197 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 11197) = 78732 * k + 16796 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16796) = 39366 * k + 8398 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8398) = 19683 * k + 4199 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 13979) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 13979)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14015_mod_65536 {n : ℕ} (hn : n % 65536 = 14015) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14015 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14015) = 98304 * k + 21023 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21023) = 147456 * k + 31535 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31535) = 221184 * k + 47303 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 47303) = 331776 * k + 70955 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 70955) = 497664 * k + 106433 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 106433) = 746496 * k + 159650 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 159650) = 373248 * k + 79825 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 79825) = 559872 * k + 119738 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 119738) = 279936 * k + 59869 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59869) = 419904 * k + 89804 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 89804) = 209952 * k + 44902 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 44902) = 104976 * k + 22451 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22451) = 157464 * k + 33677 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 33677) = 236196 * k + 50516 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 50516) = 118098 * k + 25258 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25258) = 59049 * k + 12629 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14015) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14015)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14031_mod_65536 {n : ℕ} (hn : n % 65536 = 14031) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14031 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14031) = 98304 * k + 21047 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21047) = 147456 * k + 31571 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31571) = 221184 * k + 47357 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 47357) = 331776 * k + 71036 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 71036) = 165888 * k + 35518 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 35518) = 82944 * k + 17759 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 17759) = 124416 * k + 26639 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 26639) = 186624 * k + 39959 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 39959) = 279936 * k + 59939 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 59939) = 419904 * k + 89909 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 89909) = 629856 * k + 134864 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 134864) = 314928 * k + 67432 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 67432) = 157464 * k + 33716 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 33716) = 78732 * k + 16858 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 16858) = 39366 * k + 8429 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8429) = 59049 * k + 12644 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14031) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14031)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14207_mod_65536 {n : ℕ} (hn : n % 65536 = 14207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14207) = 98304 * k + 21311 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21311) = 147456 * k + 31967 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 31967) = 221184 * k + 47951 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 47951) = 331776 * k + 71927 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 71927) = 497664 * k + 107891 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 107891) = 746496 * k + 161837 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 161837) = 1119744 * k + 242756 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 242756) = 559872 * k + 121378 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 121378) = 279936 * k + 60689 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 60689) = 419904 * k + 91034 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 91034) = 209952 * k + 45517 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 45517) = 314928 * k + 68276 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 68276) = 157464 * k + 34138 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34138) = 78732 * k + 17069 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17069) = 118098 * k + 25604 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25604) = 59049 * k + 12802 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14239_mod_65536 {n : ℕ} (hn : n % 65536 = 14239) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14239 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14239) = 98304 * k + 21359 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21359) = 147456 * k + 32039 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32039) = 221184 * k + 48059 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48059) = 331776 * k + 72089 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 72089) = 497664 * k + 108134 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 108134) = 248832 * k + 54067 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 54067) = 373248 * k + 81101 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 81101) = 559872 * k + 121652 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 121652) = 279936 * k + 60826 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 60826) = 139968 * k + 30413 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 30413) = 209952 * k + 45620 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 45620) = 104976 * k + 22810 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22810) = 52488 * k + 11405 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 11405) = 78732 * k + 17108 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17108) = 39366 * k + 8554 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8554) = 19683 * k + 4277 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14239) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14239)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14271_mod_65536 {n : ℕ} (hn : n % 65536 = 14271) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14271 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14271) = 98304 * k + 21407 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21407) = 147456 * k + 32111 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32111) = 221184 * k + 48167 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48167) = 331776 * k + 72251 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 72251) = 497664 * k + 108377 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 108377) = 746496 * k + 162566 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 162566) = 373248 * k + 81283 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 81283) = 559872 * k + 121925 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 121925) = 839808 * k + 182888 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 182888) = 419904 * k + 91444 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 91444) = 209952 * k + 45722 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 45722) = 104976 * k + 22861 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22861) = 157464 * k + 34292 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34292) = 78732 * k + 17146 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17146) = 39366 * k + 8573 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8573) = 59049 * k + 12860 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14271) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14271)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14303_mod_65536 {n : ℕ} (hn : n % 65536 = 14303) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14303 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14303) = 98304 * k + 21455 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21455) = 147456 * k + 32183 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32183) = 221184 * k + 48275 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48275) = 331776 * k + 72413 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 72413) = 497664 * k + 108620 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 108620) = 248832 * k + 54310 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 54310) = 124416 * k + 27155 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 27155) = 186624 * k + 40733 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 40733) = 279936 * k + 61100 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 61100) = 139968 * k + 30550 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 30550) = 69984 * k + 15275 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 15275) = 104976 * k + 22913 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 22913) = 157464 * k + 34370 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34370) = 78732 * k + 17185 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17185) = 118098 * k + 25778 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25778) = 59049 * k + 12889 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14303) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14303)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14363_mod_65536 {n : ℕ} (hn : n % 65536 = 14363) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14363 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14363) = 98304 * k + 21545 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21545) = 147456 * k + 32318 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32318) = 73728 * k + 16159 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 16159) = 110592 * k + 24239 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 24239) = 165888 * k + 36359 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 36359) = 248832 * k + 54539 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 54539) = 373248 * k + 81809 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 81809) = 559872 * k + 122714 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 122714) = 279936 * k + 61357 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 61357) = 419904 * k + 92036 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 92036) = 209952 * k + 46018 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 46018) = 104976 * k + 23009 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 23009) = 157464 * k + 34514 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34514) = 78732 * k + 17257 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17257) = 118098 * k + 25886 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25886) = 59049 * k + 12943 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14363) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14363)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14383_mod_65536 {n : ℕ} (hn : n % 65536 = 14383) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14383 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14383) = 98304 * k + 21575 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21575) = 147456 * k + 32363 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32363) = 221184 * k + 48545 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48545) = 331776 * k + 72818 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 72818) = 165888 * k + 36409 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 36409) = 248832 * k + 54614 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 54614) = 124416 * k + 27307 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 27307) = 186624 * k + 40961 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 40961) = 279936 * k + 61442 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 61442) = 139968 * k + 30721 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 30721) = 209952 * k + 46082 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 46082) = 104976 * k + 23041 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 23041) = 157464 * k + 34562 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34562) = 78732 * k + 17281 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17281) = 118098 * k + 25922 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 25922) = 59049 * k + 12961 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14383) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14383)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14399_mod_65536 {n : ℕ} (hn : n % 65536 = 14399) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14399 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14399) = 98304 * k + 21599 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21599) = 147456 * k + 32399 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32399) = 221184 * k + 48599 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48599) = 331776 * k + 72899 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 72899) = 497664 * k + 109349 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 109349) = 746496 * k + 164024 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 164024) = 373248 * k + 82012 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 82012) = 186624 * k + 41006 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 41006) = 93312 * k + 20503 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 20503) = 139968 * k + 30755 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 30755) = 209952 * k + 46133 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 46133) = 314928 * k + 69200 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 69200) = 157464 * k + 34600 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34600) = 78732 * k + 17300 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17300) = 39366 * k + 8650 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8650) = 19683 * k + 4325 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14399) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14399)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14439_mod_65536 {n : ℕ} (hn : n % 65536 = 14439) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14439 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14439) = 98304 * k + 21659 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21659) = 147456 * k + 32489 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32489) = 221184 * k + 48734 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48734) = 110592 * k + 24367 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 24367) = 165888 * k + 36551 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 36551) = 248832 * k + 54827 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 54827) = 373248 * k + 82241 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 82241) = 559872 * k + 123362 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 123362) = 279936 * k + 61681 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 61681) = 419904 * k + 92522 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 92522) = 209952 * k + 46261 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 46261) = 314928 * k + 69392 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 69392) = 157464 * k + 34696 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34696) = 78732 * k + 17348 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17348) = 39366 * k + 8674 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8674) = 19683 * k + 4337 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14439) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14439)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14503_mod_65536 {n : ℕ} (hn : n % 65536 = 14503) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14503 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14503) = 98304 * k + 21755 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21755) = 147456 * k + 32633 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32633) = 221184 * k + 48950 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 48950) = 110592 * k + 24475 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 24475) = 165888 * k + 36713 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 36713) = 248832 * k + 55070 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 55070) = 124416 * k + 27535 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 27535) = 186624 * k + 41303 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 41303) = 279936 * k + 61955 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 61955) = 419904 * k + 92933 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 92933) = 629856 * k + 139400 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 139400) = 314928 * k + 69700 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 69700) = 157464 * k + 34850 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 34850) = 78732 * k + 17425 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17425) = 118098 * k + 26138 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 26138) = 59049 * k + 13069 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14503) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14503)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14543_mod_65536 {n : ℕ} (hn : n % 65536 = 14543) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14543 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14543) = 98304 * k + 21815 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 21815) = 147456 * k + 32723 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 32723) = 221184 * k + 49085 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 49085) = 331776 * k + 73628 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 73628) = 165888 * k + 36814 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 36814) = 82944 * k + 18407 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 18407) = 124416 * k + 27611 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 27611) = 186624 * k + 41417 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 41417) = 279936 * k + 62126 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 62126) = 139968 * k + 31063 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 31063) = 209952 * k + 46595 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 46595) = 314928 * k + 69893 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 69893) = 472392 * k + 104840 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 104840) = 236196 * k + 52420 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 52420) = 118098 * k + 26210 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 26210) = 59049 * k + 13105 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14543) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14543)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14747_mod_65536 {n : ℕ} (hn : n % 65536 = 14747) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14747 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14747) = 98304 * k + 22121 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22121) = 147456 * k + 33182 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 33182) = 73728 * k + 16591 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 16591) = 110592 * k + 24887 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 24887) = 165888 * k + 37331 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 37331) = 248832 * k + 55997 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 55997) = 373248 * k + 83996 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 83996) = 186624 * k + 41998 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 41998) = 93312 * k + 20999 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 20999) = 139968 * k + 31499 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 31499) = 209952 * k + 47249 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 47249) = 314928 * k + 70874 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 70874) = 157464 * k + 35437 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 35437) = 236196 * k + 53156 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 53156) = 118098 * k + 26578 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 26578) = 59049 * k + 13289 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14747) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14747)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14823_mod_65536 {n : ℕ} (hn : n % 65536 = 14823) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14823 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14823) = 98304 * k + 22235 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22235) = 147456 * k + 33353 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 33353) = 221184 * k + 50030 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 50030) = 110592 * k + 25015 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 25015) = 165888 * k + 37523 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 37523) = 248832 * k + 56285 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 56285) = 373248 * k + 84428 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 84428) = 186624 * k + 42214 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 42214) = 93312 * k + 21107 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 21107) = 139968 * k + 31661 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 31661) = 209952 * k + 47492 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 47492) = 104976 * k + 23746 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 23746) = 52488 * k + 11873 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 11873) = 78732 * k + 17810 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17810) = 39366 * k + 8905 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8905) = 59049 * k + 13358 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14823) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14823)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_14895_mod_65536 {n : ℕ} (hn : n % 65536 = 14895) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 14895 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 14895) = 98304 * k + 22343 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22343) = 147456 * k + 33515 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 33515) = 221184 * k + 50273 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 50273) = 331776 * k + 75410 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 75410) = 165888 * k + 37705 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 37705) = 248832 * k + 56558 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 56558) = 124416 * k + 28279 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 28279) = 186624 * k + 42419 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 42419) = 279936 * k + 63629 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 63629) = 419904 * k + 95444 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 95444) = 209952 * k + 47722 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 47722) = 104976 * k + 23861 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 23861) = 157464 * k + 35792 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 35792) = 78732 * k + 17896 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 17896) = 39366 * k + 8948 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 8948) = 19683 * k + 4474 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 14895) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 14895)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15103_mod_65536 {n : ℕ} (hn : n % 65536 = 15103) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15103 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15103) = 98304 * k + 22655 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22655) = 147456 * k + 33983 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 33983) = 221184 * k + 50975 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 50975) = 331776 * k + 76463 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 76463) = 497664 * k + 114695 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 114695) = 746496 * k + 172043 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 172043) = 1119744 * k + 258065 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 258065) = 1679616 * k + 387098 := by unfold T; split <;> omega
  have h9 : T (1679616 * k + 387098) = 839808 * k + 193549 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 193549) = 1259712 * k + 290324 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 290324) = 629856 * k + 145162 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 145162) = 314928 * k + 72581 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 72581) = 472392 * k + 108872 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 108872) = 236196 * k + 54436 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 54436) = 118098 * k + 27218 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27218) = 59049 * k + 13609 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15103) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15103)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15167_mod_65536 {n : ℕ} (hn : n % 65536 = 15167) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15167 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15167) = 98304 * k + 22751 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22751) = 147456 * k + 34127 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34127) = 221184 * k + 51191 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51191) = 331776 * k + 76787 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 76787) = 497664 * k + 115181 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 115181) = 746496 * k + 172772 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 172772) = 373248 * k + 86386 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 86386) = 186624 * k + 43193 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 43193) = 279936 * k + 64790 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 64790) = 139968 * k + 32395 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 32395) = 209952 * k + 48593 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 48593) = 314928 * k + 72890 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 72890) = 157464 * k + 36445 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 36445) = 236196 * k + 54668 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 54668) = 118098 * k + 27334 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27334) = 59049 * k + 13667 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15167) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15167)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15175_mod_65536 {n : ℕ} (hn : n % 65536 = 15175) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15175 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15175) = 98304 * k + 22763 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22763) = 147456 * k + 34145 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34145) = 221184 * k + 51218 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51218) = 110592 * k + 25609 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 25609) = 165888 * k + 38414 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 38414) = 82944 * k + 19207 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 19207) = 124416 * k + 28811 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 28811) = 186624 * k + 43217 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 43217) = 279936 * k + 64826 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 64826) = 139968 * k + 32413 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 32413) = 209952 * k + 48620 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 48620) = 104976 * k + 24310 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 24310) = 52488 * k + 12155 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 12155) = 78732 * k + 18233 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18233) = 118098 * k + 27350 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27350) = 59049 * k + 13675 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15175) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15175)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15207_mod_65536 {n : ℕ} (hn : n % 65536 = 15207) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15207 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15207) = 98304 * k + 22811 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22811) = 147456 * k + 34217 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34217) = 221184 * k + 51326 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51326) = 110592 * k + 25663 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 25663) = 165888 * k + 38495 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 38495) = 248832 * k + 57743 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 57743) = 373248 * k + 86615 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 86615) = 559872 * k + 129923 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 129923) = 839808 * k + 194885 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 194885) = 1259712 * k + 292328 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 292328) = 629856 * k + 146164 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 146164) = 314928 * k + 73082 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 73082) = 157464 * k + 36541 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 36541) = 236196 * k + 54812 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 54812) = 118098 * k + 27406 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27406) = 59049 * k + 13703 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15207) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15207)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15215_mod_65536 {n : ℕ} (hn : n % 65536 = 15215) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15215 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15215) = 98304 * k + 22823 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22823) = 147456 * k + 34235 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34235) = 221184 * k + 51353 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51353) = 331776 * k + 77030 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 77030) = 165888 * k + 38515 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 38515) = 248832 * k + 57773 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 57773) = 373248 * k + 86660 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 86660) = 186624 * k + 43330 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 43330) = 93312 * k + 21665 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 21665) = 139968 * k + 32498 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 32498) = 69984 * k + 16249 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 16249) = 104976 * k + 24374 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 24374) = 52488 * k + 12187 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 12187) = 78732 * k + 18281 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18281) = 118098 * k + 27422 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27422) = 59049 * k + 13711 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15215) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15215)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15295_mod_65536 {n : ℕ} (hn : n % 65536 = 15295) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15295 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15295) = 98304 * k + 22943 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 22943) = 147456 * k + 34415 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34415) = 221184 * k + 51623 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51623) = 331776 * k + 77435 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 77435) = 497664 * k + 116153 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 116153) = 746496 * k + 174230 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 174230) = 373248 * k + 87115 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 87115) = 559872 * k + 130673 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 130673) = 839808 * k + 196010 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 196010) = 419904 * k + 98005 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 98005) = 629856 * k + 147008 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 147008) = 314928 * k + 73504 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 73504) = 157464 * k + 36752 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 36752) = 78732 * k + 18376 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18376) = 39366 * k + 9188 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9188) = 19683 * k + 4594 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15295) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15295)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15343_mod_65536 {n : ℕ} (hn : n % 65536 = 15343) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15343 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15343) = 98304 * k + 23015 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23015) = 147456 * k + 34523 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34523) = 221184 * k + 51785 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 51785) = 331776 * k + 77678 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 77678) = 165888 * k + 38839 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 38839) = 248832 * k + 58259 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 58259) = 373248 * k + 87389 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 87389) = 559872 * k + 131084 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 131084) = 279936 * k + 65542 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 65542) = 139968 * k + 32771 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 32771) = 209952 * k + 49157 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 49157) = 314928 * k + 73736 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 73736) = 157464 * k + 36868 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 36868) = 78732 * k + 18434 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18434) = 39366 * k + 9217 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9217) = 59049 * k + 13826 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15343) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15343)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15423_mod_65536 {n : ℕ} (hn : n % 65536 = 15423) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15423 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15423) = 98304 * k + 23135 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23135) = 147456 * k + 34703 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34703) = 221184 * k + 52055 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 52055) = 331776 * k + 78083 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 78083) = 497664 * k + 117125 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 117125) = 746496 * k + 175688 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 175688) = 373248 * k + 87844 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 87844) = 186624 * k + 43922 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 43922) = 93312 * k + 21961 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 21961) = 139968 * k + 32942 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 32942) = 69984 * k + 16471 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 16471) = 104976 * k + 24707 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 24707) = 157464 * k + 37061 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 37061) = 236196 * k + 55592 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 55592) = 118098 * k + 27796 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27796) = 59049 * k + 13898 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15423) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15423)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15487_mod_65536 {n : ℕ} (hn : n % 65536 = 15487) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15487 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15487) = 98304 * k + 23231 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23231) = 147456 * k + 34847 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34847) = 221184 * k + 52271 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 52271) = 331776 * k + 78407 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 78407) = 497664 * k + 117611 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 117611) = 746496 * k + 176417 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 176417) = 1119744 * k + 264626 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 264626) = 559872 * k + 132313 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 132313) = 839808 * k + 198470 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 198470) = 419904 * k + 99235 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 99235) = 629856 * k + 148853 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 148853) = 944784 * k + 223280 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 223280) = 472392 * k + 111640 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 111640) = 236196 * k + 55820 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 55820) = 118098 * k + 27910 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27910) = 59049 * k + 13955 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15487) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15487)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15515_mod_65536 {n : ℕ} (hn : n % 65536 = 15515) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15515 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15515) = 98304 * k + 23273 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23273) = 147456 * k + 34910 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 34910) = 73728 * k + 17455 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 17455) = 110592 * k + 26183 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 26183) = 165888 * k + 39275 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39275) = 248832 * k + 58913 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 58913) = 373248 * k + 88370 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 88370) = 186624 * k + 44185 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 44185) = 279936 * k + 66278 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 66278) = 139968 * k + 33139 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 33139) = 209952 * k + 49709 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 49709) = 314928 * k + 74564 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 74564) = 157464 * k + 37282 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 37282) = 78732 * k + 18641 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18641) = 118098 * k + 27962 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 27962) = 59049 * k + 13981 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15515) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15515)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15567_mod_65536 {n : ℕ} (hn : n % 65536 = 15567) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15567 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15567) = 98304 * k + 23351 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23351) = 147456 * k + 35027 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35027) = 221184 * k + 52541 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 52541) = 331776 * k + 78812 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 78812) = 165888 * k + 39406 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39406) = 82944 * k + 19703 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 19703) = 124416 * k + 29555 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 29555) = 186624 * k + 44333 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 44333) = 279936 * k + 66500 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 66500) = 139968 * k + 33250 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 33250) = 69984 * k + 16625 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 16625) = 104976 * k + 24938 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 24938) = 52488 * k + 12469 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 12469) = 78732 * k + 18704 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18704) = 39366 * k + 9352 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9352) = 19683 * k + 4676 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15567) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15567)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15599_mod_65536 {n : ℕ} (hn : n % 65536 = 15599) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15599 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15599) = 98304 * k + 23399 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23399) = 147456 * k + 35099 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35099) = 221184 * k + 52649 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 52649) = 331776 * k + 78974 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 78974) = 165888 * k + 39487 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39487) = 248832 * k + 59231 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 59231) = 373248 * k + 88847 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 88847) = 559872 * k + 133271 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 133271) = 839808 * k + 199907 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 199907) = 1259712 * k + 299861 := by unfold T; split <;> omega
  have h11 : T (1259712 * k + 299861) = 1889568 * k + 449792 := by unfold T; split <;> omega
  have h12 : T (1889568 * k + 449792) = 944784 * k + 224896 := by unfold T; split <;> omega
  have h13 : T (944784 * k + 224896) = 472392 * k + 112448 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 112448) = 236196 * k + 56224 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 56224) = 118098 * k + 28112 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 28112) = 59049 * k + 14056 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15599) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15599)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15643_mod_65536 {n : ℕ} (hn : n % 65536 = 15643) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15643 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15643) = 98304 * k + 23465 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23465) = 147456 * k + 35198 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35198) = 73728 * k + 17599 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 17599) = 110592 * k + 26399 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 26399) = 165888 * k + 39599 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39599) = 248832 * k + 59399 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 59399) = 373248 * k + 89099 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 89099) = 559872 * k + 133649 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 133649) = 839808 * k + 200474 := by unfold T; split <;> omega
  have h10 : T (839808 * k + 200474) = 419904 * k + 100237 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 100237) = 629856 * k + 150356 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 150356) = 314928 * k + 75178 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 75178) = 157464 * k + 37589 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 37589) = 236196 * k + 56384 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 56384) = 118098 * k + 28192 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 28192) = 59049 * k + 14096 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15643) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15643)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15687_mod_65536 {n : ℕ} (hn : n % 65536 = 15687) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15687 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15687) = 98304 * k + 23531 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23531) = 147456 * k + 35297 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35297) = 221184 * k + 52946 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 52946) = 110592 * k + 26473 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 26473) = 165888 * k + 39710 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39710) = 82944 * k + 19855 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 19855) = 124416 * k + 29783 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 29783) = 186624 * k + 44675 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 44675) = 279936 * k + 67013 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 67013) = 419904 * k + 100520 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 100520) = 209952 * k + 50260 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 50260) = 104976 * k + 25130 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25130) = 52488 * k + 12565 := by unfold T; split <;> omega
  have h14 : T (52488 * k + 12565) = 78732 * k + 18848 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18848) = 39366 * k + 9424 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9424) = 19683 * k + 4712 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15687) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15687)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15743_mod_65536 {n : ℕ} (hn : n % 65536 = 15743) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15743 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15743) = 98304 * k + 23615 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23615) = 147456 * k + 35423 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35423) = 221184 * k + 53135 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 53135) = 331776 * k + 79703 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 79703) = 497664 * k + 119555 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 119555) = 746496 * k + 179333 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 179333) = 1119744 * k + 269000 := by unfold T; split <;> omega
  have h8 : T (1119744 * k + 269000) = 559872 * k + 134500 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 134500) = 279936 * k + 67250 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 67250) = 139968 * k + 33625 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 33625) = 209952 * k + 50438 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 50438) = 104976 * k + 25219 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25219) = 157464 * k + 37829 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 37829) = 236196 * k + 56744 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 56744) = 118098 * k + 28372 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 28372) = 59049 * k + 14186 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15743) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15743)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15771_mod_65536 {n : ℕ} (hn : n % 65536 = 15771) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15771 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15771) = 98304 * k + 23657 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23657) = 147456 * k + 35486 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35486) = 73728 * k + 17743 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 17743) = 110592 * k + 26615 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 26615) = 165888 * k + 39923 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 39923) = 248832 * k + 59885 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 59885) = 373248 * k + 89828 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 89828) = 186624 * k + 44914 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 44914) = 93312 * k + 22457 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 22457) = 139968 * k + 33686 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 33686) = 69984 * k + 16843 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 16843) = 104976 * k + 25265 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25265) = 157464 * k + 37898 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 37898) = 78732 * k + 18949 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 18949) = 118098 * k + 28424 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 28424) = 59049 * k + 14212 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15771) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15771)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15839_mod_65536 {n : ℕ} (hn : n % 65536 = 15839) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15839 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15839) = 98304 * k + 23759 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23759) = 147456 * k + 35639 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35639) = 221184 * k + 53459 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 53459) = 331776 * k + 80189 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 80189) = 497664 * k + 120284 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 120284) = 248832 * k + 60142 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 60142) = 124416 * k + 30071 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 30071) = 186624 * k + 45107 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 45107) = 279936 * k + 67661 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 67661) = 419904 * k + 101492 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 101492) = 209952 * k + 50746 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 50746) = 104976 * k + 25373 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25373) = 157464 * k + 38060 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38060) = 78732 * k + 19030 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19030) = 39366 * k + 9515 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9515) = 59049 * k + 14273 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15839) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15839)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15855_mod_65536 {n : ℕ} (hn : n % 65536 = 15855) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15855 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15855) = 98304 * k + 23783 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23783) = 147456 * k + 35675 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35675) = 221184 * k + 53513 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 53513) = 331776 * k + 80270 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 80270) = 165888 * k + 40135 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 40135) = 248832 * k + 60203 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 60203) = 373248 * k + 90305 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 90305) = 559872 * k + 135458 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 135458) = 279936 * k + 67729 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 67729) = 419904 * k + 101594 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 101594) = 209952 * k + 50797 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 50797) = 314928 * k + 76196 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 76196) = 157464 * k + 38098 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38098) = 78732 * k + 19049 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19049) = 118098 * k + 28574 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 28574) = 59049 * k + 14287 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15855) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15855)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_15919_mod_65536 {n : ℕ} (hn : n % 65536 = 15919) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 15919 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 15919) = 98304 * k + 23879 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 23879) = 147456 * k + 35819 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 35819) = 221184 * k + 53729 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 53729) = 331776 * k + 80594 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 80594) = 165888 * k + 40297 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 40297) = 248832 * k + 60446 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 60446) = 124416 * k + 30223 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 30223) = 186624 * k + 45335 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 45335) = 279936 * k + 68003 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 68003) = 419904 * k + 102005 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 102005) = 629856 * k + 153008 := by unfold T; split <;> omega
  have h12 : T (629856 * k + 153008) = 314928 * k + 76504 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 76504) = 157464 * k + 38252 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38252) = 78732 * k + 19126 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19126) = 39366 * k + 9563 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9563) = 59049 * k + 14345 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 15919) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 15919)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16027_mod_65536 {n : ℕ} (hn : n % 65536 = 16027) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16027 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16027) = 98304 * k + 24041 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24041) = 147456 * k + 36062 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36062) = 73728 * k + 18031 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 18031) = 110592 * k + 27047 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 27047) = 165888 * k + 40571 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 40571) = 248832 * k + 60857 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 60857) = 373248 * k + 91286 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 91286) = 186624 * k + 45643 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 45643) = 279936 * k + 68465 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 68465) = 419904 * k + 102698 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 102698) = 209952 * k + 51349 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 51349) = 314928 * k + 77024 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 77024) = 157464 * k + 38512 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38512) = 78732 * k + 19256 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19256) = 39366 * k + 9628 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9628) = 19683 * k + 4814 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16027) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16027)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16123_mod_65536 {n : ℕ} (hn : n % 65536 = 16123) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16123 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16123) = 98304 * k + 24185 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24185) = 147456 * k + 36278 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36278) = 73728 * k + 18139 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 18139) = 110592 * k + 27209 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 27209) = 165888 * k + 40814 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 40814) = 82944 * k + 20407 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 20407) = 124416 * k + 30611 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 30611) = 186624 * k + 45917 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 45917) = 279936 * k + 68876 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 68876) = 139968 * k + 34438 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 34438) = 69984 * k + 17219 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 17219) = 104976 * k + 25829 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25829) = 157464 * k + 38744 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38744) = 78732 * k + 19372 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19372) = 39366 * k + 9686 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9686) = 19683 * k + 4843 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16123) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16123)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16191_mod_65536 {n : ℕ} (hn : n % 65536 = 16191) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16191 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16191) = 98304 * k + 24287 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24287) = 147456 * k + 36431 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36431) = 221184 * k + 54647 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 54647) = 331776 * k + 81971 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 81971) = 497664 * k + 122957 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 122957) = 746496 * k + 184436 := by unfold T; split <;> omega
  have h7 : T (746496 * k + 184436) = 373248 * k + 92218 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 92218) = 186624 * k + 46109 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 46109) = 279936 * k + 69164 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 69164) = 139968 * k + 34582 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 34582) = 69984 * k + 17291 := by unfold T; split <;> omega
  have h12 : T (69984 * k + 17291) = 104976 * k + 25937 := by unfold T; split <;> omega
  have h13 : T (104976 * k + 25937) = 157464 * k + 38906 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 38906) = 78732 * k + 19453 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19453) = 118098 * k + 29180 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29180) = 59049 * k + 14590 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16191) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16191)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16287_mod_65536 {n : ℕ} (hn : n % 65536 = 16287) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16287 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16287) = 98304 * k + 24431 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24431) = 147456 * k + 36647 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36647) = 221184 * k + 54971 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 54971) = 331776 * k + 82457 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 82457) = 497664 * k + 123686 := by unfold T; split <;> omega
  have h6 : T (497664 * k + 123686) = 248832 * k + 61843 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 61843) = 373248 * k + 92765 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 92765) = 559872 * k + 139148 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 139148) = 279936 * k + 69574 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 69574) = 139968 * k + 34787 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 34787) = 209952 * k + 52181 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 52181) = 314928 * k + 78272 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 78272) = 157464 * k + 39136 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 39136) = 78732 * k + 19568 := by unfold T; split <;> omega
  have h15 : T (78732 * k + 19568) = 39366 * k + 9784 := by unfold T; split <;> omega
  have h16 : T (39366 * k + 9784) = 19683 * k + 4892 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16287) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16287)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16411_mod_65536 {n : ℕ} (hn : n % 65536 = 16411) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16411 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16411) = 98304 * k + 24617 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24617) = 147456 * k + 36926 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36926) = 73728 * k + 18463 := by unfold T; split <;> omega
  have h4 : T (73728 * k + 18463) = 110592 * k + 27695 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 27695) = 165888 * k + 41543 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 41543) = 248832 * k + 62315 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 62315) = 373248 * k + 93473 := by unfold T; split <;> omega
  have h8 : T (373248 * k + 93473) = 559872 * k + 140210 := by unfold T; split <;> omega
  have h9 : T (559872 * k + 140210) = 279936 * k + 70105 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 70105) = 419904 * k + 105158 := by unfold T; split <;> omega
  have h11 : T (419904 * k + 105158) = 209952 * k + 52579 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 52579) = 314928 * k + 78869 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 78869) = 472392 * k + 118304 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 118304) = 236196 * k + 59152 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 59152) = 118098 * k + 29576 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29576) = 59049 * k + 14788 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16411) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16411)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16431_mod_65536 {n : ℕ} (hn : n % 65536 = 16431) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16431 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16431) = 98304 * k + 24647 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24647) = 147456 * k + 36971 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 36971) = 221184 * k + 55457 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 55457) = 331776 * k + 83186 := by unfold T; split <;> omega
  have h5 : T (331776 * k + 83186) = 165888 * k + 41593 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 41593) = 248832 * k + 62390 := by unfold T; split <;> omega
  have h7 : T (248832 * k + 62390) = 124416 * k + 31195 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 31195) = 186624 * k + 46793 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 46793) = 279936 * k + 70190 := by unfold T; split <;> omega
  have h10 : T (279936 * k + 70190) = 139968 * k + 35095 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 35095) = 209952 * k + 52643 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 52643) = 314928 * k + 78965 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 78965) = 472392 * k + 118448 := by unfold T; split <;> omega
  have h14 : T (472392 * k + 118448) = 236196 * k + 59224 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 59224) = 118098 * k + 29612 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29612) = 59049 * k + 14806 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16431) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16431)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

theorem descent_16455_mod_65536 {n : ℕ} (hn : n % 65536 = 16455) : T_iter n 16 < n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 65536 * k + 16455 := ⟨n / 65536, by omega⟩
  have h1 : T (65536 * k + 16455) = 98304 * k + 24683 := by unfold T; split <;> omega
  have h2 : T (98304 * k + 24683) = 147456 * k + 37025 := by unfold T; split <;> omega
  have h3 : T (147456 * k + 37025) = 221184 * k + 55538 := by unfold T; split <;> omega
  have h4 : T (221184 * k + 55538) = 110592 * k + 27769 := by unfold T; split <;> omega
  have h5 : T (110592 * k + 27769) = 165888 * k + 41654 := by unfold T; split <;> omega
  have h6 : T (165888 * k + 41654) = 82944 * k + 20827 := by unfold T; split <;> omega
  have h7 : T (82944 * k + 20827) = 124416 * k + 31241 := by unfold T; split <;> omega
  have h8 : T (124416 * k + 31241) = 186624 * k + 46862 := by unfold T; split <;> omega
  have h9 : T (186624 * k + 46862) = 93312 * k + 23431 := by unfold T; split <;> omega
  have h10 : T (93312 * k + 23431) = 139968 * k + 35147 := by unfold T; split <;> omega
  have h11 : T (139968 * k + 35147) = 209952 * k + 52721 := by unfold T; split <;> omega
  have h12 : T (209952 * k + 52721) = 314928 * k + 79082 := by unfold T; split <;> omega
  have h13 : T (314928 * k + 79082) = 157464 * k + 39541 := by unfold T; split <;> omega
  have h14 : T (157464 * k + 39541) = 236196 * k + 59312 := by unfold T; split <;> omega
  have h15 : T (236196 * k + 59312) = 118098 * k + 29656 := by unfold T; split <;> omega
  have h16 : T (118098 * k + 29656) = 59049 * k + 14828 := by unfold T; split <;> omega
  have e : T_iter (65536 * k + 16455) 16 =
      T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (65536 * k + 16455)))))))))))))))) := rfl
  rw [e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]; omega

end CollatzResidueDescent65536
