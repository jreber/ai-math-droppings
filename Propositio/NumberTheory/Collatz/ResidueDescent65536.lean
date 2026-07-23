import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.ResidueDescent16384
import Propositio.NumberTheory.Collatz.ResidueDescent65536A
import Propositio.NumberTheory.Collatz.ResidueDescent65536B
import Propositio.NumberTheory.Collatz.ResidueDescent65536C
import Propositio.NumberTheory.Collatz.ResidueDescent65536D
import Propositio.NumberTheory.Collatz.ResidueDescent65536E
import Propositio.NumberTheory.Collatz.ResidueDescent65536F
import Propositio.NumberTheory.Collatz.ResidueDescent65536G
import Propositio.NumberTheory.Collatz.ResidueDescent65536H
import Mathlib.Tactic

set_option maxHeartbeats 1600000

namespace CollatzResidueDescent65536

open TerrasDensity

/-!
`descent_within_sixteen_<i>`: bounded-descent aggregators over the good residues mod 2^16
(and inherited lower moduli, delegated to `CollatzResidueDescent1024.descent_within_ten`).
The full residue set is partitioned into 9 sub-aggregators to keep each disjunction shallow
(a single ~1200-deep `Or` overflows the elaborator stack; cf. the chained pattern in
`CollatzResidueDescent16384.descent_within_fourteen`).  Per-residue lemmas live in the
imported `…65536A`–`…65536H` modules.
-/

theorem descent_within_sixteen_1 {n : ℕ}
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
           ∨ n % 16384 = 14939) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_191_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_303_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_543_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_623_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1135_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1215_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1247_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1327_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1567_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_1727_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_2079_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_2271_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_2331_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_2431_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_2663_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_3067_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_3135_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_3455_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_3687_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_3967_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4079_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4091_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4159_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4199_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4251_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_4955_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5023_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5103_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5275_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5607_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5615_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5787_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5959_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_5979_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_6047_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_6559_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_6631_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_6983_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_7023_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_7375_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_7495_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_7847_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_7967_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8047_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8399_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8447_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8731_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8871_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8911_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_8991_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_9263_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_9383_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_9755_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_10175_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_10207_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_10267_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_10287_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_10799_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_11231_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_11675_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_11743_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_12027_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_12095_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_12415_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_12647_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_12699_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13051_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13119_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13383_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13563_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13631_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_13915_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_14063_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_14407_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_14567_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_14799_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_14939_mod_16384 (by assumption)⟩

theorem descent_within_sixteen_2 {n : ℕ}
    (h : n % 16384 = 15007
           ∨ n % 16384 = 15271
           ∨ n % 16384 = 15451
           ∨ n % 16384 = 15591
           ∨ n % 16384 = 15823
           ∨ n % 16384 = 15983
           ∨ n % 16384 = 16103
           ∨ n % 16384 = 16295
           ∨ n % 65536 = 127
           ∨ n % 65536 = 255
           ∨ n % 65536 = 359
           ∨ n % 65536 = 411
           ∨ n % 65536 = 415
           ∨ n % 65536 = 479
           ∨ n % 65536 = 539
           ∨ n % 65536 = 559
           ∨ n % 65536 = 603
           ∨ n % 65536 = 679
           ∨ n % 65536 = 719
           ∨ n % 65536 = 767
           ∨ n % 65536 = 799
           ∨ n % 65536 = 831
           ∨ n % 65536 = 839
           ∨ n % 65536 = 859
           ∨ n % 65536 = 1071
           ∨ n % 65536 = 1095
           ∨ n % 65536 = 1151
           ∨ n % 65536 = 1179
           ∨ n % 65536 = 1183
           ∨ n % 65536 = 1191
           ∨ n % 65536 = 1275
           ∨ n % 65536 = 1351
           ∨ n % 65536 = 1519
           ∨ n % 65536 = 1535
           ∨ n % 65536 = 1563
           ∨ n % 65536 = 1627
           ∨ n % 65536 = 1775
           ∨ n % 65536 = 1903
           ∨ n % 65536 = 1983
           ∨ n % 65536 = 2119
           ∨ n % 65536 = 2279
           ∨ n % 65536 = 2299
           ∨ n % 65536 = 2303
           ∨ n % 65536 = 2367
           ∨ n % 65536 = 2407
           ∨ n % 65536 = 2495
           ∨ n % 65536 = 2607
           ∨ n % 65536 = 2671
           ∨ n % 65536 = 2687
           ∨ n % 65536 = 2719
           ∨ n % 65536 = 2727
           ∨ n % 65536 = 2767
           ∨ n % 65536 = 2791
           ∨ n % 65536 = 2799
           ∨ n % 65536 = 2847
           ∨ n % 65536 = 2887
           ∨ n % 65536 = 2927
           ∨ n % 65536 = 2983
           ∨ n % 65536 = 3039
           ∨ n % 65536 = 3103
           ∨ n % 65536 = 3163
           ∨ n % 65536 = 3239
           ∨ n % 65536 = 3303
           ∨ n % 65536 = 3487
           ∨ n % 65536 = 3535
           ∨ n % 65536 = 3551
           ∨ n % 65536 = 3611
           ∨ n % 65536 = 3695
           ∨ n % 65536 = 3743
           ∨ n % 65536 = 3815
           ∨ n % 65536 = 3835
           ∨ n % 65536 = 4007
           ∨ n % 65536 = 4031
           ∨ n % 65536 = 4187
           ∨ n % 65536 = 4287
           ∨ n % 65536 = 4319
           ∨ n % 65536 = 4335
           ∨ n % 65536 = 4379
           ∨ n % 65536 = 4455
           ∨ n % 65536 = 4507
           ∨ n % 65536 = 4635
           ∨ n % 65536 = 4655
           ∨ n % 65536 = 4775
           ∨ n % 65536 = 4799
           ∨ n % 65536 = 4815
           ∨ n % 65536 = 4859
           ∨ n % 65536 = 4895
           ∨ n % 65536 = 4927
           ∨ n % 65536 = 4991
           ∨ n % 65536 = 5087
           ∨ n % 65536 = 5231
           ∨ n % 65536 = 5311
           ∨ n % 65536 = 5343
           ∨ n % 65536 = 5375
           ∨ n % 65536 = 5423
           ∨ n % 65536 = 5439
           ∨ n % 65536 = 5583
           ∨ n % 65536 = 5599
           ∨ n % 65536 = 5631
           ∨ n % 65536 = 5663
           ∨ n % 65536 = 5723
           ∨ n % 65536 = 5823
           ∨ n % 65536 = 5863
           ∨ n % 65536 = 6175
           ∨ n % 65536 = 6207
           ∨ n % 65536 = 6215
           ∨ n % 65536 = 6247
           ∨ n % 65536 = 6255
           ∨ n % 65536 = 6375
           ∨ n % 65536 = 6503
           ∨ n % 65536 = 6555
           ∨ n % 65536 = 6607
           ∨ n % 65536 = 6639
           ∨ n % 65536 = 6703
           ∨ n % 65536 = 6747
           ∨ n % 65536 = 6759
           ∨ n % 65536 = 6783
           ∨ n % 65536 = 6815
           ∨ n % 65536 = 6907
           ∨ n % 65536 = 6975
           ∨ n % 65536 = 7015
           ∨ n % 65536 = 7103
           ∨ n % 65536 = 7163
           ∨ n % 65536 = 7199
           ∨ n % 65536 = 7231
           ∨ n % 65536 = 7451
           ∨ n % 65536 = 7471
           ∨ n % 65536 = 7487
           ∨ n % 65536 = 7551
           ∨ n % 65536 = 7631
           ∨ n % 65536 = 7711
           ∨ n % 65536 = 7783
           ∨ n % 65536 = 7791
           ∨ n % 65536 = 7835
           ∨ n % 65536 = 7871
           ∨ n % 65536 = 7911) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15007_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15271_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15451_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15591_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15823_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_15983_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_16103_mod_16384 (by assumption)⟩
  · exact ⟨14, by norm_num, by norm_num,
        CollatzResidueDescent16384.descent_16295_mod_16384 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_411_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_539_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_603_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_719_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_859_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1151_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1179_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1275_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1563_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1627_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1903_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_1983_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2279_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2299_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2719_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2791_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_2983_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3163_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3611_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3695_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_3835_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4031_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4187_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4379_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4507_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4635_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4859_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4895_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_4991_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5583_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5723_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_5863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6175_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6555_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6747_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6783_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6907_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_6975_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7163_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7451_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7783_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7791_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7835_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7871_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_7911_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_3 {n : ℕ}
    (h : n % 65536 = 7931
           ∨ n % 65536 = 8063
           ∨ n % 65536 = 8095
           ∨ n % 65536 = 8103
           ∨ n % 65536 = 8187
           ∨ n % 65536 = 8263
           ∨ n % 65536 = 8347
           ∨ n % 65536 = 8383
           ∨ n % 65536 = 8431
           ∨ n % 65536 = 8495
           ∨ n % 65536 = 8551
           ∨ n % 65536 = 8671
           ∨ n % 65536 = 8735
           ∨ n % 65536 = 8795
           ∨ n % 65536 = 8815
           ∨ n % 65536 = 8863
           ∨ n % 65536 = 9051
           ∨ n % 65536 = 9087
           ∨ n % 65536 = 9119
           ∨ n % 65536 = 9199
           ∨ n % 65536 = 9319
           ∨ n % 65536 = 9371
           ∨ n % 65536 = 9375
           ∨ n % 65536 = 9439
           ∨ n % 65536 = 9519
           ∨ n % 65536 = 9543
           ∨ n % 65536 = 9599
           ∨ n % 65536 = 9679
           ∨ n % 65536 = 9711
           ∨ n % 65536 = 9759
           ∨ n % 65536 = 9819
           ∨ n % 65536 = 9919
           ∨ n % 65536 = 9935
           ∨ n % 65536 = 9959
           ∨ n % 65536 = 10055
           ∨ n % 65536 = 10075
           ∨ n % 65536 = 10151
           ∨ n % 65536 = 10271
           ∨ n % 65536 = 10463
           ∨ n % 65536 = 10523
           ∨ n % 65536 = 10559
           ∨ n % 65536 = 10623
           ∨ n % 65536 = 10655
           ∨ n % 65536 = 10727
           ∨ n % 65536 = 10735
           ∨ n % 65536 = 10863
           ∨ n % 65536 = 10907
           ∨ n % 65536 = 11035
           ∨ n % 65536 = 11079
           ∨ n % 65536 = 11119
           ∨ n % 65536 = 11247
           ∨ n % 65536 = 11259
           ∨ n % 65536 = 11327
           ∨ n % 65536 = 11431
           ∨ n % 65536 = 11567
           ∨ n % 65536 = 11647
           ∨ n % 65536 = 11679
           ∨ n % 65536 = 11727
           ∨ n % 65536 = 11807
           ∨ n % 65536 = 11823
           ∨ n % 65536 = 11879
           ∨ n % 65536 = 11887
           ∨ n % 65536 = 11943
           ∨ n % 65536 = 11967
           ∨ n % 65536 = 12007
           ∨ n % 65536 = 12063
           ∨ n % 65536 = 12143
           ∨ n % 65536 = 12159
           ∨ n % 65536 = 12271
           ∨ n % 65536 = 12319
           ∨ n % 65536 = 12351
           ∨ n % 65536 = 12391
           ∨ n % 65536 = 12495
           ∨ n % 65536 = 12511
           ∨ n % 65536 = 12543
           ∨ n % 65536 = 12571
           ∨ n % 65536 = 12615
           ∨ n % 65536 = 12775
           ∨ n % 65536 = 12799
           ∨ n % 65536 = 12827
           ∨ n % 65536 = 12967
           ∨ n % 65536 = 13007
           ∨ n % 65536 = 13087
           ∨ n % 65536 = 13147
           ∨ n % 65536 = 13215
           ∨ n % 65536 = 13279
           ∨ n % 65536 = 13295
           ∨ n % 65536 = 13339
           ∨ n % 65536 = 13467
           ∨ n % 65536 = 13535
           ∨ n % 65536 = 13567
           ∨ n % 65536 = 13615
           ∨ n % 65536 = 13671
           ∨ n % 65536 = 13695
           ∨ n % 65536 = 13799
           ∨ n % 65536 = 13807
           ∨ n % 65536 = 13851
           ∨ n % 65536 = 13855
           ∨ n % 65536 = 13927
           ∨ n % 65536 = 13951
           ∨ n % 65536 = 13979
           ∨ n % 65536 = 14015
           ∨ n % 65536 = 14031
           ∨ n % 65536 = 14207
           ∨ n % 65536 = 14239
           ∨ n % 65536 = 14271
           ∨ n % 65536 = 14303
           ∨ n % 65536 = 14363
           ∨ n % 65536 = 14383
           ∨ n % 65536 = 14399
           ∨ n % 65536 = 14439
           ∨ n % 65536 = 14503
           ∨ n % 65536 = 14543
           ∨ n % 65536 = 14747
           ∨ n % 65536 = 14823
           ∨ n % 65536 = 14895
           ∨ n % 65536 = 15103
           ∨ n % 65536 = 15167
           ∨ n % 65536 = 15175
           ∨ n % 65536 = 15207
           ∨ n % 65536 = 15215
           ∨ n % 65536 = 15295
           ∨ n % 65536 = 15343
           ∨ n % 65536 = 15423
           ∨ n % 65536 = 15487
           ∨ n % 65536 = 15515
           ∨ n % 65536 = 15567
           ∨ n % 65536 = 15599
           ∨ n % 65536 = 15643
           ∨ n % 65536 = 15687
           ∨ n % 65536 = 15743
           ∨ n % 65536 = 15771
           ∨ n % 65536 = 15839
           ∨ n % 65536 = 15855
           ∨ n % 65536 = 15919
           ∨ n % 65536 = 16027) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_7931_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8187_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8263_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8347_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8383_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8431_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8795_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_8863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9051_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9371_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9819_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9935_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_9959_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10075_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10151_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10463_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10523_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_10907_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11035_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11259_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11431_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11647_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11879_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11943_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_11967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12571_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12827_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_12967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13147_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13279_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13339_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13467_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13695_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13851_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13951_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_13979_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14031_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14363_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14383_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14747_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_14895_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15175_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15515_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15643_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15771_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_15919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16027_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_4 {n : ℕ}
    (h : n % 65536 = 16123
           ∨ n % 65536 = 16191
           ∨ n % 65536 = 16287
           ∨ n % 65536 = 16411
           ∨ n % 65536 = 16431
           ∨ n % 65536 = 16455
           ∨ n % 65536 = 16511
           ∨ n % 65536 = 16591
           ∨ n % 65536 = 16635
           ∨ n % 65536 = 16743
           ∨ n % 65536 = 16831
           ∨ n % 65536 = 16863
           ∨ n % 65536 = 16871
           ∨ n % 65536 = 16923
           ∨ n % 65536 = 17055
           ∨ n % 65536 = 17063
           ∨ n % 65536 = 17103
           ∨ n % 65536 = 17127
           ∨ n % 65536 = 17135
           ∨ n % 65536 = 17147
           ∨ n % 65536 = 17183
           ∨ n % 65536 = 17223
           ∨ n % 65536 = 17311
           ∨ n % 65536 = 17391
           ∨ n % 65536 = 17455
           ∨ n % 65536 = 17479
           ∨ n % 65536 = 17511
           ∨ n % 65536 = 17575
           ∨ n % 65536 = 17659
           ∨ n % 65536 = 17727
           ∨ n % 65536 = 17735
           ∨ n % 65536 = 17767
           ∨ n % 65536 = 18011
           ∨ n % 65536 = 18159
           ∨ n % 65536 = 18343
           ∨ n % 65536 = 18399
           ∨ n % 65536 = 18459
           ∨ n % 65536 = 18479
           ∨ n % 65536 = 18523
           ∨ n % 65536 = 18559
           ∨ n % 65536 = 18639
           ∨ n % 65536 = 18751
           ∨ n % 65536 = 18895
           ∨ n % 65536 = 18919
           ∨ n % 65536 = 18991
           ∨ n % 65536 = 19035
           ∨ n % 65536 = 19099
           ∨ n % 65536 = 19111
           ∨ n % 65536 = 19135
           ∨ n % 65536 = 19151
           ∨ n % 65536 = 19199
           ∨ n % 65536 = 19231
           ∨ n % 65536 = 19367
           ∨ n % 65536 = 19423
           ∨ n % 65536 = 19547
           ∨ n % 65536 = 19623
           ∨ n % 65536 = 19687
           ∨ n % 65536 = 19707
           ∨ n % 65536 = 19867
           ∨ n % 65536 = 19919
           ∨ n % 65536 = 20079
           ∨ n % 65536 = 20127
           ∨ n % 65536 = 20199
           ∨ n % 65536 = 20207
           ∨ n % 65536 = 20219
           ∨ n % 65536 = 20287
           ∨ n % 65536 = 20507
           ∨ n % 65536 = 20511
           ∨ n % 65536 = 20527
           ∨ n % 65536 = 20591
           ∨ n % 65536 = 20607
           ∨ n % 65536 = 20687
           ∨ n % 65536 = 20783
           ∨ n % 65536 = 20807
           ∨ n % 65536 = 20839
           ∨ n % 65536 = 20891
           ∨ n % 65536 = 20927
           ∨ n % 65536 = 21023
           ∨ n % 65536 = 21039
           ∨ n % 65536 = 21103
           ∨ n % 65536 = 21223
           ∨ n % 65536 = 21311
           ∨ n % 65536 = 21471
           ∨ n % 65536 = 21575
           ∨ n % 65536 = 21595
           ∨ n % 65536 = 21615
           ∨ n % 65536 = 21695
           ∨ n % 65536 = 21727
           ∨ n % 65536 = 21735
           ∨ n % 65536 = 21755
           ∨ n % 65536 = 21807
           ∨ n % 65536 = 22015
           ∨ n % 65536 = 22047
           ∨ n % 65536 = 22107
           ∨ n % 65536 = 22119
           ∨ n % 65536 = 22207
           ∨ n % 65536 = 22255
           ∨ n % 65536 = 22399
           ∨ n % 65536 = 22495
           ∨ n % 65536 = 22555
           ∨ n % 65536 = 22575
           ∨ n % 65536 = 22599
           ∨ n % 65536 = 22655
           ∨ n % 65536 = 22695
           ∨ n % 65536 = 22751
           ∨ n % 65536 = 22759
           ∨ n % 65536 = 22811
           ∨ n % 65536 = 22887
           ∨ n % 65536 = 22911
           ∨ n % 65536 = 22939
           ∨ n % 65536 = 23143
           ∨ n % 65536 = 23167
           ∨ n % 65536 = 23199
           ∨ n % 65536 = 23231
           ∨ n % 65536 = 23359
           ∨ n % 65536 = 23399
           ∨ n % 65536 = 23463
           ∨ n % 65536 = 23583
           ∨ n % 65536 = 23615
           ∨ n % 65536 = 23643
           ∨ n % 65536 = 23663
           ∨ n % 65536 = 23707
           ∨ n % 65536 = 23711
           ∨ n % 65536 = 23743
           ∨ n % 65536 = 23783
           ∨ n % 65536 = 23803
           ∨ n % 65536 = 23835
           ∨ n % 65536 = 23935
           ∨ n % 65536 = 23963
           ∨ n % 65536 = 24015
           ∨ n % 65536 = 24047
           ∨ n % 65536 = 24175
           ∨ n % 65536 = 24295
           ∨ n % 65536 = 24303
           ∨ n % 65536 = 24383
           ∨ n % 65536 = 24487) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_16123_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16411_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16431_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16635_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16871_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_16923_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17147_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17659_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_17767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18011_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18459_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18523_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18751_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18895_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_18991_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19035_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19099_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19111_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19151_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19547_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19707_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19867_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_19919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20219_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20507_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20783_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20891_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_20927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21595_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21695_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21755_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_21807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22047_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22107_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22555_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22695_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22751_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22811_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22911_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_22939_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23463_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23583_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23643_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23707_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23783_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23803_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23835_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23935_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_23963_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24047_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24175_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24383_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24487_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_5 {n : ℕ}
    (h : n % 65536 = 24559
           ∨ n % 65536 = 24571
           ∨ n % 65536 = 24639
           ∨ n % 65536 = 24647
           ∨ n % 65536 = 24679
           ∨ n % 65536 = 24703
           ∨ n % 65536 = 24731
           ∨ n % 65536 = 24767
           ∨ n % 65536 = 24815
           ∨ n % 65536 = 25247
           ∨ n % 65536 = 25371
           ∨ n % 65536 = 25415
           ∨ n % 65536 = 25471
           ∨ n % 65536 = 25503
           ∨ n % 65536 = 25583
           ∨ n % 65536 = 25599
           ∨ n % 65536 = 25671
           ∨ n % 65536 = 25691
           ∨ n % 65536 = 25703
           ∨ n % 65536 = 25711
           ∨ n % 65536 = 25791
           ∨ n % 65536 = 25823
           ∨ n % 65536 = 25831
           ∨ n % 65536 = 25851
           ∨ n % 65536 = 25903
           ∨ n % 65536 = 26015
           ∨ n % 65536 = 26063
           ∨ n % 65536 = 26087
           ∨ n % 65536 = 26143
           ∨ n % 65536 = 26267
           ∨ n % 65536 = 26303
           ∨ n % 65536 = 26343
           ∨ n % 65536 = 26351
           ∨ n % 65536 = 26367
           ∨ n % 65536 = 26439
           ∨ n % 65536 = 26459
           ∨ n % 65536 = 26527
           ∨ n % 65536 = 26535
           ∨ n % 65536 = 26619
           ∨ n % 65536 = 26655
           ∨ n % 65536 = 27039
           ∨ n % 65536 = 27111
           ∨ n % 65536 = 27119
           ∨ n % 65536 = 27239
           ∨ n % 65536 = 27291
           ∨ n % 65536 = 27303
           ∨ n % 65536 = 27343
           ∨ n % 65536 = 27423
           ∨ n % 65536 = 27559
           ∨ n % 65536 = 27643
           ∨ n % 65536 = 27675
           ∨ n % 65536 = 27711
           ∨ n % 65536 = 27739
           ∨ n % 65536 = 27759
           ∨ n % 65536 = 27839
           ∨ n % 65536 = 27855
           ∨ n % 65536 = 27879
           ∨ n % 65536 = 27903
           ∨ n % 65536 = 27951
           ∨ n % 65536 = 27975
           ∨ n % 65536 = 28031
           ∨ n % 65536 = 28095
           ∨ n % 65536 = 28191
           ∨ n % 65536 = 28263
           ∨ n % 65536 = 28319
           ∨ n % 65536 = 28327
           ∨ n % 65536 = 28351
           ∨ n % 65536 = 28447
           ∨ n % 65536 = 28507
           ∨ n % 65536 = 28527
           ∨ n % 65536 = 28543
           ∨ n % 65536 = 28667
           ∨ n % 65536 = 28703
           ∨ n % 65536 = 28827
           ∨ n % 65536 = 28879
           ∨ n % 65536 = 28927
           ∨ n % 65536 = 28999
           ∨ n % 65536 = 29087
           ∨ n % 65536 = 29231
           ∨ n % 65536 = 29467
           ∨ n % 65536 = 29531
           ∨ n % 65536 = 29599
           ∨ n % 65536 = 29631
           ∨ n % 65536 = 29679
           ∨ n % 65536 = 29743
           ∨ n % 65536 = 29807
           ∨ n % 65536 = 29823
           ∨ n % 65536 = 29851
           ∨ n % 65536 = 29863
           ∨ n % 65536 = 29887
           ∨ n % 65536 = 30079
           ∨ n % 65536 = 30191
           ∨ n % 65536 = 30207
           ∨ n % 65536 = 30235
           ∨ n % 65536 = 30311
           ∨ n % 65536 = 30415
           ∨ n % 65536 = 30535
           ∨ n % 65536 = 30555
           ∨ n % 65536 = 30575
           ∨ n % 65536 = 30591
           ∨ n % 65536 = 30655
           ∨ n % 65536 = 30687
           ∨ n % 65536 = 30715
           ∨ n % 65536 = 30747
           ∨ n % 65536 = 30767
           ∨ n % 65536 = 30887
           ∨ n % 65536 = 30971
           ∨ n % 65536 = 30975
           ∨ n % 65536 = 31079
           ∨ n % 65536 = 31135
           ∨ n % 65536 = 31199
           ∨ n % 65536 = 31207
           ∨ n % 65536 = 31335
           ∨ n % 65536 = 31359
           ∨ n % 65536 = 31471
           ∨ n % 65536 = 31559
           ∨ n % 65536 = 31599
           ∨ n % 65536 = 31711
           ∨ n % 65536 = 31727
           ∨ n % 65536 = 31771
           ∨ n % 65536 = 31775
           ∨ n % 65536 = 31899
           ∨ n % 65536 = 32155
           ∨ n % 65536 = 32223
           ∨ n % 65536 = 32239
           ∨ n % 65536 = 32283
           ∨ n % 65536 = 32303
           ∨ n % 65536 = 32423
           ∨ n % 65536 = 32543
           ∨ n % 65536 = 32575
           ∨ n % 65536 = 32603
           ∨ n % 65536 = 32623
           ∨ n % 65536 = 32703
           ∨ n % 65536 = 32763
           ∨ n % 65536 = 32859
           ∨ n % 65536 = 32895) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_24559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24571_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24647_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24731_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_24815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25371_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25583_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25691_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25791_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25851_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_25903_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26267_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26459_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26619_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_26655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27111_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27291_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27643_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27675_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27739_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27879_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27903_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27951_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_27975_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28031_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28263_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28507_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28667_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28827_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28879_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_28999_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29467_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29531_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29851_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_29887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30235_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30555_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30715_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30747_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30971_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_30975_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31771_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_31899_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32155_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32283_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32603_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32763_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32859_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32895_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_6 {n : ℕ}
    (h : n % 65536 = 32923
           ∨ n % 65536 = 32975
           ∨ n % 65536 = 33007
           ∨ n % 65536 = 33023
           ∨ n % 65536 = 33087
           ∨ n % 65536 = 33179
           ∨ n % 65536 = 33183
           ∨ n % 65536 = 33255
           ∨ n % 65536 = 33307
           ∨ n % 65536 = 33447
           ∨ n % 65536 = 33487
           ∨ n % 65536 = 33531
           ∨ n % 65536 = 33567
           ∨ n % 65536 = 33599
           ∨ n % 65536 = 33607
           ∨ n % 65536 = 33663
           ∨ n % 65536 = 33863
           ∨ n % 65536 = 33919
           ∨ n % 65536 = 34043
           ∨ n % 65536 = 34111
           ∨ n % 65536 = 34151
           ∨ n % 65536 = 34255
           ∨ n % 65536 = 34271
           ∨ n % 65536 = 34331
           ∨ n % 65536 = 34535
           ∨ n % 65536 = 34543
           ∨ n % 65536 = 34631
           ∨ n % 65536 = 34651
           ∨ n % 65536 = 34671
           ∨ n % 65536 = 34751
           ∨ n % 65536 = 34783
           ∨ n % 65536 = 34843
           ∨ n % 65536 = 34863
           ∨ n % 65536 = 34887
           ∨ n % 65536 = 34927
           ∨ n % 65536 = 35023
           ∨ n % 65536 = 35047
           ∨ n % 65536 = 35067
           ∨ n % 65536 = 35071
           ∨ n % 65536 = 35231
           ∨ n % 65536 = 35279
           ∨ n % 65536 = 35311
           ∨ n % 65536 = 35375
           ∨ n % 65536 = 35419
           ∨ n % 65536 = 35487
           ∨ n % 65536 = 35495
           ∨ n % 65536 = 35535
           ∨ n % 65536 = 35567
           ∨ n % 65536 = 35579
           ∨ n % 65536 = 35583
           ∨ n % 65536 = 35615
           ∨ n % 65536 = 35751
           ∨ n % 65536 = 35931
           ∨ n % 65536 = 36071
           ∨ n % 65536 = 36143
           ∨ n % 65536 = 36159
           ∨ n % 65536 = 36251
           ∨ n % 65536 = 36319
           ∨ n % 65536 = 36379
           ∨ n % 65536 = 36383
           ∨ n % 65536 = 36511
           ∨ n % 65536 = 36519
           ∨ n % 65536 = 36543
           ∨ n % 65536 = 36603
           ∨ n % 65536 = 36635
           ∨ n % 65536 = 36639
           ∨ n % 65536 = 36671
           ∨ n % 65536 = 36719
           ∨ n % 65536 = 36775
           ∨ n % 65536 = 36799
           ∨ n % 65536 = 36891
           ∨ n % 65536 = 36911
           ∨ n % 65536 = 36955
           ∨ n % 65536 = 36991
           ∨ n % 65536 = 37055
           ∨ n % 65536 = 37119
           ∨ n % 65536 = 37167
           ∨ n % 65536 = 37223
           ∨ n % 65536 = 37311
           ∨ n % 65536 = 37407
           ∨ n % 65536 = 37423
           ∨ n % 65536 = 37467
           ∨ n % 65536 = 37487
           ∨ n % 65536 = 37607
           ∨ n % 65536 = 37627
           ∨ n % 65536 = 37735
           ∨ n % 65536 = 37959
           ∨ n % 65536 = 37999
           ∨ n % 65536 = 38047
           ∨ n % 65536 = 38079
           ∨ n % 65536 = 38139
           ∨ n % 65536 = 38171
           ∨ n % 65536 = 38207
           ∨ n % 65536 = 38271
           ∨ n % 65536 = 38367
           ∨ n % 65536 = 38399
           ∨ n % 65536 = 38427
           ∨ n % 65536 = 38491
           ∨ n % 65536 = 38607
           ∨ n % 65536 = 38639
           ∨ n % 65536 = 38847
           ∨ n % 65536 = 38943
           ∨ n % 65536 = 39023
           ∨ n % 65536 = 39039
           ∨ n % 65536 = 39135
           ∨ n % 65536 = 39195
           ∨ n % 65536 = 39271
           ∨ n % 65536 = 39295
           ∨ n % 65536 = 39375
           ∨ n % 65536 = 39515
           ∨ n % 65536 = 39527
           ∨ n % 65536 = 39535
           ∨ n % 65536 = 39551
           ∨ n % 65536 = 39615
           ∨ n % 65536 = 39675
           ∨ n % 65536 = 39847
           ∨ n % 65536 = 39919
           ∨ n % 65536 = 39931
           ∨ n % 65536 = 39967
           ∨ n % 65536 = 40027
           ∨ n % 65536 = 40039
           ∨ n % 65536 = 40167
           ∨ n % 65536 = 40187
           ∨ n % 65536 = 40255
           ∨ n % 65536 = 40351
           ∨ n % 65536 = 40399
           ∨ n % 65536 = 40415
           ∨ n % 65536 = 40495
           ∨ n % 65536 = 40551
           ∨ n % 65536 = 40559
           ∨ n % 65536 = 40679
           ∨ n % 65536 = 40687
           ∨ n % 65536 = 40831
           ∨ n % 65536 = 40943
           ∨ n % 65536 = 40955
           ∨ n % 65536 = 41023) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_32923_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_32975_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33087_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33179_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33307_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33531_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_33919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34043_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34111_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34151_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34331_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34651_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34751_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34783_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34843_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_34927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35047_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35067_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35279_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35419_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35579_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35583_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35751_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_35931_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36251_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36379_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36383_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36603_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36635_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36719_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36891_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36911_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36955_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_36991_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37467_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37627_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37959_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_37999_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38047_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38139_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38171_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38427_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38491_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_38943_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39195_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39515_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39675_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39931_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_39967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40027_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40187_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40399_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40943_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_40955_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41023_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_7 {n : ℕ}
    (h : n % 65536 = 41063
           ∨ n % 65536 = 41115
           ∨ n % 65536 = 41183
           ∨ n % 65536 = 41199
           ∨ n % 65536 = 41243
           ∨ n % 65536 = 41263
           ∨ n % 65536 = 41447
           ∨ n % 65536 = 41503
           ∨ n % 65536 = 41563
           ∨ n % 65536 = 41583
           ∨ n % 65536 = 41627
           ∨ n % 65536 = 41723
           ∨ n % 65536 = 41819
           ∨ n % 65536 = 41855
           ∨ n % 65536 = 42075
           ∨ n % 65536 = 42095
           ∨ n % 65536 = 42139
           ∨ n % 65536 = 42143
           ∨ n % 65536 = 42175
           ∨ n % 65536 = 42207
           ∨ n % 65536 = 42215
           ∨ n % 65536 = 42239
           ∨ n % 65536 = 42287
           ∨ n % 65536 = 42303
           ∨ n % 65536 = 42343
           ∨ n % 65536 = 42447
           ∨ n % 65536 = 42471
           ∨ n % 65536 = 42479
           ∨ n % 65536 = 42527
           ∨ n % 65536 = 42651
           ∨ n % 65536 = 42687
           ∨ n % 65536 = 42727
           ∨ n % 65536 = 42823
           ∨ n % 65536 = 42843
           ∨ n % 65536 = 42911
           ∨ n % 65536 = 43071
           ∨ n % 65536 = 43111
           ∨ n % 65536 = 43215
           ∨ n % 65536 = 43231
           ∨ n % 65536 = 43291
           ∨ n % 65536 = 43335
           ∨ n % 65536 = 43391
           ∨ n % 65536 = 43423
           ∨ n % 65536 = 43471
           ∨ n % 65536 = 43503
           ∨ n % 65536 = 43611
           ∨ n % 65536 = 43623
           ∨ n % 65536 = 43631
           ∨ n % 65536 = 43775
           ∨ n % 65536 = 43847
           ∨ n % 65536 = 43887
           ∨ n % 65536 = 43967
           ∨ n % 65536 = 44095
           ∨ n % 65536 = 44143
           ∨ n % 65536 = 44223
           ∨ n % 65536 = 44239
           ∨ n % 65536 = 44335
           ∨ n % 65536 = 44359
           ∨ n % 65536 = 44415
           ∨ n % 65536 = 44447
           ∨ n % 65536 = 44575
           ∨ n % 65536 = 44699
           ∨ n % 65536 = 44711
           ∨ n % 65536 = 44735
           ∨ n % 65536 = 44831
           ∨ n % 65536 = 44911
           ∨ n % 65536 = 44959
           ∨ n % 65536 = 45039
           ∨ n % 65536 = 45051
           ∨ n % 65536 = 45083
           ∨ n % 65536 = 45103
           ∨ n % 65536 = 45119
           ∨ n % 65536 = 45159
           ∨ n % 65536 = 45211
           ∨ n % 65536 = 45223
           ∨ n % 65536 = 45279
           ∨ n % 65536 = 45311
           ∨ n % 65536 = 45339
           ∨ n % 65536 = 45359
           ∨ n % 65536 = 45503
           ∨ n % 65536 = 45535
           ∨ n % 65536 = 45595
           ∨ n % 65536 = 45599
           ∨ n % 65536 = 45679
           ∨ n % 65536 = 45735
           ∨ n % 65536 = 45775
           ∨ n % 65536 = 45799
           ∨ n % 65536 = 45851
           ∨ n % 65536 = 45855
           ∨ n % 65536 = 45983
           ∨ n % 65536 = 46063
           ∨ n % 65536 = 46127
           ∨ n % 65536 = 46247
           ∨ n % 65536 = 46335
           ∨ n % 65536 = 46407
           ∨ n % 65536 = 46463
           ∨ n % 65536 = 46567
           ∨ n % 65536 = 46619
           ∨ n % 65536 = 46747
           ∨ n % 65536 = 46799
           ∨ n % 65536 = 46919
           ∨ n % 65536 = 46939
           ∨ n % 65536 = 47007
           ∨ n % 65536 = 47039
           ∨ n % 65536 = 47099
           ∨ n % 65536 = 47167
           ∨ n % 65536 = 47207
           ∨ n % 65536 = 47231
           ∨ n % 65536 = 47327
           ∨ n % 65536 = 47387
           ∨ n % 65536 = 47423
           ∨ n % 65536 = 47487
           ∨ n % 65536 = 47519
           ∨ n % 65536 = 47591
           ∨ n % 65536 = 47663
           ∨ n % 65536 = 47807
           ∨ n % 65536 = 48063
           ∨ n % 65536 = 48095
           ∨ n % 65536 = 48111
           ∨ n % 65536 = 48155
           ∨ n % 65536 = 48295
           ∨ n % 65536 = 48335
           ∨ n % 65536 = 48379
           ∨ n % 65536 = 48455
           ∨ n % 65536 = 48607
           ∨ n % 65536 = 48687
           ∨ n % 65536 = 48795
           ∨ n % 65536 = 48807
           ∨ n % 65536 = 48879
           ∨ n % 65536 = 48891
           ∨ n % 65536 = 48927
           ∨ n % 65536 = 48987
           ∨ n % 65536 = 49007
           ∨ n % 65536 = 49055
           ∨ n % 65536 = 49135
           ∨ n % 65536 = 49215) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_41063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41115_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41199_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41243_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41263_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41563_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41583_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41627_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41723_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41819_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_41855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42075_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42139_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42175_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42651_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42727_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42823_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42843_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_42911_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43111_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43291_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43611_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_43967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44699_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44711_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44911_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_44959_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45051_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45083_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45211_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45279_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45339_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45595_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45851_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_45983_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46463_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46619_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46747_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46799_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_46939_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47039_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47099_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47387_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47487_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_47807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48095_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48111_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48155_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48379_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48795_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48807_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48879_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48891_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48927_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_48987_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49215_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_8 {n : ℕ}
    (h : n % 65536 = 49255
           ∨ n % 65536 = 49311
           ∨ n % 65536 = 49359
           ∨ n % 65536 = 49407
           ∨ n % 65536 = 49511
           ∨ n % 65536 = 49563
           ∨ n % 65536 = 49567
           ∨ n % 65536 = 49631
           ∨ n % 65536 = 49639
           ∨ n % 65536 = 49915
           ∨ n % 65536 = 49983
           ∨ n % 65536 = 50143
           ∨ n % 65536 = 50223
           ∨ n % 65536 = 50267
           ∨ n % 65536 = 50303
           ∨ n % 65536 = 50343
           ∨ n % 65536 = 50407
           ∨ n % 65536 = 50495
           ∨ n % 65536 = 50503
           ∨ n % 65536 = 50535
           ∨ n % 65536 = 50663
           ∨ n % 65536 = 50715
           ∨ n % 65536 = 50779
           ∨ n % 65536 = 50843
           ∨ n % 65536 = 50847
           ∨ n % 65536 = 51055
           ∨ n % 65536 = 51103
           ∨ n % 65536 = 51135
           ∨ n % 65536 = 51167
           ∨ n % 65536 = 51227
           ∨ n % 65536 = 51247
           ∨ n % 65536 = 51271
           ∨ n % 65536 = 51407
           ∨ n % 65536 = 51431
           ∨ n % 65536 = 51451
           ∨ n % 65536 = 51455
           ∨ n % 65536 = 51519
           ∨ n % 65536 = 51611
           ∨ n % 65536 = 51663
           ∨ n % 65536 = 51803
           ∨ n % 65536 = 51871
           ∨ n % 65536 = 51951
           ∨ n % 65536 = 51967
           ∨ n % 65536 = 52031
           ∨ n % 65536 = 52071
           ∨ n % 65536 = 52191
           ∨ n % 65536 = 52335
           ∨ n % 65536 = 52391
           ∨ n % 65536 = 52415
           ∨ n % 65536 = 52431
           ∨ n % 65536 = 52507
           ∨ n % 65536 = 52551
           ∨ n % 65536 = 52635
           ∨ n % 65536 = 52687
           ∨ n % 65536 = 52703
           ∨ n % 65536 = 52735
           ∨ n % 65536 = 52763
           ∨ n % 65536 = 52847
           ∨ n % 65536 = 52967
           ∨ n % 65536 = 53055
           ∨ n % 65536 = 53159
           ∨ n % 65536 = 53183
           ∨ n % 65536 = 53275
           ∨ n % 65536 = 53295
           ∨ n % 65536 = 53319
           ∨ n % 65536 = 53339
           ∨ n % 65536 = 53375
           ∨ n % 65536 = 53439
           ∨ n % 65536 = 53551
           ∨ n % 65536 = 53659
           ∨ n % 65536 = 53695
           ∨ n % 65536 = 53791
           ∨ n % 65536 = 53871
           ∨ n % 65536 = 53887
           ∨ n % 65536 = 53919
           ∨ n % 65536 = 53991
           ∨ n % 65536 = 54011
           ∨ n % 65536 = 54043
           ∨ n % 65536 = 54079
           ∨ n % 65536 = 54239
           ∨ n % 65536 = 54303
           ∨ n % 65536 = 54319
           ∨ n % 65536 = 54343
           ∨ n % 65536 = 54375
           ∨ n % 65536 = 54439
           ∨ n % 65536 = 54495
           ∨ n % 65536 = 54523
           ∨ n % 65536 = 54575
           ∨ n % 65536 = 54591
           ∨ n % 65536 = 54751
           ∨ n % 65536 = 54815
           ∨ n % 65536 = 54975
           ∨ n % 65536 = 55023
           ∨ n % 65536 = 55207
           ∨ n % 65536 = 55291
           ∨ n % 65536 = 55327
           ∨ n % 65536 = 55367
           ∨ n % 65536 = 55407
           ∨ n % 65536 = 55423
           ∨ n % 65536 = 55519
           ∨ n % 65536 = 55527
           ∨ n % 65536 = 55535
           ∨ n % 65536 = 55579
           ∨ n % 65536 = 55679
           ∨ n % 65536 = 55707
           ∨ n % 65536 = 55759
           ∨ n % 65536 = 55899
           ∨ n % 65536 = 55963
           ∨ n % 65536 = 55967
           ∨ n % 65536 = 55999
           ∨ n % 65536 = 56059
           ∨ n % 65536 = 56127
           ∨ n % 65536 = 56167
           ∨ n % 65536 = 56191
           ∨ n % 65536 = 56231
           ∨ n % 65536 = 56287
           ∨ n % 65536 = 56315
           ∨ n % 65536 = 56347
           ∨ n % 65536 = 56383
           ∨ n % 65536 = 56411
           ∨ n % 65536 = 56551
           ∨ n % 65536 = 56571
           ∨ n % 65536 = 56603
           ∨ n % 65536 = 56639
           ∨ n % 65536 = 56703
           ∨ n % 65536 = 56935
           ∨ n % 65536 = 57071
           ∨ n % 65536 = 57179
           ∨ n % 65536 = 57215
           ∨ n % 65536 = 57255
           ∨ n % 65536 = 57327
           ∨ n % 65536 = 57375
           ∨ n % 65536 = 57407
           ∨ n % 65536 = 57415
           ∨ n % 65536 = 57447
           ∨ n % 65536 = 57535) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_49255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49563_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49567_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49915_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_49983_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50223_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50267_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50715_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50779_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50843_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_50847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51103_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51227_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51431_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51451_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51611_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51803_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51871_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51951_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_51967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52031_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52431_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52507_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52635_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52687_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52735_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52763_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52847_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_52967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53055_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53275_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53339_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53659_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53695_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53791_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53871_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53919_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_53991_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54011_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54043_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54319_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54439_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54523_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54575_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54751_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54815_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_54975_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55291_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55579_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55679_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55707_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55899_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55963_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_55999_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56059_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56315_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56347_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56383_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56411_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56571_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56603_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56639_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56703_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_56935_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57071_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57179_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57215_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57255_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57415_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57535_mod_65536 (by assumption)⟩

theorem descent_within_sixteen_9 {n : ℕ}
    (h : n % 65536 = 57647
           ∨ n % 65536 = 57671
           ∨ n % 65536 = 57755
           ∨ n % 65536 = 57759
           ∨ n % 65536 = 57839
           ∨ n % 65536 = 57887
           ∨ n % 65536 = 57947
           ∨ n % 65536 = 57967
           ∨ n % 65536 = 58015
           ∨ n % 65536 = 58175
           ∨ n % 65536 = 58203
           ∨ n % 65536 = 58271
           ∨ n % 65536 = 58351
           ∨ n % 65536 = 58459
           ∨ n % 65536 = 58471
           ∨ n % 65536 = 58479
           ∨ n % 65536 = 58495
           ∨ n % 65536 = 58523
           ∨ n % 65536 = 58527
           ∨ n % 65536 = 58559
           ∨ n % 65536 = 58599
           ∨ n % 65536 = 58855
           ∨ n % 65536 = 58863
           ∨ n % 65536 = 58983
           ∨ n % 65536 = 59035
           ∨ n % 65536 = 59247
           ∨ n % 65536 = 59263
           ∨ n % 65536 = 59295
           ∨ n % 65536 = 59303
           ∨ n % 65536 = 59423
           ∨ n % 65536 = 59463
           ∨ n % 65536 = 59559
           ∨ n % 65536 = 59615
           ∨ n % 65536 = 59623
           ∨ n % 65536 = 59643
           ∨ n % 65536 = 59647
           ∨ n % 65536 = 59675
           ∨ n % 65536 = 59775
           ∨ n % 65536 = 59879
           ∨ n % 65536 = 60007
           ∨ n % 65536 = 60015
           ∨ n % 65536 = 60059
           ∨ n % 65536 = 60063
           ∨ n % 65536 = 60143
           ∨ n % 65536 = 60231
           ∨ n % 65536 = 60271
           ∨ n % 65536 = 60411
           ∨ n % 65536 = 60527
           ∨ n % 65536 = 60571
           ∨ n % 65536 = 60607
           ∨ n % 65536 = 60623
           ∨ n % 65536 = 60743
           ∨ n % 65536 = 60831
           ∨ n % 65536 = 60911
           ∨ n % 65536 = 60955
           ∨ n % 65536 = 61031
           ∨ n % 65536 = 61135
           ∨ n % 65536 = 61311
           ∨ n % 65536 = 61351
           ∨ n % 65536 = 61375
           ∨ n % 65536 = 61423
           ∨ n % 65536 = 61435
           ∨ n % 65536 = 61471
           ∨ n % 65536 = 61503
           ∨ n % 65536 = 61531
           ∨ n % 65536 = 61543
           ∨ n % 65536 = 61595
           ∨ n % 65536 = 61631
           ∨ n % 65536 = 61647
           ∨ n % 65536 = 61663
           ∨ n % 65536 = 61723
           ∨ n % 65536 = 61767
           ∨ n % 65536 = 61979
           ∨ n % 65536 = 62119
           ∨ n % 65536 = 62159
           ∨ n % 65536 = 62235
           ∨ n % 65536 = 62239
           ∨ n % 65536 = 62279
           ∨ n % 65536 = 62299
           ∨ n % 65536 = 62511
           ∨ n % 65536 = 62619
           ∨ n % 65536 = 62631
           ∨ n % 65536 = 62719
           ∨ n % 65536 = 62943
           ∨ n % 65536 = 62951
           ∨ n % 65536 = 62959
           ∨ n % 65536 = 63023
           ∨ n % 65536 = 63079
           ∨ n % 65536 = 63131
           ∨ n % 65536 = 63303
           ∨ n % 65536 = 63323
           ∨ n % 65536 = 63335
           ∨ n % 65536 = 63359
           ∨ n % 65536 = 63391
           ∨ n % 65536 = 63455
           ∨ n % 65536 = 63483
           ∨ n % 65536 = 63515
           ∨ n % 65536 = 63519
           ∨ n % 65536 = 63535
           ∨ n % 65536 = 63551
           ∨ n % 65536 = 63591
           ∨ n % 65536 = 63599
           ∨ n % 65536 = 63655
           ∨ n % 65536 = 63903
           ∨ n % 65536 = 64047
           ∨ n % 65536 = 64167
           ∨ n % 65536 = 64207
           ∨ n % 65536 = 64251
           ∨ n % 65536 = 64287
           ∨ n % 65536 = 64327
           ∨ n % 65536 = 64367
           ∨ n % 65536 = 64447
           ∨ n % 65536 = 64479
           ∨ n % 65536 = 64507
           ∨ n % 65536 = 64539
           ∨ n % 65536 = 64667
           ∨ n % 65536 = 64719
           ∨ n % 65536 = 64831
           ∨ n % 65536 = 64839
           ∨ n % 65536 = 64871
           ∨ n % 65536 = 64923
           ∨ n % 65536 = 65007
           ∨ n % 65536 = 65127
           ∨ n % 65536 = 65179
           ∨ n % 65536 = 65183
           ∨ n % 65536 = 65191
           ∨ n % 65536 = 65275
           ∨ n % 65536 = 65311
           ∨ n % 65536 = 65343
           ∨ n % 65536 = 65371
           ∨ n % 65536 = 65391
           ∨ n % 65536 = 65407
           ∨ n % 65536 = 65439) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 ∧ T_iter n k < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨16, by norm_num, by norm_num, descent_57647_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57671_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57755_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57759_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57887_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57947_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_57967_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58175_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58203_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58459_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58495_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58523_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58855_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58863_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_58983_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59035_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59247_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59263_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59295_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59463_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59559_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59615_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59643_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59647_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59675_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59775_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_59879_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60015_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60059_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60063_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60143_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60231_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60271_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60411_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60527_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60571_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60607_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60623_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60743_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60911_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_60955_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61031_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61135_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61351_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61375_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61423_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61435_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61471_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61503_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61531_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61543_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61595_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61647_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61663_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61723_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61767_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_61979_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62119_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62159_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62235_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62239_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62279_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62299_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62511_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62619_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62631_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62719_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62943_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62951_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_62959_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63023_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63079_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63131_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63303_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63323_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63335_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63359_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63455_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63483_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63515_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63519_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63535_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63551_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63591_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63599_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63655_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_63903_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64047_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64167_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64207_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64251_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64287_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64327_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64367_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64447_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64479_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64507_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64539_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64667_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64719_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64831_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64839_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64871_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_64923_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65007_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65127_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65179_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65183_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65191_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65275_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65311_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65343_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65371_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65391_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65407_mod_65536 (by assumption)⟩
  · exact ⟨16, by norm_num, by norm_num, descent_65439_mod_65536 (by assumption)⟩

end CollatzResidueDescent65536
