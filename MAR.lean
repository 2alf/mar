import MAR.MAR01
import MAR.MAR02
import MAR.MAR03
import MAR.MAR04
import MAR.MAR05
import MAR.MAR06
import MAR.MAR07
import MAR.MAR08
import MAR.MAR09
import MAR.MAR10
import MAR.MAR10b
import MAR.MAR11
import MAR.MAR12
import MAR.MAR13
import MAR.MAR14
import MAR.MAR15
import MAR.MAR16
import MAR.MAR17

/-!
# Monster Assignment Rigidity (MAR): the results

One file per result, `MAR/MARnn.lean`. Each restates the headline theorem(s) under the name
`MAR.MARn…` and proves it by the implementation in `MonsterCN/`.

* `MAR01`: MAR-1: exactly two power-compatible surjective tables
  (`MAR.MAR1`)
* `MAR02`: MAR-2: the hidden symmetry σ
  (`MAR.MAR2`)
* `MAR03`: MAR-3: uniqueness given the catalogue
  (`MAR.MAR3_surj`, `MAR.MAR3_coh`)
* `MAR04`: MAR-4: sharpness of MAR-3
  (`MAR.MAR4`, `MAR.MAR4_twist`, `MAR.MAR4_alt18`)
* `MAR05`: MAR-5: exactly eight compatible tables
  (`MAR.MAR5`, `MAR.MAR5_distinct`)
* `MAR06`: MAR-6: the power-map symmetries of the Monster
  (`MAR.MAR6`, `MAR.MAR6_galois`, `MAR.MAR6_sigma`)
* `MAR07`: MAR-7: no power-map rule gives the thread at 32A and 32B
  (`MAR.MAR7`, `MAR.MAR7_sigma`)
* `MAR08`: MAR-8: with the catalogue, the thread is determined except at 32A, 32B
  (`MAR.MAR8`, `MAR.MAR8_both`, `MAR.LeBruyn_check`)
* `MAR09`: MAR-9 (main theorem): catalogue-free rigidity
  (`MAR.MAR9`, `MAR.MAR9_converse`, `MAR.MAR9_exhaustive`, `MAR.MAR9_universe`, `MAR.MAR9_normal_form`, `MAR.MAR9_orders`)
* `MAR10`: MAR-10: every hypothesis of MAR-9 is necessary
  (`MAR.MAR10`, `MAR.MAR10_power`, `MAR.MAR10_power_names`, `MAR.MAR10_genus`, `MAR.MAR10_genus_admissible`)
* `MAR10b`: MAR-10′: the Atkin–Lehner part of the power rule is necessary
  (`MAR.MAR10b`, `MAR.MAR10b_differs`, `MAR.MAR10b_names`)
* `MAR11`: MAR-11: hidden symmetries of the Baby Monster
  (`MAR.MAR11_H1`, `MAR.MAR11_H2`, `MAR.MAR11_names`, `MAR.MAR11_values`, `MAR.MAR11_names₂`)
* `MAR12`: MAR-12: no power-map rule recovers Baby Monster moonshine
  (`MAR.MAR12`)
* `MAR13`: MAR-13 (erratum): two wrong labels in the Conway-moonshine table
  (`MAR.MAR13`, `MAR.MAR13_evidence`, `MAR.MAR13_identities`, `MAR.MAR13_twist`, `MAR.MAR13_group30`, `MAR.MAR13_group12`)
* `MAR14`: MAR-14: hidden symmetries of Co₀
  (`MAR.MAR14`, `MAR.MAR14_no_rule`, `MAR.MAR14_names`)
* `MAR15`: MAR-15: Conway moonshine is not rigid
  (`MAR.MAR15`, `MAR.MAR15_two`, `MAR.MAR15_published`, `MAR.MAR15_rows`, `MAR.MAR15_names`)
* `MAR16`: MAR-16: no squaring rule in Conway moonshine
  (`MAR.MAR16`, `MAR.MAR16_no_rule`, `MAR.MAR16_odd`, `MAR.MAR16_monster`, `MAR.MAR16_names`)
* `MAR17`: MAR-17 (errata): misprints in published tables
  (`MAR.MAR17_46c`, `MAR.MAR17_94b`, `MAR.MAR17_194`)
-/
