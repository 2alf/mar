/-
# Axiom audit for MonsterCN

Run from the project root, after `lake build`:

    lake env lean check_axioms.lean

Every line of output must read either
  `'X' depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset), or
  `'X' does not depend on any axioms`.
Anything else (in particular `sorryAx`, or a user-declared axiom) is a failure.
`verify.ps1` / `verify.sh` run this file and check the output automatically.

This file is not part of the `MonsterCN` library target; it only imports it.
-/
import MonsterCN
import MAR

/-! ## Data integrity and the known Conway–Norton facts (`Checks.lean`) -/
#print axioms MonsterCN.lengths
#print axioms MonsterCN.monsterOrder_eq
#print axioms MonsterCN.class_equation
#print axioms MonsterCN.orthogonality
#print axioms MonsterCN.j_coefficients
#print axioms MonsterCN.pw_ord
#print axioms MonsterCN.ord_one_iff
#print axioms MonsterCN.cn_shape
#print axioms MonsterCN.cn_power_rule
#print axioms MonsterCN.card_distinct_labels
#print axioms MonsterCN.label_fibres
#print axioms MonsterCN.galois_same_label
#print axioms MonsterCN.rational_27
#print axioms MonsterCN.catalogue_spec
#print axioms MonsterCN.coeff_vanishing
#print axioms MonsterCN.coeff_coherent
#print axioms MonsterCN.not_determined_by_order_and_centralizer
#print axioms MonsterCN.fricke_not_power_closed
#print axioms MonsterCN.h_not_dvd_n_div_h

/-! ## MAR-1 … MAR-5: rigidity given the catalogue of 171 groups (`Rigidity.lean`) -/
#print axioms MonsterCN.compatible_surj_iff        -- MAR-1
#print axioms MonsterCN.sigma_automorphism         -- MAR-2
#print axioms MonsterCN.unique_of_surj_van         -- MAR-3
#print axioms MonsterCN.unique_of_van_coh          -- MAR-3
#print axioms MonsterCN.sharpness                  -- MAR-4
#print axioms MonsterCN.not_van2_twist             -- MAR-4
#print axioms MonsterCN.not_coh1_alt18             -- MAR-4
#print axioms MonsterCN.compat_iff_variant         -- MAR-5
#print axioms MonsterCN.variant_injective          -- MAR-5
#print axioms MonsterCN.compat_variant
#print axioms MonsterCN.compat_cn
#print axioms MonsterCN.surj_cn
#print axioms MonsterCN.van_cn
#print axioms MonsterCN.coh_cn
#print axioms MonsterCN.compat_twist
#print axioms MonsterCN.surj_twist
#print axioms MonsterCN.van13_twist
#print axioms MonsterCN.coh_twist
#print axioms MonsterCN.compat_alt18
#print axioms MonsterCN.van_alt18
#print axioms MonsterCN.not_surj_alt18
#print axioms MonsterCN.twist_names

/-! ## MAR-6 … MAR-8: symmetries of the power-map data (`Automorphisms.lean`) -/
#print axioms MonsterCN.powerAut_classification    -- MAR-6
#print axioms MonsterCN.galois_pairs_invisible     -- MAR-6
#print axioms MonsterCN.sigma_pairs_visible        -- MAR-6
#print axioms MonsterCN.sigma_isPowerAut
#print axioms MonsterCN.label_of_powerAut
#print axioms MonsterCN.no_invariant_h_rule        -- MAR-7
#print axioms MonsterCN.thread_determined_by_compat -- MAR-8
#print axioms MonsterCN.thread_ambiguous_at_32     -- MAR-8
#print axioms MonsterCN.lebruyn_exceptions
#print axioms MonsterCN.autPairs_names

/-! ## MAR-9, MAR-10, MAR-10′: catalogue-free rigidity (`GenusZero.lean`) -/
#print axioms MonsterCN.GZ.gz_table_spec
#print axioms MonsterCN.GZ.genus_sanity
#print axioms MonsterCN.GZ.cn_isGZ
#print axioms MonsterCN.GZ.cn_unique_genus_zero    -- MAR-9
#print axioms MonsterCN.GZ.cn_satisfies_gz         -- MAR-9 (converse)
#print axioms MonsterCN.GZ.fake_names
#print axioms MonsterCN.GZ.fake18_props            -- MAR-10
#print axioms MonsterCN.GZ.fake27_props            -- MAR-10
#print axioms MonsterCN.GZ.fake32_props            -- MAR-10
#print axioms MonsterCN.GZ.fakeNG_props            -- MAR-10
#print axioms MonsterCN.GZ.sharpness_gz            -- MAR-10
#print axioms MonsterCN.GZ.fakeW_names
#print axioms MonsterCN.GZ.fakeW_props             -- MAR-10′
#print axioms MonsterCN.GZ.fakeW_differs           -- MAR-10′

/-! ## MAR-11, MAR-12: the Baby Monster (`BabyMonster.lean`) -/
#print axioms MonsterCN.Baby.data_integrity
#print axioms MonsterCN.Baby.witness_names
#print axioms MonsterCN.Baby.hidden_moonshine_symmetries   -- MAR-11
#print axioms MonsterCN.Baby.h1_values
#print axioms MonsterCN.Baby.chi185_norm
#print axioms MonsterCN.Baby.hidden_moonshine_symmetries₂  -- MAR-11
#print axioms MonsterCN.Baby.witness2_names
#print axioms MonsterCN.Baby.no_invariant_baby_rule        -- MAR-12

/-! ## MAR-13, MAR-14: Conway moonshine (`ConwayMoonshine.lean`, `ConwayErratum.lean`) -/
#print axioms MonsterCN.Conway.co_integrity
#print axioms MonsterCN.Conway.lambda2_chi24
#print axioms MonsterCN.Conway.dmc_label_inconsistency       -- MAR-13
#print axioms MonsterCN.Conway.dmc_corrected_label_evidence  -- MAR-13
#print axioms MonsterCN.Conway.conway_witness_names
#print axioms MonsterCN.Conway.conway_hidden_symmetries      -- MAR-14
#print axioms MonsterCN.Conway.no_invariant_conway_rule      -- MAR-14
#print axioms MonsterCN.Erratum.frames_match_chi24
#print axioms MonsterCN.Erratum.printed_labels_and_mismatch  -- MAR-13
#print axioms MonsterCN.Erratum.twist_identity_check
#print axioms MonsterCN.Erratum.identity_30J_30K             -- MAR-13
#print axioms MonsterCN.Erratum.identities_12E_30J           -- MAR-13
#print axioms MonsterCN.Erratum.group_30K                    -- MAR-13
#print axioms MonsterCN.Erratum.group_12E                    -- MAR-13

/-! ## MAR-15: Conway moonshine is not rigid (`ConwayOdd.lean`) -/
#print axioms MonsterCN.ConwayOdd.frame_matches_chi24
#print axioms MonsterCN.ConwayOdd.rows_certified
#print axioms MonsterCN.ConwayOdd.t2_table_spec
#print axioms MonsterCN.ConwayOdd.rows_0_6_irrelevant
#print axioms MonsterCN.ConwayOdd.T2_matches_characters
#print axioms MonsterCN.ConwayOdd.names_9
#print axioms MonsterCN.ConwayOdd.dmc_admissible
#print axioms MonsterCN.ConwayOdd.alt_admissible
#print axioms MonsterCN.ConwayOdd.conway_not_rigid           -- MAR-15

/-! ## Modular groups (`Groups.lean`) -/
#print axioms MonsterCN.gamma0_le_gamma0Bar
#print axioms MonsterCN.translation_mem
#print axioms MonsterCN.gamma0Bar_one
#print axioms MonsterCN.inGamma0Bar_iff_conj
#print axioms MonsterCN.fricke_conj_mem
#print axioms MonsterCN.fricke_inv_conj_mem

/-! ## The stated (not proved) per-class theorem and what is proved about it (`Statement.lean`) -/
#print axioms MonsterCN.cn_invariant
#print axioms MonsterCN.cn_n_pos
#print axioms MonsterCN.gamma0R_le_cnGroup₁
#print axioms MonsterCN.ConwayNortonTable.existential

/-! ## Ogg's observation, finite check (`Ogg.lean`; known mathematics) -/
#print axioms MonsterCN.Ogg.classNo_values
#print axioms MonsterCN.Ogg.known_genera
#print axioms MonsterCN.Ogg.formulas_consistent
#print axioms MonsterCN.Ogg.ogg_below_bound
#print axioms MonsterCN.Ogg.monster_fricke_classes

/-! ## MAR-16: no label-level squaring rule in Conway moonshine (`ConwayPowers.lean`) -/
#print axioms MonsterCN.ConwayPowers.frames_match_chi24
#print axioms MonsterCN.ConwayPowers.pair_names
#print axioms MonsterCN.ConwayPowers.rowP_29
#print axioms MonsterCN.ConwayPowers.conway_not_functorial_at_2  -- MAR-16
#print axioms MonsterCN.ConwayPowers.no_label_squaring_rule      -- MAR-16
#print axioms MonsterCN.ConwayPowers.conway_functorial_odd
#print axioms MonsterCN.ConwayPowers.monster_functorial

/-! ## MAR-17: audit of published moonshine tables (`Audit.lean`) -/
#print axioms MonsterCN.Audit.cm_46c                             -- MAR-17
#print axioms MonsterCN.Audit.cm_94b                             -- MAR-17
#print axioms MonsterCN.Audit.dgo_count                          -- MAR-17

/-! ## MAR-10 completion (`Sharpness.lean`) -/
#print axioms MonsterCN.GZ.fakeC_props
#print axioms MonsterCN.GZ.fakeNG_admissible

/-! ## MAR-15 exact count, all rows certified; supplementary facts -/
#print axioms MonsterCN.ConwayOdd.conway_exactly_12
#print axioms MonsterCN.ConwayOdd.oddRoot_eq
#print axioms MonsterCN.ConwayOdd.search_spec
#print axioms MonsterCN.ConwayOdd.rows_all_certified
#print axioms MonsterCN.no_sigma_invariant_h_rule
#print axioms MonsterCN.monster_orders_73
#print axioms MonsterCN.GZ.isGZ_normal_form

/-! ## The labelled results (`MAR/`, one file per result) -/
#print axioms MAR.MAR1
#print axioms MAR.MAR1_names
#print axioms MAR.MAR2
#print axioms MAR.MAR3_surj
#print axioms MAR.MAR3_coh
#print axioms MAR.MAR4
#print axioms MAR.MAR4_twist
#print axioms MAR.MAR4_alt18
#print axioms MAR.MAR4_names
#print axioms MAR.MAR5
#print axioms MAR.MAR5_distinct
#print axioms MAR.MAR6
#print axioms MAR.MAR6_galois
#print axioms MAR.MAR6_sigma
#print axioms MAR.MAR7
#print axioms MAR.MAR7_sigma
#print axioms MAR.MAR8
#print axioms MAR.MAR8_both
#print axioms MAR.LeBruyn_check
#print axioms MAR.MAR9
#print axioms MAR.MAR9_converse
#print axioms MAR.MAR9_exhaustive
#print axioms MAR.MAR9_universe
#print axioms MAR.MAR9_normal_form
#print axioms MAR.MAR9_orders
#print axioms MAR.MAR10
#print axioms MAR.MAR10_power
#print axioms MAR.MAR10_power_names
#print axioms MAR.MAR10_genus
#print axioms MAR.MAR10_genus_admissible
#print axioms MAR.MAR10_names
#print axioms MAR.MAR10b
#print axioms MAR.MAR10b_differs
#print axioms MAR.MAR10b_names
#print axioms MAR.MAR11_H1
#print axioms MAR.MAR11_H2
#print axioms MAR.MAR11_names
#print axioms MAR.MAR11_values
#print axioms MAR.MAR11_names₂
#print axioms MAR.MAR12
#print axioms MAR.MAR13
#print axioms MAR.MAR13_evidence
#print axioms MAR.MAR13_identities
#print axioms MAR.MAR13_twist
#print axioms MAR.MAR13_group30
#print axioms MAR.MAR13_group12
#print axioms MAR.MAR14
#print axioms MAR.MAR14_no_rule
#print axioms MAR.MAR14_names
#print axioms MAR.MAR15
#print axioms MAR.MAR15_two
#print axioms MAR.MAR15_published
#print axioms MAR.MAR15_rows
#print axioms MAR.MAR15_names
#print axioms MAR.MAR16
#print axioms MAR.MAR16_no_rule
#print axioms MAR.MAR16_odd
#print axioms MAR.MAR16_monster
#print axioms MAR.MAR16_names
#print axioms MAR.MAR17_46c
#print axioms MAR.MAR17_94b
#print axioms MAR.MAR17_194
