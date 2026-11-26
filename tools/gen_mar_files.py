"""Generate the `MAR/` directory: one Lean file per result MAR-N.

Each file restates the headline theorem(s) of MAR-N under the name `MAR.MARn...`, with the statement
copied verbatim from the implementation in `MonsterCN/`, and proves it by the implementation's
theorem. The restated statements are type-checked against the originals when `MAR` is built, so the
files cannot drift from the proofs. Run from anywhere:

    python tools/gen_mar_files.py
"""
import os, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def src(module):
    return open(os.path.join(ROOT, 'MonsterCN', module + '.lean'), encoding='utf8').read()


def namespace_and_opens(module):
    s = src(module)
    ns = re.findall(r'^namespace (\S+)', s, re.M)[0]
    opens = []
    for line in re.findall(r'^open ([^\n]+)$', s, re.M):
        for x in line.split():
            if x != 'in' and x not in opens:
                opens.append(x)
    return ns, opens


def signature(module, name):
    s = src(module)
    m = re.search(r'^theorem ' + re.escape(name) + r'(?=[\s:({])(.*?)\s*:=', s, re.S | re.M)
    if not m:
        raise SystemExit('missing %s.%s' % (module, name))
    return m.group(1).strip()


# (file, title, module(s), overview, [theorems]); theorem = (new name, module, original, args, doc)
# Extra hand-written lines (name checks) go in `extra`.
RESULTS = [
 ('MAR01', 'MAR-1: exactly two power-compatible surjective tables', ['Rigidity'],
  '''Given the catalogue of the 171 Conway–Norton groups, a labelling of the 194 Monster classes that
is compatible with element orders and the ATLAS power maps (via the Conway–Norton power rule) and
uses every group is either the Conway–Norton table `cn` or its twist `twist = cn ∘ σ`, where
`σ = (16B 16C)(32A 32B)`.''',
  [('MAR1', 'Rigidity', 'compatible_surj_iff', 'L',
    'Compatible + surjective ⇔ `cn` or `cn ∘ σ`.')],
  ['/-- The classes moved by `σ` (indices are positions in the ATLAS table of `M`). -/',
   'theorem MAR1_names : nameOf 54 = "16B" ∧ nameOf 55 = "16C" ∧ nameOf 106 = "32A" ∧',
   '    nameOf 107 = "32B" := by decide +kernel']),
 ('MAR02', 'MAR-2: the hidden symmetry σ', ['Rigidity'],
  '''`σ = (16B 16C)(32A 32B)` commutes with every prime power map and preserves element orders and
centralizer orders, so power-map data cannot tell the two tables of MAR-1 apart. Only character
values separate them, e.g. `a₂(32A) = 4 ≠ 0 = a₂(32B)`.''',
  [('MAR2', 'Rigidity', 'sigma_automorphism', '',
    '`σ` is a symmetry of all group-order data; `a₂` separates `32A` from `32B`.')], []),
 ('MAR03', 'MAR-3: uniqueness given the catalogue', ['Rigidity'],
  '''With the 171-group catalogue, the Conway–Norton table is the only compatible labelling that is
(a) surjective and satisfies `a₂`-vanishing, or (b) satisfies `a₂`-vanishing and `a₁`-coherence.''',
  [('MAR3_surj', 'Rigidity', 'unique_of_surj_van', 'hC hS hV',
    'Compatible + surjective + `a₂`-vanishing ⇒ `cn`.'),
   ('MAR3_coh', 'Rigidity', 'unique_of_van_coh', 'hC hV hCoh',
    'Compatible + `a₂`-vanishing + `a₁`-coherence ⇒ `cn`.')], []),
 ('MAR04', 'MAR-4: sharpness of MAR-3', ['Rigidity'],
  '''Neither coefficient hypothesis of MAR-3 can be dropped: the twist `cn ∘ σ` satisfies everything
except `a₂`-vanishing, and `alt18` (`cn` with `18E ↦ 18-`) satisfies everything except
`a₁`-coherence.''',
  [('MAR4', 'Rigidity', 'sharpness', '', 'The two counterexamples and their properties.'),
   ('MAR4_twist', 'Rigidity', 'not_van2_twist', '', 'The twist violates `a₂`-vanishing.'),
   ('MAR4_alt18', 'Rigidity', 'not_coh1_alt18', '', '`alt18` violates `a₁`-coherence.')],
  ['theorem MAR4_names : nameOf 60 = "18D" ∧ nameOf 61 = "18E" := by decide +kernel']),
 ('MAR05', 'MAR-5: exactly eight compatible tables', ['Rigidity'],
  '''Without surjectivity or coefficient data, exactly 8 labellings by the catalogue are compatible
with the power maps. They come from three independent binary choices
(`variant b₁ b₂ b₃`), and they are pairwise distinct.''',
  [('MAR5', 'Rigidity', 'compat_iff_variant', 'L', 'Compatible ⇔ one of the eight variants.'),
   ('MAR5_distinct', 'Rigidity', 'variant_injective', '', 'The eight variants are distinct.')], []),
 ('MAR06', 'MAR-6: the power-map symmetries of the Monster', ['Automorphisms'],
  '''Every permutation of the classes that preserves element orders and commutes with the 15 prime
power maps moves classes only within 24 explicit pairs: the 22 Galois-conjugate pairs (on which
characters and moonshine labels agree) and the two pairs of `σ` (on which they do not).''',
  [('MAR6', 'Automorphisms', 'powerAut_classification', 'h',
    'Every power-map symmetry fixes a class or swaps it with its partner.'),
   ('MAR6_galois', 'Automorphisms', 'galois_pairs_invisible', '',
    'On the 22 Galois pairs, characters, centralizers and labels agree.'),
   ('MAR6_sigma', 'Automorphisms', 'sigma_pairs_visible', '',
    'On the two pairs of `σ`, characters differ.')], []),
 ('MAR07', 'MAR-7: no power-map rule gives the thread at 32A and 32B', ['Automorphisms', 'Supplement'],
  '''Any function of the classes that is invariant under power-map symmetries (as is anything
computed from power maps and element orders) differs from the Conway–Norton thread `h` at `32A`
(`h = 1`) or at `32B` (`h = 2`). This explains one exception in Le Bruyn's reconstruction.''',
  [('MAR7', 'Automorphisms', 'no_invariant_h_rule', 'F hF',
    'No power-map-invariant rule computes the thread `h` at both `32A` and `32B`.'),
   ('MAR7_sigma', 'Supplement', 'no_sigma_invariant_h_rule', 'F hF',
    'Strong form: invariance under `σ` alone suffices (covers rules using centralizer orders too).')],
  []),
 ('MAR08', 'MAR-8: with the catalogue, the thread is determined except at 32A, 32B',
  ['Automorphisms'],
  '''Every compatible labelling by the catalogue has the Conway–Norton thread `h` at every class except
`32A` and `32B`, and both values occur there. (Also: Le Bruyn's rule, evaluated on the ATLAS data,
fails at exactly 14 classes; this is a check of known work, not a new result.)''',
  [('MAR8', 'Automorphisms', 'thread_determined_by_compat', 'L hL',
    'The thread is forced away from `32A`, `32B`.'),
   ('MAR8_both', 'Automorphisms', 'thread_ambiguous_at_32', '',
    'Both thread values occur at `32A`.'),
   ('LeBruyn_check', 'Automorphisms', 'lebruyn_exceptions', '',
    "Le Bruyn's rule (arXiv:1804.04127, Thm 2) fails at exactly these 14 classes.")], []),
 ('MAR09', 'MAR-9 (main theorem): catalogue-free rigidity', ['GenusZero', 'NormalForm', 'Supplement'],
  '''No list of moonshine groups is used. Allow every class any label `n|h+W` of Conway–Norton shape
whose curve `X₀(n/h)/W` has genus zero (385 labels in all, `MAR9_universe`). Then the
Conway–Norton table is the **only** labelling that satisfies
* (C) compatibility with element orders and the ATLAS power maps via the power rule,
* (V) vanishing of `a₁`, `a₂` where the thread requires it,
* (H) equal groups ⇒ equal `a₁`,
and it does satisfy them (`MAR9_converse`). The hypothesis `CompatGZ` quantifies over *all*
labels: `MAR9_exhaustive` proves that every label satisfying the admissibility predicate `IsGZ`
lies in the enumeration `candidates`, and `MAR9_universe` that the enumeration is the stored table,
so no candidate can be missed. External input (A4): the classical Atkin–Lehner fixed-point
formula used to compute the genus.''',
  [('MAR9', 'GenusZero', 'cn_unique_genus_zero', 'hC hV hH',
    '**MAR-9.** (C) + (V) + (H) over genus-zero labels ⇒ the Conway–Norton table.'),
   ('MAR9_converse', 'GenusZero', 'cn_satisfies_gz', '',
    'The Conway–Norton table satisfies all the hypotheses.'),
   ('MAR9_exhaustive', 'GenusZero', 'mem_candidates', 'l hl',
    'Exhaustiveness: every admissible genus-zero label (any `n|h+W`) is in the enumeration.'),
   ('MAR9_universe', 'GenusZero', 'gz_table_spec', '',
    'The enumeration equals the stored universe of 385 labels.'),
   ('MAR9_normal_form', 'NormalForm', 'isGZ_normal_form', 'h₁ h₂ hn hh hW',
    'Each group `n|h+W` has exactly one admissible encoding (`W` in increasing order).'),
   ('MAR9_orders', 'Supplement', 'monster_orders_73', '',
    'The universe is spread over the 73 element orders of the Monster.')], []),
 ('MAR10', 'MAR-10: every hypothesis of MAR-9 is necessary', ['GenusZero', 'Sharpness'],
  '''Dropping any one hypothesis of MAR-9 admits a fake table, which satisfies all the other
hypotheses and differs from the Conway–Norton table: without (H), `18E ↦ 18-`; without
`a₁`-vanishing, `27B ↦ 27|3`; without `a₂`-vanishing, `16B, 16C, 32A, 32B` relabelled; without the
power rule, `9B ↦ 9|3`; without genus zero, `24I ↦ 24-` and `32A ↦ 32-` (genus one, but
otherwise admissible). The order condition `n = o(g)` is the normalization of a label and has no
witness.''',
  [('MAR10', 'GenusZero', 'sharpness_gz', '',
    'The fakes without (H), without `a₁`-vanishing and without `a₂`-vanishing.'),
   ('MAR10_power', 'Sharpness', 'fakeC_props', '',
    'The fake without the power rule: admissible, (V), (H), differs, power rule fails.'),
   ('MAR10_power_names', 'Sharpness', 'fakeC_names', '', 'Class 27 is `9B`, labelled `9-`.'),
   ('MAR10_genus', 'GenusZero', 'fakeNG_props', '',
    'The fake with genus-one labels satisfies (C), (V), (H).'),
   ('MAR10_genus_admissible', 'Sharpness', 'fakeNG_admissible', '',
    'It is admissible except for genus zero, which fails exactly at its two changed labels.')],
  ['theorem MAR10_names : nameOf 61 = "18E" ∧ nameOf 91 = "27B" ∧ nameOf 85 = "24I" := by',
   '  decide +kernel']),
 ('MAR10b', "MAR-10′: the Atkin–Lehner part of the power rule is necessary", ['GenusZero'],
  '''If the power rule only requires `W(g^p) ⊇ {e ∈ W(g) : e ∣ n'/h'}` instead of equality, a
genus-zero labelling satisfying (V) and (H) differs from the Conway–Norton table at 15 classes.''',
  [("MAR10b", 'GenusZero', 'fakeW_props', '', 'The fake table under the weakened rule.'),
   ("MAR10b_differs", 'GenusZero', 'fakeW_differs', '', 'It differs from `cn` at 15 classes.'),
   ("MAR10b_names", 'GenusZero', 'fakeW_names', '', 'The 15 classes.')], []),
 ('MAR11', 'MAR-11: hidden symmetries of the Baby Monster', ['BabyMonster'],
  '''There are permutations of the 247 classes of `2·𝔹` that preserve element and centralizer orders
and commute with all power maps, yet exchange classes whose generalized moonshine functions
`T_{t,g}` differ: six pairs differ in `H₁ = 1 + χ₄₃₇₁`, two more in `H₂ = χ₉₆₂₅₆`.
External input (A3): Höhn's identification of `H₁`, `H₂`.''',
  [('MAR11_H1', 'BabyMonster', 'hidden_moonshine_symmetries', '',
    'Six power-map symmetries moving classes with different `H₁`.'),
   ('MAR11_H2', 'BabyMonster', 'hidden_moonshine_symmetries₂', '',
    'Two more, moving classes with different `H₂`.'),
   ('MAR11_names', 'BabyMonster', 'witness_names', '', 'The six pairs.'),
   ('MAR11_values', 'BabyMonster', 'h1_values', '', 'Their `H₁` values.'),
   ('MAR11_names₂', 'BabyMonster', 'witness2_names', '', 'The other two pairs and `H₂`.')], []),
 ('MAR12', 'MAR-12: no power-map rule recovers Baby Monster moonshine', ['BabyMonster'],
  '''Any function of the classes of `2·𝔹` that is invariant under power-map symmetries differs from
the first generalized moonshine coefficient `H₁` somewhere.''',
  [('MAR12', 'BabyMonster', 'no_invariant_baby_rule', 'F hF',
    'Power-map data cannot reproduce `H₁`.')], []),
 ('MAR13', 'MAR-13 (erratum): two wrong labels in the Conway-moonshine table',
  ['ConwayMoonshine', 'ConwayErratum'],
  '''Duncan–Mack-Crane (Forum Math. Sigma 3 (2015) e10), Table A.1, gives one group to classes with
different series: `12E` and `6M` are both labelled `12-`, and `30J` and `30K` are both labelled
`60+12,15,20`. Since a genus-zero group has only one normalized Hauptmodul, `12E` and `30J` are
mislabelled; their groups are `(24|2+12)^{↑1/4}` and `(60+12,15,20)^{↑1/2}`. This is an
erratum, not a discovery: the correct groups already appear in Kondo (1985). The finite
computations of the correction are below; the classical inputs C1–C4 (Newman, Ligozat, valence
formula, Euler) are stated in `MonsterCN/ConwayErratum.lean`.''',
  [('MAR13', 'ConwayMoonshine', 'dmc_label_inconsistency', '',
    'The printed labels contradict the series.'),
   ('MAR13_evidence', 'ConwayMoonshine', 'dmc_corrected_label_evidence', '',
    '`12E` matches `12L`, and `30J` matches `30G`, in `a₁` and `a₂`.'),
   ('MAR13_identities', 'ConwayErratum', 'identities_12E_30J', '',
    'Finite data for the exact identities `T_{12E} = T_{12L} = T_{12M}`, `T_{30J} = T_{30G}`.'),
   ('MAR13_twist', 'ConwayErratum', 'identity_30J_30K', '',
    '`T_{30J}` is the `q ↦ -q` twist of `T_{30K}`.'),
   ('MAR13_group30', 'ConwayErratum', 'group_30K', '',
    'Finite data showing the group of `30K` is exactly `60+12,15,20`.'),
   ('MAR13_group12', 'ConwayErratum', 'group_12E', '',
    'Finite data showing the group of `12E` is exactly `(24|2+12)^{↑1/4}`.')], []),
 ('MAR14', 'MAR-14: hidden symmetries of Co₀', ['ConwayMoonshine'],
  '''Power-map symmetries of `Co₀` (preserving element and centralizer orders) exchange 6 pairs of
classes with different Conway-moonshine series, so no power-map rule recovers Conway moonshine.''',
  [('MAR14', 'ConwayMoonshine', 'conway_hidden_symmetries', '',
    'Six power-map symmetries moving classes with different series.'),
   ('MAR14_no_rule', 'ConwayMoonshine', 'no_invariant_conway_rule', 'F hF',
    'No power-map-invariant rule reproduces `(a₁, a₂)`.'),
   ('MAR14_names', 'ConwayMoonshine', 'conway_witness_names', '', 'The six pairs.')], []),
 ('MAR15', 'MAR-15: Conway moonshine is not rigid', ['ConwayOdd', 'ConwayOddCount', 'ConwayOddRows'],
  '''On the 29 odd-order classes of `Co₀`, the MAR-9 hypotheses (genus-zero labels of level `2·o(g)`,
the power rule, vanishing of all coefficients to `q³⁹`, coherence of whole series) admit
**exactly 12** labellings. They agree with the published table except at `9A, 9B, 9C`, and the
published table is one of them. The series are kernel-certified for all 29 classes against their
frame shapes (`MAR15_rows`).''',
  [('MAR15', 'ConwayOddCount', 'conway_exactly_12', '',
    'Exactly 12 admissible labellings (verified exhaustive search).'),
   ('MAR15_two', 'ConwayOdd', 'conway_not_rigid', '',
    'In particular the published labelling and the one with `9B ↦ 18|3` both pass.'),
   ('MAR15_published', 'ConwayOddCount', 'oddTriples_spec', '',
    'The 12 are distinct, and the published labelling is one of them.'),
   ('MAR15_rows', 'ConwayOddRows', 'rows_all_certified', '',
    'All 29 series rows are certified against their frame shapes.'),
   ('MAR15_names', 'ConwayOdd', 'names_9', '', 'Class names and the published label of `9B`.')],
  []),
 ('MAR16', 'MAR-16: no squaring rule in Conway moonshine', ['ConwayPowers'],
  '''In Conway moonshine the group of `g²` is not a function of the group of `g`: there are 8 pairs of
classes with the same order, the same series (certified to `q³⁹`) and the same group, whose
squares have different groups. At odd primes, and in the Monster at every prime, the group of
`g^p` is a function of the group of `g`.''',
  [('MAR16', 'ConwayPowers', 'conway_not_functorial_at_2', '', 'The eight pairs.'),
   ('MAR16_no_rule', 'ConwayPowers', 'no_label_squaring_rule', '',
    'No map on group labels describes squaring.'),
   ('MAR16_odd', 'ConwayPowers', 'conway_functorial_odd', '',
    'Contrast: at odd primes such a map exists.'),
   ('MAR16_monster', 'ConwayPowers', 'monster_functorial', '',
    'Contrast: in the Monster it exists at every prime.'),
   ('MAR16_names', 'ConwayPowers', 'pair_names', '', 'The pairs and their squares.')], []),
 ('MAR17', 'MAR-17 (errata): misprints in published tables', ['Audit'],
  '''Errata of no mathematical consequence, recorded for readers of these tables; not results. In
Cummins–Matias (SIGMA 14 (2018) 060), Table 3, `46c` is printed as squaring to a non-existent
class `23c`, and `94b` as squaring to `47a` (it squares to `47b`). Duncan–Griffin–Ono
(arXiv:1411.6571) state that the Monster has 196 conjugacy classes; it has 194. All three are
present in the latest versions we could read.''',
  [('MAR17_46c', 'Audit', 'cm_46c', '', '`46C² = 23A`; there is no class `23C`.'),
   ('MAR17_94b', 'Audit', 'cm_94b', '', '`94B² = 47B`, not `47A`.'),
   ('MAR17_194', 'Audit', 'dgo_count', '', '194 classes, with 22 pairs of inverse classes.')], []),
]


def main():
    d = os.path.join(ROOT, 'MAR')
    os.makedirs(d, exist_ok=True)
    index = []
    for fname, title, modules, overview, thms, extra in RESULTS:
        opens = []
        for mod in modules:
            ns, op = namespace_and_opens(mod)
            for x in [ns] + op:
                if x not in opens:
                    opens.append(x)
        lines = ['import MonsterCN.' + m for m in modules]
        lines += ['', '/-!', '# ' + title, '', overview, '',
                  'Restated from `' + '`, `'.join('MonsterCN/%s.lean' % m for m in modules) +
                  '`, where the proofs are.', 'Generated by `tools/gen_mar_files.py`.', '-/']
        lines += ['', 'namespace MAR', '', 'open ' + ' '.join(opens), '']
        for new, mod, orig, args, doc in thms:
            ns, _ = namespace_and_opens(mod)
            sig = signature(mod, orig)
            lines.append('/-- ' + doc + ' -/')
            lines.append('theorem ' + new + ' ' + sig + ' :=')
            lines.append('  ' + ns + '.' + orig + ((' ' + args) if args else ''))
            lines.append('')
        if extra:
            lines += extra + ['']
        lines += ['end MAR', '']
        open(os.path.join(d, fname + '.lean'), 'w', encoding='utf8', newline='\n').write(
            '\n'.join(lines))
        index.append((fname, title, [t[0] for t in thms]))
    root = ['import MAR.' + f for f, _, _ in index] + ['', '/-!',
            '# Monster Assignment Rigidity (MAR): the results', '',
            'One file per result, `MAR/MARnn.lean`. Each restates the headline theorem(s) under the name',
            '`MAR.MARn…` and proves it by the implementation in `MonsterCN/`.', '']
    for fname, title, names in index:
        root.append('* `%s`: %s' % (fname, title))
        root.append('  (`%s`)' % '`, `'.join('MAR.' + n for n in names))
    root += ['-/', '']
    open(os.path.join(ROOT, 'MAR.lean'), 'w', encoding='utf8', newline='\n').write('\n'.join(root))
    print('wrote', len(index), 'files')


main()
