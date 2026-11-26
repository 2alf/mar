# Monster Assignment Rigidity (MAR) 
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24569482.svg)](https://doi.org/10.5281/zenodo.24569482)

Lean 4 formalization of the paper [*The Conway–Norton Table Is Forced: Monstrous Moonshine
Assignment Rigidity, Formally Verified*](https://zenodo.org/records/24569482).

**In one sentence:** for the published character-table data of the Monster, the Conway–Norton
moonshine table is the only assignment of genus-zero groups of the right shape that obeys Conway
and Norton's rule for powers and two simple conditions on the first moonshine coefficients, and
every one of these conditions is needed. /// **The Monster's moonshine table couldn't have been anything else.**



## A personal note

The existence of the Monster group was one of the first things in mathematics to catch my
attention, back in high school. Thanks to 3Blue1Brown (Grant Sanderson), whose videos first got me
interested in the topic back then. This project grew out of that interest.

## Contents

* [The result](#the-result)
* [The results, one file each](#the-results-one-file-each)
* [Scope: what is proved and what is an input](#scope-what-is-proved-and-what-is-an-input)
* [Verifying the proofs](#verifying-the-proofs)
* [Repository layout](#repository-layout)
* [The paper](#the-paper)
* [How to cite](#how-to-cite)
* [Declaration of generative AI and AI-assisted technologies](#declaration-of-generative-ai-and-ai-assisted-technologies)
* [Licences](#licences)

## The result

**Main theorem (MAR-9).** Allow each of the 194 conjugacy classes of the Monster any label `n|h+W`
of Conway–Norton shape whose modular curve has genus zero (385 candidates in all). Exactly one
assignment satisfies the Conway–Norton power rule, the vanishing of the first two McKay–Thompson
coefficients forced by the label, and coherence of the first coefficient: the Conway–Norton
table. No list of moonshine groups is used, and each condition is necessary (MAR-10). The same
conditions do not single out a table for the Baby Monster or for Conway moonshine (MAR-11 to
MAR-16).

Every result is a Lean theorem, with all finite computations checked by the Lean kernel
(`decide +kernel`). There is no `sorry`, no `native_decide`, and no added axiom; `#print axioms`
reports only `propext`, `Classical.choice` and `Quot.sound` for every result.

## The results, one file each

| Result | Statement | File |
|---|---|---|
| MAR-1 | Given the 171 Conway–Norton groups, the compatible tables that use every group are CN and CN∘σ, σ = (16B 16C)(32A 32B) | `MAR/MAR01.lean` |
| MAR-2 | σ preserves orders, centralizer orders and power maps; a₂(32A) ≠ a₂(32B) | `MAR/MAR02.lean` |
| MAR-3 | CN is unique given the catalogue and a₂-vanishing plus surjectivity or coherence | `MAR/MAR03.lean` |
| MAR-4 | Neither coefficient condition of MAR-3 can be dropped | `MAR/MAR04.lean` |
| MAR-5 | Exactly 8 compatible tables given the catalogue | `MAR/MAR05.lean` |
| MAR-6 | Power-map symmetries of the Monster move classes only within 24 explicit pairs | `MAR/MAR06.lean` |
| MAR-7 | No σ-invariant rule gives the twist h at both 32A and 32B | `MAR/MAR07.lean` |
| MAR-8 | Given the catalogue, the twist h is determined except at 32A, 32B | `MAR/MAR08.lean` |
| **MAR-9** | **The Conway–Norton table is the unique solution among the 385 genus-zero labels** | `MAR/MAR09.lean` |
| MAR-10 | Every condition of MAR-9 is necessary (explicit counterexamples) | `MAR/MAR10.lean` |
| MAR-10′ | The Atkin–Lehner part of the power rule is necessary | `MAR/MAR10b.lean` |
| MAR-11 | Power-map symmetries of 2·𝔹 swap classes with different generalized moonshine functions | `MAR/MAR11.lean` |
| MAR-12 | No power-map rule recovers Baby Monster moonshine | `MAR/MAR12.lean` |
| MAR-13 | Two inconsistent labels in Duncan–Mack-Crane's Conway-moonshine table (erratum) | `MAR/MAR13.lean` |
| MAR-14 | Power-map symmetries of Co₀ swap classes with different Conway-moonshine series | `MAR/MAR14.lean` |
| MAR-15 | Exactly 12 admissible tables on the odd-order classes of Co₀ | `MAR/MAR15.lean` |
| MAR-16 | In Conway moonshine the group of g² is not a function of the group of g | `MAR/MAR16.lean` |
| MAR-17 | Misprints in two published tables (errata) | `MAR/MAR17.lean` |

Each file explains its result in words and restates the theorems verbatim as `MAR.MARn…`, proved by
the implementation in `MonsterCN/`. Because `MAR` is part of the build, every restatement is
type-checked against its proof.

## Scope: what is proved and what is an input

The theorems are statements about explicit Lean objects: the class data and characters of the GAP
Character Table Library 1.3.11 (`sources/`), the transcribed Conway–Norton and Duncan–Mack-Crane
labels, and the function `genusZero` (the Riemann–Hurwitz formula with the classical count of
Atkin–Lehner fixed points). For these objects they are proved completely. Reading them as
statements about the Monster uses five standard facts that are not formalized (paper, Section 2.3):

* (A1) the library tables are the character tables of 𝕄, 2·𝔹 and Co₀;
* (A2) the transcribed labels are those of Conway–Norton and Duncan–Mack-Crane;
* (A3) the moonshine coefficients are given by the stated characters (V♮₂ = 1 + χ₂,
  V♮₃ = 1 + χ₂ + χ₃, and the analogues for 2·𝔹 and Co₀);
* (A4) `genusZero` decides correctly whether X₀(N)/W has genus zero;
* (A5) a genus-zero group has a unique normalized Hauptmodul, and a quotient of a genus-zero curve
  has genus zero.

The kernel checks the internal consistency of the data (class equations, character norms and
orthogonality, power maps against element orders, frame shapes against χ₂₄). The erratum MAR-13
also uses four classical theorems on eta quotients, stated in `MonsterCN/ConwayErratum.lean`.

## Verifying the proofs

Requirements: [elan](https://github.com/leanprover/elan), which installs Lean `v4.37.0-rc1` from
`lean-toolchain`, and 16 GB of RAM (no single `lean` process needs more than about 9 GB).

One step, with a per-process memory guard and an automatic check of the axiom report:

```
./verify.sh                                              # Linux / macOS
powershell -ExecutionPolicy Bypass -File .\verify.ps1     # Windows
```

By hand:

```
lake exe cache get                 # download the Mathlib build cache
lake build                         # build MonsterCN and MAR
lake env lean check_axioms.lean    # print the axioms of every result
```

A full build takes about 15–30 minutes on a desktop machine.

## Repository layout

```
MAR.lean, MAR/          one file per result (start here)
MonsterCN.lean          root of the implementation
MonsterCN/              the proofs (see below); MonsterCN/Data/ holds the data as Lean definitions
check_axioms.lean       #print axioms for every result
verify.sh, verify.ps1   build and axiom check with a memory guard
paper/mar.tex           the paper (LaTeX)
sources/                original inputs: GAP tables and label transcriptions (sources/README.md)
provenance/             scripts that generated the Lean data files (provenance/README.md)
tools/                  gen_mar_files.py (regenerates MAR/), check_tex.py (checks the LaTeX)
```

The modules of `MonsterCN/`:

| Module | Content |
|---|---|
| `Basic`, `Checks` | labels, the power rule, coefficients; consistency checks of the Monster data |
| `Rigidity` | MAR-1 to MAR-5 (the catalogue version) |
| `Automorphisms`, `Supplement` | MAR-6 to MAR-8; Le Bruyn's rule; the 73 element orders |
| `Ogg`, `GenusZero` | the genus formula; MAR-9, MAR-10, MAR-10′ |
| `Sharpness`, `NormalForm` | further counterexamples for MAR-10; uniqueness of the label normal form |
| `BabyMonster` | MAR-11, MAR-12 |
| `ConwayMoonshine`, `ConwayErratum` | MAR-13 (erratum), MAR-14 |
| `ConwayOdd`, `ConwayOddCount`, `ConwayOddRows` | MAR-15 (verified exhaustive search; certified series) |
| `ConwayPowers` | MAR-16 |
| `Audit` | MAR-17 (errata) |
| `Groups`, `Statement` | the groups Γ₀(n\|h); the per-class Hauptmodul statement (stated, not proved) |

## The paper

`paper/mar.tex` is a single amsart file with the bibliography included. Compile it with
`pdflatex mar.tex` (twice, for the cross-references) or upload it to Overleaf.
`python tools/check_tex.py` runs a few mechanical checks (balanced environments, defined citations
and references).

## How to cite

If you use or write about these notes or verification code, please credit the authors named on the
result and cite this source. For a specific result, please link to its proof or verification record
and cite the original paper. Please also cite xladn0.com when covering Andrej Alfirevic's work. If
author profiles would help readers, link to https://github.com/2alf.

Repository: https://github.com/2alf/mar. DOI: [10.5281/zenodo.24569482](https://doi.org/10.5281/zenodo.24569482). Citation metadata: `CITATION.cff`.

## Declaration of generative AI and AI-assisted technologies

During the preparation of this work the author used Claude (Anthropic), an AI system, to write most
of the Lean proofs and the verification code, to search the literature, and to draft the text of the
paper, under the author's direction. The correctness of the theorems does not depend on the AI:
every proof is checked by the Lean kernel, and all code, data and proofs are public. The author
reviewed the results and the text and takes full responsibility for the content.

## Licences

* Code (Lean files, scripts): Apache License 2.0, `LICENSE`.
* Paper, documentation and the transcriptions in `sources/`: Creative Commons Attribution 4.0,
  `LICENSE-CC-BY-4.0.txt`.
* `sources/ctomonst.tbl` and `sources/ctoconja.tbl` are files of the GAP Character Table Library by
  Thomas Breuer, distributed under the GNU General Public License as part of that package; they are
  not covered by the licences above. Mathlib is Apache-2.0.
