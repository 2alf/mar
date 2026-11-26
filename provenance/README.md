# Provenance of the Lean data files

The files in `MonsterCN/Data/` are Lean definitions of the data in `sources/`. They were generated
by the scripts in this folder. **Nothing in the verification depends on these scripts**: the
results are proved about the Lean definitions as they stand, and the kernel checks their internal
consistency. The scripts document how the definitions were obtained.

## Lean generators (`provenance/lean/`)

These produce literals for long kernel computations; each literal is proved equal, in the kernel,
to the computation it replaces, so the generators are not trusted. Run from the repository root
after `lake build`:

| Script | Output | Certified by |
|---|---|---|
| `gen_rigidity_domains.lean` | `MonsterCN/Data/RigidityDomains.lean` | `roundA1` … `roundE4` (`Rigidity.lean`) |
| `gen_aut_domains.lean` | `MonsterCN/Data/AutDomains.lean` | `around1` … `around3` (`Automorphisms.lean`) |
| `gen_gz_domains.lean` | `MonsterCN/Data/GZDomains.lean` | `gzRound0` … `gzRound4` (`GenusZero.lean`) |
| `gen_odd_root.lean` | `MonsterCN/Data/ConwayOddRoot.lean` | `oddRoot_eq` (`ConwayOddCount.lean`) |

Example: `lake env lean provenance/lean/gen_gz_domains.lean`.

## Python generators (`provenance/python/`)

Python 3, standard library only. They were run in the development repository, whose layout was
`data/` (these scripts and the files of `sources/`), `conway/` (the files of `sources/conway/`) and
`ogg/common.py`; to rerun them, recreate that layout.

| Script | Output |
|---|---|
| `gen_lean.py` (with `ctparse.py`, `names.py`) | `Atlas.lean`, `CNTable.lean` |
| `gen_catalogue.py` | `Catalogue.lean` |
| `gen_parents.py` (input `pmaps.json`, written by `names.py`) | `Parents.lean` |
| `co0_data.py`, `co0_frames.py`, `co0_tests2.py`, `co0_hidden.py` | JSON intermediates for `Co₀` |
| `gen_co0_lean.py`, `gen_conway_frames.py`, `gen_conway_odd.py` | `Conway.lean`, `ConwayFrames.lean`, `ConwayOdd.lean` |
| `baby_labels.py`, `baby_witness.py`, `baby_proj.py`, `gen_baby_lean.py` | `Baby.lean` |

Data with no generator in this folder, certified directly in the kernel:

* `Erratum.lean` (frame shapes of seven `Co₀` classes): `Erratum.frames_match_chi24`.
* `bbChi185` and `witnesses2` in `Baby.lean`: `Baby.chi185_norm` (norm 1 and degree 96256) and
  `Baby.hidden_moonshine_symmetries₂`.
* The table `gzTable` in `GenusZero.lean`: `GZ.gz_table_spec` (equal to the enumeration of all
  admissible labels).
* The series table in `Data/ConwayOdd.lean`: `ConwayOdd.rows_all_certified` (every row is the
  eta-quotient expansion of its frame shape).
* The table `fakeWDiffs` in `GenusZero.lean`: `GZ.fakeW_props`.
