# Sources

| File | Content and origin |
|---|---|
| `ctomonst.tbl` | GAP Character Table Library (T. Breuer), version 1.3.11: tables `M`, `B`, `2.B` with power maps and characters. Distributed under the GNU GPL as part of that package. |
| `ctoconja.tbl` | Same library and version: tables `Co1` and `2.Co1`. Distributed under the GNU GPL. |
| `atlas_names.tsv` | Class names, element orders and centralizer orders of `M`, extracted from `ctomonst.tbl`. |
| `monster_cn_labels.tsv` | The Conway–Norton labels of the 194 classes, transcribed from Duncan–Griffin–Ono, *Moonshine*, Res. Math. Sci. 2 (2015), arXiv:1411.6571, App. A, and compared with Conway–Norton 1979, Table 2. |
| `baby_2B_table.tsv` | Per-class data for 2·𝔹 following Höhn (2003) and Cummins–Matias, SIGMA 14 (2018) 060, Table 3 (used only to locate candidate pairs; MAR-11/12 are proved from the character data). |
| `conway/` | Duncan–Mack-Crane, *The moonshine module for Conway's group*, Forum Math. Sigma 3 (2015) e10 (arXiv:1409.3829v2), Tables A.1 and A.2, transcribed with source line numbers (`conway/README.txt`). |

Correctness of these transcriptions is input (A1)/(A2) of the paper; the Lean kernel checks their
internal consistency (class equations, character norms and orthogonality, power maps against
element orders, the Conway–Norton power rule on all 194 × 15 pairs, frame shapes against χ₂₄).
