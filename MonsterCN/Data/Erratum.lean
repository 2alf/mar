/-
# Frame shapes of the Co0 classes involved in the Duncan–Mack-Crane erratum
(AUTO-GENERATED; computed from `χ₂₄` on powers in `provenance/python/co0_frames.py`, re-checked in the kernel by
`MonsterCN.Erratum.frames_match_chi24`.)
-/
namespace MonsterCN.Erratum

def erratumClasses : List Nat := [73, 81, 82, 150, 145, 151, 37]
def frameOf : Nat → List (Nat × Int)
  | 73 => [(2, 2), (4, -4), (6, -2), (12, 4)]  -- 12E
  | 81 => [(1, 1), (2, 2), (3, 1), (4, -2), (12, 2)]  -- 12L
  | 82 => [(1, -1), (2, 3), (3, -1), (4, -2), (6, 1), (12, 2)]  -- 12M
  | 150 => [(2, 1), (3, 1), (5, 1), (6, -1), (10, -1), (30, 1)]  -- 30J
  | 145 => [(1, -1), (2, 2), (3, 1), (5, 1), (6, -2), (10, -2), (15, -1), (30, 2)]  -- 30G
  | 151 => [(2, 1), (3, -1), (5, -1), (30, 1)]  -- 30K
  | 37 => [(1, -1), (2, -1), (3, 3), (6, 3)]  -- 6M
  | _ => []
end MonsterCN.Erratum
