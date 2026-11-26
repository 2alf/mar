/-
# MAR-15: certification of the remaining two series rows (`1A`, `3A`)

`ConwayOdd.lean` certifies 27 of the 29 rows of the Conway-moonshine series table on odd-order
classes; the rows of `1A` (frame shape `1²⁴`) and `3A` (`3¹²/1¹²`) were too expensive for a single
kernel check. Here they are certified by the same division-free identity (`rowOK`), with the
eta products computed in separately checked pieces against explicit literals (the literals are
not trusted: each is proved equal to the product it stands for). With this, **all 29 rows** are
certified (`rows_all_certified`).
-/
import MonsterCN.ConwayOdd

namespace MonsterCN.ConwayOdd

open MonsterCN

/-- `∏ (1 - qⁿ)²⁴` to `q⁴⁰` (the frame of `1A`; Ramanujan `τ`). -/
def p0pos : List Int :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
   401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688, 18643272,
   21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840, -52843168,
   -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080, -145589976,
   408038400, 308120442]
/-- `∏ (1 - q²ⁿ)²⁴` to `q⁴⁰`. -/
def p0neg : List Int :=
  [1, 0, -24, 0, 252, 0, -1472, 0, 4830, 0, -6048, 0, -16744, 0, 84480, 0, -113643, 0, -115920,
   0, 534612, 0, -370944, 0, -577738, 0, 401856, 0, 1217160, 0, 987136, 0, -6905934, 0, 2727432,
   0, 10661420, 0, -7109760, 0, -4219488]
/-- `∏ (1 - q³ⁿ)¹² (1 - q²ⁿ)¹²` to `q⁴⁰` (the frame of `3A`). -/
def p6pos : List Int :=
  [1, 0, -12, -12, 54, 144, -34, -648, -747, 968, 3456, 2244, -5269, -11232, -4806, 13300, 24408,
   10008, -13442, -25488, -19119, -21416, -48060, -1332, 123695, 253584, 159534, -238920,
   -474660, -437976, 33714, 384264, 309978, 611952, 498960, 673236, -440660, -2261952, -1679556,
   -1009732, 2446686]
/-- `∏ (1 - qⁿ)¹² (1 - q⁶ⁿ)¹²` to `q⁴⁰`. -/
def p6neg : List Int :=
  [1, -12, 54, -88, -99, 540, -430, -504, -54, 1892, 2244, -10584, 4861, 11232, -4806, -10528,
   -24498, 73656, -20450, -78168, 51678, -10284, 138150, -213408, 19912, 212508, -276912, 339328,
   -378927, 58968, 118240, 61632, 696330, -1486320, 293184, 1091232, -184207, -1679556, 117126,
   2367664, 565695]
/-- Checkpoint: the first 10 factors of `p0pos`. -/
def chk10 : List Int :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370920, -578290,
   407352, 1187328, 1073224, -6964998, 2266512, 12228020, -8270592, -8162400, -3942912, 18628692,
   7401744, -29672621, 38525184, -23816340, -92492800, 71144586, 189262560, -21359872,
   -312769824, -177244992, 291206936, 391799112, -20382552, 272458278, -969340104, -1756513632,
   1326735680, 3119361474]
/-- Checkpoint: the first 20 factors of `p0pos`. -/
def chk20 : List Int :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
   401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830664, 18642720,
   21294456, -25529057, 13951800, -73338144, 24186248, 129973230, -30372672, -56786080,
   -187818528, 134707344, 151861824, -85109568, 192258288, -133546258, -372949440, -197206968,
   612295488, 341743290]
/-- Checkpoint: the first 30 factors of `p0pos`. -/
def chk30 : List Int :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
   401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688, 18643272,
   21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840, -52843168,
   -196706280, 134721672, 165747912, -80903352, 167368584, -182272378, -256335000, -144023376,
   406877568, 304177530]

def init0 : List Int := (List.range (PREC + 1)).map fun t => if t = 0 then 1 else 0

/-- `posProd` of a single factor `P_m^k`, unfolded (holds by definition, for all `m`, `k`). -/
theorem posProd_single (m k : Nat) : posProd [(m, k)] =
    (List.range (PREC / m)).foldl
      (fun s n => (List.range k).foldl (fun s _ => mulOneMinus s (m * (n + 1))) s) init0 := rfl

theorem frames_0_6 :
    ePos (frameShape 0) = [(1, 24)] ∧ eNeg (frameShape 0) = [(2, 24)] ∧
    ePos (frameShape 6) = [(3, 12), (2, 12)] ∧ eNeg (frameShape 6) = [(1, 12), (6, 12)] := by
  decide +kernel

theorem chunk1 : (List.range' 0 10).foldl
    (fun s n => (List.range 24).foldl (fun s _ => mulOneMinus s (1 * (n + 1))) s) init0 = chk10 := by
  decide +kernel
theorem chunk2 : (List.range' 10 10).foldl
    (fun s n => (List.range 24).foldl (fun s _ => mulOneMinus s (1 * (n + 1))) s) chk10 = chk20 := by
  decide +kernel
theorem chunk3 : (List.range' 20 10).foldl
    (fun s n => (List.range 24).foldl (fun s _ => mulOneMinus s (1 * (n + 1))) s) chk20 = chk30 := by
  decide +kernel
theorem chunk4 : (List.range' 30 10).foldl
    (fun s n => (List.range 24).foldl (fun s _ => mulOneMinus s (1 * (n + 1))) s) chk30 = p0pos := by
  decide +kernel

/-- The `1A` product, in four separately checked chunks of 10 factors. -/
theorem p0pos_eq : posProd (ePos (frameShape 0)) = p0pos := by
  have hr : List.range (PREC / 1) = List.range' 0 10 ++ List.range' 10 10 ++ List.range' 20 10 ++
      List.range' 30 10 := by decide
  rw [frames_0_6.1, posProd_single, hr, List.foldl_append, List.foldl_append, List.foldl_append,
    chunk1, chunk2, chunk3, chunk4]

theorem p0neg_eq : posProd (eNeg (frameShape 0)) = p0neg := by decide +kernel
theorem p6pos_eq : posProd (ePos (frameShape 6)) = p6pos := by decide +kernel
theorem p6neg_eq : posProd (eNeg (frameShape 6)) = p6neg := by decide +kernel

theorem row_0 : rowOK 0 = true := by
  unfold rowOK
  dsimp only
  rw [p0pos_eq, p0neg_eq]
  decide +kernel

theorem row_6 : rowOK 6 = true := by
  unfold rowOK
  dsimp only
  rw [p6pos_eq, p6neg_eq]
  decide +kernel

/-- **All 29 rows** of the series table on odd-order classes are certified against their frame
shapes. -/
theorem rows_all_certified : ∀ c ∈ oddClasses, rowOK c = true := by
  intro c hc
  by_cases h0 : c = 0
  · subst h0; exact row_0
  by_cases h6 : c = 6
  · subst h6; exact row_6
  apply rows_certified
  rw [← t2_table_spec.2, List.mem_filter]
  exact ⟨hc, by simp [h0, h6]⟩

end MonsterCN.ConwayOdd
