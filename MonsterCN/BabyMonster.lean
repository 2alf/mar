/-
# Baby Monster: hidden power-map symmetries move generalized moonshine (MAR, part IV)

Setting: Norton's generalized moonshine for the commuting pairs `(t, g)`, with `t ∈ 2A` and
`g ∈ C_M(t) = 2.B`. Höhn proved (preprint 2003) that `T_{t,g}(2τ) = q⁻¹ + 0 + H₁(g) q + …` is a
Hauptmodul, where `H₁ = χ₁ + χ₄₃₇₁` evaluated on the image of `g` in `B` (Höhn, Table 3).
Cummins–Matias (SIGMA 14 (2018) 060) reproduce the per-class assignment for all 247 classes.

**Result (MAR-11, `hidden_moonshine_symmetries`).** There are permutations of the 247 classes of
`2.B` that preserve element orders and centralizer orders and commute with all 11 prime power maps
(power-map symmetries), yet exchange classes whose series `T_{t,g}` differ already in the first
coefficient `H₁`. Six explicit witnesses are kernel-checked:
`8C↔8D`, `16A↔16B`, `24B↔24C`, `24D↔24E`, `40B↔40C`, `48A↔48B`.

**Corollary (MAR-12, `no_invariant_baby_rule`).** No rule computed from the power maps, element
orders and centralizer orders of `2.B` can reproduce the Baby Monster's generalized moonshine
functions, not even their first coefficient.

Only ctbllib data and Höhn's identification `H₁ = 1 + χ₄₃₇₁` are used. The moonshine labels
themselves are not needed, because the six pairs already differ in `χ₄₃₇₁`.
-/
import MonsterCN.Data.Baby

namespace MonsterCN.Baby

def ordB (c : Nat) : Nat := bbOrd.getD c 0
def centB (c : Nat) : Nat := bbCent.getD c 0
def pwB (p c : Nat) : Nat := (bbPmap p).getD c 0
def fusB (c : Nat) : Nat := bbFus.getD c 0
def nameB (c : Nat) : String := bbNames.getD c ""

/-- First coefficient of `T_{t,g}(2τ)`: `H₁(g) = 1 + χ₄₃₇₁(ḡ)`, `ḡ` the image of `g` in `B`. -/
def H1 (c : Nat) : Int := 1 + bChi2.getD (fusB c) 0

/-! ## Integrity of the transcribed data -/

theorem data_integrity :
    bbNames.length = 247 ∧ bbOrd.length = 247 ∧ bbCent.length = 247 ∧ bbFus.length = 247 ∧
    bChi2.length = 184 ∧ bChi2.getD 0 0 = 4371 ∧
    bbPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47] ∧
    bbPrimes.all (fun p => (bbPmap p).length == 247) = true ∧
    -- class equation of 2.B
    ((List.range 247).map fun c => centB 0 / centB c).sum = centB 0 ∧
    (List.range 247).all (fun c => centB 0 % centB c == 0) = true ∧
    -- orders consistent with power maps
    (List.range 247).all (fun c => bbPrimes.all fun p =>
      pwB p c < 247 && ordB (pwB p c) == ordB c / Nat.gcd (ordB c) p) = true ∧
    -- the fusion 2.B → B lands in the 184 classes of B
    (List.range 247).all (fun c => fusB c < 184) = true := by
  decide +kernel

/-! ## Power-map symmetries -/

/-- `π` is a power-map symmetry of `2.B`: a permutation of the 247 classes preserving element
orders and centralizer orders and commuting with all prime power maps. -/
def IsPowerAutB (π : Nat → Nat) : Prop :=
  (∀ c, c < 247 → π c < 247) ∧
  (∀ c, c < 247 → ∀ d, d < 247 → π c = π d → c = d) ∧
  (∀ c, c < 247 → ordB (π c) = ordB c ∧ centB (π c) = centB c) ∧
  (∀ c, c < 247 → ∀ p ∈ bbPrimes, π (pwB p c) = pwB p (π c))

def permOf (l : List Nat) (c : Nat) : Nat := l.getD c 0

/-- A linear-time checker for `IsPowerAutB (permOf l)` when `l` is an involution: `l` maps
`[0, 247)` into itself, `l ∘ l = id` there (which gives injectivity), and `l` preserves orders and
centralizer orders and commutes with the power maps. (Deciding the injectivity clause of
`IsPowerAutB` directly needs `247²` comparisons per witness and over 20 GB of kernel memory.) -/
def checkInvolAutB (l : List Nat) : Bool :=
  (List.range 247).all fun c =>
    decide (permOf l c < 247) && (permOf l (permOf l c) == c) &&
    (ordB (permOf l c) == ordB c) && (centB (permOf l c) == centB c) &&
    bbPrimes.all fun p => permOf l (pwB p c) == pwB p (permOf l c)

theorem isPowerAutB_of_check (l : List Nat) (h : checkInvolAutB l = true) :
    IsPowerAutB (permOf l) := by
  have H : ∀ c, c < 247 → permOf l c < 247 ∧ permOf l (permOf l c) = c ∧
      ordB (permOf l c) = ordB c ∧ centB (permOf l c) = centB c ∧
      ∀ p ∈ bbPrimes, permOf l (pwB p c) = pwB p (permOf l c) := by
    intro c hc
    have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    exact ⟨h1, h2, h3, h4, h5⟩
  refine ⟨fun c hc => (H c hc).1, fun c hc d hd e => ?_,
    fun c hc => ⟨(H c hc).2.2.1, (H c hc).2.2.2.1⟩, fun c hc p hp => (H c hc).2.2.2.2 p hp⟩
  rw [← (H c hc).2.1, ← (H d hd).2.1, e]

def wit (i : Nat) : Nat × Nat × List Nat := witnesses.getD i (0, 0, [])

theorem witness_names :
    (witnesses.map fun w => (nameB w.1, nameB w.2.1)) =
      [("8C", "8D"), ("16A", "16B"), ("24B", "24C"), ("24D", "24E"), ("40B", "40C"),
       ("48A", "48B")] := by
  decide +kernel

theorem wit_checks : (List.range 6).all (fun i => checkInvolAutB (wit i).2.2) = true := by
  decide +kernel

theorem wit_rest : (List.range 6).all (fun i => permOf (wit i).2.2 (wit i).1 == (wit i).2.1 &&
    decide ((wit i).1 < 247) && H1 (wit i).1 != H1 (wit i).2.1) = true := by
  decide +kernel

/-- **MAR-11.** Each witness is a power-map symmetry of `2.B` (preserving orders and centralizer
orders) exchanging two classes whose generalized moonshine functions differ in `H₁`. -/
theorem hidden_moonshine_symmetries : ∀ i, i < 6 →
    IsPowerAutB (permOf (wit i).2.2) ∧ permOf (wit i).2.2 (wit i).1 = (wit i).2.1 ∧
    (wit i).1 < 247 ∧ H1 (wit i).1 ≠ H1 (wit i).2.1 := by
  intro i hi
  refine ⟨isPowerAutB_of_check (wit i).2.2 ?_, ?_⟩
  · exact List.all_eq_true.mp wit_checks i (List.mem_range.mpr hi)
  · have h := List.all_eq_true.mp wit_rest i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

/-- The first coefficients at the six pairs (`8C/8D`: `8` vs `-8`, etc.). -/
theorem h1_values :
    (witnesses.map fun w => (H1 w.1, H1 w.2.1)) =
      [(8, -8), (4, -4), (-1, 1), (3, -3), (-2, 2), (1, -1)] := by
  decide +kernel

/-- **MAR-12 (impossibility).** If `F` is invariant under all power-map symmetries of `2.B`
(as is anything computed from power maps, orders and centralizer orders), then `F` differs from
the first generalized moonshine coefficient `H₁` somewhere. -/
theorem no_invariant_baby_rule (F : Nat → Int)
    (hF : ∀ π, IsPowerAutB π → ∀ c, c < 247 → F (π c) = F c) :
    ∃ c, c < 247 ∧ F c ≠ H1 c := by
  obtain ⟨hπ, hmap, hlt, hne⟩ := hidden_moonshine_symmetries 0 (by decide)
  have e := hF _ hπ _ hlt
  rw [hmap] at e
  by_cases h : F (wit 0).1 = H1 (wit 0).1
  · refine ⟨(wit 0).2.1, ?_, ?_⟩
    · have := hπ.1 _ hlt; rwa [hmap] at this
    · rw [e, h]; exact hne
  · exact ⟨(wit 0).1, hlt, h⟩

/-! ## The two pairs over a single class of `B` (second coefficient) -/

/-- Second coefficient of `T_{t,g}(2τ)`: `H₂ = χ₁₈₅` (Höhn, Table 3). -/
def H2 (c : Nat) : Int := bbChi185.getD c 0

/-- Sanity: `χ₁₈₅` has degree 96256 and norm 1 (`Σ |2.B|/|C(c)| · χ(c)² = |2.B|`). -/
theorem chi185_norm :
    bbChi185.length = 247 ∧ bbChi185.getD 0 0 = 96256 ∧
    ((List.range 247).map fun c => ((centB 0 / centB c : Nat) : Int) * H2 c * H2 c).sum =
      (centB 0 : Int) := by
  decide +kernel

def wit2 (i : Nat) : Nat × Nat × List Nat := witnesses2.getD i (0, 0, [])

theorem wit2_checks : (List.range 2).all (fun i => checkInvolAutB (wit2 i).2.2) = true := by
  decide +kernel

theorem wit2_rest : (List.range 2).all (fun i => permOf (wit2 i).2.2 (wit2 i).1 == (wit2 i).2.1 &&
    decide ((wit2 i).1 < 247) && H2 (wit2 i).1 != H2 (wit2 i).2.1) = true := by
  decide +kernel

/-- **MAR-11 (complete).** Two further power-map symmetries exchange `12X ↔ 12Y` and
`16H ↔ 16I`. Each pair lies over one class of `B`, so `H₁` agrees, but `H₂` differs (`6` vs `-6`,
`4` vs `-4`). Together with `hidden_moonshine_symmetries`, all 8 label-moving pairs are certified
from character-table data alone. -/
theorem hidden_moonshine_symmetries₂ : ∀ i, i < 2 →
    IsPowerAutB (permOf (wit2 i).2.2) ∧ permOf (wit2 i).2.2 (wit2 i).1 = (wit2 i).2.1 ∧
    (wit2 i).1 < 247 ∧ H2 (wit2 i).1 ≠ H2 (wit2 i).2.1 := by
  intro i hi
  refine ⟨isPowerAutB_of_check (wit2 i).2.2 ?_, ?_⟩
  · exact List.all_eq_true.mp wit2_checks i (List.mem_range.mpr hi)
  · have h := List.all_eq_true.mp wit2_rest i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

theorem witness2_names :
    (witnesses2.map fun w => (nameB w.1, nameB w.2.1, H2 w.1, H2 w.2.1)) =
      [("12X", "12Y", 6, -6), ("16H", "16I", 4, -4)] := by
  decide +kernel

end MonsterCN.Baby
