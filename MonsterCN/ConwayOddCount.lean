/-
# MAR-15, exact count: exactly 12 admissible labellings of the odd-order classes of `Co₀`

`ConwayOdd.lean` shows that the hypotheses of the MAR method admit at least two labellings of the
29 odd-order classes of `Co₀` (`conway_not_rigid`). Here we prove that they admit **exactly 12**,
all equal to the published labelling except at `9A`, `9B`, `9C`.

Method: verified search. `OInv D L` says that the labelling `L` lies in the domains `D`. Every
admissible labelling lies in the initial domains (`oInit_sound`); propagation (`ostep_sound`) and
case splits (`restrictO_sound`) preserve this, so `search_sound` shows that every admissible
labelling lies in one of the leaves of `search`. The kernel evaluates the search: it has exactly
12 leaves, each a singleton domain at every odd-order class, and they are the 12 labellings
`oddSol t` for `t ∈ oddTriples` (`search_spec`). Conversely, each of the 12 is admissible
(`oddTriples_admissible`).
-/
import MonsterCN.ConwayOdd
import MonsterCN.Data.ConwayOddRoot

namespace MonsterCN.ConwayOdd

open MonsterCN MonsterCN.Conway MonsterCN.GZ

/-- Domains: a list of candidate labels for each of the 167 classes. -/
abbrev ODom := List (List CNLabel)

/-- The vanishing condition of `admissible` at class `c`. -/
def vanC (c : Nat) (l : CNLabel) : Bool :=
  (List.range 39).all fun i => let m := i + 1; (m + 1) % l.h == 0 || (ser c).getD (m + 1) 0 == 0

/-- The power edge `g ↦ g^p`: at `p = 2` the label is unchanged, at odd `p` the power rule. -/
def edge (p : Nat) (l : CNLabel) : CNLabel := if p = 2 then l else powRule l p

/-- `L` lies in the domains `D` at every odd-order class. -/
def OInv (D : ODom) (L : Nat → CNLabel) : Prop := ∀ c ∈ oddClasses, L c ∈ D.getD c []

/-- Initial domains: admissible genus-zero labels of level `2·o(g)` passing the vanishing test. -/
def oInit : ODom := (List.range 167).map fun c =>
  if oddClasses.contains c then (candidates (2 * ordC c)).filter (vanC c) else []

/-- Arc-consistency test: power edges in both directions, and coherence against fixed classes. -/
def okeep (D : ODom) (c : Nat) (l : CNLabel) : Bool :=
  (coPrimes.all fun p => (D.getD (pwC p c) []).contains (edge p l)) &&
  (oddClasses.all fun d => coPrimes.all fun p =>
    !(pwC p d == c) || (D.getD d []).any fun l' => edge p l' == l) &&
  (oddClasses.all fun d => !(D.getD d [] == [l]) || ser c == ser d)

def ostep (D : ODom) : ODom := (List.range 167).map fun c => (D.getD c []).filter (okeep D c)

/-- Case split: fix the label of `c₀`. -/
def restrictO (D : ODom) (c₀ : Nat) (l₀ : CNLabel) : ODom :=
  (List.range 167).map fun c => if c == c₀ then [l₀] else D.getD c []

/-- Propagate until nothing changes (at most `k` rounds). -/
def fixp : Nat → ODom → ODom
  | 0, D => D
  | k + 1, D => if ostep D == D then D else fixp k (ostep D)

/-- Backtracking search: propagate; fail on an empty domain; stop when all domains are
singletons; otherwise split on the first ambiguous class. -/
def search : Nat → ODom → List ODom
  | 0, D => [D]
  | k + 1, D =>
    if oddClasses.any (fun c => (fixp 6 D).getD c [] == []) then [] else
    match oddClasses.find? (fun c => ((fixp 6 D).getD c []).length > 1) with
    | none => [fixp 6 D]
    | some c => ((fixp 6 D).getD c []).flatMap fun l => search k (restrictO (fixp 6 D) c l)

/-! ## Soundness -/

theorem odd_lt : ∀ c ∈ oddClasses, c < 167 := by decide

theorem odd_closed : ∀ c ∈ oddClasses, ∀ p ∈ coPrimes, pwC p c ∈ oddClasses := by
  decide +kernel

theorem getD_range_map {f : Nat → List CNLabel} {c : Nat} (hc : c < 167) :
    ((List.range 167).map f).getD c [] = f c := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]

theorem isGZb_spec {l : CNLabel} (h : isGZb l = true) : IsGZ l := by
  unfold isGZb at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨List.contains_iff_mem.mp h1, h2, h3, h4, h5⟩

/-- What `admissible` says, as propositions. -/
theorem adm_facts {L : Nat → CNLabel} (h : admissible L = true) :
    (∀ c ∈ oddClasses, isGZb (L c) = true ∧ (L c).n = 2 * ordC c ∧
      (∀ p ∈ coPrimes, L (pwC p c) = edge p (L c)) ∧ vanC c (L c) = true) ∧
    (∀ c ∈ oddClasses, ∀ d ∈ oddClasses, L c = L d → ser c = ser d) := by
  unfold admissible at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c hc => ?_, fun c hc d hd e => ?_⟩
  · have hc1 := h1 c hc
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc1
    obtain ⟨⟨⟨hg, hn⟩, hp⟩, hv⟩ := hc1
    refine ⟨hg, beq_iff_eq.mp hn, fun p hpm => ?_, hv⟩
    have hpp := List.all_eq_true.mp hp p hpm
    unfold edge
    by_cases h2' : p = 2
    · subst h2'
      simp only [ite_true] at hpp ⊢
      exact beq_iff_eq.mp hpp
    · simp only [h2', ite_false] at hpp ⊢
      exact beq_iff_eq.mp hpp
  · have hcd := List.all_eq_true.mp (h2 c hc) d hd
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hcd
    exact hcd.resolve_left (fun hne => hne e)

theorem oInit_sound {L : Nat → CNLabel} (h : admissible L = true) : OInv oInit L := by
  intro c hc
  obtain ⟨hf, -⟩ := adm_facts h
  obtain ⟨hg, hn, -, hv⟩ := hf c hc
  unfold oInit
  rw [getD_range_map (odd_lt c hc)]
  have hcon : oddClasses.contains c = true := List.contains_iff_mem.mpr hc
  rw [ite_eq_left_iff.mpr (fun hn => absurd hcon hn), List.mem_filter]
  refine ⟨?_, hv⟩
  have hm := mem_candidates (L c) (isGZb_spec hg)
  rwa [hn] at hm

theorem ostep_sound {L : Nat → CNLabel} {D : ODom} (h : admissible L = true) (hI : OInv D L) :
    OInv (ostep D) L := by
  obtain ⟨hf, hcoh⟩ := adm_facts h
  intro c hc
  unfold ostep
  rw [getD_range_map (odd_lt c hc), List.mem_filter]
  refine ⟨hI c hc, ?_⟩
  unfold okeep
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun p hp => ?_, fun d hd p hp => ?_⟩, fun d hd => ?_⟩
  · rw [← (hf c hc).2.2.1 p hp]
    exact List.contains_iff_mem.mpr (hI _ (odd_closed c hc p hp))
  · by_cases e : pwC p d = c
    · have hany : (D.getD d []).any (fun l' => edge p l' == L c) = true := by
        refine List.any_eq_true.mpr ⟨L d, hI d hd, ?_⟩
        rw [← (hf d hd).2.2.1 p hp, e]
        exact beq_self_eq_true _
      rw [hany, Bool.or_true]
    · rw [beq_eq_false_iff_ne.mpr e]
      rfl
  · by_cases e : D.getD d [] = [L c]
    · have hmem := hI d hd
      rw [e, List.mem_singleton] at hmem
      have hs := hcoh c hc d hd hmem.symm
      rw [beq_iff_eq.mpr hs, Bool.or_true]
    · rw [beq_eq_false_iff_ne.mpr e]
      rfl

theorem restrictO_sound {L : Nat → CNLabel} {D : ODom} {c₀ : Nat} {l₀ : CNLabel}
    (hI : OInv D L) (h : L c₀ = l₀) : OInv (restrictO D c₀ l₀) L := by
  intro c hc
  unfold restrictO
  rw [getD_range_map (odd_lt c hc)]
  by_cases e : c = c₀
  · subst e
    simp [h]
  · simp only [beq_iff_eq, e, ite_false]
    exact hI c hc

theorem fixp_sound {L : Nat → CNLabel} (h : admissible L = true) :
    ∀ k D, OInv D L → OInv (fixp k D) L
  | 0, _, hI => hI
  | k + 1, D, hI => by
    unfold fixp
    split
    · exact hI
    · exact fixp_sound h k _ (ostep_sound h hI)

theorem search_sound {L : Nat → CNLabel} (h : admissible L = true) :
    ∀ k D, OInv D L → ∃ R ∈ search k D, OInv R L
  | 0, D, hI => ⟨D, List.mem_singleton_self _, hI⟩
  | k + 1, D, hI => by
    have hI' := fixp_sound h 6 D hI
    unfold search
    split
    · rename_i hany
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hany
      have hm := hI' c hc
      rw [beq_iff_eq.mp he] at hm
      simp at hm
    · split
      · exact ⟨_, List.mem_singleton_self _, hI'⟩
      · rename_i c hfind
        have hc : c ∈ oddClasses := List.mem_of_find?_eq_some hfind
        obtain ⟨R, hR, hRI⟩ := search_sound h k _ (restrictO_sound hI' (rfl : L c = L c))
        exact ⟨R, List.mem_flatMap.mpr ⟨L c, hI' c hc, hR⟩, hRI⟩

/-! ## The twelve labellings -/

/-- The labelling equal to the published one except at `9A`, `9B`, `9C` (classes 54, 56, 58). -/
def oddSol (t : CNLabel × CNLabel × CNLabel) (c : Nat) : CNLabel :=
  if c = 54 then t.1 else if c = 56 then t.2.1 else if c = 58 then t.2.2 else dmcOdd c

/-- The labels at `9A`, `9B`, `9C` of the 12 admissible labellings (`18-`, `18+9`, `18+18`,
`18|3`). -/
def oddTriples : List (CNLabel × CNLabel × CNLabel) :=
  [(⟨18, 1, [1]⟩, ⟨18, 1, [1, 9]⟩, ⟨18, 1, [1, 18]⟩), (⟨18, 1, [1]⟩, ⟨18, 1, [1, 18]⟩, ⟨18, 1, [1, 9]⟩),
   (⟨18, 1, [1]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1, 9]⟩), (⟨18, 1, [1]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1, 18]⟩),
   (⟨18, 1, [1, 9]⟩, ⟨18, 1, [1]⟩, ⟨18, 1, [1, 18]⟩), (⟨18, 1, [1, 9]⟩, ⟨18, 1, [1, 18]⟩, ⟨18, 1, [1]⟩),
   (⟨18, 1, [1, 9]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1]⟩), (⟨18, 1, [1, 9]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1, 18]⟩),
   (⟨18, 1, [1, 18]⟩, ⟨18, 1, [1]⟩, ⟨18, 1, [1, 9]⟩), (⟨18, 1, [1, 18]⟩, ⟨18, 1, [1, 9]⟩, ⟨18, 1, [1]⟩),
   (⟨18, 1, [1, 18]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1]⟩), (⟨18, 1, [1, 18]⟩, ⟨18, 3, [1]⟩, ⟨18, 1, [1, 9]⟩)]

/-- A leaf is good if it is the singleton domain of one of the 12 labellings. -/
def leafOK (R : ODom) : Bool :=
  oddTriples.any fun t => oddClasses.all fun c => R.getD c [] == [oddSol t c]

/-- One level of the search, taken apart, so that its branches can be checked separately. -/
theorem search_split {D : ODom} {k c : Nat} {P : ODom → Bool}
    (h0 : oddClasses.any (fun c => (fixp 6 D).getD c [] == []) = false)
    (h1 : oddClasses.find? (fun c => ((fixp 6 D).getD c []).length > 1) = some c)
    (h2 : ((fixp 6 D).getD c []).all (fun l => (search k (restrictO (fixp 6 D) c l)).all P) = true) :
    (search (k + 1) D).all P = true := by
  unfold search
  rw [h0, h1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [List.all_flatMap]
  exact h2

/-- The root of the search: propagation from the initial domains, certified against the literal
`oddRoot` (`Data/ConwayOddRoot.lean`). -/
theorem oddRoot_eq : fixp 6 oInit = oddRoot := by decide +kernel

theorem root_facts :
    oddClasses.any (fun c => (fixp 6 oddRoot).getD c [] == []) = false ∧
    oddClasses.find? (fun c => ((fixp 6 oddRoot).getD c []).length > 1) = some 0 ∧
    (fixp 6 oddRoot).getD 0 [] = [⟨2, 1, [1]⟩, ⟨2, 1, [1, 2]⟩] := by
  decide +kernel

/-- First branch of the search (class `1A` labelled `2-`). -/
theorem branch_1 : (search 29 (restrictO (fixp 6 oddRoot) 0 ⟨2, 1, [1]⟩)).all leafOK = true := by
  decide +kernel

/-- Second branch of the search (class `1A` labelled `2+`). -/
theorem branch_2 : (search 29 (restrictO (fixp 6 oddRoot) 0 ⟨2, 1, [1, 2]⟩)).all leafOK = true := by
  decide +kernel

/-- Every leaf of the search is one of the 12 labellings. -/
theorem search_spec : (search 30 oddRoot).all leafOK = true := by
  obtain ⟨h0, h1, h2⟩ := root_facts
  refine search_split h0 h1 ?_
  rw [h2]
  simp only [List.all_cons, List.all_nil, Bool.and_true, branch_1, branch_2]

set_option maxRecDepth 100000 in
/-- Each of the 12 labellings is admissible. -/
theorem oddTriples_admissible : oddTriples.all (fun t => admissible (oddSol t)) = true := by
  decide +kernel

theorem oddTriples_spec : oddTriples.length = 12 ∧ oddTriples.Nodup ∧
    (dmcOdd 54, dmcOdd 56, dmcOdd 58) ∈ oddTriples := by
  decide +kernel

/-- **MAR-15 (exact count).** A labelling of the odd-order classes of `Co₀` satisfies all the
hypotheses of the MAR method (`admissible`) if and only if it agrees on these classes with one of
the 12 labellings `oddSol t`, `t ∈ oddTriples`; these are pairwise distinct (they differ at `9A`,
`9B` or `9C`), and the published labelling is one of them. -/
theorem conway_exactly_12 :
    (∀ L : Nat → CNLabel, admissible L = true →
      ∃ t ∈ oddTriples, ∀ c ∈ oddClasses, L c = oddSol t c) ∧
    (∀ t ∈ oddTriples, admissible (oddSol t) = true) ∧
    oddTriples.length = 12 ∧ oddTriples.Nodup := by
  refine ⟨fun L hL => ?_, fun t ht => List.all_eq_true.mp oddTriples_admissible t ht,
    oddTriples_spec.1, oddTriples_spec.2.1⟩
  have hroot : OInv oddRoot L := oddRoot_eq ▸ fixp_sound hL 6 oInit (oInit_sound hL)
  obtain ⟨R, hR, hRI⟩ := search_sound hL 30 oddRoot hroot
  obtain ⟨t, ht, hall⟩ := List.any_eq_true.mp (List.all_eq_true.mp search_spec R hR)
  refine ⟨t, ht, fun c hc => ?_⟩
  have he := beq_iff_eq.mp (List.all_eq_true.mp hall c hc)
  have hm := hRI c hc
  rw [he, List.mem_singleton] at hm
  exact hm

end MonsterCN.ConwayOdd
