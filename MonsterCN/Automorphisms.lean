/-
# Symmetries of the Monster's power-map data (MAR, part II)

**Question.** Which relabellings of the 194 Monster classes are invisible to the ATLAS power maps
and element orders? Any such symmetry limits what *any* power-map-based reconstruction of the
moonshine assignment (Conway–Norton 1979 §6; Le Bruyn 2018, arXiv:1804.04127) can achieve.

**Results (kernel-checked; no `native_decide`, no new axioms).**
* `powerAut_classification`: every power-map automorphism moves each class at most to its
  partner in one of 24 explicit pairs: 22 algebraically conjugate pairs (`23A/B`, …,
  `119A/B`) and the two pairs `16B/16C`, `32A/32B` of `σ`.
* `galois_pairs_invisible`: on the 22 Galois pairs the characters `χ₂, χ₃, χ₄` and the moonshine
  labels agree; `sigma_pairs_visible`: on `σ`'s pairs `χ₂` differs.
  So among the 24 pairs, only the two pairs of `σ` are separated by `χ₂, χ₃, χ₄`.
* `label_of_powerAut`: for every power-map automorphism `π`, `cn ∘ π` is `cn` or the twist
  (a direct corollary of MAR-1, `compatible_surj_iff`).
* `no_invariant_h_rule`: **impossibility** — no rule computed from power maps and orders
  (i.e. invariant under all power-map automorphisms) can return the Conway–Norton `h` at both
  `32A` (h = 1) and `32B` (h = 2).
* `lebruyn_exceptions`: Le Bruyn's Theorem 2 rule, evaluated on the ATLAS data, fails at exactly
  14 classes (his "12 counterexamples", with 40C/D and 88A/B merged).
* `thread_determined_by_compat`: with the 171-group catalogue (MAR's `Compat`), the thread `h`
  is determined at every class except `32A, 32B` — the optimum allowed by `no_invariant_h_rule`.
-/
import MonsterCN.Rigidity
import MonsterCN.Data.AutDomains

namespace MonsterCN

/-! ## Power-map automorphisms -/

/-- `π` is a power-map automorphism: a permutation of the 194 classes preserving element orders
and commuting with all 15 prime power maps. -/
def IsPowerAut (π : Nat → Nat) : Prop :=
  (∀ c, c < 194 → π c < 194) ∧
  (∀ c, c < 194 → ∀ d, d < 194 → π c = π d → c = d) ∧
  (∀ d, d < 194 → ∃ c, c < 194 ∧ π c = d) ∧
  (∀ c, c < 194 → ordOf (π c) = ordOf c) ∧
  (∀ c, c < 194 → ∀ p ∈ monsterPrimes, π (pw p c) = pw p (π c))

/-- The 24 pairs (class indices). -/
def autPairs : List (Nat × Nat) :=
  [(54, 55), (75, 76), (104, 105), (106, 107), (120, 121), (124, 125), (131, 132), (134, 135),
   (136, 137), (138, 139), (148, 149), (151, 152), (159, 160), (164, 165), (168, 169), (171, 172),
   (176, 177), (178, 179), (180, 181), (182, 183), (184, 185), (186, 187), (188, 189), (192, 193)]

/-- The 22 pairs of algebraically conjugate classes (all pairs except `σ`'s). -/
def galoisPairs : List (Nat × Nat) := autPairs.filter fun q => q != (54, 55) && q != (106, 107)

theorem autPairs_names :
    autPairs.map (fun q => (nameOf q.1, nameOf q.2)) =
      [("16B", "16C"), ("23A", "23B"), ("31A", "31B"), ("32A", "32B"), ("39C", "39D"),
       ("40C", "40D"), ("44A", "44B"), ("46A", "46B"), ("46C", "46D"), ("47A", "47B"),
       ("56B", "56C"), ("59A", "59B"), ("62A", "62B"), ("69A", "69B"), ("71A", "71B"),
       ("78B", "78C"), ("87A", "87B"), ("88A", "88B"), ("92A", "92B"), ("93A", "93B"),
       ("94A", "94B"), ("95A", "95B"), ("104A", "104B"), ("119A", "119B")] := by
  decide +kernel

/-- On the 22 Galois pairs, `χ₂, χ₃, χ₄`, centralizer orders and the moonshine labels agree. -/
theorem galois_pairs_invisible :
    galoisPairs.length = 22 ∧
    galoisPairs.all (fun q => chi2.getD q.1 0 == chi2.getD q.2 0 &&
      chi3.getD q.1 0 == chi3.getD q.2 0 && chi4.getD q.1 0 == chi4.getD q.2 0 &&
      centOf q.1 == centOf q.2 && cn q.1 == cn q.2) = true := by
  decide +kernel

/-- On `σ`'s pairs the centralizer orders agree but `χ₂` (hence `a₁`) or `χ₃` differ. -/
theorem sigma_pairs_visible :
    centOf 54 = centOf 55 ∧ chi2.getD 54 0 = -1 ∧ chi2.getD 55 0 = 7 ∧
    centOf 106 = centOf 107 ∧ chi3.getD 106 0 = 2 ∧ chi3.getD 107 0 = -2 := by
  decide +kernel

/-! ### Verified propagation for automorphisms -/

abbrev ADom := List (List Nat)

def AInv (D : ADom) (π : Nat → Nat) : Prop := ∀ c, c < 194 → π c ∈ D.getD c []

def ainit : ADom := classes.map fun c => classes.filter fun d => ordOf d == ordOf c

def akeep (D : ADom) (c d : Nat) : Bool :=
  (monsterPrimes.all fun p => (D.getD (pw p c) []).contains (pw p d)) &&
  ((parentsTbl.getD c []).all fun ep =>
      !(decide (ep.1 < 194) && monsterPrimes.contains ep.2 && pw ep.2 ep.1 == c) ||
      (D.getD ep.1 []).any fun x => pw ep.2 x == d)

def astage1 (D : ADom) : ADom := classes.map fun c => (D.getD c []).filter (akeep D c)

/-- Injectivity: a value forced at another class is removed. -/
def astage2 (E : ADom) : ADom := classes.map fun c => (E.getD c []).filter fun d =>
  !(classes.any fun c₂ => c₂ != c && E.getD c₂ [] == [d])

/-- Surjectivity: a value (`< 194`) that only `c` can take is taken by `c`. -/
def asole (F : ADom) (c d : Nat) : Bool :=
  decide (d < 194) && classes.all fun c₂ => c₂ == c || !(F.getD c₂ []).contains d

def astage3 (F : ADom) : ADom := classes.map fun c =>
  match (F.getD c []).find? (asole F c) with
  | some d => [d]
  | none => F.getD c []

def astep (D : ADom) : ADom := astage3 (astage2 (astage1 D))

def aiter : Nat → ADom → ADom
  | 0, D => D
  | k + 1, D => aiter k (astep D)

theorem getD_classes_map' {f : Nat → List Nat} {c : Nat} (hc : c < 194) :
    (classes.map f).getD c [] = f c := by
  simp [classes, numClasses, List.getD_eq_getElem?_getD, List.getElem?_range hc]

theorem ainit_sound {π} (h : IsPowerAut π) : AInv ainit π := by
  intro c hc
  obtain ⟨hlt, -, -, hord, -⟩ := h
  rw [ainit, getD_classes_map' hc, List.mem_filter]
  refine ⟨by simpa [classes, numClasses] using hlt c hc, by simp [hord c hc]⟩

theorem astage1_sound {π D} (h : IsPowerAut π) (hI : AInv D π) : AInv (astage1 D) π := by
  obtain ⟨-, -, -, -, hpow⟩ := h
  intro c hc
  rw [astage1, getD_classes_map' hc, List.mem_filter]
  refine ⟨hI c hc, ?_⟩
  simp only [akeep, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun ep _ => ?_⟩
  · rw [← hpow c hc p hp]
    simpa using hI _ (pw_lt c hc p hp)
  · by_cases hq : (decide (ep.1 < 194) && monsterPrimes.contains ep.2 && pw ep.2 ep.1 == c) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at hq
      obtain ⟨⟨he, hp⟩, hpc⟩ := hq
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq]
      refine Or.inr ⟨π ep.1, hI _ he, ?_⟩
      rw [← hpow ep.1 he ep.2 hp, hpc]
    · simp only [Bool.not_eq_true] at hq
      rw [hq]; rfl

theorem astage2_sound {π E} (h : IsPowerAut π) (hI : AInv E π) : AInv (astage2 E) π := by
  obtain ⟨-, hinj, -, -, -⟩ := h
  intro c hc
  rw [astage2, getD_classes_map' hc, List.mem_filter]
  refine ⟨hI c hc, ?_⟩
  rw [Bool.not_eq_true', List.any_eq_false]
  intro c₂ hc₂ hq
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hq
  obtain ⟨hne, hsing⟩ := hq
  have hc₂' : c₂ < 194 := by simpa [classes, numClasses] using hc₂
  have := hI c₂ hc₂'
  rw [hsing, List.mem_singleton] at this
  exact hne (hinj c₂ hc₂' c hc this)

theorem astage3_sound {π F} (h : IsPowerAut π) (hI : AInv F π) : AInv (astage3 F) π := by
  obtain ⟨-, -, hsurj, -, -⟩ := h
  intro c hc
  rw [astage3, getD_classes_map' hc]
  split
  · next d hd =>
    have hsole := List.find?_some hd
    simp only [asole, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at hsole
    obtain ⟨hd194, hall⟩ := hsole
    obtain ⟨c', hc', hπc'⟩ := hsurj d hd194
    have hc'mem : c' ∈ classes := by simpa [classes, numClasses] using hc'
    rcases hall c' hc'mem with h | h
    · subst h; simp [hπc']
    · have hm := hI c' hc'
      rw [hπc'] at hm
      have h2 : (F.getD c' []).contains d = true := List.contains_iff_mem.mpr hm
      rw [h] at h2; exact absurd h2 (by decide)
  · exact hI c hc

theorem astep_sound {π D} (h : IsPowerAut π) (hI : AInv D π) : AInv (astep D) π :=
  astage3_sound h (astage2_sound h (astage1_sound h hI))

theorem aiter_sound {π} (h : IsPowerAut π) : ∀ k D, AInv D π → AInv (aiter k D) π
  | 0, _, hI => hI
  | k + 1, D, hI => aiter_sound h k (astep D) (astep_sound h hI)

/-- The partner of `c` in `autPairs` (or `c` itself). -/
def partner (c : Nat) : Nat :=
  match autPairs.find? (fun q => q.1 == c || q.2 == c) with
  | some q => if q.1 == c then q.2 else q.1
  | none => c

/-! Each propagation round is certified separately against an explicit literal
(`Data/AutDomains.lean`, generated by `provenance/lean/gen_aut_domains.lean`), to keep kernel memory low. -/

theorem around1 : astep ainit = AutDom.autD1 := by decide +kernel
theorem around2 : astep AutDom.autD1 = AutDom.autD2 := by decide +kernel
theorem around3 : astep AutDom.autD2 = AutDom.autD3 := by decide +kernel

theorem aiter_eq : aiter 3 ainit = AutDom.autD3 := by
  show astep (astep (astep ainit)) = _
  rw [around1, around2, around3]

/-- After three propagation rounds every domain is contained in `{c, partner c}`. -/
theorem aiter_pairs :
    classes.all (fun c => ((aiter 3 ainit).getD c []).all fun d => d == c || d == partner c) = true := by
  rw [aiter_eq]
  decide +kernel

/-- **Classification of power-map automorphisms.** Every permutation of the Monster classes
preserving element orders and commuting with the 15 prime power maps fixes every class or
exchanges it with its partner in one of the 24 pairs `autPairs`. -/
theorem powerAut_classification {π : Nat → Nat} (h : IsPowerAut π) :
    ∀ c, c < 194 → π c = c ∨ π c = partner c := by
  intro c hc
  have hm := aiter_sound h 3 ainit (ainit_sound h) c hc
  have hall := aiter_pairs
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hall
  exact hall c (by simpa [classes, numClasses] using hc) (π c) hm

/-! ## `σ` is a power-map automorphism -/

theorem sigma_isPowerAut : IsPowerAut sigma := by
  have hinv : ∀ c, c < 194 → sigma (sigma c) = c := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro c hc d hd e
    rw [← hinv c hc, ← hinv d hd, e]
  · intro d hd
    refine ⟨sigma d, ?_, ?_⟩
    · revert d; decide +kernel
    · revert d hd; decide +kernel
  · intro c hc; exact (sigma_automorphism.2.1 c hc).1
  · intro c hc p hp; exact (sigma_automorphism.1 c hc p hp).symm

/-! ## Labels under automorphisms (corollary of MAR-1) -/

theorem label_of_powerAut {π : Nat → Nat} (h : IsPowerAut π) :
    (∀ c, c < 194 → cn (π c) = cn c) ∨ (∀ c, c < 194 → cn (π c) = twist c) := by
  obtain ⟨hlt, -, hsurj, hord, hpow⟩ := h
  refine (compatible_surj_iff (fun c => cn (π c))).1 ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨h1, h2, h3⟩ := compat_cn (π c) (hlt c hc)
    refine ⟨h1, h2.trans (hord c hc), fun p hp => ?_⟩
    simp only [hpow c hc p hp]; exact h3 p hp
  · intro l hl
    obtain ⟨d, hd, hld⟩ := surj_cn l hl
    obtain ⟨c, hc, hπ⟩ := hsurj d hd
    exact ⟨c, hc, by simp [hπ, hld]⟩

/-! ## Impossibility of exceptionless power-map rules -/

/-- **No power-map rule recovers `h` everywhere.** If `F` is invariant under all power-map
automorphisms (as is any rule computed from the power maps and element orders, e.g.
Le Bruyn's), then `F` errs at `32A` or at `32B`, because `σ` swaps them while
`h(32A) = 1 ≠ 2 = h(32B)`. -/
theorem no_invariant_h_rule (F : Nat → Nat)
    (hF : ∀ π, IsPowerAut π → ∀ c, c < 194 → F (π c) = F c) :
    F 106 ≠ (cn 106).h ∨ F 107 ≠ (cn 107).h := by
  have e : F 107 = F 106 := by
    have := hF sigma sigma_isPowerAut 106 (by decide)
    simpa [sigma] using this
  have h106 : (cn 106).h = 1 := by decide +kernel
  have h107 : (cn 107).h = 2 := by decide +kernel
  by_cases h : F 106 = 1
  · exact Or.inr (by rw [e, h, h107]; decide)
  · exact Or.inl (by rw [h106]; exact h)

/-! ## Le Bruyn's rule (arXiv:1804.04127, Theorem 2) -/

/-- Classes reachable by iterated prime power maps (all powers `g^k`). -/
def powersOf (c : Nat) : List Nat :=
  (List.range 8).foldl
    (fun S _ => (S ++ S.flatMap fun x => monsterPrimes.map fun p => pw p x).eraseDups) [c]

/-- Le Bruyn's special classes: the powers of `24J` and of `8C`. -/
def lbSpecialNames : List String :=
  ["24J", "12J", "8F", "6F", "4D", "3C", "2B", "1A", "8C", "4B", "2A"]

def idxOf (s : String) : Nat := ((List.range 194).find? fun i => nameOf i == s).getD 0

/-- Le Bruyn's predicted thread: `Y` = the largest-order special class that is a power of `X`;
`t = o(Y)/2` if even, `3` if `Y = 3C`, `1` if `Y = 1A`. -/
def lbThread (c : Nat) : Nat :=
  let P := powersOf c
  let Y := ((lbSpecialNames.map idxOf).filter fun y => P.contains y).foldl
    (fun best y => if ordOf y > ordOf best then y else best) 0
  if nameOf Y == "1A" then 1 else if nameOf Y == "3C" then 3 else ordOf Y / 2

/-- **Le Bruyn's Theorem 2, checked on the ATLAS data.** The rule gives the Conway–Norton `h`
except at exactly these 14 classes (his "12 counterexamples", merging 40C/D and 88A/B). -/
theorem lebruyn_exceptions :
    (classes.filter fun c => lbThread c != (cn c).h).map nameOf =
      ["8B", "8D", "16A", "24A", "24D", "24E", "24H", "32B", "40B", "40C", "40D", "48A",
       "88A", "88B"] := by
  decide +kernel

/-- **With the catalogue, the thread is determined everywhere except `{32A, 32B}`.** For every
MAR-compatible labelling `L` (one of the eight `variant`s by MAR-5), `h(L c) = h(cn c)` at every
class other than `32A, 32B`. This is optimal: by `no_invariant_h_rule` no power-map rule can do
better, and `variant true false false` (`32A ↦ 32|2+`) shows both values occur. -/
theorem thread_determined_by_compat (L : Nat → CNLabel) (hL : Compat L) :
    ∀ c, c < 194 → c ≠ 106 → c ≠ 107 → (L c).h = (cn c).h := by
  obtain ⟨b₁, b₂, b₃, h⟩ := (compat_iff_variant L).1 hL
  have key : ∀ b₁ b₂ b₃ : Bool, ∀ c, c < 194 → c ≠ 106 → c ≠ 107 →
      (variant b₁ b₂ b₃ c).h = (cn c).h := by
    decide +kernel
  intro c hc h1 h2
  rw [h c hc]; exact key b₁ b₂ b₃ c hc h1 h2

theorem thread_ambiguous_at_32 :
    (variant true false false 106).h = 2 ∧ (cn 106).h = 1 := by
  decide +kernel

end MonsterCN
