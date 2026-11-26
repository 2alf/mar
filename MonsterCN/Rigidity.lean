/-
# Monster Assignment Rigidity (MAR)

*Assignment Rigidity in Monstrous Moonshine: A Formal Reduction of the Conway–Norton
Correspondence.*

We ask how much of the Conway–Norton (CN) table is forced by finite group-theoretic data.

A *compatible labelling* is a map `L` from the 194 Monster classes to the catalogue of the 171
CN groups such that
* (order)  the `n` of `L g` is the element order of `g`;
* (power)  `L (g^p) = powRule (L g) p` for the 15 primes `p ∣ |M|`, where `powRule` is the
  CN power rule `(n|h+W)^p = n'|h' + {e ∈ W : e ∣ n'/h'}`.

Optional extra hypotheses:
* `Surj L`  : every catalogue group is attained;
* `Van ms L`: `a_m(g) = 0` whenever `h(L g) ∤ m+1`, for `m ∈ ms` (forced by
  `T_g(τ+1/h) = e^{-2πi/h} T_g(τ)`);
* `Coh ms L`: `L g = L g' → a_m(g) = a_m(g')` for `m ∈ ms` (forced by uniqueness of the
  normalized Hauptmodul of a given group).

Main results (all proved by a verified constraint-propagation procedure, kernel-evaluated):
* `compatible_surj_iff` : the compatible surjective labellings are **exactly two**: CN and an
  explicit "twist" exchanging the labels of `16B ↔ 16C` and `32A ↔ 32B`.
* `unique_of_surj_van` : compatible + surjective + `Van [2]` ⇒ `L = CN`.
* `unique_of_van_coh` : compatible + `Van [2]` + `Coh [1]` ⇒ `L = CN` (no surjectivity).
* Sharpness: the twist satisfies compatible + surjective + `Van [1,3]` + `Coh [1,2,3]`;
  `alt18` (CN with `18E ↦ 18-`) satisfies compatible + `Van [1,2,3]`.
-/
import MonsterCN.Basic
import MonsterCN.Data.Parents
import MonsterCN.Data.Catalogue
import MonsterCN.Data.RigidityDomains

namespace MonsterCN

/-! ## Hypotheses -/

/-- `L` is a compatible labelling (order + power-map compatibility, values in the catalogue). -/
def Compat (L : Nat → CNLabel) : Prop :=
  ∀ c, c < 194 → L c ∈ catalogue ∧ (L c).n = ordOf c ∧
    ∀ p ∈ monsterPrimes, L (pw p c) = powRule (L c) p

/-- Every catalogue group occurs. -/
def Surj (L : Nat → CNLabel) : Prop := ∀ l ∈ catalogue, ∃ c, c < 194 ∧ L c = l

/-- Coefficient vanishing `a_m(g) = 0` unless `h ∣ m+1`, for `m ∈ ms`. -/
def Van (ms : List Nat) (L : Nat → CNLabel) : Prop :=
  ∀ c, c < 194 → ∀ m ∈ ms, (m + 1) % (L c).h ≠ 0 → coeff m c = 0

/-- Same group ⇒ same coefficients `a_m`, `m ∈ ms`. -/
def Coh (ms : List Nat) (L : Nat → CNLabel) : Prop :=
  ∀ c, c < 194 → ∀ d, d < 194 → L c = L d → ∀ m ∈ ms, coeff m c = coeff m d

/-! ## Domains and propagation -/

/-- A domain assigns to each class a list of candidate labels. -/
abbrev Dom := List (List CNLabel)

/-- `L` lies in the domain `D`. -/
def Inv (D : Dom) (L : Nat → CNLabel) : Prop := ∀ c, c < 194 → L c ∈ D.getD c []

def vanOK (ms : List Nat) (c : Nat) (l : CNLabel) : Bool :=
  ms.all fun m => (m + 1) % l.h == 0 || coeff m c == 0

/-- Initial domains: catalogue groups of the right order satisfying the vanishing test. -/
def init (ms : List Nat) : Dom :=
  classes.map fun c => catalogue.filter fun l => l.n == ordOf c && vanOK ms c l

/-- Arc-consistency test for candidate `l` at class `c`. -/
def keep (ms : List Nat) (D : Dom) (c : Nat) (l : CNLabel) : Bool :=
  (monsterPrimes.all fun p => (D.getD (pw p c) []).contains (powRule l p)) &&
  ((parentsTbl.getD c []).all fun dp =>
      !(decide (dp.1 < 194) && monsterPrimes.contains dp.2 && pw dp.2 dp.1 == c) ||
      (D.getD dp.1 []).any fun l' => powRule l' dp.2 == l) &&
  (classes.all fun d => !(D.getD d [] == [l]) || ms.all fun m => coeff m c == coeff m d)

def step (ms : List Nat) (D : Dom) : Dom :=
  classes.map fun c => (D.getD c []).filter (keep ms D c)

/-- `l` is a candidate for no class other than `c` (and is in the catalogue). -/
def soleHolder (D : Dom) (c : Nat) (l : CNLabel) : Bool :=
  catalogue.contains l && classes.all fun d => d == c || !(D.getD d []).contains l

/-- Surjectivity propagation: a group that only `c` can take must be taken by `c`. -/
def surjStep (D : Dom) : Dom :=
  classes.map fun c =>
    match (D.getD c []).find? (soleHolder D c) with
    | some l => [l]
    | none => D.getD c []

/-- Case split: fix the label of `c₀`. -/
def restrict (D : Dom) (c₀ : Nat) (l₀ : CNLabel) : Dom :=
  classes.map fun c => if c == c₀ then [l₀] else D.getD c []

def iter : Nat → (Dom → Dom) → Dom → Dom
  | 0, _, D => D
  | k + 1, f, D => iter k f (f D)

/-! ## Soundness -/

theorem getD_classes_map {f : Nat → List CNLabel} {c : Nat} (hc : c < 194) :
    (classes.map f).getD c [] = f c := by
  simp [classes, numClasses, List.getD_eq_getElem?_getD, List.getElem?_range hc]

theorem pw_lt : ∀ c, c < 194 → ∀ p ∈ monsterPrimes, pw p c < 194 := by
  decide +kernel

theorem init_sound {ms L} (hC : Compat L) (hV : Van ms L) : Inv (init ms) L := by
  intro c hc
  obtain ⟨hcat, hn, -⟩ := hC c hc
  rw [init, getD_classes_map hc, List.mem_filter]
  refine ⟨hcat, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, vanOK, List.all_eq_true, Bool.or_eq_true]
  refine ⟨hn, fun m hm => ?_⟩
  by_cases h : (m + 1) % (L c).h = 0
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [hV c hc m hm h])

theorem step_sound {ms L D} (hC : Compat L) (hCoh : Coh ms L) (hI : Inv D L) :
    Inv (step ms D) L := by
  intro c hc
  obtain ⟨-, -, hpow⟩ := hC c hc
  rw [step, getD_classes_map hc, List.mem_filter]
  refine ⟨hI c hc, ?_⟩
  simp only [keep, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun p hp => ?_, fun dp _ => ?_⟩, fun d hd => ?_⟩
  · rw [← hpow p hp]
    simpa using hI _ (pw_lt c hc p hp)
  · by_cases h : (decide (dp.1 < 194) && monsterPrimes.contains dp.2 && pw dp.2 dp.1 == c) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at h
      obtain ⟨⟨hd, hp⟩, he⟩ := h
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq]
      refine Or.inr ⟨L dp.1, hI _ hd, ?_⟩
      rw [← (hC dp.1 hd).2.2 dp.2 hp, he]
    · simp only [Bool.not_eq_true] at h
      rw [h]
      rfl
  · have hd' : d < 194 := by simpa [classes, numClasses] using hd
    by_cases hD : D.getD d [] = [L c]
    · have hLd : L d = L c := by
        have := hI d hd'
        rw [hD] at this
        simpa using this
      have := hCoh c hc d hd' hLd.symm
      simp only [hD, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq]
      exact Or.inr (fun m hm => this m hm)
    · have : (D.getD d [] == [L c]) = false := by simpa using hD
      simp only [this, Bool.not_false, Bool.true_or]

theorem surjStep_sound {L D} (hS : Surj L) (hI : Inv D L) : Inv (surjStep D) L := by
  intro c hc
  rw [surjStep, getD_classes_map hc]
  split
  · next l hl =>
    have hsole := List.find?_some hl
    simp only [soleHolder, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hsole
    obtain ⟨hcat, hall⟩ := hsole
    obtain ⟨d, hd, hLd⟩ := hS l hcat
    have hdmem : d ∈ classes := by simpa [classes, numClasses] using hd
    rcases hall d hdmem with h | h
    · subst h; simp [hLd]
    · have hm := hI d hd
      rw [hLd] at hm
      have : (D.getD d []).contains l = true := List.contains_iff_mem.mpr hm
      rw [h] at this
      exact absurd this (by decide)
  · exact hI c hc

theorem restrict_sound {L D c₀ l₀} (hI : Inv D L) (h : L c₀ = l₀) :
    Inv (restrict D c₀ l₀) L := by
  intro c hc
  rw [restrict, getD_classes_map hc]
  by_cases hcc : c = c₀
  · subst hcc; simp [h]
  · have : (c == c₀) = false := by simpa using hcc
    simp only [this]
    exact hI c hc

theorem iter_sound {L} {f : Dom → Dom} (hf : ∀ D, Inv D L → Inv (f D) L) :
    ∀ k D, Inv D L → Inv (iter k f D) L
  | 0, _, h => h
  | k + 1, D, h => iter_sound hf k (f D) (hf D h)

theorem inv_eq {L D} {g : Nat → CNLabel} (hI : Inv D L)
    (hD : D = classes.map fun c => [g c]) : ∀ c, c < 194 → L c = g c := by
  intro c hc
  have := hI c hc
  rw [hD, getD_classes_map hc] at this
  simpa using this

/-! ## The two solutions -/

/-- The CN assignment. -/
def cnL : Nat → CNLabel := cn

/-- The *twist*: CN with the labels of `16B ↔ 16C` (classes 54, 55) and `32A ↔ 32B`
(classes 106, 107) exchanged. -/
def twist (c : Nat) : CNLabel :=
  if c == 54 then cn 55 else if c == 55 then cn 54 else
  if c == 106 then cn 107 else if c == 107 then cn 106 else cn c

/-- CN with `18E` (class 61) relabelled `18-` (the label of `18D`, class 60). -/
def alt18 (c : Nat) : CNLabel := if c == 61 then cn 60 else cn c

theorem twist_names :
    nameOf 54 = "16B" ∧ nameOf 55 = "16C" ∧ nameOf 106 = "32A" ∧ nameOf 107 = "32B" ∧
    nameOf 60 = "18D" ∧ nameOf 61 = "18E" ∧
    cn 54 = ⟨16, 1, [1]⟩ ∧ cn 55 = ⟨16, 1, [1, 16]⟩ ∧
    cn 106 = ⟨32, 1, [1, 32]⟩ ∧ cn 107 = ⟨32, 2, [1, 16]⟩ := by
  decide +kernel

end MonsterCN

/-! ## Transfer lemmas -/

namespace MonsterCN

theorem compat_congr {L g : Nat → CNLabel} (h : ∀ c, c < 194 → L c = g c) :
    Compat L ↔ Compat g := by
  constructor
  · intro hC c hc
    obtain ⟨h1, h2, h3⟩ := hC c hc
    refine ⟨h c hc ▸ h1, h c hc ▸ h2, fun p hp => ?_⟩
    rw [← h c hc, ← h _ (pw_lt c hc p hp)]; exact h3 p hp
  · intro hC c hc
    obtain ⟨h1, h2, h3⟩ := hC c hc
    refine ⟨(h c hc).symm ▸ h1, (h c hc).symm ▸ h2, fun p hp => ?_⟩
    rw [h c hc, h _ (pw_lt c hc p hp)]; exact h3 p hp

theorem surj_congr {L g : Nat → CNLabel} (h : ∀ c, c < 194 → L c = g c) :
    Surj L ↔ Surj g := by
  constructor
  · intro hS l hl
    obtain ⟨c, hc, e⟩ := hS l hl
    exact ⟨c, hc, (h c hc) ▸ e⟩
  · intro hS l hl
    obtain ⟨c, hc, e⟩ := hS l hl
    exact ⟨c, hc, (h c hc).symm ▸ e⟩

theorem van_nil (L : Nat → CNLabel) : Van [] L := by
  intro c _ m hm; simp at hm

theorem coh_nil (L : Nat → CNLabel) : Coh [] L := by
  intro c _ d _ _ m hm; simp at hm

/-! ## Kernel computations (each is a finite evaluation, checked by the kernel) -/

/-! Each propagation round is certified separately against an explicit literal domain
(`Data/RigidityDomains.lean`, generated by `provenance/lean/gen_rigidity_domains.lean`). Evaluating several
rounds in one kernel check would need up to 17 GB of memory; one round needs about 6 GB. -/

open MonsterCN.RigDom

theorem roundA1 : step [1] (init [2]) = domA1 := by decide +kernel
theorem roundA2 : step [1] domA1 = domA2 := by decide +kernel
theorem roundB1 : surjStep (step [] (init [2])) = domB1 := by decide +kernel
theorem roundB2 : surjStep (step [] domB1) = domB2 := by decide +kernel
theorem roundS1 : surjStep (step [] (init [])) = domS1 := by decide +kernel
theorem roundS2 : surjStep (step [] domS1) = domS2 := by decide +kernel
theorem roundS3 : surjStep (step [] domS2) = domS3 := by decide +kernel
theorem roundE1 : step [] (init []) = domE1 := by decide +kernel
theorem roundE2 : step [] domE1 = domE2 := by decide +kernel
theorem roundE3 : step [] domE2 = domE3 := by decide +kernel
theorem roundE4 : step [] domE3 = domE4 := by decide +kernel

/-- Propagation with `Van [2]`, `Coh [1]` solves every class. -/
theorem solveA : iter 3 (step [1]) (init [2]) = classes.map (fun c => [cn c]) := by
  show step [1] (step [1] (step [1] (init [2]))) = _
  rw [roundA1, roundA2]
  decide +kernel

/-- Surjectivity-propagation with `Van [2]` solves every class. -/
theorem solveB : iter 3 (fun D => surjStep (step [] D)) (init [2]) =
    classes.map (fun c => [cn c]) := by
  show surjStep (step [] (surjStep (step [] (surjStep (step [] (init [2])))))) = _
  rw [roundB1, roundB2]
  decide +kernel

/-- Domains after surjectivity-propagation without coefficient information. -/
def Dstar : Dom := iter 3 (fun D => surjStep (step [] D)) (init [])

theorem Dstar_eq : Dstar = domS3 := by
  show surjStep (step [] (surjStep (step [] (surjStep (step [] (init [])))))) = _
  rw [roundS1, roundS2, roundS3]

theorem Dstar_54 : Dstar.getD 54 [] = [⟨16, 1, [1]⟩, ⟨16, 1, [1, 16]⟩] := by
  rw [Dstar_eq]
  decide +kernel

theorem solveC₁ : iter 1 (fun D => surjStep (step [] D)) (restrict Dstar 54 ⟨16, 1, [1]⟩) =
    classes.map (fun c => [cn c]) := by
  rw [Dstar_eq]
  decide +kernel

theorem solveC₂ : iter 1 (fun D => surjStep (step [] D)) (restrict Dstar 54 ⟨16, 1, [1, 16]⟩) =
    classes.map (fun c => [twist c]) := by
  rw [Dstar_eq]
  decide +kernel

/-! ## Properties of the explicit labellings -/

theorem compat_cn : Compat cn := by unfold Compat; decide +kernel
theorem surj_cn : Surj cn := by unfold Surj; decide +kernel
theorem van_cn : Van [1, 2, 3] cn := by unfold Van; decide +kernel
theorem coh_cn : Coh [1, 2, 3] cn := by unfold Coh; decide +kernel

theorem compat_twist : Compat twist := by unfold Compat; decide +kernel
theorem surj_twist : Surj twist := by unfold Surj; decide +kernel
theorem van13_twist : Van [1, 3] twist := by unfold Van; decide +kernel
theorem coh_twist : Coh [1, 2, 3] twist := by unfold Coh; decide +kernel
/-- The twist violates `a₂`-vanishing at `32A` (class 106, which it labels `32|2+`). -/
theorem not_van2_twist : ¬ Van [2] twist := by
  intro h
  have := h 106 (by decide) 2 (by decide) (by decide +kernel)
  revert this; decide +kernel

theorem compat_alt18 : Compat alt18 := by unfold Compat; decide +kernel
theorem van_alt18 : Van [1, 2, 3] alt18 := by unfold Van; decide +kernel
/-- `alt18` violates `a₁`-coherence (`18D`, `18E` get the same group, different `a₁`). -/
theorem not_coh1_alt18 : ¬ Coh [1] alt18 := by
  intro h
  have := h 60 (by decide) 61 (by decide) (by decide +kernel) 1 (by decide)
  revert this; decide +kernel
theorem not_surj_alt18 : ¬ Surj alt18 := by
  intro h
  obtain ⟨c, hc, e⟩ := h (cn 61) (by decide +kernel)
  revert e; revert c; decide +kernel

theorem twist_ne_cn : twist 54 ≠ cn 54 := by decide +kernel
theorem alt18_ne_cn : alt18 61 ≠ cn 61 := by decide +kernel

/-! ## Main rigidity theorems -/

/-- **Uniqueness I.** Power-map compatibility + `a₂`-vanishing + `a₁`-coherence force the
Conway–Norton assignment. -/
theorem unique_of_van_coh {L : Nat → CNLabel} (hC : Compat L) (hV : Van [2] L)
    (hCoh : Coh [1] L) : ∀ c, c < 194 → L c = cn c :=
  inv_eq (iter_sound (fun _ h => step_sound hC hCoh h) 3 _ (init_sound hC hV)) solveA

/-- **Uniqueness II.** Power-map compatibility + surjectivity + `a₂`-vanishing force the
Conway–Norton assignment. -/
theorem unique_of_surj_van {L : Nat → CNLabel} (hC : Compat L) (hS : Surj L)
    (hV : Van [2] L) : ∀ c, c < 194 → L c = cn c :=
  inv_eq (iter_sound (fun _ h => surjStep_sound hS (step_sound hC (coh_nil L) h)) 3 _
    (init_sound hC hV)) solveB

/-- **Two solutions.** The compatible surjective labellings are exactly CN and the twist. -/
theorem compatible_surj_iff (L : Nat → CNLabel) :
    Compat L ∧ Surj L ↔ (∀ c, c < 194 → L c = cn c) ∨ (∀ c, c < 194 → L c = twist c) := by
  constructor
  · rintro ⟨hC, hS⟩
    have F : ∀ D, Inv D L → Inv (surjStep (step [] D)) L :=
      fun _ h => surjStep_sound hS (step_sound hC (coh_nil L) h)
    have hI : Inv Dstar L := iter_sound F 3 _ (init_sound hC (van_nil L))
    have h54 : L 54 ∈ Dstar.getD 54 [] := hI 54 (by decide)
    rw [Dstar_54] at h54
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h54
    rcases h54 with h | h
    · exact Or.inl (inv_eq (iter_sound F 1 _ (restrict_sound hI h)) solveC₁)
    · exact Or.inr (inv_eq (iter_sound F 1 _ (restrict_sound hI h)) solveC₂)
  · rintro (h | h)
    · exact ⟨(compat_congr h).2 compat_cn, (surj_congr h).2 surj_cn⟩
    · exact ⟨(compat_congr h).2 compat_twist, (surj_congr h).2 surj_twist⟩

/-- **Sharpness.** Neither uniqueness theorem survives dropping its coefficient hypothesis:
the twist is compatible, surjective, satisfies `Van [1,3]` and `Coh [1,2,3]`, but is not CN;
`alt18` is compatible and satisfies `Van [1,2,3]`, but is not CN. -/
theorem sharpness :
    (Compat twist ∧ Surj twist ∧ Van [1, 3] twist ∧ Coh [1, 2, 3] twist ∧ twist 54 ≠ cn 54) ∧
    (Compat alt18 ∧ Van [1, 2, 3] alt18 ∧ alt18 61 ≠ cn 61) :=
  ⟨⟨compat_twist, surj_twist, van13_twist, coh_twist, twist_ne_cn⟩,
   ⟨compat_alt18, van_alt18, alt18_ne_cn⟩⟩

end MonsterCN

namespace MonsterCN

/-- The permutation `σ = (16B 16C)(32A 32B)` of class indices. -/
def sigma (c : Nat) : Nat :=
  if c == 54 then 55 else if c == 55 then 54 else
  if c == 106 then 107 else if c == 107 then 106 else c

/-- **Why the twist exists.** `σ = (16B 16C)(32A 32B)` is an automorphism of all the
"group-order" data: it commutes with every `p`-power map and preserves element orders and
centralizer orders. Hence `cn ∘ σ` (the twist) is power-compatible. The two pairs are separated
only by character values, e.g. `a₂(32A) = 4 ≠ 0 = a₂(32B)`. -/
theorem sigma_automorphism :
    (∀ c, c < 194 → ∀ p ∈ monsterPrimes, pw p (sigma c) = sigma (pw p c)) ∧
    (∀ c, c < 194 → ordOf (sigma c) = ordOf c ∧ centOf (sigma c) = centOf c) ∧
    (∀ c, c < 194 → twist c = cn (sigma c)) ∧
    coeff 2 106 = 4 ∧ coeff 2 107 = 0 ∧ coeff 1 106 = coeff 1 107 := by
  decide +kernel

end MonsterCN

namespace MonsterCN

/-! ## Without surjectivity: exactly eight compatible labellings -/

/-- The eight compatible labellings. `b₁` relabels `16B ↦ 16+`, `32A ↦ 32|2+`;
`b₂` relabels `16C ↦ 16-`, `32B ↦ 32+`; `b₃` relabels `18E ↦ 18-`.
`variant false false false = cn`, `variant true true false = twist`. -/
def variant (b₁ b₂ b₃ : Bool) (c : Nat) : CNLabel :=
  if b₁ && c == 54 then cn 55 else if b₁ && c == 106 then cn 107 else
  if b₂ && c == 55 then cn 54 else if b₂ && c == 107 then cn 106 else
  if b₃ && c == 61 then cn 60 else cn c

/-- Domains after four rounds of power-map propagation (no coefficient data). -/
def Ecompat : Dom := iter 4 (step []) (init [])

open MonsterCN.RigDom in
theorem Ecompat_eq : Ecompat = domE4 := by
  show step [] (step [] (step [] (step [] (init [])))) = _
  rw [roundE1, roundE2, roundE3, roundE4]

theorem Ecompat_vals :
    Ecompat.getD 54 [] = [cn 54, cn 55] ∧ Ecompat.getD 55 [] = [cn 54, cn 55] ∧
    Ecompat.getD 61 [] = [cn 60, cn 61] := by
  rw [Ecompat_eq]
  decide +kernel

/-- One propagation round from `Ecompat` with the three choices fixed (one kernel check per
choice, to keep memory low). -/
def eightOK (b₁ b₂ b₃ : Bool) : Prop :=
  iter 1 (step []) (restrict (restrict (restrict RigDom.domE4 54 (variant b₁ b₂ b₃ 54)) 55
    (variant b₁ b₂ b₃ 55)) 61 (variant b₁ b₂ b₃ 61)) =
  classes.map (fun c => [variant b₁ b₂ b₃ c])

theorem eight_fff : eightOK false false false := by unfold eightOK; decide +kernel
theorem eight_fft : eightOK false false true := by unfold eightOK; decide +kernel
theorem eight_ftf : eightOK false true false := by unfold eightOK; decide +kernel
theorem eight_ftt : eightOK false true true := by unfold eightOK; decide +kernel
theorem eight_tff : eightOK true false false := by unfold eightOK; decide +kernel
theorem eight_tft : eightOK true false true := by unfold eightOK; decide +kernel
theorem eight_ttf : eightOK true true false := by unfold eightOK; decide +kernel
theorem eight_ttt : eightOK true true true := by unfold eightOK; decide +kernel

theorem solveEight : ∀ b₁ b₂ b₃ : Bool,
    iter 1 (step []) (restrict (restrict (restrict Ecompat 54 (variant b₁ b₂ b₃ 54)) 55
      (variant b₁ b₂ b₃ 55)) 61 (variant b₁ b₂ b₃ 61)) =
    classes.map (fun c => [variant b₁ b₂ b₃ c]) := by
  intro b₁ b₂ b₃
  rw [Ecompat_eq]
  cases b₁ <;> cases b₂ <;> cases b₃
  · exact eight_fff
  · exact eight_fft
  · exact eight_ftf
  · exact eight_ftt
  · exact eight_tff
  · exact eight_tft
  · exact eight_ttf
  · exact eight_ttt

theorem compat_variant : ∀ b₁ b₂ b₃ : Bool, Compat (variant b₁ b₂ b₃) := by
  unfold Compat; decide +kernel

theorem variant_injective : ∀ b₁ b₂ b₃ b₁' b₂' b₃' : Bool,
    (variant b₁ b₂ b₃ 54 = variant b₁' b₂' b₃' 54 ∧ variant b₁ b₂ b₃ 55 = variant b₁' b₂' b₃' 55 ∧
      variant b₁ b₂ b₃ 61 = variant b₁' b₂' b₃' 61) → b₁ = b₁' ∧ b₂ = b₂' ∧ b₃ = b₃' := by
  decide

theorem variant_vals (b₁ b₂ b₃ : Bool) :
    variant b₁ b₂ b₃ 54 = (if b₁ then cn 55 else cn 54) ∧
    variant b₁ b₂ b₃ 55 = (if b₂ then cn 54 else cn 55) ∧
    variant b₁ b₂ b₃ 61 = (if b₃ then cn 60 else cn 61) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> decide +kernel

/-- **Exactly eight.** The labellings compatible with element orders and the ATLAS power maps
(values in the 171-group catalogue) are exactly the eight `variant b₁ b₂ b₃`, which are pairwise
distinct (`variant_injective`). -/
theorem compat_iff_variant (L : Nat → CNLabel) :
    Compat L ↔ ∃ b₁ b₂ b₃ : Bool, ∀ c, c < 194 → L c = variant b₁ b₂ b₃ c := by
  constructor
  · intro hC
    have hI : Inv Ecompat L :=
      iter_sound (fun _ h => step_sound hC (coh_nil L) h) 4 _ (init_sound hC (van_nil L))
    obtain ⟨e54, e55, e61⟩ := Ecompat_vals
    have h54 := hI 54 (by decide)
    have h55 := hI 55 (by decide)
    have h61 := hI 61 (by decide)
    rw [e54] at h54; rw [e55] at h55; rw [e61] at h61
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h54 h55 h61
    have key : ∀ b₁ b₂ b₃ : Bool, L 54 = variant b₁ b₂ b₃ 54 → L 55 = variant b₁ b₂ b₃ 55 →
        L 61 = variant b₁ b₂ b₃ 61 → ∀ c, c < 194 → L c = variant b₁ b₂ b₃ c :=
      fun b₁ b₂ b₃ a b c =>
        inv_eq (iter_sound (fun _ h => step_sound hC (coh_nil L) h) 1 _
          (restrict_sound (restrict_sound (restrict_sound hI a) b) c)) (solveEight b₁ b₂ b₃)

    rcases h54 with a | a <;> rcases h55 with b | b <;> rcases h61 with c | c
    · exact ⟨false, true, true, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨false, true, false, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨false, false, true, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨false, false, false, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨true, true, true, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨true, true, false, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨true, false, true, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
    · exact ⟨true, false, false, key _ _ _ (a.trans (by decide +kernel)) (b.trans (by decide +kernel))
        (c.trans (by decide +kernel))⟩
  · rintro ⟨b₁, b₂, b₃, h⟩
    exact (compat_congr h).2 (compat_variant b₁ b₂ b₃)

end MonsterCN
