/-
# Conway moonshine: a table inconsistency and hidden power-map symmetries (MAR, part V)

Conway moonshine (Duncan 2007; Duncan–Mack-Crane, Forum Math. Sigma 3 (2015) e10): for
`g ∈ Co₀ = 2.Co₁` the super-trace series satisfies `T^s_g(2τ) = q⁻¹ + 0 + a₁(g) q + a₂(g) q² + …`,
and `T^s_g(2τ)` is the normalized Hauptmodul of a genus-zero group `Γ_g` listed in their Table A.1.
Here `a₁ = χ₂₇₆` (`V₁ ≅ Λ²(24)`) and `a₂ = −(χ₂₄ + χ₂₀₂₄)` (the 2048-dimensional odd space); this
is input (A3) of the paper. `lambda2_chi24` below certifies `Λ²χ₂₄ = χ₂₇₆` in the kernel.

**MAR-13 (`dmc_label_inconsistency`).** Table A.1 assigns the same group to classes whose series
differ, which contradicts the uniqueness of normalized Hauptmoduln.
* `12E` and `6M` are both labelled `12-` (`Γ₀(12)`), but `a₁(12E) = −2 ≠ 2 = a₁(6M)`. The
  normalized Hauptmodul of `Γ₀(12)` is the Monster series `T_{12I}`, with `a₁ = 2`
  (`MonsterCN.coeff 1 42`). So the label of `12E` is wrong.
* `30J` and `30K` are both labelled `60+12,15,20`, but `a₂(30J) = −1 ≠ 1 = a₂(30K)`. The
  Hauptmodul of `60+12,15,20` is `T_{60D}`, with `a₂ = 1` (`MonsterCN.coeff 2 156`). So the label of
  `30J` is wrong.

The intended groups are those of `12L/12M`, `(24|2+12)^{up(1/4)}`, for `12E`, and of `30G`,
`(60+12,15,20)^{up(1/2)}`, for `30J` (as in Kondo 1985); the finite computations of a certificate
are kernel-checked in `ConwayErratum.lean`.

**MAR-14 (`conway_hidden_symmetries`, `no_invariant_conway_rule`).** Power-map symmetries of `Co₀`
exchange six pairs of classes with different Conway-moonshine series: `9B↔9C`, `18B↔18C`, `12Q↔12R`,
`16B↔16C`, `18F↔18H`, `18G↔18I`. So no rule built from power maps, orders and centralizer orders
recovers Conway moonshine.
-/
import MonsterCN.Data.Conway
import MonsterCN.Basic

namespace MonsterCN.Conway

def ordC (c : Nat) : Nat := coOrd.getD c 0
def centC (c : Nat) : Nat := coCent.getD c 0
def pwC (p c : Nat) : Nat := (coPmap p).getD c 0
def nameC (c : Nat) : String := coNames.getD c ""
def labC (c : Nat) : String := dmcLabel.getD c ""

/-- `q¹`-coefficient of `T^s_g(2τ)`: `a₁ = χ₂₇₆`. -/
def a1 (c : Nat) : Int := coChi276.getD c 0
/-- `q²`-coefficient of `T^s_g(2τ)`: `a₂ = −(χ₂₄ + χ₂₀₂₄)`. -/
def a2 (c : Nat) : Int := -(coChi24.getD c 0 + coChi2024.getD c 0)

def wsumC (f : Nat → Int) : Int :=
  ((List.range 167).map fun c => ((centC 0 / centC c : Nat) : Int) * f c).sum

/-! ## Data integrity -/

theorem co_integrity :
    coNames.length = 167 ∧ coOrd.length = 167 ∧ coCent.length = 167 ∧ dmcLabel.length = 167 ∧
    coPrimes = [2, 3, 5, 7, 11, 13, 23] ∧
    ((List.range 167).map fun c => centC 0 / centC c).sum = centC 0 ∧
    (List.range 167).all (fun c => coPrimes.all fun p =>
      pwC p c < 167 && ordC (pwC p c) == ordC c / Nat.gcd (ordC c) p) = true ∧
    coChi24.getD 0 0 = 24 ∧ coChi276.getD 0 0 = 276 ∧ coChi2024.getD 0 0 = 2024 ∧
    wsumC (fun c => coChi24.getD c 0 ^ 2) = centC 0 ∧
    wsumC (fun c => coChi276.getD c 0 ^ 2) = centC 0 ∧
    wsumC (fun c => coChi2024.getD c 0 ^ 2) = centC 0 := by
  decide +kernel

/-- `Λ²χ₂₄ = χ₂₇₆`: `(χ₂₄(g)² − χ₂₄(g²))/2 = χ₂₇₆(g)` for every class. -/
theorem lambda2_chi24 :
    (List.range 167).all (fun c =>
      (coChi24.getD c 0 * coChi24.getD c 0 - coChi24.getD (pwC 2 c) 0) == 2 * coChi276.getD c 0) =
      true := by
  decide +kernel

/-! ## MAR-13: an inconsistency in Duncan–Mack-Crane, Table A.1 -/

theorem dmc_label_inconsistency :
    -- 12E and 6M (also 6N) carry the same label 12- ...
    nameC 73 = "12E" ∧ nameC 37 = "6M" ∧ nameC 38 = "6N" ∧
    labC 73 = "12-" ∧ labC 37 = "12-" ∧ labC 38 = "12-" ∧
    -- ... but their series differ in the q-coefficient
    a1 73 = -2 ∧ a1 37 = 2 ∧ a1 38 = 2 ∧
    -- the Gamma0(12) Hauptmodul is the Monster series T_{12I} (CN label 12-), with a1 = 2
    MonsterCN.nameOf 42 = "12I" ∧ MonsterCN.cn 42 = ⟨12, 1, [1]⟩ ∧ MonsterCN.coeff 1 42 = 2 ∧
    -- 30J and 30K carry the same label 60+12,15,20 ...
    nameC 150 = "30J" ∧ nameC 151 = "30K" ∧
    labC 150 = "60+12,15,20" ∧ labC 151 = "60+12,15,20" ∧
    -- ... but differ in the q²-coefficient
    a2 150 = -1 ∧ a2 151 = 1 ∧
    -- the Hauptmodul of 60+12,15,20 is T_{60D}, with a2 = 1
    MonsterCN.nameOf 156 = "60D" ∧ MonsterCN.cn 156 = ⟨60, 1, [1, 12, 15, 20]⟩ ∧
    MonsterCN.coeff 2 156 = 1 := by
  decide +kernel

/-- Evidence for the corrected labels: `12E` agrees with `12L` (labelled `(24|2+12)^{up(1/4)}`),
and `30J` with `30G` (labelled `(60+12,15,20)^{up(1/2)}`), in `a₁` and `a₂`. -/
theorem dmc_corrected_label_evidence :
    nameC 81 = "12L" ∧ a1 73 = a1 81 ∧ a2 73 = a2 81 ∧
    nameC 145 = "30G" ∧ a1 150 = a1 145 ∧ a2 150 = a2 145 := by
  decide +kernel

/-! ## MAR-14: hidden power-map symmetries move Conway moonshine -/

/-- Power-map symmetry of `Co₀`: a permutation of the 167 classes that preserves element orders and
centralizer orders and commutes with all prime power maps. -/
def IsPowerAutC (π : Nat → Nat) : Prop :=
  (∀ c, c < 167 → π c < 167) ∧
  (∀ c, c < 167 → ∀ d, d < 167 → π c = π d → c = d) ∧
  (∀ c, c < 167 → ordC (π c) = ordC c ∧ centC (π c) = centC c) ∧
  (∀ c, c < 167 → ∀ p ∈ coPrimes, π (pwC p c) = pwC p (π c))

def permOfC (l : List Nat) (c : Nat) : Nat := l.getD c 0
def witC (i : Nat) : Nat × Nat × List Nat := coWitnesses.getD i (0, 0, [])

theorem conway_witness_names :
    (coWitnesses.map fun w => (nameC w.1, nameC w.2.1)) =
      [("9B", "9C"), ("18B", "18C"), ("12Q", "12R"), ("16B", "16C"), ("18F", "18H"),
       ("18G", "18I")] := by
  decide +kernel

/-- **MAR-14.** Each witness is a power-map symmetry of `Co₀` exchanging two classes whose
Conway-moonshine series differ in `a₁` or `a₂`. -/
theorem conway_hidden_symmetries : ∀ i, i < 6 →
    IsPowerAutC (permOfC (witC i).2.2) ∧ permOfC (witC i).2.2 (witC i).1 = (witC i).2.1 ∧
    (witC i).1 < 167 ∧
    (a1 (witC i).1 ≠ a1 (witC i).2.1 ∨ a2 (witC i).1 ≠ a2 (witC i).2.1) := by
  unfold IsPowerAutC; decide +kernel

/-- **Impossibility.** A function invariant under all power-map symmetries of `Co₀` differs from
the pair `(a₁, a₂)` of Conway-moonshine coefficients somewhere. -/
theorem no_invariant_conway_rule (F : Nat → Int × Int)
    (hF : ∀ π, IsPowerAutC π → ∀ c, c < 167 → F (π c) = F c) :
    ∃ c, c < 167 ∧ F c ≠ (a1 c, a2 c) := by
  obtain ⟨hπ, hmap, hlt, hne⟩ := conway_hidden_symmetries 0 (by decide)
  have e := hF _ hπ _ hlt
  rw [hmap] at e
  by_cases h : F (witC 0).1 = (a1 (witC 0).1, a2 (witC 0).1)
  · refine ⟨(witC 0).2.1, ?_, ?_⟩
    · have := hπ.1 _ hlt; rwa [hmap] at this
    · rw [e, h]
      intro h'
      simp only [Prod.mk.injEq] at h'
      rcases hne with h1 | h1
      · exact h1 h'.1
      · exact h1 h'.2
  · exact ⟨(witC 0).1, hlt, h⟩

end MonsterCN.Conway
