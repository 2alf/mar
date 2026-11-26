/-
# MAR-10, completed: witnesses for the remaining hypotheses of MAR-9

`GenusZero.lean` gives fake tables for dropping (H), `a₁`-vanishing, `a₂`-vanishing and genus zero.
This file adds:

* `fakeC_props`: a witness for dropping the **power rule** (the part of (C) relating `g` and `g^p`):
  `9B ↦ 9|3` instead of `9-`. Every label is still an admissible genus-zero label of the right
  order, (V) and (H) still hold, the table differs from Conway–Norton's, and the power rule fails
  (on the edges into `9B` from classes of order 18).
* `fakeNG_admissible`: the genus-one fake of `GenusZero.lean` (`24I ↦ 24-`, `32A ↦ 32-`) satisfies
  every admissibility condition except genus zero (`h ∈ {1,2,3,4,6,8,12,24}`, `h ∣ n`, `W` a group
  of Hall divisors of `n/h` in normal form), so it differs from the hypotheses of MAR-9 only in the
  genus.

The part `n(L(g)) = o(g)` of (C) is the normalization of what a label of `g` is (the level of the
Hauptmodul of `g` is a multiple of `o(g)`, Conway–Norton); no witness for dropping it is given.
-/
import MonsterCN.GenusZero

namespace MonsterCN.GZ

open MonsterCN

/-- Drop the power rule: `9B ↦ 9|3` (Conway–Norton: `9-`). -/
def fakeC (c : Nat) : CNLabel := if c == 27 then ⟨9, 3, [1]⟩ else cn c

theorem fakeC_names : nameOf 27 = "9B" ∧ cn 27 = ⟨9, 1, [1]⟩ := by decide +kernel

/-- **MAR-10 (power rule).** `fakeC` uses only admissible genus-zero labels of the right order,
satisfies (V) and (H), differs from `cn`, and violates the power rule. -/
theorem fakeC_props :
    (∀ c, c < 194 → IsGZ (fakeC c) ∧ (fakeC c).n = ordOf c) ∧
    Van [1, 2] fakeC ∧ Coh [1] fakeC ∧ fakeC 27 ≠ cn 27 ∧
    ¬ (∀ c, c < 194 → ∀ p ∈ monsterPrimes, fakeC (pw p c) = powRule (fakeC c) p) := by
  have hb : (classes.all fun c => monsterPrimes.all fun p =>
      fakeC (pw p c) == powRule (fakeC c) p) = false := by decide +kernel
  refine ⟨?_, ?_, ?_, by decide +kernel, ?_⟩
  · unfold IsGZ; decide +kernel
  · unfold Van; decide +kernel
  · unfold Coh; decide +kernel
  · intro h
    have : (classes.all fun c => monsterPrimes.all fun p =>
        fakeC (pw p c) == powRule (fakeC c) p) = true := by
      simp only [List.all_eq_true, beq_iff_eq]
      intro c hc p hp
      exact h c (by simpa [classes, numClasses] using hc) p hp
    rw [hb] at this
    exact Bool.false_ne_true this

/-- **MAR-10 (genus zero), admissibility.** The genus-one fake satisfies every admissibility
condition of MAR-9 except genus zero, and genus zero fails exactly at its two changed labels. -/
theorem fakeNG_admissible :
    (∀ c, c < 194 → (fakeNG c).h ∈ hs ∧ (fakeNG c).n % (fakeNG c).h = 0 ∧
      (fakeNG c).W.isSublist (hallList ((fakeNG c).n / (fakeNG c).h)) = true ∧
      validW (fakeNG c).W = true) ∧
    (∀ c, c < 194 → c = 85 ∨ c = 106 ∨ IsGZ (fakeNG c)) ∧
    fakeNG 85 = ⟨24, 1, [1]⟩ ∧ fakeNG 106 = ⟨32, 1, [1]⟩ ∧
    genusZero 24 [1] = false ∧ genusZero 32 [1] = false := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
  unfold IsGZ; decide +kernel

end MonsterCN.GZ
