/-
# Supplementary facts stated in the paper

* `monster_orders_73`: the Monster has elements of exactly 73 different orders; these are the levels
  of the universe of MAR-9.
* `no_sigma_invariant_h_rule` (MAR-7, strong form): a rule that is merely invariant under the single
  symmetry `σ = (16B 16C)(32A 32B)` cannot give the Conway–Norton thread at both `32A` and `32B`.
  Since `σ` preserves element orders and centralizer orders and commutes with all power maps
  (`sigma_automorphism`), this covers every rule computed from power maps, element orders and
  centralizer orders.
-/
import MonsterCN.GenusZero
import MonsterCN.Automorphisms

namespace MonsterCN

open MonsterCN.GZ

/-- The Monster has elements of exactly 73 different orders. -/
theorem monster_orders_73 : monsterOrders.length = 73 := by decide +kernel

/-- **MAR-7 (strong form).** If `F` is invariant under `σ`, then `F` differs from the thread `h`
at `32A` or at `32B`. -/
theorem no_sigma_invariant_h_rule (F : Nat → Nat) (hF : ∀ c, c < 194 → F (sigma c) = F c) :
    F 106 ≠ (cn 106).h ∨ F 107 ≠ (cn 107).h := by
  have e : F 107 = F 106 := by
    have h := hF 106 (by decide)
    rwa [show sigma 106 = 107 by decide] at h
  have h106 : (cn 106).h = 1 := by decide +kernel
  have h107 : (cn 107).h = 2 := by decide +kernel
  by_cases h : F 106 = 1
  · right
    rw [e, h, h107]
    decide
  · left
    rw [h106]
    exact h

end MonsterCN
