/-
# Labels in normal form are unique

A Conway–Norton label `n|h+W` is stored as `⟨n, h, W⟩` with `W` a list. The admissibility predicate
`IsGZ` of MAR-9 requires `W` to be a sublist of `hallList (n / h)`, the Hall divisors of `n / h` in
increasing order. This file proves that this normal form is unique: two admissible labels with the
same `n`, the same `h` and the same *set* of Atkin–Lehner indices are equal. So restricting MAR-9
to normal-form labels loses nothing: every group `n|h+W` has exactly one admissible encoding.
-/
import MonsterCN.GenusZero
import Mathlib.Data.List.Sort

namespace MonsterCN.GZ

open MonsterCN

/-- `divisorsN m` is strictly increasing. -/
theorem divisorsN_sorted (m : Nat) : (divisorsN m).Pairwise (· < ·) := by
  unfold divisorsN
  exact (List.pairwise_lt_range).filter _

/-- `hallList m` is strictly increasing. -/
theorem hallList_sorted (m : Nat) : (hallList m).Pairwise (· < ·) := by
  unfold hallList
  exact (divisorsN_sorted m).filter _

/-- Two sublists of a strictly increasing list with the same elements are equal. -/
theorem eq_of_sublist_of_mem_iff {H W₁ W₂ : List Nat} (hH : H.Pairwise (· < ·))
    (h₁ : W₁.Sublist H) (h₂ : W₂.Sublist H) (hm : ∀ e, e ∈ W₁ ↔ e ∈ W₂) : W₁ = W₂ := by
  have s₁ : W₁.Pairwise (· < ·) := hH.sublist h₁
  have s₂ : W₂.Pairwise (· < ·) := hH.sublist h₂
  have n₁ : W₁.Nodup := s₁.imp (fun h => Nat.ne_of_lt h)
  have n₂ : W₂.Nodup := s₂.imp (fun h => Nat.ne_of_lt h)
  have hp : W₁.Perm W₂ := (List.perm_ext_iff_of_nodup n₁ n₂).mpr hm
  exact List.Perm.eq_of_pairwise
    (fun a _ _ _ hab hba => absurd (Nat.lt_trans hab hba) (Nat.lt_irrefl a)) s₁ s₂ hp

/-- **Normal form.** Two admissible labels with the same level `n`, the same `h` and the same set
of Atkin–Lehner indices `W` are equal. -/
theorem isGZ_normal_form {l₁ l₂ : CNLabel} (h₁ : IsGZ l₁) (h₂ : IsGZ l₂) (hn : l₁.n = l₂.n)
    (hh : l₁.h = l₂.h) (hW : ∀ e, e ∈ l₁.W ↔ e ∈ l₂.W) : l₁ = l₂ := by
  obtain ⟨n₁, h₁', W₁⟩ := l₁
  obtain ⟨n₂, h₂', W₂⟩ := l₂
  simp only at hn hh hW
  subst hn hh
  have s₁ : W₁.Sublist (hallList (n₁ / h₁')) := List.isSublist_iff_sublist.mp h₁.2.2.1
  have s₂ : W₂.Sublist (hallList (n₁ / h₁')) := List.isSublist_iff_sublist.mp h₂.2.2.1
  rw [eq_of_sublist_of_mem_iff (hallList_sorted _) s₁ s₂ hW]

end MonsterCN.GZ
