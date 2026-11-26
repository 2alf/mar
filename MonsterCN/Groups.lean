/-
# The Conway–Norton groups `Γ₀(n|h)`

Standard definitions (Conway–Norton, *Monstrous Moonshine*, Bull. LMS 11 (1979), §3;
Conway–McKay–Sebbar, *On the discrete groups of moonshine*, Proc. AMS 132 (2004)):

For positive integers `h ∣ n`,
`Γ₀(n|h) = { [[a, b/h], [c n, d]] : a b c d ∈ ℤ, ad - bc n/h = 1 }  ⊆ SL₂(ℚ)`.

It is the conjugate `D⁻¹ Γ₀(n/h) D` with `D = diag(h, 1)`, it contains `Γ₀(n h)`, and it
contains the translation `τ ↦ τ + 1/h`. In Conway–Norton's notation a moonshine group
`n|h+e,f,…` is an index-`h` subgroup of `⟨Γ₀(n|h), W_e, W_f, …⟩`; its level is `n·h`.

Everything in this file is proved from Mathlib; nothing here depends on Monster data.
-/
import Mathlib

open Matrix Matrix.SpecialLinearGroup MatrixGroups

namespace MonsterCN

/-- The embedding `SL₂(ℤ) → SL₂(ℚ)`. -/
abbrev toQ : SL(2, ℤ) →* SL(2, ℚ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ)

lemma toQ_apply (A : SL(2, ℤ)) (i j : Fin 2) : (toQ A) i j = ((A i j : ℤ) : ℚ) := rfl

/-- Membership predicate for `Γ₀(n|h)`: entries of the shape `[[a, b/h], [c n, d]]`
with `a b c d ∈ ℤ`. -/
def InGamma0Bar (n h : ℕ) (A : SL(2, ℚ)) : Prop :=
  ∃ a b c d : ℤ, A 0 0 = a ∧ A 0 1 = b / h ∧ A 1 0 = c * n ∧ A 1 1 = d

lemma det_fin_two_SL (A : SL(2, ℚ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := A.2
  rw [Matrix.det_fin_two] at this
  exact this

lemma SL_mul_apply (A B : SL(2, ℚ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Entries of a triple product of `2 × 2` matrices. -/
lemma mul3_apply (P M Q : Matrix (Fin 2) (Fin 2) ℚ) (i j : Fin 2) :
    (P * M * Q) i j = (P i 0 * M 0 0 + P i 1 * M 1 0) * Q 0 j +
      (P i 0 * M 0 1 + P i 1 * M 1 1) * Q 1 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]

/-- `Γ₀(n|h)` as a subgroup of `SL₂(ℚ)`, for `h ∣ n`, `h ≠ 0`. -/
def Gamma0Bar (n h : ℕ) (hh : h ≠ 0) (hdvd : h ∣ n) : Subgroup SL(2, ℚ) where
  carrier := {A | InGamma0Bar n h A}
  one_mem' := ⟨1, 0, 0, 1, by simp⟩
  mul_mem' := by
    rintro A B ⟨a, b, c, d, ha, hb, hc, hd⟩ ⟨a', b', c', d', ha', hb', hc', hd'⟩
    obtain ⟨m, rfl⟩ := hdvd
    have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
    refine ⟨a * a' + b * c' * m, a * b' + b * d', c * a' + d * c', c * b' * m + d * d',
      ?_, ?_, ?_, ?_⟩ <;>
      rw [SL_mul_apply] <;> simp only [ha, hb, hc, hd, ha', hb', hc', hd'] <;> push_cast <;>
      field_simp
  inv_mem' := by
    rintro A ⟨a, b, c, d, ha, hb, hc, hd⟩
    refine ⟨d, -b, -c, a, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.adjugate_fin_two, ha, hb, hc, hd, neg_div]

/-- **Level relation.** `Γ₀(n h) ⊆ Γ₀(n|h)` (inside `SL₂(ℚ)`). -/
theorem gamma0_le_gamma0Bar (n h : ℕ) (hh : h ≠ 0) (hdvd : h ∣ n) :
    (CongruenceSubgroup.Gamma0 (n * h)).map toQ ≤ Gamma0Bar n h hh hdvd := by
  rintro _ ⟨A, hA, rfl⟩
  have hA' : ((A 1 0 : ℤ) : ZMod (n * h)) = 0 := CongruenceSubgroup.Gamma0_mem.1 hA
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hA'
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  refine ⟨A 0 0, A 0 1 * h, k * h, A 1 1, ?_, ?_, ?_, ?_⟩
  · rw [toQ_apply]
  · rw [toQ_apply]; push_cast; field_simp
  · rw [toQ_apply, hk]; push_cast; ring
  · rw [toQ_apply]

/-- The translation `τ ↦ τ + 1/h`. -/
def translation (h : ℕ) : SL(2, ℚ) :=
  ⟨!![1, 1 / (h : ℚ); 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The translation `τ ↦ τ + 1/h` lies in `Γ₀(n|h)`. -/
theorem translation_mem (n h : ℕ) (hh : h ≠ 0) (hdvd : h ∣ n) :
    translation h ∈ Gamma0Bar n h hh hdvd :=
  ⟨1, 1, 0, 1, by simp [translation]⟩

/-- `Γ₀(n|1)` is (the image of) `Γ₀(n)`. -/
theorem gamma0Bar_one (n : ℕ) :
    Gamma0Bar n 1 one_ne_zero (one_dvd n) = (CongruenceSubgroup.Gamma0 n).map toQ := by
  ext A
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd⟩
    have hdet := det_fin_two_SL A
    rw [ha, hb, hc, hd] at hdet
    simp only [Nat.cast_one, div_one] at hdet
    have hdetZ : a * d - b * (c * n) = 1 := by exact_mod_cast hdet
    refine ⟨⟨!![a, b; c * n, d], by rw [Matrix.det_fin_two_of]; exact hdetZ⟩,
      CongruenceSubgroup.Gamma0_mem.2 (by simp), ?_⟩
    ext i j
    erw [toQ_apply]
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · rintro ⟨B, hB, rfl⟩
    apply gamma0_le_gamma0Bar n 1 one_ne_zero (one_dvd n)
    rw [mul_one]
    exact ⟨B, hB, rfl⟩

/-! ### Conjugacy `Γ₀(n|h) = D⁻¹ Γ₀(n/h) D` -/

/-- `D = diag(h, 1)`. -/
def diagD (h : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![(h : ℚ), 0; 0, 1]

lemma diagD_inv (h : ℕ) (hh : h ≠ 0) : (diagD h)⁻¹ = !![1 / (h : ℚ), 0; 0, 1] := by
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  apply Matrix.inv_eq_right_inv
  rw [diagD, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hq]

lemma diag_conj (p q : ℚ) (M : Matrix (Fin 2) (Fin 2) ℚ) :
    !![p, 0; 0, 1] * M * !![q, 0; 0, 1] = !![p * M 0 0 * q, p * M 0 1; M 1 0 * q, M 1 1] := by
  ext i j
  rw [mul3_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- **Conjugacy.** `A ∈ Γ₀(n|h)` iff `D A D⁻¹` (with `D = diag(h,1)`) is the image of an
element of `Γ₀(n/h)`. -/
theorem inGamma0Bar_iff_conj (n h : ℕ) (hh : h ≠ 0) (hdvd : h ∣ n) (A : SL(2, ℚ)) :
    InGamma0Bar n h A ↔ ∃ B ∈ CongruenceSubgroup.Gamma0 (n / h),
      ((toQ B : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) =
        diagD h * (A : Matrix (Fin 2) (Fin 2) ℚ) * (diagD h)⁻¹ := by
  obtain ⟨m, rfl⟩ := hdvd
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hm : h * m / h = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hh)
  rw [hm, diagD_inv h hh, diagD, diag_conj]
  have hdet := det_fin_two_SL A
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd⟩
    rw [ha, hb, hc, hd] at hdet
    have hdetZ : a * d - b * (c * m) = 1 := by
      have : ((a * d - b * (c * m) : ℤ) : ℚ) = 1 := by
        rw [← hdet]; push_cast; field_simp
      exact_mod_cast this
    refine ⟨⟨!![a, b; c * m, d], by rw [Matrix.det_fin_two_of]; exact hdetZ⟩,
      CongruenceSubgroup.Gamma0_mem.2 (by simp), ?_⟩
    ext i j
    erw [toQ_apply]
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd] <;> field_simp
  · rintro ⟨B, hB, hBA⟩
    have hB' : ((B 1 0 : ℤ) : ZMod m) = 0 := CongruenceSubgroup.Gamma0_mem.1 hB
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hB'
    have e00 : ((B 0 0 : ℤ) : ℚ) = h * A 0 0 * (1 / h) := by
      rw [← toQ_apply, hBA]; rfl
    have e01 : ((B 0 1 : ℤ) : ℚ) = h * A 0 1 := by
      rw [← toQ_apply, hBA]; rfl
    have e10 : ((B 1 0 : ℤ) : ℚ) = A 1 0 * (1 / h) := by
      rw [← toQ_apply, hBA]; rfl
    have e11 : ((B 1 1 : ℤ) : ℚ) = A 1 1 := by
      rw [← toQ_apply, hBA]; rfl
    refine ⟨B 0 0, B 0 1, k, B 1 1, ?_, ?_, ?_, ?_⟩
    · rw [e00]; field_simp
    · rw [e01]; field_simp
    · rw [hk] at e10
      push_cast at e10
      field_simp at e10
      push_cast
      linear_combination -e10
    · rw [e11]

/-! ### The Fricke involution `W_N = [[0, -1], [N, 0]]` normalizes `Γ₀(N)` -/

/-- The Fricke matrix `W_N = [[0, -1], [N, 0]]`. -/
def fricke (N : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; (N : ℚ), 0]

lemma fricke_inv (N : ℕ) (hN : 0 < N) : (fricke N)⁻¹ = !![0, 1 / (N : ℚ); -1, 0] := by
  have hq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  apply Matrix.inv_eq_right_inv
  rw [fricke, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hq]

lemma fricke_conj (N q : ℚ) (M : Matrix (Fin 2) (Fin 2) ℚ) :
    !![0, -1; N, 0] * M * !![0, q; -1, 0] =
      !![M 1 1, -(M 1 0 * q); -(N * M 0 1), N * M 0 0 * q] := by
  ext i j
  rw [mul3_apply]
  fin_cases i <;> fin_cases j <;> simp

lemma fricke_inv_conj (N q : ℚ) (M : Matrix (Fin 2) (Fin 2) ℚ) :
    !![0, q; -1, 0] * M * !![0, -1; N, 0] =
      !![q * M 1 1 * N, -(q * M 1 0); -(M 0 1 * N), M 0 0] := by
  ext i j
  rw [mul3_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- The element `[[d, -c], [-N b, a]]` of `Γ₀(N)` attached to `A = [[a, b], [N c, d]]`. -/
lemma fricke_aux (N : ℕ) (A : SL(2, ℤ)) (k : ℤ) (hk : A 1 0 = N * k) :
    ∃ B ∈ CongruenceSubgroup.Gamma0 N,
      B 0 0 = A 1 1 ∧ B 0 1 = -k ∧ B 1 0 = -(N * A 0 1) ∧ B 1 1 = A 0 0 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  rw [hk] at hdet
  refine ⟨⟨!![A 1 1, -k; -(N * A 0 1), A 0 0], ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 (by simp), rfl, rfl, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination hdet

/-- **Fricke involution.** For `A ∈ Γ₀(N)`, `W_N A W_N⁻¹` is (the image of) an element of
`Γ₀(N)`. -/
theorem fricke_conj_mem (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ B ∈ CongruenceSubgroup.Gamma0 N,
      ((toQ B : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) =
        fricke N * ((toQ A : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) * (fricke N)⁻¹ := by
  have hq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA)
  obtain ⟨B, hB, h00, h01, h10, h11⟩ := fricke_aux N A k hk
  refine ⟨B, hB, ?_⟩
  rw [fricke_inv N hN, fricke, fricke_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk] <;> field_simp

/-- **Fricke involution, other direction.** For `A ∈ Γ₀(N)`, `W_N⁻¹ A W_N` is (the image of)
an element of `Γ₀(N)`. Together with `fricke_conj_mem`, `W_N` normalizes `Γ₀(N)`. -/
theorem fricke_inv_conj_mem (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ B ∈ CongruenceSubgroup.Gamma0 N,
      ((toQ B : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) =
        (fricke N)⁻¹ * ((toQ A : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) * fricke N := by
  have hq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA)
  obtain ⟨B, hB, h00, h01, h10, h11⟩ := fricke_aux N A k hk
  refine ⟨B, hB, ?_⟩
  rw [fricke_inv N hN, fricke, fricke_inv_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk] <;> field_simp

end MonsterCN
