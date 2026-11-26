/-
# Kernel-checked facts about the Monster class data and the Conway–Norton table

Every theorem here is a statement about the finite data in `MonsterCN.Data.*`, proved by
kernel evaluation (`decide +kernel`); no `native_decide`, no `sorry`, no new axioms.

Contents:
* §1–§2 are integrity checks of the transcribed ATLAS data.
* §3–§4 machine-check *known* statements of Conway–Norton (1979) against the ATLAS data.
* §5 records simple counterexamples to natural-sounding strengthenings.
-/
import MonsterCN.Basic
import MonsterCN.Data.Catalogue

namespace MonsterCN

/-! ## §1 Shape and integrity of the ATLAS data -/

theorem lengths :
    className.length = 194 ∧ ord.length = 194 ∧ cent.length = 194 ∧ cnTable.length = 194 ∧
    chi2.length = 194 ∧ chi3.length = 194 ∧ chi4.length = 194 ∧
    monsterPrimes.all (fun p => (pmap p).length == 194) = true := by
  decide +kernel

/-- `|M| = 2⁴⁶·3²⁰·5⁹·7⁶·11²·13³·17·19·23·29·31·41·47·59·71`. -/
theorem monsterOrder_eq :
    monsterOrder = 2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 *
      59 * 71 := by
  decide +kernel

/-- Every centralizer order divides `|M|`, and the **class equation** holds:
`Σ_C |M|/|C_M(g_C)| = |M|`. -/
theorem class_equation :
    classes.all (fun c => monsterOrder % centOf c == 0) = true ∧
    (classes.map fun c => monsterOrder / centOf c).sum = monsterOrder := by
  decide +kernel

/-- Weighted sum `Σ_C |C| · f(C)`, i.e. `|M|·⟨f, 1⟩`-type sums. -/
def wsum (f : Nat → Int) : Int :=
  (classes.map fun c => ((monsterOrder / centOf c : Nat) : Int) * f c).sum

/-- First orthogonality relations for `1, χ₂, χ₃, χ₄` (all rational-valued):
`⟨χᵢ, χⱼ⟩ = δᵢⱼ`. This certifies the three transcribed character rows. -/
theorem orthogonality :
    wsum (fun c => chi2.getD c 0) = 0 ∧ wsum (fun c => chi3.getD c 0) = 0 ∧
    wsum (fun c => chi4.getD c 0) = 0 ∧
    wsum (fun c => chi2.getD c 0 ^ 2) = monsterOrder ∧
    wsum (fun c => chi3.getD c 0 ^ 2) = monsterOrder ∧
    wsum (fun c => chi4.getD c 0 ^ 2) = monsterOrder ∧
    wsum (fun c => chi2.getD c 0 * chi3.getD c 0) = 0 ∧
    wsum (fun c => chi2.getD c 0 * chi4.getD c 0) = 0 ∧
    wsum (fun c => chi3.getD c 0 * chi4.getD c 0) = 0 := by
  decide +kernel

/-- Degrees: `χ₂(1) = 196883`, `χ₃(1) = 21296876`, `χ₄(1) = 842609326`, so
`a₁(1A) = 196884`, `a₂(1A) = 21493760`, `a₃(1A) = 864299970` — the coefficients of `j - 744`. -/
theorem j_coefficients :
    coeff 1 0 = 196884 ∧ coeff 2 0 = 21493760 ∧ coeff 3 0 = 864299970 := by
  decide +kernel

/-! ## §2 Power maps and element orders -/

/-- Power maps send classes to classes, and are compatible with element orders:
`o(g^p) = o(g)/gcd(o(g),p)`. -/
theorem pw_ord :
    classes.all (fun c => monsterPrimes.all fun p =>
      pw p c < 194 && ordOf (pw p c) == ordOf c / Nat.gcd (ordOf c) p) = true := by
  decide +kernel

/-- Only `1A` has order 1. (Together with `pw_ord`, this determines `ord` from the power maps:
for `p ∣ o(g)` the `p`-th power has order `o(g)/p`.) -/
theorem ord_one_iff : classes.all (fun c => (ordOf c == 1) == (c == 0)) = true := by
  decide +kernel

/-! ## §3 Shape of the Conway–Norton labels (known; CN 1979 §3) -/

/-- For every class `g`: `n = o(g)`, `h ∣ gcd(o(g), 24)`, and `W` is a subgroup of the group of
Hall divisors of `n/h` (contains `1`, consists of Hall divisors, closed under `alMul`).
In particular the level `N = n·h = o(g)·h` divides `24·o(g)`. -/
theorem cn_shape :
    classes.all (fun c =>
      let l := cn c
      l.n == ordOf c && l.h != 0 && Nat.gcd l.n 24 % l.h == 0 &&
      l.W.contains 1 &&
      l.W.all (isHall (l.n / l.h)) &&
      l.W.all (fun e => l.W.all fun f => l.W.contains (alMul e f))) = true := by
  decide +kernel

/-- **Conway–Norton power rule**, checked against the ATLAS power maps for all
194 classes and all 15 primes: `Γ_{g^p} = powRule Γ_g p`. -/
theorem cn_power_rule :
    classes.all (fun c => monsterPrimes.all fun p => cn (pw p c) == powRule (cn c) p) = true := by
  decide +kernel

/-- There are exactly 171 distinct moonshine groups among the 194 classes. -/
theorem card_distinct_labels : cnTable.eraseDups.length = 171 := by
  decide +kernel

/-- Equal labels occur exactly for Galois-conjugate classes (one Galois power map step), with
the single exception `{27A, 27B}` (classes 90, 91), which are not Galois conjugate. -/
theorem label_fibres :
    classes.all (fun c => classes.all fun d =>
      cn c != cn d || c == d ||
      monsterPrimes.any (fun p => ordOf c % p != 0 && pw p c == d) ||
      (c == 90 && d == 91) || (c == 91 && d == 90)) = true ∧
    monsterPrimes.all (fun p => pw p 90 != 91 && pw p 91 != 90) = true ∧
    nameOf 90 = "27A" ∧ nameOf 91 = "27B" ∧ cn 90 = cn 91 := by
  decide +kernel

/-- Converse direction: Galois-conjugate classes (one prime power map with `p ∤ o(g)`) have the
same label. -/
theorem galois_same_label :
    classes.all (fun c => monsterPrimes.all fun p =>
      ordOf c % p == 0 || cn (pw p c) == cn c) = true := by
  decide +kernel

/-- `27A` and `27B` are rational: every prime power map with `p ∤ 27` fixes each of them (and the
residues of these primes generate `(ℤ/27)ˣ`, e.g. `2` alone does). -/
theorem rational_27 :
    monsterPrimes.all (fun p => 27 % p == 0 || (pw p 90 == 90 && pw p 91 == 91)) = true ∧
    ((List.range 18).map (fun k => 2 ^ k % 27)).eraseDups.length = 18 := by
  decide +kernel

/-- The catalogue (`Data/Catalogue.lean`) is exactly the set of labels occurring in the table,
without repetition. -/
theorem catalogue_spec :
    catalogue.all (fun l => cnTable.contains l) = true ∧
    cnTable.all (fun l => catalogue.contains l) = true ∧
    catalogue.eraseDups.length = catalogue.length ∧ catalogue.length = 171 := by
  decide +kernel

/-! ## §4 Consistency of the labels with the character table (first three coefficients)

If `Γ_g = n|h + …` then `T_g(τ + 1/h) = e^{-2πi/h} T_g(τ)` (CN 1979), so `a_m(g) = 0` unless
`h ∣ m + 1`. We check this for `m = 1, 2, 3` against the ATLAS characters, and check that classes
with the same label have the same coefficients (as they must, a normalized Hauptmodul being
unique). These are two independent data sources agreeing. -/

theorem coeff_vanishing :
    classes.all (fun c => [1, 2, 3].all fun m =>
      (m + 1) % (cn c).h == 0 || coeff m c == 0) = true := by
  decide +kernel

theorem coeff_coherent :
    classes.all (fun c => classes.all fun d =>
      cn c != cn d || [1, 2, 3].all fun m => coeff m c == coeff m d) = true := by
  decide +kernel

/-! ## §5 Counterexamples to natural strengthenings -/

/-- The pair (element order, centralizer order) does **not** determine `Γ_g`:
`16B` and `16C` both have order 16 and centralizer order 8192, but `Γ_{16B} = 16-` while
`Γ_{16C} = 16+`. (See `MonsterCN.sigma_automorphism` for the full explanation.) -/
theorem not_determined_by_order_and_centralizer :
    nameOf 54 = "16B" ∧ nameOf 55 = "16C" ∧ ordOf 54 = ordOf 55 ∧ centOf 54 = centOf 55 ∧
    cn 54 ≠ cn 55 := by
  decide +kernel

/-- The Fricke property is **not** inherited by powers: `4A` is Fricke (`4+`) but
`4A² = 2B` is not (`2-`). -/
theorem fricke_not_power_closed :
    nameOf 6 = "4A" ∧ isFricke (cn 6) = true ∧ pw 2 6 = 2 ∧ nameOf 2 = "2B" ∧
    isFricke (cn 2) = false := by
  decide +kernel

/-- The tempting strengthening `h ∣ n/h` (equivalently `h² ∣ n`) of `h ∣ gcd(n, 24)` is
**false**: `3C` has `Γ = 3|3`, so `n/h = 1`. (It fails for 25 classes; `cn_shape` proves the
correct condition `h ∣ gcd(n, 24)`.) -/
theorem h_not_dvd_n_div_h :
    nameOf 5 = "3C" ∧ cn 5 = ⟨3, 3, [1]⟩ := by
  decide +kernel

end MonsterCN
