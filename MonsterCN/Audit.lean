/-
# Audit of published moonshine tables (MAR-17)

Machine-checked confirmations of three errors found by auditing published tables against the GAP
Character Table Library (ctbllib 1.3.11). The fourth confirmed error, the two labels in
Duncan–Mack-Crane Table A.1, is MAR-13 (`MonsterCN.Conway.dmc_label_inconsistency`).

* **F1 (`cm_46c`).** Cummins–Matias, *(2+)-Replication and the Baby Monster*, SIGMA 14 (2018) 060,
  Table 3, prints the class of `g²` for `g ∈ 46c` as `23c`. But `2.B` has exactly two classes of
  order 23 (`23a`, `23b`), and the 2-power map sends `46c` to `23a`.
* **F2 (`cm_94b`).** Same table: it prints `94a ↦ 47a` and `94b ↦ 47a` for the class of `g²`. The
  2-power map gives `94b ↦ 47b`. Independently of naming, both classes of order 94 have 47th power
  the central involution, and the 2-power map is injective on them. So two different classes
  cannot both square into `47a`.
* **F3 (`dgo_count`).** Duncan–Griffin–Ono, *Moonshine*, Res. Math. Sci. 2 (2015), Appendix A,
  says "The Monster group has 196 conjugacy classes in total". The ATLAS table has 194, with exactly
  22 pairs of distinct mutually inverse classes (the 22 merged entries of their table).

Class names are GAP-derived (uppercase here; Cummins–Matias write them in lowercase).
-/
import MonsterCN.BabyMonster
import MonsterCN.Checks

namespace MonsterCN.Audit

open MonsterCN MonsterCN.Baby

/-! ## F1 and F2: Cummins–Matias Table 3 -/

theorem cm_46c :
    nameB 223 = "46C" ∧ pwB 2 223 = 146 ∧ nameB 146 = "23A" ∧
    -- the classes of order 23 in 2.B are exactly 23A and 23B
    (List.range 247).filter (fun c => ordB c == 23) = [146, 148] ∧ nameB 148 = "23B" ∧
    -- there is no class named 23C
    (List.range 247).all (fun c => nameB c != "23C") = true := by
  decide +kernel

theorem cm_94b :
    nameB 228 = "94A" ∧ nameB 230 = "94B" ∧ nameB 227 = "47A" ∧ nameB 229 = "47B" ∧
    -- the classes of order 94
    (List.range 247).filter (fun c => ordB c == 94) = [228, 230] ∧
    -- 2-power map: 94A -> 47A, 94B -> 47B (not 47A)
    pwB 2 228 = 227 ∧ pwB 2 230 = 229 ∧
    -- both 47th powers are the central involution (class 2A of 2.B)
    nameB 1 = "2A" ∧ pwB 47 228 = 1 ∧ pwB 47 230 = 1 ∧
    -- hence (g = z·(g²)^24) squaring is injective on the classes of order 94
    pwB 2 228 ≠ pwB 2 230 := by
  decide +kernel

/-! ## F3: Duncan–Griffin–Ono, Appendix A -/

/-- Prime factors with multiplicity (trial division with fuel). -/
def primeFactorsM (k : Nat) : List Nat :=
  (List.range 20).foldl (fun (acc : List Nat × Nat) _ =>
    match ((List.range (acc.2 + 1)).filter fun d => d ≥ 2 && acc.2 % d == 0).head? with
    | some d => (acc.1 ++ [d], acc.2 / d)
    | none => acc) ([], k) |>.1

/-- The class of `g^k` in the Monster, by composing prime power maps. -/
def powM (c k : Nat) : Nat := (primeFactorsM k).foldl (fun x p => pw p x) c

/-- An exponent `k ≡ -1 (mod o(g))` all of whose prime factors divide `|M|`, so that `g^k = g⁻¹`
is computable from the stored power maps. -/
def invExp (c : Nat) : Nat :=
  let o := ordOf c
  (((List.range 60).map fun t => o - 1 + t * o).find? fun k =>
    k ≥ 1 && (primeFactorsM k).all monsterPrimes.contains).getD 0

/-- The class of `g⁻¹`. -/
def invM (c : Nat) : Nat := if ordOf c ≤ 2 then c else powM c (invExp c)

/-- Pairs of distinct mutually inverse classes `(c, d)` with `c < d`. -/
def inversePairs : List (Nat × Nat) :=
  ((List.range 194).filter fun c => c < invM c).map fun c => (c, invM c)

theorem dgo_count :
    className.length = 194 ∧
    -- the exponents used are valid: k ≡ -1 mod o(g) and k ≥ 1, for every class of order > 2
    (List.range 194).all (fun c => ordOf c ≤ 2 ||
      (invExp c ≥ 1 && invExp c % ordOf c == ordOf c - 1)) = true ∧
    -- inversion is an involution on classes
    (List.range 194).all (fun c => invM (invM c) == c) = true ∧
    -- exactly 22 pairs of distinct mutually inverse classes
    inversePairs.length = 22 ∧
    (inversePairs.map fun x => (nameOf x.1, nameOf x.2)) =
      [("23A", "23B"), ("31A", "31B"), ("39C", "39D"), ("40C", "40D"), ("44A", "44B"),
       ("46A", "46B"), ("46C", "46D"), ("47A", "47B"), ("56B", "56C"), ("59A", "59B"),
       ("62A", "62B"), ("69A", "69B"), ("71A", "71B"), ("78B", "78C"), ("87A", "87B"),
       ("88A", "88B"), ("92A", "92B"), ("93A", "93B"), ("94A", "94B"), ("95A", "95B"),
       ("104A", "104B"), ("119A", "119B")] := by
  decide +kernel

end MonsterCN.Audit
