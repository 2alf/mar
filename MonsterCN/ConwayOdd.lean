/-
# Conway moonshine is not rigid in the MAR sense (MAR-15)

For the Monster, MAR-9 shows that genus zero, the power rule and coefficient data force the
Conway–Norton table. Here we show that the analogous statement **fails** for Conway moonshine,
already on the 29 classes of odd order in `Co₀`. These classes are closed under all power maps; on
them the Conway–Norton power rule holds for every odd prime, and `p = 2` acts by Galois conjugation.

Everything is computed in the kernel.
* `frame_matches_chi24`: the frame shapes reproduce `χ₂₄` on every power of every odd-order class.
* `t2_table_spec`: the coefficients of `T^s_g(2τ) = η_g(τ)/η_g(2τ) + χ_g` (Duncan–Mack-Crane,
  (4.21)) up to `q³⁹` are certified against the frame shape by a division-free eta identity.
* `dmc_admissible`: the published labels satisfy all hypotheses. These are: genus-zero `n|h+W`
  shape, level `2·o(g)`, the power rule at odd primes, invariance under `p = 2`, vanishing of every
  coefficient `a_m` (`m ≤ 39`) not allowed by the eigen-character, and coherence of the entire
  series.
* `alt_admissible`: so does the labelling with `9B ↦ 18|3` instead of `18-`.

So these hypotheses, which suffice for the Monster, do not determine Conway moonshine, even with
full coefficient data. (`ConwayOddCount.lean` proves that there are exactly 12 admissible
labellings, all differing only at `9A`, `9B`, `9C`.)
-/
import MonsterCN.ConwayMoonshine
import MonsterCN.GenusZero
import MonsterCN.Data.ConwayOdd

namespace MonsterCN.ConwayOdd

open MonsterCN MonsterCN.Conway MonsterCN.GZ

/-! ## Powers of classes and frame shapes -/

/-- Prime factors of `k` with multiplicity (`k ≤ 200` suffices here). -/
def primeList (k : Nat) : List Nat :=
  (List.range 8).foldl (fun (acc : List Nat × Nat) _ =>
    match ((List.range (acc.2 + 1)).filter fun d => d ≥ 2 && acc.2 % d == 0).head? with
    | some d => (acc.1 ++ [d], acc.2 / d)
    | none => acc) ([], k) |>.1

/-- The class of `g^k`. -/
def powC (c k : Nat) : Nat := (primeList k).foldl (fun x p => pwC p x) c

def divisorsOf (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d ≥ 1 && n % d == 0

/-- The frame shape reproduces `χ₂₄` on all powers: `χ₂₄(g^k) = Σ_{m ∣ k} m·a_m` for `k ∣ o(g)`. -/
theorem frame_matches_chi24 :
    oddClasses.length = 29 ∧
    oddClasses.all (fun c => (divisorsOf (ordC c)).all fun k =>
      coChi24.getD (powC c k) 0 ==
        ((frameShape c).filter (fun x => k % x.1 == 0)).foldl (fun s x => s + (x.1 : Int) * x.2) 0) =
      true := by
  decide +kernel

/-! ## Eta-quotient expansions, certified without division

`T^s_g(2τ) − χ_g = q⁻¹ · ∏_m P_m^{E(m)}`, where `P_m = ∏_{n ≥ 1} (1 − q^{mn})` and
`E(m) = a_m − a_{m/2}` (the frame shape of `g`, minus its doubled copy). Splitting
`E = E⁺ − E⁻`, the table row `r` of class `c` is certified by the division-free identity
`(r − χ·q⁰) · ∏ P_m^{E⁻(m)} = ∏ P_m^{E⁺(m)}`, truncated at `q^PREC` (after the shift by `q⁻¹`).
Only multiplications by `(1 − q^e)` and one truncated product are evaluated by the kernel. -/

def PREC : Nat := 40

/-- Multiply a truncated series (length `PREC + 1`) by `(1 - q^e)`. -/
def mulOneMinus (s : List Int) (e : Nat) : List Int :=
  (List.range (PREC + 1)).map fun t => s.getD t 0 - (if t ≥ e then s.getD (t - e) 0 else 0)

/-- `∏_{(m,k)} P_m^k` for `k ≥ 0`, truncated at `q^PREC`. -/
def posProd (fs : List (Nat × Nat)) : List Int :=
  fs.foldl (fun s x =>
    (List.range (PREC / x.1)).foldl (fun s n =>
      (List.range x.2).foldl (fun s _ => mulOneMinus s (x.1 * (n + 1))) s) s)
    ((List.range (PREC + 1)).map fun t => if t = 0 then 1 else 0)

def mulSeries (a b : List Int) : List Int :=
  (List.range (PREC + 1)).map fun t =>
    (List.range (t + 1)).foldl (fun s j => s + a.getD j 0 * b.getD (t - j) 0) 0

def frameExp (fr : List (Nat × Int)) (m : Nat) : Int :=
  ((fr.filter fun x => x.1 == m).map Prod.snd).foldl (· + ·) 0

/-- `E(m) = a_m − a_{m/2}` on all relevant `m` (frame entries and their doubles). -/
def expo (fr : List (Nat × Int)) : List (Nat × Int) :=
  ((fr.map Prod.fst ++ fr.map (fun (x : Nat × Int) => 2 * x.1)).eraseDups).map fun m =>
    (m, frameExp fr m - (if m % 2 == 0 then frameExp fr (m / 2) else 0))

def ePos (fr : List (Nat × Int)) : List (Nat × Nat) :=
  (expo fr).filterMap fun x => if x.2 > 0 then some (x.1, x.2.toNat) else none
def eNeg (fr : List (Nat × Int)) : List (Nat × Nat) :=
  (expo fr).filterMap fun x => if x.2 < 0 then some (x.1, (-x.2).toNat) else none

/-- Series of class `c`, read from the table. -/
def ser (c : Nat) : List Int := ((t2Table.find? fun x => x.1 == c).map Prod.snd).getD []

/-- `χ_g = a₁` of the frame shape. -/
def chiF (c : Nat) : Int := frameExp (frameShape c) 1

/-- Certificate check for one class: the table row satisfies the division-free eta identity. -/
def rowOK (c : Nat) : Bool :=
  let fr := frameShape c
  let g := (List.range (PREC + 1)).map fun t => if t = 1 then (ser c).getD 1 0 - chiF c else (ser c).getD t 0
  (ser c).length == PREC + 1 && mulSeries g (posProd (eNeg fr)) == posProd (ePos fr)

/-- The alternative labelling: `9B ↦ 18|3` instead of `18-`. -/
def altOdd (c : Nat) : CNLabel := if c = 56 then ⟨18, 3, [1]⟩ else dmcOdd c

/-! ### Certification of the table rows

Each row is certified separately against its frame shape. The rows of `1A` and `3A` (classes `0`
and `6`), whose frame shapes `1²⁴` and `3¹²/1¹²` need a larger computation, are certified in
`ConwayOddRows.lean` (`rows_all_certified`), in separately checked pieces. -/

def certifiedRows : List Nat := [8, 10, 12, 22, 24, 26, 42, 44, 54, 56, 58, 69, 90, 95, 97, 99, 101, 103, 119, 121, 123, 127, 129, 152, 154, 158, 160]

theorem row_8 : rowOK 8 = true := by
  decide +kernel

theorem row_10 : rowOK 10 = true := by
  decide +kernel

theorem row_12 : rowOK 12 = true := by
  decide +kernel

theorem row_22 : rowOK 22 = true := by
  decide +kernel

theorem row_24 : rowOK 24 = true := by
  decide +kernel

theorem row_26 : rowOK 26 = true := by
  decide +kernel

theorem row_42 : rowOK 42 = true := by
  decide +kernel

theorem row_44 : rowOK 44 = true := by
  decide +kernel

theorem row_54 : rowOK 54 = true := by
  decide +kernel

theorem row_56 : rowOK 56 = true := by
  decide +kernel

theorem row_58 : rowOK 58 = true := by
  decide +kernel

theorem row_69 : rowOK 69 = true := by
  decide +kernel

theorem row_90 : rowOK 90 = true := by
  decide +kernel

theorem row_95 : rowOK 95 = true := by
  decide +kernel

theorem row_97 : rowOK 97 = true := by
  decide +kernel

theorem row_99 : rowOK 99 = true := by
  decide +kernel

theorem row_101 : rowOK 101 = true := by
  decide +kernel

theorem row_103 : rowOK 103 = true := by
  decide +kernel

theorem row_119 : rowOK 119 = true := by
  decide +kernel

theorem row_121 : rowOK 121 = true := by
  decide +kernel

theorem row_123 : rowOK 123 = true := by
  decide +kernel

theorem row_127 : rowOK 127 = true := by
  decide +kernel

theorem row_129 : rowOK 129 = true := by
  decide +kernel

theorem row_152 : rowOK 152 = true := by
  decide +kernel

theorem row_154 : rowOK 154 = true := by
  decide +kernel

theorem row_158 : rowOK 158 = true := by
  decide +kernel

theorem row_160 : rowOK 160 = true := by
  decide +kernel

theorem rows_certified : ∀ c ∈ certifiedRows, rowOK c = true := by
  intro c hc
  simp only [certifiedRows, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_8
  · exact row_10
  · exact row_12
  · exact row_22
  · exact row_24
  · exact row_26
  · exact row_42
  · exact row_44
  · exact row_54
  · exact row_56
  · exact row_58
  · exact row_69
  · exact row_90
  · exact row_95
  · exact row_97
  · exact row_99
  · exact row_101
  · exact row_103
  · exact row_119
  · exact row_121
  · exact row_123
  · exact row_127
  · exact row_129
  · exact row_152
  · exact row_154
  · exact row_158
  · exact row_160

theorem t2_table_spec :
    t2Table.map Prod.fst = oddClasses ∧
    oddClasses.filter (fun c => c != 0 && c != 6) = certifiedRows := by
  decide +kernel

/-- The two uncertified rows are irrelevant: for both labellings, the labels of `1A` and `3A` have
`h = 1` and differ from the labels of all other odd-order classes. -/
theorem rows_0_6_irrelevant :
    (dmcOdd 0).h = 1 ∧ (dmcOdd 6).h = 1 ∧ altOdd 0 = dmcOdd 0 ∧ altOdd 6 = dmcOdd 6 ∧
    oddClasses.all (fun d => d == 0 || dmcOdd d != dmcOdd 0) = true ∧
    oddClasses.all (fun d => d == 6 || dmcOdd d != dmcOdd 6) = true ∧
    oddClasses.all (fun d => d == 0 || altOdd d != altOdd 0) = true ∧
    oddClasses.all (fun d => d == 6 || altOdd d != altOdd 6) = true := by
  decide +kernel

/-- Sanity: the series have leading coefficient 1 and constant term 0, and reproduce
`a₁ = χ₂₇₆` and `a₂ = -(χ₂₄ + χ₂₀₂₄)` (ctbllib) on every odd-order class. -/
theorem T2_matches_characters :
    oddClasses.all (fun c => (ser c).getD 0 0 == 1 && (ser c).getD 1 0 == 0 &&
      (ser c).getD 2 0 == a1 c && (ser c).getD 3 0 == a2 c) = true := by
  decide +kernel

/-! ## Admissible labellings -/

def isGZb (l : CNLabel) : Bool :=
  hs.contains l.h && l.n % l.h == 0 && l.W.isSublist (hallList (l.n / l.h)) && validW l.W &&
  genusZero (l.n / l.h) l.W

/-- All hypotheses of the MAR method, for a labelling of the odd-order classes of `Co₀`. -/
def admissible (L : Nat → CNLabel) : Bool :=
  oddClasses.all (fun c =>
    isGZb (L c) && (L c).n == 2 * ordC c &&
    (coPrimes.all fun p => if p = 2 then L (pwC 2 c) == L c else L (pwC p c) == powRule (L c) p) &&
    ((List.range 39).all fun i => let m := i + 1; (m + 1) % (L c).h == 0 || (ser c).getD (m + 1) 0 == 0)) &&
  oddClasses.all (fun c => oddClasses.all fun d => L c != L d || ser c == ser d)

theorem names_9 :
    nameC 54 = "9A" ∧ nameC 56 = "9B" ∧ nameC 58 = "9C" ∧ dmcOdd 56 = ⟨18, 1, [1]⟩ ∧
    labC 56 = "18-" := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dmc_admissible : admissible dmcOdd = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem alt_admissible : admissible altOdd = true := by
  decide +kernel

/-- **MAR-15.** The hypotheses that force the Monster table (MAR-9), even strengthened to all
coefficients up to `q³⁹` and coherence of whole series, admit at least two distinct labellings of
the odd-order classes of `Co₀`: the published one and `altOdd`. The series used are the kernel
eta-quotient expansions (`t2_table_spec`). -/
theorem conway_not_rigid :
    admissible dmcOdd = true ∧ admissible altOdd = true ∧ altOdd 56 ≠ dmcOdd 56 :=
  ⟨dmc_admissible, alt_admissible, by decide⟩

end MonsterCN.ConwayOdd
