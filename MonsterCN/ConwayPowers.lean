/-
# Conway moonshine is not power-functorial at `p = 2` (MAR-16)

**MAR-16 (`conway_not_functorial_at_2`).** There are 8 pairs (all kernel-certified) of classes `(g, h)` of `Co₀` with
the following properties.
* Their Conway series `T^s_g(2τ)`, `T^s_h(2τ)` coincide (kernel-certified up to `q³⁹`, each row
  against its own frame shape), and Duncan–Mack-Crane assign them the same group.
* The squares `g², h²` have different series (`a₁ = χ₂₇₆` differs, from ctbllib) and different
  groups.
Examples: `6E, 6J ↦ 3A, 3C`; `18D, 18G ↦ 9A, 9B`; `30F, 30K ↦ 15A, 15E`.

Hence no rule determines the group (or the series) of `g²` from that of `g`.

Note that the series coincide although the frame shapes differ: the two eta quotients differ by
the constant `1`, which the term `χ_g` compensates.

**Contrast.** For every odd prime `p`, equal groups give equal groups of `p`-th powers
(`conway_functorial_odd`), and in the Monster the label of `g^p` is a function of the label of
`g` for every `p` (`monster_functorial`).

So the MAR framework, whose power rule is a function on groups, cannot be applied to the full `Co₀`
table. Together with MAR-15, Conway moonshine is not rigid in the MAR sense.

Group labels use the Duncan–Mack-Crane table with the two corrections of MAR-13 (`corrLabel`).
-/
import MonsterCN.ConwayOdd
import MonsterCN.Data.ConwayFrames

namespace MonsterCN.ConwayPowers

open MonsterCN MonsterCN.Conway MonsterCN.ConwayOdd

/-- All 167 classes. -/
def allC : List Nat := List.range 167

/-- The frame shapes reproduce `χ₂₄` on every power of every class of `Co₀`. -/
theorem frames_match_chi24 :
    allC.all (fun c => (divisorsOf (ordC c)).all fun k =>
      coChi24.getD (powC c k) 0 ==
        ((frameAll c).filter (fun x => k % x.1 == 0)).foldl (fun s x => s + (x.1 : Int) * x.2) 0) =
      true := by
  decide +kernel

/-- Duncan–Mack-Crane labels with the two corrections established by MAR-13. -/
def corrLabel (c : Nat) : String :=
  if c = 73 then "(24|2+12)^{up(1/4)}" else if c = 150 then "(60+12,15,20)^{up(1/2)}" else labC c

/-! ## Certified series for the pair classes -/

def serP (c : Nat) : List Int := ((pairTable.find? fun x => x.1 == c).map Prod.snd).getD []

/-- Division-free certificate (as in `ConwayOdd.rowOK`), using the frame shape `frameAll c`. -/
def rowOKP (c : Nat) : Bool :=
  let fr := frameAll c
  let g := (List.range (PREC + 1)).map fun t =>
    if t = 1 then (serP c).getD 1 0 - frameExp fr 1 else (serP c).getD t 0
  (serP c).length == PREC + 1 && mulSeries g (posProd (eNeg fr)) == posProd (ePos fr)

theorem rowP_28 : rowOKP 28 = true := by decide +kernel
theorem rowP_34 : rowOKP 34 = true := by decide +kernel
/-- The `6F` row (about 8 GB of kernel memory). -/
theorem rowP_29 : rowOKP 29 = true := by decide +kernel
theorem rowP_33 : rowOKP 33 = true := by decide +kernel
theorem rowP_60 : rowOKP 60 = true := by decide +kernel
theorem rowP_67 : rowOKP 67 = true := by decide +kernel
theorem rowP_61 : rowOKP 61 = true := by decide +kernel
theorem rowP_66 : rowOKP 66 = true := by decide +kernel
theorem rowP_108 : rowOKP 108 = true := by decide +kernel
theorem rowP_111 : rowOKP 111 = true := by decide +kernel
theorem rowP_109 : rowOKP 109 = true := by decide +kernel
theorem rowP_110 : rowOKP 110 = true := by decide +kernel
theorem rowP_144 : rowOKP 144 = true := by decide +kernel
theorem rowP_151 : rowOKP 151 = true := by decide +kernel
theorem rowP_145 : rowOKP 145 = true := by decide +kernel
theorem rowP_150 : rowOKP 150 = true := by decide +kernel

/-! ## MAR-16 -/

/-- The eight pairs. Each of their 16 series rows is kernel-certified above (`rowP_*`). -/
def pairs : List (Nat × Nat) :=
  [(28, 34), (29, 33), (60, 67), (61, 66), (108, 111), (109, 110), (144, 151), (145, 150)]

theorem pair_names :
    (pairs.map fun x => (nameC x.1, nameC x.2, nameC (pwC 2 x.1), nameC (pwC 2 x.2))) =
      [("6E", "6J", "3A", "3C"), ("6F", "6I", "3A", "3C"), ("10D", "10I", "5A", "5C"),
       ("10E", "10H", "5A", "5C"), ("18D", "18G", "9A", "9B"), ("18E", "18F", "9A", "9B"),
       ("30F", "30K", "15A", "15E"), ("30G", "30J", "15A", "15E")] := by
  decide +kernel

/-- **MAR-16.** For each pair `(g, h)`, the following hold:
* same order;
* identical certified series up to `q³⁹`;
* the same (corrected) Duncan–Mack-Crane group;
* the squares have different `a₁ = χ₂₇₆` and different groups. -/
theorem conway_not_functorial_at_2 :
    pairs.all (fun x =>
      ordC x.1 == ordC x.2 && serP x.1 == serP x.2 && corrLabel x.1 == corrLabel x.2 &&
      coChi276.getD (pwC 2 x.1) 0 != coChi276.getD (pwC 2 x.2) 0 &&
      corrLabel (pwC 2 x.1) != corrLabel (pwC 2 x.2)) = true := by
  decide +kernel

/-- Consequence: no function `R` on group labels describes squaring in Conway moonshine. -/
theorem no_label_squaring_rule :
    ¬ ∃ R : String → String, ∀ c, c < 167 → corrLabel (pwC 2 c) = R (corrLabel c) := by
  rintro ⟨R, hR⟩
  have h1 := hR 28 (by decide)
  have h2 := hR 34 (by decide)
  have e : corrLabel 28 = corrLabel 34 := by decide +kernel
  have d : corrLabel (pwC 2 28) ≠ corrLabel (pwC 2 34) := by decide +kernel
  exact d (by rw [h1, h2, e])

/-- Contrast: for every odd prime, equal (corrected) groups give equal groups of `p`-th powers. -/
theorem conway_functorial_odd :
    allC.all (fun c => allC.all fun d =>
      corrLabel c != corrLabel d ||
      coPrimes.all fun p => p == 2 || corrLabel (pwC p c) == corrLabel (pwC p d)) = true := by
  decide +kernel

/-- Contrast: in the Monster, the Conway–Norton label of `g^p` is a function of the label of `g`,
for every prime `p ∣ |M|`. -/
theorem monster_functorial :
    (List.range 194).all (fun c => (List.range 194).all fun d =>
      cn c != cn d || monsterPrimes.all fun p => cn (pw p c) == cn (pw p d)) = true := by
  decide +kernel

end MonsterCN.ConwayPowers
