/-
# The Duncan–Mack-Crane erratum: all computations kernel-checked (MAR-13, complete)

This file certifies, in the Lean kernel, every *computational* step of the proof that
* the printed labels of `12E` and `30J` in Duncan–Mack-Crane, Table A.1, are wrong, and
* the correct groups are `Γ_{12E} = (24|2+12)^{↑1/4}` and `Γ_{30J} = (60+12,15,20)^{↑1/2}`.

Notation: `F_g(τ) := T^s_g(2τ) = q⁻¹ ∏_δ P_δ^{r_δ} + χ_g` with `P_δ = ∏_{n≥1}(1 − q^{δn})`, where
`r = E(g)` comes from the frame shape (Duncan–Mack-Crane (4.21)).

**Classical theorems used as external inputs (not formalized: Mathlib has no theory of eta
quotients or modular curves).**
* (C1) Newman's criterion: `newmanOK r M` implies that `∏ η(δτ)^{r_δ}` is invariant under `Γ₀(M)`.
* (C2) Ligozat's formula: the order at a cusp `a/d` in the local uniformizer of `X₀(M)` is `ordQ r M d`.
* (C3) `η` has no zeros or poles in the upper half-plane. Valence formula: a nonzero modular function
  on a compact curve has equally many zeros and poles. Normalizer elements permute cusps, and a
  normalized Hauptmodul determines its group.
* (C4) Euler: `∏_n (1 − (−q^δ)^n) = P_{2δ}³ / (P_δ P_{4δ})` for odd `δ` (the `q ↦ −q` twist).
  This is also kernel-checked to high order below (`twist_identity_check`).

**What the kernel checks** (all `decide +kernel`, no `native_decide`):
1. frame shapes ↔ `χ₂₄` on all powers;
2. the printed labels and the coefficient mismatches;
3. exact identities `F_{12E} = F_{12L} = F_{12M}` and `F_{30J} = −F_{30K}(τ+½)`. Each is an exponent
   or series equality beyond the pole bound computed from (C2), with Newman levels (C1);
4. `Γ_{30K} = 60+12,15,20`: Newman level 60, cusp-divisor invariance under `W₁₂, W₁₅, W₂₀`,
   elliptic elements in the cosets of `W₁₅` and `W₂₀`, `W₁₅W₂₀ ≡ W₁₂`, and degree 4 = coset count;
5. `Γ_G = 24|2+12` for `G = i·F_{12E}(τ+¼)`: Newman level 48, support in odd powers, Fricke
   divisor invariance plus an elliptic element, the coset table of `Γ₀(24|2)+12` modulo `Γ₀(48)` (8
   cosets) with its sign character, a kernel of size 4, and degree 4.
-/
import MonsterCN.ConwayMoonshine
import MonsterCN.Data.Erratum

namespace MonsterCN.Erratum

open MonsterCN.Conway

/-! ## Frame shapes and exponent vectors -/

def primeList (k : Nat) : List Nat :=
  ((List.range 8).foldl (fun (acc : List Nat × Nat) _ =>
    match ((List.range (acc.2 + 1)).filter fun d => d ≥ 2 && acc.2 % d == 0).head? with
    | some d => (acc.1 ++ [d], acc.2 / d)
    | none => acc) ([], k)).1

def powC (c k : Nat) : Nat := (primeList k).foldl (fun x p => pwC p x) c
def divs (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d ≥ 1 && n % d == 0

theorem frames_match_chi24 :
    erratumClasses.all (fun c => (divs (ordC c)).all fun k =>
      coChi24.getD (powC c k) 0 ==
        ((frameOf c).filter (fun x => k % x.1 == 0)).foldl (fun s x => s + (x.1 : Int) * x.2) 0) =
      true := by
  decide +kernel

/-- Coefficient of `δ` in an exponent list (entries with equal keys are summed). -/
def cf (r : List (Nat × Int)) (δ : Nat) : Int := ((r.filter fun x => x.1 == δ).map Prod.snd).foldl (· + ·) 0

/-- `E(m) = a_m − a_{m/2}`: exponents of `η_g(τ)/η_g(2τ)`. -/
def expo (fr : List (Nat × Int)) : List (Nat × Int) :=
  (fr.map fun x => (x.1, x.2)) ++ (fr.map fun x => (2 * x.1, -x.2))

def chiOf (c : Nat) : Int := cf (frameOf c) 1

/-- `q ↦ −q` twist of the products (C4). -/
def twistMinus (r : List (Nat × Int)) : List (Nat × Int) :=
  r.flatMap fun x => if x.1 % 2 == 0 then [x] else [(2 * x.1, 3 * x.2), (x.1, -x.2), (4 * x.1, -x.2)]

/-- `q ↦ i q` twist (requires all `δ` even): `δ ≡ 2 (4)` behaves like `q ↦ −q` on `q^δ` (C4). -/
def twistI (r : List (Nat × Int)) : List (Nat × Int) :=
  r.flatMap fun x => if x.1 % 4 == 0 then [x] else [(2 * x.1, 3 * x.2), (x.1, -x.2), (4 * x.1, -x.2)]

/-- Exponent lists as functions on `δ ≤ bound`. -/
def sameExp (r s : List (Nat × Int)) (bound : Nat) : Bool :=
  (List.range (bound + 1)).all fun δ => cf r δ == cf s δ

def keys (r : List (Nat × Int)) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter fun δ => δ ≥ 1 && cf r δ != 0

/-! ## Truncated power series (multiplication only) -/

def mulOneMinus (P : Nat) (s : List Int) (e : Nat) : List Int :=
  (List.range (P + 1)).map fun t => s.getD t 0 - (if t ≥ e then s.getD (t - e) 0 else 0)

/-- `∏ P_δ^{k}` over entries with `k > 0` (or `k < 0` if `neg`), truncated at `q^P`. -/
def prodPart (P : Nat) (r : List (Nat × Int)) (bound : Nat) (neg : Bool) : List Int :=
  (keys r bound).foldl (fun s δ =>
    let k := cf r δ
    let m := if neg then (if k < 0 then (-k).toNat else 0) else (if k > 0 then k.toNat else 0)
    (List.range (P / δ)).foldl (fun s n =>
      (List.range m).foldl (fun s _ => mulOneMinus P s (δ * (n + 1))) s) s)
    ((List.range (P + 1)).map fun t => if t = 0 then 1 else 0)

def mulS (P : Nat) (a b : List Int) : List Int :=
  (List.range (P + 1)).map fun t => (List.range (t + 1)).foldl (fun s j => s + a.getD j 0 * b.getD (t - j) 0) 0

def addShift1 (P : Nat) (a b : List Int) (c : Int) : List Int :=
  (List.range (P + 1)).map fun t => a.getD t 0 + (if t ≥ 1 then c * b.getD (t - 1) 0 else 0)

/-- `q·F_A ≡ q·F_B (mod q^{P+1})`, i.e. `F_A − F_B = O(q^P)`, by cross-multiplication with the
denominators of both sides: `X_A·N = X_B·N` with `X = ∏P^r + χ q` and `N` invertible. -/
def seriesAgree (P : Nat) (rA rB : List (Nat × Int)) (cA cB : Int) (bound : Nat) : Bool :=
  let nA := prodPart P rA bound true
  let nB := prodPart P rB bound true
  let N := mulS P nA nB
  addShift1 P (mulS P (prodPart P rA bound false) nB) N cA ==
  addShift1 P (mulS P (prodPart P rB bound false) nA) N cB

/-! ## Newman, Ligozat, degrees -/

def vp (p n : Nat) : Nat := ((List.range (n + 1)).filter fun k => k ≥ 1 && n % p ^ k == 0).length
def isPrimeN (n : Nat) : Bool := 2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

def newmanOK (r : List (Nat × Int)) (M : Nat) : Bool :=
  (keys r M).all (fun δ => M % δ == 0) && (keys r 1000).all (fun δ => δ ≤ M) &&
  ((keys r M).map fun δ => cf r δ).foldl (· + ·) 0 == 0 &&
  ((keys r M).map fun δ => Int.ofNat δ * cf r δ).foldl (· + ·) 0 % 24 == 0 &&
  ((keys r M).map fun δ => ((M / δ : Nat) : Int) * cf r δ).foldl (· + ·) 0 % 24 == 0 &&
  ((List.range (M + 1)).filter isPrimeN).all fun p =>
    ((keys r M).map fun δ => (vp p δ : Int) * cf r δ).foldl (· + ·) 0 % 2 == 0

/-- Ligozat numerator/denominator at level `d`: `ord = num / (24·gcd(d,M/d)·d)`. -/
def ordNum (r : List (Nat × Int)) (M d : Nat) : Int :=
  ((keys r M).map fun δ => ((Nat.gcd d δ ^ 2 * (M / δ) : Nat) : Int) * cf r δ).foldl (· + ·) 0
def ordDen (M d : Nat) : Int := (24 * Nat.gcd d (M / d) * d : Nat)
def ordInt (r : List (Nat × Int)) (M d : Nat) : Bool := ordNum r M d % ordDen M d == 0
def ord (r : List (Nat × Int)) (M d : Nat) : Int := ordNum r M d / ordDen M d

def phiN (n : Nat) : Nat := ((List.range n).filter fun k => Nat.gcd (k + 1) n == 1).length

/-- Total pole order on `X₀(M)`. -/
def degree (r : List (Nat × Int)) (M : Nat) : Int :=
  ((divs M).map fun d => (phiN (Nat.gcd d (M / d)) : Int) * max 0 (-(ord r M d))).foldl (· + ·) 0

/-- Pole bound for `F_A − F_B` away from `∞`. -/
def poleBound (rA rB : List (Nat × Int)) (M : Nat) : Int :=
  (((divs M).filter (· != M)).map fun d =>
    (phiN (Nat.gcd d (M / d)) : Int) * max 0 (max (-(ord rA M d)) (-(ord rB M d)))).foldl (· + ·) 0

/-! ## Cusp action, Atkin–Lehner elements, cosets -/

def cuspLevel (x y : Int) (M : Nat) : Nat :=
  if y = 0 then M else Nat.gcd (y.natAbs / Nat.gcd x.natAbs y.natAbs) M

/-- Every cusp `a/d` (`0 ≤ a < d`, `gcd(a,d)=1`) and `∞` is mapped by `s` to a cusp whose Ligozat
order equals its own (C2, C3): the divisor of the eta quotient is `s`-invariant. -/
def divInv (r : List (Nat × Int)) (M : Nat) (s : Int × Int × Int × Int) : Bool :=
  let (a, b, c, d) := s
  ((divs M).all fun dd => ((List.range dd).filter fun x => Nat.gcd x dd == 1).all fun x =>
    let X := a * x + b * dd; let Y := c * x + d * dd
    ord r M (cuspLevel X Y M) == ord r M dd) &&
  ord r M (cuspLevel a c M) == ord r M M

def det4 (s : Int × Int × Int × Int) : Int := s.1 * s.2.2.2 - s.2.1 * s.2.2.1
def trace4 (s : Int × Int × Int × Int) : Int := s.1 + s.2.2.2

/-- `s = [[e x, y],[M z, e w]]` with determinant `e`: an Atkin–Lehner element `W_e` of `Γ₀(M)`. -/
def isAL (M e : Nat) (s : Int × Int × Int × Int) : Bool :=
  s.1 % e == 0 && s.2.2.2 % e == 0 && s.2.2.1 % M == 0 && det4 s == e
def elliptic (s : Int × Int × Int × Int) : Bool := trace4 s * trace4 s < 4 * det4 s

def mm (p q : Int × Int × Int × Int) : Int × Int × Int × Int :=
  (p.1 * q.1 + p.2.1 * q.2.2.1, p.1 * q.2.1 + p.2.1 * q.2.2.2,
   p.2.2.1 * q.1 + p.2.2.2 * q.2.2.1, p.2.2.1 * q.2.1 + p.2.2.2 * q.2.2.2)
def adj (m : Int × Int × Int × Int) : Int × Int × Int × Int := (m.2.2.2, -m.2.1, -m.2.2.1, m.1)
def prim (m : Int × Int × Int × Int) : Int × Int × Int × Int :=
  let g : Int := (Nat.gcd (Nat.gcd m.1.natAbs m.2.1.natAbs) (Nat.gcd m.2.2.1.natAbs m.2.2.2.natAbs) : Nat)
  (m.1 / g, m.2.1 / g, m.2.2.1 / g, m.2.2.2 / g)

/-- `p ~ q` modulo scalars and right multiplication by `Γ₀(M)`. -/
def sameCoset (M : Nat) (p q : Int × Int × Int × Int) : Bool :=
  let X := prim (mm (adj p) q)
  (det4 X == 1 || det4 X == -1 && false) && X.2.2.1 % M == 0 && det4 X == 1

/-- `reps` is closed under right multiplication by `gens` modulo `Γ₀(M)` and pairwise distinct:
it is the full set of cosets of the generated group (contains the identity). -/
def closedTable (M : Nat) (reps gens : List (Int × Int × Int × Int)) : Bool :=
  reps.contains (1, 0, 0, 1) &&
  (reps.all fun g => gens.all fun s => reps.any fun h => sameCoset M (mm g s) h) &&
  ((List.range reps.length).all fun i => (List.range reps.length).all fun j =>
    i == j || !sameCoset M (reps.getD i (1, 0, 0, 1)) (reps.getD j (1, 0, 0, 1)))

/-! ## 1–2. Data, labels and mismatches (12E = 73, 12L = 81, 12M = 82, 30J = 150, 30G = 145,
30K = 151, 6M = 37) -/

theorem printed_labels_and_mismatch :
    nameC 73 = "12E" ∧ nameC 81 = "12L" ∧ nameC 82 = "12M" ∧ nameC 150 = "30J" ∧
    nameC 145 = "30G" ∧ nameC 151 = "30K" ∧ nameC 37 = "6M" ∧
    labC 73 = "12-" ∧ labC 37 = "12-" ∧ labC 81 = "(24|2+12)^{up(1/4)}" ∧
    labC 150 = "60+12,15,20" ∧ labC 151 = "60+12,15,20" ∧ labC 145 = "(60+12,15,20)^{up(1/2)}" ∧
    a1 73 = -2 ∧ a1 37 = 2 ∧ a2 150 = -1 ∧ a2 151 = 1 := by
  decide +kernel

/-! ## 3. Exact identities -/

def r (c : Nat) : List (Nat × Int) := expo (frameOf c)

theorem twist_identity_check :
    -- (C4) for δ = 1, sanity to q^60: ∏(1-(-q)^n) = P2^3 / (P1 P4), cross-multiplied
    (let P := 60
     let lhs := (List.range P).foldl (fun s n => let m := n + 1
        if m % 2 == 0 then mulOneMinus P s m
        else (List.range (P + 1)).map fun t => s.getD t 0 + (if t ≥ m then s.getD (t - m) 0 else 0))
        ((List.range (P + 1)).map fun t => if t = 0 then 1 else 0)
     mulS P lhs (prodPart P [(1, 1), (4, 1)] 4 false) == prodPart P [(2, 3)] 2 false) = true := by
  decide +kernel

/-- `F_{30J}(τ) = −F_{30K}(τ+½)`: the `q ↦ −q` twist of `30K`'s exponents equals `30J`'s exactly
(C4), with `χ = 0` on both sides; and both have Newman level 60. -/
theorem identity_30J_30K :
    sameExp (twistMinus (r 151)) (r 150) 240 = true ∧ chiOf 150 = 0 ∧ chiOf 151 = 0 ∧
    newmanOK (r 150) 60 = true ∧ newmanOK (r 151) 60 = true := by
  decide +kernel

/-- `F_{12E} = F_{12L} = F_{12M}`: common Newman level 24, pole bound 1 away from `∞` (C2),
simple pole at `∞`, and agreement to `O(q⁵)` > bound, so the difference vanishes (C3).
`F_{30J} = F_{30G}`: level 60, bound 3, agreement to `O(q⁷)`. -/
theorem identities_12E_30J :
    newmanOK (r 73) 24 = true ∧ newmanOK (r 81) 24 = true ∧ newmanOK (r 82) 24 = true ∧
    (divs 24).all (fun d => ordInt (r 73) 24 d && ordInt (r 81) 24 d && ordInt (r 82) 24 d) = true ∧
    ord (r 73) 24 24 = -1 ∧ ord (r 81) 24 24 = -1 ∧ ord (r 82) 24 24 = -1 ∧
    poleBound (r 73) (r 81) 24 = 1 ∧ poleBound (r 73) (r 82) 24 = 1 ∧
    seriesAgree 5 (r 73) (r 81) (chiOf 73) (chiOf 81) 48 = true ∧
    seriesAgree 5 (r 73) (r 82) (chiOf 73) (chiOf 82) 48 = true ∧
    newmanOK (r 145) 60 = true ∧
    (divs 60).all (fun d => ordInt (r 150) 60 d && ordInt (r 145) 60 d) = true ∧
    ord (r 150) 60 60 = -1 ∧ ord (r 145) 60 60 = -1 ∧
    poleBound (r 150) (r 145) 60 = 3 ∧
    seriesAgree 7 (r 150) (r 145) (chiOf 150) (chiOf 145) 120 = true := by
  decide +kernel

/-! ## 4. `Γ_{30K} = 60+12,15,20` exactly -/

def W12 : Int × Int × Int × Int := (12, -1, -3300, 276)
def W15 : Int × Int × Int × Int := (15, -2, -3480, 465)
def W20 : Int × Int × Int × Int := (20, -1, -3180, 160)
def E15 : Int × Int × Int × Int := (-435, 1, -189240, 435)
def E20 : Int × Int × Int × Int := (-580, 1, -336420, 580)
def K60 : List (Int × Int × Int × Int) := [(1, 0, 0, 1), W12, W15, W20]

theorem group_30K :
    isAL 60 12 W12 = true ∧ isAL 60 15 W15 = true ∧ isAL 60 20 W20 = true ∧
    divInv (r 151) 60 W12 = true ∧ divInv (r 151) 60 W15 = true ∧ divInv (r 151) 60 W20 = true ∧
    isAL 60 15 E15 = true ∧ elliptic E15 = true ∧ isAL 60 20 E20 = true ∧ elliptic E20 = true ∧
    sameCoset 60 (prim (mm W15 W20)) W12 = true ∧
    closedTable 60 K60 [W12, W15, W20] = true ∧
    (divs 60).all (fun d => ordInt (r 151) 60 d) = true ∧ degree (r 151) 60 = 4 := by
  decide +kernel

/-! ## 5. `Γ_G = 24|2+12` exactly, `G = i·F_{12E}(τ+¼)` -/

def rG : List (Nat × Int) := twistI (r 73)
def T2 : Int × Int × Int × Int := (2, 1, 0, 2)
def Lm : Int × Int × Int × Int := (1, 0, 24, 1)
def Wf : Int × Int × Int × Int := (0, -1, 48, 0)
def Ef : Int × Int × Int × Int := (-1440, 1, -2073648, 1440)
def K48 : List (Int × Int × Int × Int) :=
  [(1, 0, 0, 1), (2, 1, 0, 2), (1, 0, 24, 1), (0, -1, 48, 0), (26, 1, 48, 2), (24, -1, 48, 0),
   (0, -1, 48, -24), (24, -13, 48, -24)]
/-- The sign character on `K48`: `λ(T_{1/2}) = λ(L) = −1`, `λ(W₄₈) = 1`. -/
def lam : List Int := [1, -1, -1, 1, 1, -1, -1, 1]
def lamOf (g : Int × Int × Int × Int) : Int :=
  ((List.range 8).filter fun i => sameCoset 48 g (K48.getD i (1, 0, 0, 1))).foldl (fun _ i => lam.getD i 0) 0

theorem group_12E :
    -- G is an eta quotient of Newman level 48, with all δ even (so G ∈ q⁻¹ℤ[[q²]], G(τ+½) = −G(τ))
    chiOf 73 = 0 ∧ (keys (r 73) 48).all (fun δ => δ % 2 == 0) = true ∧
    newmanOK rG 48 = true ∧ (keys rG 200).all (fun δ => δ % 2 == 0) = true ∧
    (divs 48).all (fun d => ordInt rG 48 d) = true ∧
    -- Fricke invariance: divisor invariance (C2, C3) and an elliptic element in the coset
    divInv rG 48 Wf = true ∧ isAL 48 48 Ef = true ∧ elliptic Ef = true ∧
    -- L = W T_{-1/2} W^{-1} mod Γ₀(48), so λ(L) = λ(T)^{-1} = −1
    sameCoset 48 (prim (mm (mm Wf (2, -1, 0, 2)) (adj Wf))) Lm = true ∧
    -- coset table of Γ₀(24|2)+12 modulo Γ₀(48): 8 cosets, λ a homomorphism, kernel of size 4
    closedTable 48 K48 [T2, Lm, Wf] = true ∧
    (K48.all fun g => [(T2, (-1 : Int)), (Lm, -1), (Wf, 1)].all fun s =>
      lamOf (mm g s.1) == lamOf g * s.2) = true ∧
    (lam.filter (· == 1)).length = 4 ∧
    degree rG 48 = 4 := by
  decide +kernel

end MonsterCN.Erratum
