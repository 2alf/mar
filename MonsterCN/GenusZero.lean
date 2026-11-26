/-
# Catalogue-free assignment rigidity (MAR, part III)

MAR-1…MAR-8 assume the catalogue of the 171 Conway–Norton groups, which is read off the very table
being reconstructed. Here the catalogue is **removed**. A label may be *any* Conway–Norton-shaped
group `n|h + W` (`h ∣ gcd(n, 24)`, `W` a group of Atkin–Lehner involutions of level `n/h`) whose
normalizer curve `X₀(n/h)/W` has **genus zero**: exactly genus zero for `h = 1`, and a necessary
condition for `h > 1`, so the label universe only gets bigger.

**MAR-9 (`cn_unique_genus_zero`).** The Conway–Norton assignment is the unique labelling of the
194 Monster classes by genus-zero Conway–Norton-shaped groups that
* matches element orders and the ATLAS power maps via the Conway–Norton power rule,
* satisfies `a₁(g) = 0` unless `h ∣ 2` and `a₂(g) = 0` unless `h ∣ 3` (eigen-character), and
* gives equal `a₁` to classes with the same group.
No list of moonshine groups is an input.

**MAR-10 (`sharpness_gz`, `fakeNG_props`).** Every hypothesis is necessary, with explicit fake
tables: coherence (`fake18`), `a₁`-vanishing (`fake27`), `a₂`-vanishing (`fake32`), and genus
zero (`fakeNG`, which uses the genus-one groups `24-` and `32-`).

**External assumption (A4).** `genusZero` is the classical Riemann–Hurwitz formula
`g(X₀(N)/W) = 1 + (2g(X₀(N)) − 2 − Σ_{Q∈W∖1} ν(N,Q)) / (2|W|)`. Here `ν(N,Q)`, the number of fixed
points of `w_Q`, is given by the class-number formula (Fricke; Ogg 1974; Kluit;
Furumoto–Hasegawa 1999) with local factors as implemented in `provenance/python/common.py`. Those local factors
were also compared with brute-force fixed-point counts for all `N ≤ 300`.
Sanity checks of the formula are kernel-checked below.
-/
import MonsterCN.Rigidity
import MonsterCN.Ogg
import Mathlib.Data.List.Sublists
import MonsterCN.Data.GZDomains

namespace MonsterCN.GZ

open MonsterCN MonsterCN.Ogg

/-! ## Arithmetic -/

def divisorsN (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d != 0 && n % d == 0
def primeFactors (n : Nat) : List Nat := (divisorsN n).filter isPrimeB
/-- `p`-adic valuation for `n ≥ 1` (`p ≥ 2`). -/
def vp (p n : Nat) : Nat := ((List.range (n + 1)).filter fun k => k ≥ 1 && n % p ^ k == 0).length
def phi (n : Nat) : Nat := ((List.range n).filter fun k => Nat.gcd (k + 1) n == 1).length

/-- Kronecker symbol `(D/p)` for a prime `p`. -/
def kron (D : Int) (p : Nat) : Int :=
  if p == 2 then
    (if D % 2 == 0 then 0 else if D % 8 == 1 || D % 8 == 7 then 1 else -1)
  else
    let r := (D % (p : Int)).toNat
    if r == 0 then 0 else if r ^ ((p - 1) / 2) % p == 1 then 1 else -1

/-! ## Genus of `X₀(N)` -/

def mu (n : Nat) : Nat := (primeFactors n).foldl (fun m p => m / p * (p + 1)) n
def nu2 (n : Nat) : Int :=
  if n % 4 == 0 then 0 else (primeFactors n).foldl (fun x p => x * (1 + kron (-4) p)) 1
def nu3 (n : Nat) : Int :=
  if n % 9 == 0 then 0 else (primeFactors n).foldl (fun x p => x * (1 + kron (-3) p)) 1
def cusps (n : Nat) : Nat := ((divisorsN n).map fun d => phi (Nat.gcd d (n / d))).sum
/-- `12·g(X₀(n))`. -/
def twelveG (n : Nat) : Int := 12 + (mu n : Int) - 3 * nu2 n - 4 * nu3 n - 6 * (cusps n : Int)

/-! ## Fixed points of Atkin–Lehner involutions -/

/-- Elliptic data `(t, g, D₀)` for `w_Q`: trace `t ∈ {0} ∪ {±Q : Q < 4}`, `t² − 4Q = g²D₀`,
`D₀ ≡ 0, 1 (mod 4)`, `gcd(g, Q) = 1`. -/
def fixedTerms (Q : Nat) : List (Int × Nat × Int) :=
  ([0] ++ (if Q < 4 then [(Q : Int), -(Q : Int)] else [])).flatMap fun t =>
    let disc : Int := t * t - 4 * Q
    ((List.range (Nat.sqrt disc.natAbs + 1)).filter fun g => g ≥ 1 &&
        disc % ((g * g : Nat) : Int) == 0 &&
        ((disc / ((g * g : Nat) : Int)) % 4 == 0 || (disc / ((g * g : Nat) : Int)) % 4 == 1) &&
        Nat.gcd g Q == 1).map fun g => (t, g, disc / ((g * g : Nat) : Int))

/-- `6 / |Aut(f₀)/{±1}|`. -/
def autW6 (D0 : Int) : Int := if D0 == -3 then 2 else if D0 == -4 then 3 else 6

/-- Local factor at `p^k ‖ N/Q` (closed form; `-1000` flags an unexpected case). -/
def localFactor (p k g : Nat) (D0 : Int) (Q : Nat) : Int :=
  if Q % p == 0 then (if g % p != 0 then 1 else 0)
  else if p != 2 then 1 + kron D0 p
  else if g == 1 && D0 == -4 * (Q : Int) then
    (if k == 1 then 1 else if k == 2 then (if Q % 4 == 3 then 2 else 0)
     else (if Q % 8 == 7 then 4 else 0))
  else if g == 2 && D0 == -(Q : Int) then
    (if k == 1 then 3 else 2 * (1 + kron D0 2))
  else if g == 1 && D0 == -3 then 0
  else -1000

def cuspFixed (N Q : Nat) : Nat :=
  if Q != 4 then 0 else
    let M := N / 4
    ((divisorsN M).map fun d => phi (Nat.gcd d (M / d))).sum

/-- `6·ν(N,Q)`: six times the number of fixed points of `w_Q` on `X₀(N)`. -/
def nu6 (N Q : Nat) : Int :=
  let M := N / Q
  ((fixedTerms Q).map fun x =>
    autW6 x.2.2 * (classNo x.2.2.natAbs : Int) *
      ((primeFactors M).foldl (fun acc p => acc * localFactor p (vp p M) x.2.1 x.2.2 Q) 1)).sum +
  6 * (cuspFixed N Q : Int)

/-- `X₀(m)/W` has genus zero: `Σ_{Q ∈ W, Q ≠ 1} ν(m,Q) = 2g(X₀(m)) − 2 + 2|W|`. -/
def genusZero (m : Nat) (W : List Nat) : Bool :=
  ((W.filter (· != 1)).map (nu6 m)).sum == twelveG m - 12 + 12 * (W.length : Int)

/-! ## Labels -/

def hallList (m : Nat) : List Nat := (divisorsN m).filter fun e => Nat.gcd e (m / e) == 1
def validW (W : List Nat) : Bool :=
  W.contains 1 && W.all fun e => W.all fun f => W.contains (alMul e f)
def hs : List Nat := [1, 2, 3, 4, 6, 8, 12, 24]

/-- `l` is a genus-zero Conway–Norton-shaped label (with `W` in sorted normal form). -/
def IsGZ (l : CNLabel) : Prop :=
  l.h ∈ hs ∧ l.n % l.h = 0 ∧ (l.W.isSublist (hallList (l.n / l.h))) = true ∧
  validW l.W = true ∧ genusZero (l.n / l.h) l.W = true

def candidates (n : Nat) : List CNLabel :=
  hs.flatMap fun h => if n % h == 0 then
    ((hallList (n / h)).sublists.filter fun W => validW W && genusZero (n / h) W).map
      fun W => ⟨n, h, W⟩ else []

theorem mem_candidates (l : CNLabel) (hl : IsGZ l) : l ∈ candidates l.n := by
  obtain ⟨hh, hdiv, hsub, hv, hg⟩ := hl
  unfold candidates
  simp only [List.mem_flatMap]
  refine ⟨l.h, hh, ?_⟩
  have : (l.n % l.h == 0) = true := by simpa using hdiv
  rw [if_pos this, List.mem_map]
  refine ⟨l.W, ?_, rfl⟩
  rw [List.mem_filter, List.mem_sublists]
  exact ⟨List.isSublist_iff_sublist.mp hsub, by simp [hv, hg]⟩

/-- The genus-zero universe, grouped by `n` (computed by enumeration; `gz_table_spec`
proves that it contains every candidate). -/
def gzTable : List (Nat × List CNLabel) := [
  (1, [⟨1, 1, [1]⟩]),
  (2, [⟨2, 1, [1]⟩, ⟨2, 1, [1, 2]⟩, ⟨2, 2, [1]⟩]),
  (3, [⟨3, 1, [1]⟩, ⟨3, 1, [1, 3]⟩, ⟨3, 3, [1]⟩]),
  (4, [⟨4, 1, [1]⟩, ⟨4, 1, [1, 4]⟩, ⟨4, 2, [1]⟩, ⟨4, 2, [1, 2]⟩, ⟨4, 4, [1]⟩]),
  (5, [⟨5, 1, [1]⟩, ⟨5, 1, [1, 5]⟩]),
  (6, [⟨6, 1, [1]⟩, ⟨6, 1, [1, 2]⟩, ⟨6, 1, [1, 2, 3, 6]⟩, ⟨6, 1, [1, 3]⟩, ⟨6, 1, [1, 6]⟩, ⟨6, 2, [1]⟩, ⟨6, 2, [1, 3]⟩, ⟨6, 3, [1]⟩, ⟨6, 3, [1, 2]⟩, ⟨6, 6, [1]⟩]),
  (7, [⟨7, 1, [1]⟩, ⟨7, 1, [1, 7]⟩]),
  (8, [⟨8, 1, [1]⟩, ⟨8, 1, [1, 8]⟩, ⟨8, 2, [1]⟩, ⟨8, 2, [1, 4]⟩, ⟨8, 4, [1]⟩, ⟨8, 4, [1, 2]⟩, ⟨8, 8, [1]⟩]),
  (9, [⟨9, 1, [1]⟩, ⟨9, 1, [1, 9]⟩, ⟨9, 3, [1]⟩, ⟨9, 3, [1, 3]⟩]),
  (10, [⟨10, 1, [1]⟩, ⟨10, 1, [1, 2]⟩, ⟨10, 1, [1, 2, 5, 10]⟩, ⟨10, 1, [1, 5]⟩, ⟨10, 1, [1, 10]⟩, ⟨10, 2, [1]⟩, ⟨10, 2, [1, 5]⟩]),
  (11, [⟨11, 1, [1, 11]⟩]),
  (12, [⟨12, 1, [1]⟩, ⟨12, 1, [1, 3]⟩, ⟨12, 1, [1, 3, 4, 12]⟩, ⟨12, 1, [1, 4]⟩, ⟨12, 1, [1, 12]⟩, ⟨12, 2, [1]⟩, ⟨12, 2, [1, 2]⟩, ⟨12, 2, [1, 2, 3, 6]⟩, ⟨12, 2, [1, 3]⟩, ⟨12, 2, [1, 6]⟩, ⟨12, 3, [1]⟩, ⟨12, 3, [1, 4]⟩, ⟨12, 4, [1]⟩, ⟨12, 4, [1, 3]⟩, ⟨12, 6, [1]⟩, ⟨12, 6, [1, 2]⟩, ⟨12, 12, [1]⟩]),
  (13, [⟨13, 1, [1]⟩, ⟨13, 1, [1, 13]⟩]),
  (14, [⟨14, 1, [1, 2, 7, 14]⟩, ⟨14, 1, [1, 7]⟩, ⟨14, 1, [1, 14]⟩, ⟨14, 2, [1]⟩, ⟨14, 2, [1, 7]⟩]),
  (15, [⟨15, 1, [1, 3, 5, 15]⟩, ⟨15, 1, [1, 5]⟩, ⟨15, 1, [1, 15]⟩, ⟨15, 3, [1]⟩, ⟨15, 3, [1, 5]⟩]),
  (16, [⟨16, 1, [1]⟩, ⟨16, 1, [1, 16]⟩, ⟨16, 2, [1]⟩, ⟨16, 2, [1, 8]⟩, ⟨16, 4, [1]⟩, ⟨16, 4, [1, 4]⟩, ⟨16, 8, [1]⟩, ⟨16, 8, [1, 2]⟩]),
  (17, [⟨17, 1, [1, 17]⟩]),
  (18, [⟨18, 1, [1]⟩, ⟨18, 1, [1, 2]⟩, ⟨18, 1, [1, 2, 9, 18]⟩, ⟨18, 1, [1, 9]⟩, ⟨18, 1, [1, 18]⟩, ⟨18, 2, [1]⟩, ⟨18, 2, [1, 9]⟩, ⟨18, 3, [1]⟩, ⟨18, 3, [1, 2]⟩, ⟨18, 3, [1, 2, 3, 6]⟩, ⟨18, 3, [1, 3]⟩, ⟨18, 3, [1, 6]⟩, ⟨18, 6, [1]⟩, ⟨18, 6, [1, 3]⟩]),
  (19, [⟨19, 1, [1, 19]⟩]),
  (20, [⟨20, 1, [1, 4]⟩, ⟨20, 1, [1, 4, 5, 20]⟩, ⟨20, 1, [1, 20]⟩, ⟨20, 2, [1]⟩, ⟨20, 2, [1, 2]⟩, ⟨20, 2, [1, 2, 5, 10]⟩, ⟨20, 2, [1, 5]⟩, ⟨20, 2, [1, 10]⟩, ⟨20, 4, [1]⟩, ⟨20, 4, [1, 5]⟩]),
  (21, [⟨21, 1, [1, 3]⟩, ⟨21, 1, [1, 3, 7, 21]⟩, ⟨21, 1, [1, 21]⟩, ⟨21, 3, [1]⟩, ⟨21, 3, [1, 7]⟩]),
  (22, [⟨22, 1, [1, 2, 11, 22]⟩, ⟨22, 1, [1, 11]⟩, ⟨22, 2, [1, 11]⟩]),
  (23, [⟨23, 1, [1, 23]⟩]),
  (24, [⟨24, 1, [1, 3, 8, 24]⟩, ⟨24, 1, [1, 8]⟩, ⟨24, 1, [1, 24]⟩, ⟨24, 2, [1]⟩, ⟨24, 2, [1, 3]⟩, ⟨24, 2, [1, 3, 4, 12]⟩, ⟨24, 2, [1, 4]⟩, ⟨24, 2, [1, 12]⟩, ⟨24, 3, [1]⟩, ⟨24, 3, [1, 8]⟩, ⟨24, 4, [1]⟩, ⟨24, 4, [1, 2]⟩, ⟨24, 4, [1, 2, 3, 6]⟩, ⟨24, 4, [1, 3]⟩, ⟨24, 4, [1, 6]⟩, ⟨24, 6, [1]⟩, ⟨24, 6, [1, 4]⟩, ⟨24, 8, [1]⟩, ⟨24, 8, [1, 3]⟩, ⟨24, 12, [1]⟩, ⟨24, 12, [1, 2]⟩, ⟨24, 24, [1]⟩]),
  (25, [⟨25, 1, [1]⟩, ⟨25, 1, [1, 25]⟩]),
  (26, [⟨26, 1, [1, 2, 13, 26]⟩, ⟨26, 1, [1, 26]⟩, ⟨26, 2, [1]⟩, ⟨26, 2, [1, 13]⟩]),
  (27, [⟨27, 1, [1, 27]⟩, ⟨27, 3, [1]⟩, ⟨27, 3, [1, 9]⟩]),
  (28, [⟨28, 1, [1, 4, 7, 28]⟩, ⟨28, 1, [1, 7]⟩, ⟨28, 2, [1, 2, 7, 14]⟩, ⟨28, 2, [1, 7]⟩, ⟨28, 2, [1, 14]⟩, ⟨28, 4, [1]⟩, ⟨28, 4, [1, 7]⟩]),
  (29, [⟨29, 1, [1, 29]⟩]),
  (30, [⟨30, 1, [1, 2, 3, 5, 6, 10, 15, 30]⟩, ⟨30, 1, [1, 2, 15, 30]⟩, ⟨30, 1, [1, 3, 5, 15]⟩, ⟨30, 1, [1, 5, 6, 30]⟩, ⟨30, 1, [1, 6, 10, 15]⟩, ⟨30, 1, [1, 15]⟩, ⟨30, 2, [1, 3, 5, 15]⟩, ⟨30, 2, [1, 5]⟩, ⟨30, 2, [1, 15]⟩, ⟨30, 3, [1]⟩, ⟨30, 3, [1, 2]⟩, ⟨30, 3, [1, 2, 5, 10]⟩, ⟨30, 3, [1, 5]⟩, ⟨30, 3, [1, 10]⟩, ⟨30, 6, [1]⟩, ⟨30, 6, [1, 5]⟩]),
  (31, [⟨31, 1, [1, 31]⟩]),
  (32, [⟨32, 1, [1, 32]⟩, ⟨32, 2, [1]⟩, ⟨32, 2, [1, 16]⟩, ⟨32, 4, [1]⟩, ⟨32, 4, [1, 8]⟩, ⟨32, 8, [1]⟩, ⟨32, 8, [1, 4]⟩]),
  (33, [⟨33, 1, [1, 3, 11, 33]⟩, ⟨33, 1, [1, 11]⟩, ⟨33, 3, [1, 11]⟩]),
  (34, [⟨34, 1, [1, 2, 17, 34]⟩, ⟨34, 2, [1, 17]⟩]),
  (35, [⟨35, 1, [1, 5, 7, 35]⟩, ⟨35, 1, [1, 35]⟩]),
  (36, [⟨36, 1, [1, 4]⟩, ⟨36, 1, [1, 4, 9, 36]⟩, ⟨36, 1, [1, 36]⟩, ⟨36, 2, [1]⟩, ⟨36, 2, [1, 2]⟩, ⟨36, 2, [1, 2, 9, 18]⟩, ⟨36, 2, [1, 9]⟩, ⟨36, 2, [1, 18]⟩, ⟨36, 3, [1]⟩, ⟨36, 3, [1, 3]⟩, ⟨36, 3, [1, 3, 4, 12]⟩, ⟨36, 3, [1, 4]⟩, ⟨36, 3, [1, 12]⟩, ⟨36, 4, [1]⟩, ⟨36, 4, [1, 9]⟩, ⟨36, 6, [1]⟩, ⟨36, 6, [1, 2]⟩, ⟨36, 6, [1, 2, 3, 6]⟩, ⟨36, 6, [1, 3]⟩, ⟨36, 6, [1, 6]⟩, ⟨36, 12, [1]⟩, ⟨36, 12, [1, 3]⟩]),
  (38, [⟨38, 1, [1, 2, 19, 38]⟩, ⟨38, 2, [1, 19]⟩]),
  (39, [⟨39, 1, [1, 3, 13, 39]⟩, ⟨39, 1, [1, 39]⟩, ⟨39, 3, [1]⟩, ⟨39, 3, [1, 13]⟩]),
  (40, [⟨40, 2, [1, 4]⟩, ⟨40, 2, [1, 4, 5, 20]⟩, ⟨40, 2, [1, 20]⟩, ⟨40, 4, [1]⟩, ⟨40, 4, [1, 2]⟩, ⟨40, 4, [1, 2, 5, 10]⟩, ⟨40, 4, [1, 5]⟩, ⟨40, 4, [1, 10]⟩, ⟨40, 8, [1]⟩, ⟨40, 8, [1, 5]⟩]),
  (41, [⟨41, 1, [1, 41]⟩]),
  (42, [⟨42, 1, [1, 2, 3, 6, 7, 14, 21, 42]⟩, ⟨42, 1, [1, 3, 14, 42]⟩, ⟨42, 1, [1, 6, 14, 21]⟩, ⟨42, 2, [1, 3]⟩, ⟨42, 2, [1, 3, 7, 21]⟩, ⟨42, 2, [1, 21]⟩, ⟨42, 3, [1, 2, 7, 14]⟩, ⟨42, 3, [1, 7]⟩, ⟨42, 3, [1, 14]⟩, ⟨42, 6, [1]⟩, ⟨42, 6, [1, 7]⟩]),
  (44, [⟨44, 1, [1, 4, 11, 44]⟩, ⟨44, 2, [1, 2, 11, 22]⟩, ⟨44, 2, [1, 11]⟩, ⟨44, 4, [1, 11]⟩]),
  (45, [⟨45, 1, [1, 5, 9, 45]⟩, ⟨45, 3, [1, 3, 5, 15]⟩, ⟨45, 3, [1, 5]⟩, ⟨45, 3, [1, 15]⟩]),
  (46, [⟨46, 1, [1, 2, 23, 46]⟩, ⟨46, 1, [1, 23]⟩, ⟨46, 2, [1, 23]⟩]),
  (47, [⟨47, 1, [1, 47]⟩]),
  (48, [⟨48, 2, [1, 3, 8, 24]⟩, ⟨48, 2, [1, 8]⟩, ⟨48, 2, [1, 24]⟩, ⟨48, 3, [1]⟩, ⟨48, 3, [1, 16]⟩, ⟨48, 4, [1]⟩, ⟨48, 4, [1, 3]⟩, ⟨48, 4, [1, 3, 4, 12]⟩, ⟨48, 4, [1, 4]⟩, ⟨48, 4, [1, 12]⟩, ⟨48, 6, [1]⟩, ⟨48, 6, [1, 8]⟩, ⟨48, 8, [1]⟩, ⟨48, 8, [1, 2]⟩, ⟨48, 8, [1, 2, 3, 6]⟩, ⟨48, 8, [1, 3]⟩, ⟨48, 8, [1, 6]⟩, ⟨48, 12, [1]⟩, ⟨48, 12, [1, 4]⟩, ⟨48, 24, [1]⟩, ⟨48, 24, [1, 2]⟩]),
  (50, [⟨50, 1, [1, 2, 25, 50]⟩, ⟨50, 1, [1, 50]⟩, ⟨50, 2, [1]⟩, ⟨50, 2, [1, 25]⟩]),
  (51, [⟨51, 1, [1, 3, 17, 51]⟩, ⟨51, 3, [1, 17]⟩]),
  (52, [⟨52, 2, [1, 2, 13, 26]⟩, ⟨52, 2, [1, 26]⟩, ⟨52, 4, [1]⟩, ⟨52, 4, [1, 13]⟩]),
  (54, [⟨54, 1, [1, 2, 27, 54]⟩, ⟨54, 2, [1, 27]⟩, ⟨54, 3, [1]⟩, ⟨54, 3, [1, 2]⟩, ⟨54, 3, [1, 2, 9, 18]⟩, ⟨54, 3, [1, 9]⟩, ⟨54, 3, [1, 18]⟩, ⟨54, 6, [1]⟩, ⟨54, 6, [1, 9]⟩]),
  (55, [⟨55, 1, [1, 5, 11, 55]⟩]),
  (56, [⟨56, 1, [1, 7, 8, 56]⟩, ⟨56, 2, [1, 4, 7, 28]⟩, ⟨56, 2, [1, 7]⟩, ⟨56, 4, [1, 2, 7, 14]⟩, ⟨56, 4, [1, 7]⟩, ⟨56, 4, [1, 14]⟩, ⟨56, 8, [1]⟩, ⟨56, 8, [1, 7]⟩]),
  (57, [⟨57, 3, [1, 19]⟩]),
  (59, [⟨59, 1, [1, 59]⟩]),
  (60, [⟨60, 1, [1, 3, 4, 5, 12, 15, 20, 60]⟩, ⟨60, 1, [1, 4, 15, 60]⟩, ⟨60, 1, [1, 12, 15, 20]⟩, ⟨60, 2, [1, 2, 3, 5, 6, 10, 15, 30]⟩, ⟨60, 2, [1, 2, 15, 30]⟩, ⟨60, 2, [1, 3, 5, 15]⟩, ⟨60, 2, [1, 5, 6, 30]⟩, ⟨60, 2, [1, 6, 10, 15]⟩, ⟨60, 2, [1, 15]⟩, ⟨60, 3, [1, 4]⟩, ⟨60, 3, [1, 4, 5, 20]⟩, ⟨60, 3, [1, 20]⟩, ⟨60, 4, [1, 3, 5, 15]⟩, ⟨60, 4, [1, 5]⟩, ⟨60, 4, [1, 15]⟩, ⟨60, 6, [1]⟩, ⟨60, 6, [1, 2]⟩, ⟨60, 6, [1, 2, 5, 10]⟩, ⟨60, 6, [1, 5]⟩, ⟨60, 6, [1, 10]⟩, ⟨60, 12, [1]⟩, ⟨60, 12, [1, 5]⟩]),
  (62, [⟨62, 1, [1, 2, 31, 62]⟩, ⟨62, 2, [1, 31]⟩]),
  (66, [⟨66, 1, [1, 2, 3, 6, 11, 22, 33, 66]⟩, ⟨66, 1, [1, 6, 11, 66]⟩, ⟨66, 2, [1, 3, 11, 33]⟩, ⟨66, 2, [1, 11]⟩, ⟨66, 3, [1, 2, 11, 22]⟩, ⟨66, 3, [1, 11]⟩, ⟨66, 6, [1, 11]⟩]),
  (68, [⟨68, 2, [1, 2, 17, 34]⟩, ⟨68, 4, [1, 17]⟩]),
  (69, [⟨69, 1, [1, 3, 23, 69]⟩, ⟨69, 3, [1, 23]⟩]),
  (70, [⟨70, 1, [1, 2, 5, 7, 10, 14, 35, 70]⟩, ⟨70, 1, [1, 10, 14, 35]⟩, ⟨70, 2, [1, 5, 7, 35]⟩, ⟨70, 2, [1, 35]⟩]),
  (71, [⟨71, 1, [1, 71]⟩]),
  (78, [⟨78, 1, [1, 2, 3, 6, 13, 26, 39, 78]⟩, ⟨78, 1, [1, 6, 26, 39]⟩, ⟨78, 2, [1, 3, 13, 39]⟩, ⟨78, 2, [1, 39]⟩, ⟨78, 3, [1, 2, 13, 26]⟩, ⟨78, 3, [1, 26]⟩, ⟨78, 6, [1]⟩, ⟨78, 6, [1, 13]⟩]),
  (84, [⟨84, 2, [1, 2, 3, 6, 7, 14, 21, 42]⟩, ⟨84, 2, [1, 3, 14, 42]⟩, ⟨84, 2, [1, 6, 14, 21]⟩, ⟨84, 3, [1, 4, 7, 28]⟩, ⟨84, 3, [1, 7]⟩, ⟨84, 4, [1, 3]⟩, ⟨84, 4, [1, 3, 7, 21]⟩, ⟨84, 4, [1, 21]⟩, ⟨84, 6, [1, 2, 7, 14]⟩, ⟨84, 6, [1, 7]⟩, ⟨84, 6, [1, 14]⟩, ⟨84, 12, [1]⟩, ⟨84, 12, [1, 7]⟩]),
  (87, [⟨87, 1, [1, 3, 29, 87]⟩, ⟨87, 3, [1, 29]⟩]),
  (88, [⟨88, 2, [1, 4, 11, 44]⟩, ⟨88, 4, [1, 2, 11, 22]⟩, ⟨88, 4, [1, 11]⟩, ⟨88, 8, [1, 11]⟩]),
  (92, [⟨92, 1, [1, 4, 23, 92]⟩, ⟨92, 2, [1, 2, 23, 46]⟩, ⟨92, 2, [1, 23]⟩, ⟨92, 4, [1, 23]⟩]),
  (93, [⟨93, 3, [1, 31]⟩]),
  (94, [⟨94, 1, [1, 2, 47, 94]⟩, ⟨94, 2, [1, 47]⟩]),
  (95, [⟨95, 1, [1, 5, 19, 95]⟩]),
  (104, [⟨104, 4, [1, 2, 13, 26]⟩, ⟨104, 4, [1, 26]⟩, ⟨104, 8, [1]⟩, ⟨104, 8, [1, 13]⟩]),
  (105, [⟨105, 1, [1, 3, 5, 7, 15, 21, 35, 105]⟩, ⟨105, 3, [1, 5, 7, 35]⟩, ⟨105, 3, [1, 35]⟩]),
  (110, [⟨110, 1, [1, 2, 5, 10, 11, 22, 55, 110]⟩, ⟨110, 2, [1, 5, 11, 55]⟩]),
  (119, [⟨119, 1, [1, 7, 17, 119]⟩])
]

def gzLookup (n : Nat) : List CNLabel := ((gzTable.find? fun x => x.1 == n).map Prod.snd).getD []

/-- The element orders of the Monster. -/
def monsterOrders : List Nat := (classes.map ordOf).eraseDups

set_option maxRecDepth 100000 in
/-- Every genus-zero candidate of each Monster element order is in `gzTable`, and conversely,
and the table has 385 labels. -/
theorem gz_table_spec :
    monsterOrders.all (fun n => (candidates n).all fun l => (gzLookup n).contains l) = true ∧
    monsterOrders.all (fun n => (gzLookup n).all fun l => (candidates n).contains l) = true ∧
    (gzTable.map fun x => x.2.length).sum = 385 := by
  decide +kernel

/-! ### Sanity checks of the genus formula -/

/-- Known values: `g(X₀(11)) = 1`, `g(X₀(37)) = 2`, `g(X₀(25)) = 0`, `g(X₀(389)) = 32`;
`X₀(71)⁺` has genus zero but `X₀(37)⁺` does not; `X₀(49)⁺` (the CN ghost) has genus zero; and
every `h = 1` Conway–Norton label passes. -/
theorem genus_sanity :
    twelveG 11 = 12 ∧ twelveG 37 = 24 ∧ twelveG 25 = 0 ∧ twelveG 389 = 12 * 32 ∧
    genusZero 71 [1, 71] = true ∧ genusZero 37 [1, 37] = false ∧ genusZero 49 [1, 49] = true ∧
    classes.all (fun c => (cn c).h != 1 || genusZero (cn c).n (cn c).W) = true := by
  decide +kernel

/-- Every Conway–Norton label satisfies `IsGZ` (so `cn` is an admissible labelling). -/
theorem cn_isGZ : ∀ c, c < 194 → IsGZ (cn c) := by
  unfold IsGZ; decide +kernel

/-! ## Hypotheses and propagation -/

/-- Compatible labelling by genus-zero Conway–Norton-shaped groups (no catalogue). -/
def CompatGZ (L : Nat → CNLabel) : Prop :=
  ∀ c, c < 194 → IsGZ (L c) ∧ (L c).n = ordOf c ∧
    ∀ p ∈ monsterPrimes, L (pw p c) = powRule (L c) p

def gzInit (ms : List Nat) : Dom :=
  classes.map fun c => (gzLookup (ordOf c)).filter (vanOK ms c)

theorem ordOf_mem (c : Nat) (hc : c < 194) : ordOf c ∈ monsterOrders := by
  have : c ∈ classes := by simpa [classes, numClasses] using hc
  simp only [monsterOrders, List.mem_eraseDups]
  exact List.mem_map_of_mem this

theorem gzInit_sound {ms L} (hC : CompatGZ L) (hV : Van ms L) : Inv (gzInit ms) L := by
  intro c hc
  obtain ⟨hgz, hn, -⟩ := hC c hc
  rw [gzInit, getD_classes_map hc, List.mem_filter]
  constructor
  · have hm := mem_candidates (L c) hgz
    rw [hn] at hm
    have spec := gz_table_spec.1
    simp only [List.all_eq_true, List.contains_iff_mem] at spec
    exact spec _ (ordOf_mem c hc) _ hm
  · simp only [vanOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    intro m hm
    by_cases h : (m + 1) % (L c).h = 0
    · exact Or.inl h
    · exact Or.inr (hV c hc m hm h)

theorem step_sound' {ms L D}
    (hpow : ∀ c, c < 194 → ∀ p ∈ monsterPrimes, L (pw p c) = powRule (L c) p)
    (hCoh : Coh ms L) (hI : Inv D L) : Inv (step ms D) L := by
  intro c hc
  rw [step, getD_classes_map hc, List.mem_filter]
  refine ⟨hI c hc, ?_⟩
  simp only [keep, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun p hp => ?_, fun dp _ => ?_⟩, fun d hd => ?_⟩
  · rw [← hpow c hc p hp]
    simpa using hI _ (pw_lt c hc p hp)
  · by_cases h : (decide (dp.1 < 194) && monsterPrimes.contains dp.2 && pw dp.2 dp.1 == c) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at h
      obtain ⟨⟨hd, hp⟩, he⟩ := h
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq]
      refine Or.inr ⟨L dp.1, hI _ hd, ?_⟩
      rw [← hpow dp.1 hd dp.2 hp, he]
    · simp only [Bool.not_eq_true] at h
      rw [h]; rfl
  · have hd' : d < 194 := by simpa [classes, numClasses] using hd
    by_cases hD : D.getD d [] = [L c]
    · have hLd : L d = L c := by
        have := hI d hd'
        rw [hD] at this
        simpa using this
      have := hCoh c hc d hd' hLd.symm
      simp only [hD, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq]
      exact Or.inr (fun m hm => this m hm)
    · have : (D.getD d [] == [L c]) = false := by simpa using hD
      simp only [this, Bool.not_false, Bool.true_or]

/-! ## MAR-9: uniqueness without the catalogue -/

/-! Each propagation round is certified separately against an explicit literal
(`Data/GZDomains.lean`, generated by `provenance/lean/gen_gz_domains.lean`), to keep kernel memory low. -/

theorem gzRound0 : gzInit [1, 2] = GZDom.gzD0 := by decide +kernel
theorem gzRound1 : step [1] GZDom.gzD0 = GZDom.gzD1 := by decide +kernel
theorem gzRound2 : step [1] GZDom.gzD1 = GZDom.gzD2 := by decide +kernel
theorem gzRound3 : step [1] GZDom.gzD2 = GZDom.gzD3 := by decide +kernel
theorem gzRound4 : step [1] GZDom.gzD3 = classes.map (fun c => [cn c]) := by decide +kernel

theorem solveGZ : iter 4 (step [1]) (gzInit [1, 2]) = classes.map (fun c => [cn c]) := by
  show step [1] (step [1] (step [1] (step [1] (gzInit [1, 2])))) = _
  rw [gzRound0, gzRound1, gzRound2, gzRound3, gzRound4]

/-- **MAR-9.** The Conway–Norton table is the unique labelling of the Monster classes by
genus-zero Conway–Norton-shaped groups compatible with element orders and power maps, with
`a₁, a₂`-vanishing and `a₁`-coherence. -/
theorem cn_unique_genus_zero {L : Nat → CNLabel} (hC : CompatGZ L) (hV : Van [1, 2] L)
    (hH : Coh [1] L) : ∀ c, c < 194 → L c = cn c :=
  inv_eq (iter_sound (fun _ h => step_sound' (fun c hc => (hC c hc).2.2) hH h) 4 _
    (gzInit_sound hC hV)) solveGZ

/-- Conversely, `cn` satisfies all the hypotheses. -/
theorem cn_satisfies_gz : CompatGZ cn ∧ Van [1, 2, 3] cn ∧ Coh [1, 2, 3] cn :=
  ⟨fun c hc => ⟨cn_isGZ c hc, (compat_cn c hc).2⟩, van_cn, coh_cn⟩

/-! ## MAR-10: sharpness (explicit fake tables) -/

/-- Drop coherence: `18E ↦ 18-`. -/
def fake18 (c : Nat) : CNLabel := if c == 61 then ⟨18, 1, [1]⟩ else cn c
/-- Drop `a₁`-vanishing: `27B ↦ 27|3`. -/
def fake27 (c : Nat) : CNLabel := if c == 91 then ⟨27, 3, [1]⟩ else cn c
/-- Drop `a₂`-vanishing: `16B ↦ 16+, 16C ↦ 16-, 32A ↦ 32|2+, 32B ↦ 32+`. -/
def fake32 (c : Nat) : CNLabel :=
  if c == 54 then ⟨16, 1, [1, 16]⟩ else if c == 55 then ⟨16, 1, [1]⟩ else
  if c == 106 then ⟨32, 2, [1, 16]⟩ else if c == 107 then ⟨32, 1, [1, 32]⟩ else cn c
/-- Drop genus zero: `24I ↦ 24-`, `32A ↦ 32-` (both genus one). -/
def fakeNG (c : Nat) : CNLabel :=
  if c == 85 then ⟨24, 1, [1]⟩ else if c == 106 then ⟨32, 1, [1]⟩ else cn c

theorem fake_names : nameOf 61 = "18E" ∧ nameOf 91 = "27B" ∧ nameOf 85 = "24I" := by
  decide +kernel

theorem fake18_props : CompatGZ fake18 ∧ Van [1, 2, 3] fake18 ∧ fake18 61 ≠ cn 61 := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · unfold CompatGZ IsGZ; decide +kernel
  · unfold Van; decide +kernel

theorem fake27_props : CompatGZ fake27 ∧ Van [2] fake27 ∧ Coh [1, 2, 3] fake27 ∧
    fake27 91 ≠ cn 91 := by
  refine ⟨?_, ?_, ?_, by decide +kernel⟩
  · unfold CompatGZ IsGZ; decide +kernel
  · unfold Van; decide +kernel
  · unfold Coh; decide +kernel

theorem fake32_props : CompatGZ fake32 ∧ Van [1, 3] fake32 ∧ Coh [1, 2, 3] fake32 ∧
    fake32 54 ≠ cn 54 := by
  refine ⟨?_, ?_, ?_, by decide +kernel⟩
  · unfold CompatGZ IsGZ; decide +kernel
  · unfold Van; decide +kernel
  · unfold Coh; decide +kernel

/-- `fakeNG` satisfies everything except genus zero: power-compatible with the right orders,
all vanishing and coherence conditions; but `X₀(24)` and `X₀(32)` have genus one. -/
theorem fakeNG_props :
    (∀ c, c < 194 → (fakeNG c).n = ordOf c ∧
      ∀ p ∈ monsterPrimes, fakeNG (pw p c) = powRule (fakeNG c) p) ∧
    Van [1, 2, 3] fakeNG ∧ Coh [1, 2, 3] fakeNG ∧
    genusZero 24 [1] = false ∧ genusZero 32 [1] = false ∧ twelveG 24 = 12 ∧ twelveG 32 = 12 := by
  refine ⟨by decide +kernel, ?_, ?_, by decide +kernel⟩
  · unfold Van; decide +kernel
  · unfold Coh; decide +kernel

/-- **Sharpness (MAR-10).** Each hypothesis of MAR-9 is necessary. -/
theorem sharpness_gz :
    (CompatGZ fake18 ∧ Van [1, 2] fake18 ∧ fake18 61 ≠ cn 61) ∧
    (CompatGZ fake27 ∧ Van [2] fake27 ∧ Coh [1] fake27 ∧ fake27 91 ≠ cn 91) ∧
    (CompatGZ fake32 ∧ Van [1] fake32 ∧ Coh [1] fake32 ∧ fake32 54 ≠ cn 54) := by
  obtain ⟨a1, a2, a3⟩ := fake18_props
  obtain ⟨b1, b2, b3, b4⟩ := fake27_props
  obtain ⟨c1, c2, c3, c4⟩ := fake32_props
  refine ⟨⟨a1, fun c hc m hm => a2 c hc m (by simp at hm ⊢; omega), a3⟩,
          ⟨b1, fun c hc m hm => b2 c hc m (by simp at hm ⊢; omega),
            fun c hc d hd he m hm => b3 c hc d hd he m (by simp at hm ⊢; omega), b4⟩,
          ⟨c1, fun c hc m hm => c2 c hc m (by simp at hm ⊢; omega),
            fun c hc d hd he m hm => c3 c hc d hd he m (by simp at hm ⊢; omega), c4⟩⟩


/-! ## MAR-10′: the Atkin–Lehner part of the power rule is necessary -/

/-- One-sided power compatibility: `(n, h)` behave as in the Conway–Norton power rule, and the
Atkin–Lehner set of `g^p` merely *contains* the restriction of the set of `g`. -/
def powRuleWeak (l lp : CNLabel) (p : Nat) : Bool :=
  lp.n == l.n / Nat.gcd l.n p && lp.h == l.h / Nat.gcd l.h p &&
  (l.W.filter fun e => (lp.n / lp.h) % e == 0).all lp.W.contains

/-- Differences of the fake table `fakeW` from Conway–Norton (found by a search; certified by `fakeW_props`). -/
def fakeWDiffs : List (Nat × CNLabel) := [(53, ⟨16, 2, [1]⟩), (54, ⟨16, 1, [1, 16]⟩), (55, ⟨16, 1, [1]⟩), (60, ⟨18, 1, [1, 18]⟩), (61, ⟨18, 1, [1]⟩), (64, ⟨20, 2, [1, 10]⟩), (67, ⟨20, 2, [1]⟩), (77, ⟨24, 2, [1, 12]⟩), (84, ⟨24, 2, [1]⟩), (107, ⟨32, 1, [1, 32]⟩), (115, ⟨36, 2, [1, 18]⟩), (122, ⟨40, 4, [1, 10]⟩), (140, ⟨48, 2, [1, 24]⟩), (153, ⟨60, 2, [1, 6, 10, 15]⟩), (158, ⟨60, 6, [1]⟩)]

def fakeW (c : Nat) : CNLabel :=
  ((fakeWDiffs.find? fun x => x.1 == c).map Prod.snd).getD (cn c)

theorem fakeW_names : (fakeWDiffs.map fun x => nameOf x.1) =
    ["16A", "16B", "16C", "18D", "18E", "20B", "20E", "24A", "24H", "32B", "36C", "40A", "48A",
     "60A", "60F"] := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **MAR-10′.** `fakeW` uses genus-zero labels, has the right orders, satisfies the weakened
power rule, `a₁, a₂`-vanishing and `a₁`-coherence, yet differs from Conway–Norton at 15 classes.
So in MAR-9 the exact Atkin–Lehner part of the power rule cannot be weakened to containment. -/
theorem fakeW_props :
    (∀ c, c < 194 → IsGZ (fakeW c) ∧ (fakeW c).n = ordOf c ∧
      ∀ p ∈ monsterPrimes, powRuleWeak (fakeW c) (fakeW (pw p c)) p = true) ∧
    Van [1, 2] fakeW ∧ Coh [1] fakeW ∧ fakeW 53 ≠ cn 53 ∧
    (∀ c, c < 194 → ∀ p ∈ monsterPrimes, powRuleWeak (cn c) (cn (pw p c)) p = true) := by
  refine ⟨?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · unfold IsGZ; decide +kernel
  · unfold Van; decide +kernel
  · unfold Coh; decide +kernel


/-- `fakeW` differs from Conway–Norton at each of its 15 modified classes. -/
theorem fakeW_differs : fakeWDiffs.all (fun x => x.2 != cn x.1 && decide (x.1 < 194)) = true := by
  decide +kernel

end MonsterCN.GZ
