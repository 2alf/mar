/-
# Ogg's observation: the finite, kernel-checked part

Ogg (1974) observed that the primes `p` for which the Fricke quotient `X₀(p)⁺ = X₀(p)/⟨w_p⟩` has
genus zero are exactly the 15 primes dividing `|M|`.

This file (Lean core only, kernel evaluation, no `native_decide`):
* defines class numbers `classNo D` of positive definite binary quadratic forms of discriminant
  `-D` (count of reduced primitive forms);
* defines `genusPlus p` by the classical formula
  `g(X₀(p)⁺) = (g(X₀(p)) + 1)/2 - ν(w_p)/4`, with
  `g(X₀(p)) = (p + 1 - 3ν₂ - 4ν₃)/12` and the Fricke fixed-point count
  `ν(w_p) = h(-4p)` (`p ≡ 1 mod 4`), `h(-4p) + h(-p)` (`p ≡ 3 mod 4`), for `p ≥ 5`
  (Fricke; Ogg, *Hyperelliptic modular curves*, Bull. SMF 102 (1974); Kluit);
* proves, for every prime `p < oggBound`, `genusPlus p = 0 ↔ p ∈ monsterPrimes`;
* proves the Monster side: each of the 15 primes is the order of a class whose moonshine group is
  exactly the Fricke group `Γ₀(p)+` (`p+`), which by moonshine (Borcherds) is genus zero.

**External assumption (A4), special case.** `genusPlus` is the genus of `X₀(p)⁺`. This is the classical
Riemann–Hurwitz/fixed-point formula, not proved in Lean (Mathlib has no genus of modular curves).
-/
import MonsterCN.Basic

namespace MonsterCN.Ogg

open MonsterCN

/-- Integer absolute value as a natural number. -/
def natAbs' (b : Int) : Nat := b.natAbs

/-- Is `(a, b, c)` with `b² - 4ac = -D` reduced and primitive? (`a, c > 0`, `|b| ≤ a ≤ c`,
`b ≥ 0` if `|b| = a` or `a = c`, `gcd(a, b, c) = 1`.) -/
def isReduced (a : Nat) (b : Int) (c : Nat) : Bool :=
  natAbs' b ≤ a && a ≤ c && (if natAbs' b == a || a == c then decide (0 ≤ b) else true) &&
  Nat.gcd (Nat.gcd a (natAbs' b)) c == 1

/-- Number of reduced primitive forms with `a` fixed. `b` runs over `-a..a`. -/
def countA (D a : Nat) : Nat :=
  ((List.range (2 * a + 1)).filter fun (i : Nat) =>
    let b : Int := (i : Int) - a
    let n := b.natAbs * b.natAbs + D
    n % (4 * a) == 0 && isReduced a b (n / (4 * a))).length

/-- Class number `h(-D)`: reduced primitive positive definite forms of discriminant `-D`.
Reduced forms have `a ≤ √(D/3)`. -/
def classNo (D : Nat) : Nat :=
  ((List.range (Nat.sqrt (D / 3) + 1)).map fun a => if a == 0 then 0 else countA D a).sum

/-- Trial-division primality test. -/
def isPrimeB (n : Nat) : Bool :=
  2 ≤ n && (List.range (Nat.sqrt n + 1)).all fun d => d < 2 || n % d != 0

/-- `12·g(X₀(p))` numerator for a prime `p ≥ 5`: `p + 1 - 3ν₂ - 4ν₃`. -/
def nu2 (p : Nat) : Nat := if p % 4 == 1 then 2 else 0
def nu3 (p : Nat) : Nat := if p % 3 == 1 then 2 else 0

/-- Genus of `X₀(p)`, `p ≥ 5` prime. -/
def g0 (p : Nat) : Nat := (p + 1 - 3 * nu2 p - 4 * nu3 p) / 12

/-- Number of fixed points of the Fricke involution on `X₀(p)`, `p ≥ 5`. -/
def fricke (p : Nat) : Nat :=
  if p % 4 == 1 then classNo (4 * p) else classNo (4 * p) + classNo p

/-- `4·g(X₀(p)⁺) = 2(g(X₀(p)) + 1) - ν(w_p)` (Riemann–Hurwitz), as an integer. -/
def fourGenusPlus (p : Nat) : Int :=
  if p < 5 then 0 else 2 * ((g0 p : Int) + 1) - fricke p

/-- Genus of `X₀(p)⁺` (for `p = 2, 3`, `X₀(p)` itself has genus 0). -/
def genusPlus (p : Nat) : Int := fourGenusPlus p / 4

/-- The bound below which everything is checked by the kernel. -/
def oggBound : Nat := 2000

/-! ## Sanity checks of the formulas -/

theorem classNo_values :
    classNo 3 = 1 ∧ classNo 4 = 1 ∧ classNo 23 = 3 ∧ classNo 44 = 3 ∧ classNo 71 = 7 ∧
    classNo 148 = 2 ∧ classNo 163 = 1 ∧ classNo 284 = 7 ∧ classNo 47 = 5 := by
  decide +kernel

theorem known_genera :
    g0 11 = 1 ∧ g0 13 = 0 ∧ g0 23 = 2 ∧ g0 37 = 2 ∧ g0 71 = 6 ∧
    genusPlus 37 = 1 ∧ genusPlus 43 = 1 ∧ genusPlus 71 = 0 ∧ genusPlus 67 = 2 := by
  decide +kernel

/-- The formulas are internally consistent: `12 ∣ p+1-3ν₂-4ν₃` and `4 ∣ 2(g+1) - ν(w_p)`, and the
resulting genus is `≥ 0`, for every prime `5 ≤ p < oggBound`. -/
theorem formulas_consistent :
    (List.range oggBound).all (fun p => !(isPrimeB p && 5 ≤ p) ||
      ((p + 1 - 3 * nu2 p - 4 * nu3 p) % 12 == 0 && fourGenusPlus p % 4 == 0 &&
        decide (0 ≤ fourGenusPlus p))) = true := by
  decide +kernel

/-! ## Ogg's theorem below the bound -/

/-- **Ogg's observation, finite range.** For every prime `p < oggBound`,
`g(X₀(p)⁺) = 0` iff `p` is one of the 15 primes dividing `|M|`. -/
theorem ogg_below_bound :
    (List.range oggBound).all (fun p => !isPrimeB p ||
      ((genusPlus p == 0) == monsterPrimes.contains p)) = true := by
  decide +kernel

/-! ## The Monster side -/

/-- The Fricke group `Γ₀(p)+` as a Conway–Norton label. -/
def frickeLabel (p : Nat) : CNLabel := ⟨p, 1, [1, p]⟩

/-- **Moonshine side.** For each of the 15 primes `p ∣ |M|` there is a Monster class (namely
`pA`) whose McKay–Thompson series has moonshine group exactly `Γ₀(p)+`; and conversely every
prime-level Fricke label `p+` occurring in the table has `p ∣ |M|`. By Borcherds' theorem this
makes `X₀(p)⁺` genus zero for these `p` — the classical moonshine explanation of the forward
direction of Ogg's observation. -/
theorem monster_fricke_classes :
    monsterPrimes.all (fun p => classes.any fun c => cn c == frickeLabel p && ordOf c == p) = true ∧
    classes.all (fun c => !(isPrimeB (cn c).n && cn c == frickeLabel (cn c).n) ||
      monsterPrimes.contains (cn c).n) = true ∧
    monsterPrimes.all (fun p => monsterOrder % p == 0) = true := by
  decide +kernel

end MonsterCN.Ogg
