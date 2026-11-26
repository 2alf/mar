/-
# Basic operations on the Monster class data and Conway–Norton labels

Only Lean core is used here, so that every statement about the finite data is checked by the
kernel (`decide +kernel` / `rfl`), with no `native_decide` and no extra axioms.
-/
import MonsterCN.Data.Atlas
import MonsterCN.Data.CNTable

namespace MonsterCN

/-- Element order of class `c` (ATLAS). -/
def ordOf (c : Nat) : Nat := ord.getD c 0
/-- Centralizer order of class `c`. -/
def centOf (c : Nat) : Nat := cent.getD c 0
/-- The `p`-th power of class `c`. -/
def pw (p c : Nat) : Nat := (pmap p).getD c 0
/-- Conway–Norton label of class `c`. -/
def cn (c : Nat) : CNLabel := cnTable.getD c ⟨0, 0, []⟩
/-- Class name. -/
def nameOf (c : Nat) : String := className.getD c ""

/-- The `m`-th coefficient of the McKay–Thompson series `T_g = q⁻¹ + Σ a_m(g) qᵐ`, for
`m = 1, 2, 3`, from the decompositions
`V₂ = 1 + χ₂`, `V₃ = 1 + χ₂ + χ₃`, `V₄ = 2·1 + 2χ₂ + χ₃ + χ₄` of the moonshine module
(Conway–Norton 1979, §2; these decompositions are part of the standard data, not proved here). -/
def coeff (m c : Nat) : Int :=
  let x2 := chi2.getD c 0
  let x3 := chi3.getD c 0
  let x4 := chi4.getD c 0
  match m with
  | 1 => 1 + x2
  | 2 => 1 + x2 + x3
  | 3 => 2 + 2 * x2 + x3 + x4
  | _ => 0

/-- `e` is an exact (Hall) divisor of `q`: `e ∣ q` and `gcd(e, q/e) = 1`. -/
def isHall (q e : Nat) : Bool := e != 0 && q % e == 0 && Nat.gcd e (q / e) == 1

/-- The Atkin–Lehner product on Hall divisors: `e * f = ef / gcd(e,f)²`. -/
def alMul (e f : Nat) : Nat := e * f / (Nat.gcd e f * Nat.gcd e f)

/-- The **Conway–Norton power rule** (Conway–Norton 1979, §6): if `Γ_g = n|h + W` then
`Γ_{g^p} = n'|h' + {e ∈ W : e ∣ n'/h'}` with `n' = n/(n,p)`, `h' = h/(h,p)`. -/
def powRule (l : CNLabel) (p : Nat) : CNLabel :=
  let n' := l.n / Nat.gcd l.n p
  let h' := l.h / Nat.gcd l.h p
  ⟨n', h', l.W.filter (fun e => (n' / h') % e == 0)⟩

/-- A label is *Fricke* if it contains the Fricke involution `W_{n/h}`. -/
def isFricke (l : CNLabel) : Bool := l.W.contains (l.n / l.h)

/-- All class indices. -/
def classes : List Nat := List.range numClasses

end MonsterCN
