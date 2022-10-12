import YatimaStdLib.Polynomial
import YatimaStdLib.Zmod

/-
Here we post some definitions from https://hackage.haskell.org/package/galois-field-1.0.2
-/

namespace GaloisField

class GaloisField (K : Type _) where
  plus : K → K → K
  times : K → K → K
  null : K
  ein : K
  minus : K → K → K
  divis : K → K → K
  
  -- Characteristic @p@ of field and order of prime subfield.
  char : Nat

  -- Degree q of field as extension field over prime subfield.
  deg : K → Nat

  -- Frobenius endomorphism x ↦ x^p of prime subfield.
  frob : K → K

open GaloisField

instance [GaloisField K] : Add K where
  add := plus

instance [GaloisField K] : Mul K where
  mul := times

instance [GaloisField K] : OfNat K 1 where
  ofNat := ein

instance [GaloisField K] : OfNat K 0 where
  ofNat := null

instance [GaloisField K] : Div K where
  div := divis

instance [GaloisField K] : Sub K where
  sub := minus

def galPow [GaloisField K] : K → Nat → K
  | _, 0 => 1
  | x, (k + 1) => x * (galPow x k)

instance [GaloisField K] : HPow K Nat K where
  hPow := galPow

variable [gal : GaloisField K]

-- Order p^q of field.
def order (x : K) : Nat := gal.char ^ (gal.deg x)

instance : GaloisField (Zmod p) where
  plus := (. + .)
  times := (. * .)
  null := 0
  ein := 1
  minus := (. - .)
  divis := (. / .)
  char := p - 1
  deg _ := 1
  frob r := r ^ p

class PrimeField (K : Type _) [GaloisField K] where
  fromP : K → Int

instance : PrimeField (Zmod p) where
  fromP a := (a : Int)

open Polynomial

def frobenius [gal : GaloisField K] [HShiftRight K Nat K] [Neg K] :
  Polynomial K → Polynomial K → Option (Polynomial K)
  | #[], _ => .some #[]
  | #[a],_ => .some #[frob a]
  | #[a,b], #[x,0,1] =>
    if gal.deg x == 2 then .some #[a, -b] else
    if gal.char == 2 then .some #[frob a - frob b * x]
    else
      let nxq : K := (-x) ^ (gal.char >>> 1)
      .some #[frob a, frob b * nxq]
  | #[a,b], #[x,0,0,1] =>
    let (q,r) := Int.quotRem (gal.char) 3
    let nxq : K := (-x) ^ q
    if gal.char == 3 then .some #[frob a - frob b * x] else
    if r == 1 then .some #[frob a, frob b * nxq] else
    .some #[frob a, 0, frob b * nxq]
  | #[a,b,c], #[x,0,0,1] =>
    let (q,r) := Int.quotRem (gal.char) 3
    let nxq : K := (-x) ^ q
    if gal.char == 3 then .some #[frob a - (frob b - frob c * x) * x] else
    if r == 1 then .some #[frob a, frob b * nxq, frob c * nxq * nxq] else
    .some #[frob a, frob c * (-x) * nxq * nxq, frob b * nxq]
  | _,_ => .none

-- #eval frobenius (#[1,1,1] : Polynomial (Zmod 91)) (#[53,6] : Polynomial (Zmod 91))

inductive Extension (P : Type _) (K : Type _) where
  | E : Polynomial K → Extension P K

def unExt : Extension P K → Polynomial K
  | .E p => p

class IrreducibleMonic (P : Type _) (K : Type _) [GaloisField K] where
  poly : Extension P K → Polynomial K

def polyPow [OfNat K 0] : Polynomial K → Nat → Polynomial K
  | _, 0 => #[1]
  | p, k + 1 => polyMul p (polyPow p k)

variable [OfNat K 0] [Neg K] [BEq K] [HShiftRight K Nat K]

instance [gal : GaloisField K] [irr : IrreducibleMonic P K] : GaloisField (Extension P K) where
  plus e₁ e₂ := .E $ polyAdd (unExt e₁) (unExt e₂)
  times e₁ e₂ := .E $ polyMul (unExt e₁) (unExt e₂)
  null := .E zero
  ein := .E #[1]
  minus e₁ e₂ := .E $ polySub (unExt e₁) (unExt e₂)
  divis e₁ e₂ := .E $ polyDiv (unExt e₁) (unExt e₂)
  char := gal.char
  deg x := gal.deg 1 * degree (unExt x)
  frob
    | e@(.E p) =>
      match frobenius p (irr.poly e) with
        | .some z => .E z
        | .none => .E $ polyPow (irr.poly e) gal.char

end GaloisField