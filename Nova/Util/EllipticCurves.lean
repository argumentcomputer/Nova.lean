import Nova.Util.GaloisField

open GaloisField

namespace EllipticCurves

class Curve (Q : Type _) (R : Type _) [GaloisField Q] [GaloisField R] [PrimeField R] where
  Point : Type
  char : Point → Nat
  cof : Point → Nat
  isWellDefined : Point → Bool
  disc : Point → Q
  order : Point → Nat
  add : Point → Point → Point
  dbl : Point → Point
  id : Point
  inv : Point → Point
  frob : Point → Point
  gen : Point
  point : Q → Q → Option Point

open Curve

namespace Weierstrass

variable {Q R : Type _}  [galq : GaloisField Q] 
  [Neg Q] [OfNat Q 4] [OfNat Q 27] [OfNat Q 2] [OfNat Q 3] 
  [galr : GaloisField R] [prr : PrimeField R]

instance [Curve Q R] [BEq (Point Q R)] : Add (Point Q R) where
  add x y := if x == y then dbl x else add x y

instance [Curve Q R] : OfNat (Point Q R) 0 where
  ofNat := id

open Nat in
def mulNat [Curve Q R] (p : Curve.Point Q R) (n : Nat) : Point Q R :=
  match h : n with
    | 0 => id
    | (Nat.succ k) =>
      if k == 0 then p
      else
        have : n / 2 < n := 
        div_lt_self (zero_lt_of_ne_zero (h ▸ succ_ne_zero k)) (by decide)
        let p' := mulNat (dbl p) (n / 2)
        let isEven n := if n % 2 == 0 then true else false
        if isEven n then p' else add p p'
    termination_by _ => n

def mul' [Curve Q R] (p : Point Q R) (n : Int) : Point Q R :=
  match n with
    | (n : Nat) => mulNat p n
    | (Int.negSucc n) => inv $ mulNat p n

instance [Curve Q R] : HPow (Point Q R) Int (Point Q R) where
  hPow := mul'

instance [Curve Q R] [BEq (Point Q R)] : Sub (Point Q R) where
  sub a b := a + (Curve.inv b)

inductive ProjectivePoint (Q : Type _) (R : Type _) where
  | P : Q → Q → Q → ProjectivePoint Q R

instance prEq [OfNat Q 0] [BEq Q] : BEq (ProjectivePoint Q R) where
  beq p₁ p₂ :=
    match (p₁, p₂) with
      | (.P x y z, .P x' y' z') =>
      z == 0 && z' == 0 || x * z' == x' * z && y * z' == y' * z

class WCurve (Q : Type _) (R : Type _) 
      [GaloisField Q] 
      [GaloisField R] [PrimeField R]
      [Curve Q R] where
  a_ : Q
  b_ : Q
  h_ : Nat
  q_ : Nat
  r_ : Nat

class WPCurve (Q : Type _) (R : Type _) [GaloisField Q] [GaloisField R] [PrimeField R]
      [Curve Q R] [WCurve Q R] where
  gP : ProjectivePoint Q R

instance [PrimeField R] [PrimeField Q] [Curve Q R] [WCurve Q R] [WPCurve Q R] 
         [BEq Q] : Curve Q R where
  Point := ProjectivePoint Q R
  add p₁ p₂ :=
    match (p₁, p₂) with
      | (.P x₁ y₁ z₁, .P x₂ y₂ z₂) =>
        if z₂ == 0 then p₁
        else if z₁ == 0 then p₂
        else
          let y₁z₂ : Q := y₁ * z₂
          let x₁z₂ : Q := x₁ * z₂
          let z₁z₂ : Q := z₁ * z₂
          let u : Q := (y₂ * z₁) - y₁z₂
          let uu : Q := u * u
          let v : Q := (x₂ * z₁) - x₁z₂
          let vv := v * v
          let vvv := v * vv
          let r := vv * x₁z₂
          let a := ((uu * x₁z₂) - vvv) - (2 * r)
          let x₃ := v * a
          let y₃ := (u * (r - a)) - (vvv * y₁z₂)
          let z₃ := vvv * z₁z₂
          (.P x₃ y₃ z₃)
  char _ := WCurve.q_ Q R
  id := .P 0 1 0
  cof _ := WCurve.h_ Q R
  isWellDefined p :=
    let a : Q := WCurve.a_ R
    let b : Q := WCurve.b_ R
    match p with
      | (.P x y z) => ((x * x) + (a * z) * z) * x == ((y * y) - (b * z) * z) * z
  inv 
    | .P x y z => .P x (-y) z
  disc _ :=
    let a : Q := WCurve.a_ R
    let b : Q := WCurve.b_ R
    (((4 * a) * a) * a) + ((27 * b) * a)
  frob
    | .P x y z => .P (galq.frob x) (galq.frob y) (galq.frob z)
  order _ := WCurve.r_ Q R
  dbl
    | (.P x y z) => 
    if z == 0 
    then .P 1 0 1 
    else
    let a : Q := WCurve.a_ R
    let xx := x * x
    let zz := z * z
    let w := (a * zz) + (3 * xx)
    let s := (2 * y) * z
    let ss := s * s
    let sss := ss * s
    let r := y * s
    let rr := r * r
    let xr := x + r
    let b := ((xr * xr) - xx) - xr
    let h := (w * w) - 2 * b
    let x' := h * s
    let y' := (w * (b - h)) - (2 * rr)
    .P x' y' sss
  gen := WPCurve.gP
  point x y := 
    let p : ProjectivePoint Q R := .P x y 1
    let a : Q := WCurve.a_ R
    let b : Q := WCurve.b_ R
    if ((x * x) + (a * 1) * 1) * x == ((y * y) - (b * 1) * 1) * 1 then .some p else none

end Weierstrass

end EllipticCurves