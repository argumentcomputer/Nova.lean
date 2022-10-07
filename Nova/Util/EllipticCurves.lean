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
  [Neg Q] [OfNat Q 4] [OfNat Q 27] [OfNat Q 2] [OfNat Q 3] [galr : GaloisField R] [prr : PrimeField R]

instance [Curve Q R] : Add (Curve.Point Q R) where
  add := add

def isEven (n : Nat) : Bool :=
  if n % 2 == 0 then true else false

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
        if isEven n then p' else add p p'
    termination_by _ => n

def mul' [Curve Q R] (p : Point Q R) (n : Int) : Point Q R :=
  match n with
    | (n : Nat) => mulNat p n
    | (Int.negSucc n) => inv $ mulNat p n

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
  a_ : ProjectivePoint Q R → Q
  b_ : ProjectivePoint Q R → Q
  h_ : ProjectivePoint Q R → Nat
  q_ : ProjectivePoint Q R → Nat
  r_ : ProjectivePoint Q R → Nat

class WPCurve (Q : Type _) (R : Type _) [GaloisField Q] [GaloisField R] [PrimeField R]
      [Curve Q R] [WCurve Q R] where
  gP : ProjectivePoint Q R

def witness : (A : Type _) := sorry

instance [inst₁ : Curve Q R] 
         [inst₂ : WCurve Q R] [inst₃ : WPCurve Q R] 
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
  char := WCurve.q_
  id := .P 0 1 0
  cof := WCurve.h_
  isWellDefined p :=
    let a' := @WCurve.a_ Q R galq galr prr inst₁ inst₂
    let b' := @WCurve.b_ Q R galq galr prr inst₁ inst₂
    let a := a' witness
    let b := b' witness
    match p with
      | (.P x y z) => ((x * x) + (a * z) * z) * x == ((y * y) - (b * z) * z) * z
  inv 
    | .P x y z => .P x (-y) z
  disc _ :=
    let a' := 
      @WCurve.a_ Q R galq galr prr inst₁ inst₂
    let b' :=
      @WCurve.b_ Q R galq galr prr inst₁ inst₂
    let a := a' witness
    let b := b' witness
    (((4 * a) * a) * a) + ((27 * b) * b)
  frob
    | .P x y z => .P (galq.frob x) (galq.frob y) (galq.frob z)
  order := WCurve.r_
  dbl
    | (.P x y z) => 
    if z == 0 
    then .P 1 0 1 
    else
    let a' := 
      @WCurve.a_ Q R galq galr prr inst₁ inst₂
    let a := a' witness
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
  gen := inst₃.gP
  point x y := 
    let p : ProjectivePoint Q R := .P x y 1
    let a' := 
      @WCurve.a_ Q R galq galr prr inst₁ inst₂
    let b' := 
      @WCurve.b_ Q R galq galr prr inst₁ inst₂
    let a := a' witness
    let b := b' witness
    if ((x * x) + (a * 1) * 1) * x == ((y * y) - (b * 1) * 1) * 1 then .some p else none

end Weierstrass

end EllipticCurves