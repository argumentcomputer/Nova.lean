import Nova.Util.GaloisField

open GaloisField

namespace EllipticCurves

inductive Form : Type where
  | Binary
  | Edwards
  | Montgomery
  | Weierstrass

inductive Coordinate : Type where
  | Jacobian
  | Affine
  | Projective

class Curve (f : Form) (c : Coordinate) 
      (E : Type _) (Q : Type _) (R : Type _) 
      [Add Q] [Mul Q] [Sub Q] [Div Q] [GaloisField Q] 
      [Add R] [Mul R] [Sub R] [Div R] [GaloisField R] [PrimeField R] where
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
  pointX : Q → Option Point
  yx : Point → Q → Option Q

open Curve

variable {Q R : Type _} 
  [addq : Add Q] [mulq : Mul Q] [div : Div Q] 
  [subq : Sub Q] [galq : GaloisField Q] 
  [Neg Q] [OfNat Q 4] [OfNat Q 27] [OfNat Q 0] [OfNat Q 1] [OfNat Q 2] [OfNat Q 3]
  [addr : Add R] [mulr : Mul R] [divr : Div R] 
  [subr : Sub R] [galr : GaloisField R] [prr : PrimeField R]

instance [Curve f c E Q R] : Add (Curve.Point f c E Q R) where
  add := add

def isEven (n : Nat) : Bool :=
  if n % 2 == 0 then true else false

open Nat in
def mulNat [Curve f c E Q R] (p : Point f c E Q R) (n : Nat) : Point f c E Q R :=
  match h : n with
    | 0 => id
    | (Nat.succ k) =>
      if k == 0 then p
      else
        have : n / 2 < n := div_lt_self (zero_lt_of_ne_zero (h ▸ succ_ne_zero k)) (by decide)
        let p' := mulNat (dbl p) (n / 2)
        if isEven n then p' else add p p'
    termination_by _ => n

def mul' [Curve f c E Q R] (p : Point f c E Q R) (n : Int) : Point f c E Q R :=
  match n with
    | (n : Nat) => mulNat p n
    | (Int.negSucc n) => inv $ mulNat p n

open Form Coordinate

inductive ProjectivePoint (f : Form) (p : Coordinate) (E : Type _) (Q : Type _) (R : Type _) where
  | P : Q → Q → Q → ProjectivePoint f p E Q R

instance prEq [OfNat Q 0] [BEq Q] : BEq (ProjectivePoint Weierstrass Projective E Q R) where
  beq p₁ p₂ :=
    match (p₁, p₂) with
      | (.P x y z, .P x' y' z') =>
      z == 0 && z' == 0 || x * z' == x' * z && y * z' == y' * z

class WCurve (c : Coordinate) (E : Type _) (Q : Type _) (R : Type _) 
      [Add Q] [Mul Q] [Sub Q] [Div Q] [GaloisField Q] 
      [Add R] [Mul R] [Sub R] [Div R] [GaloisField R] [PrimeField R]
      [Curve Weierstrass c E Q R] where
  a_ : ProjectivePoint Weierstrass c E Q R → Q
  b_ : ProjectivePoint Weierstrass c E Q R → Q
  h_ : ProjectivePoint Weierstrass c E Q R → Nat
  q_ : ProjectivePoint Weierstrass c E Q R → Nat
  r_ : ProjectivePoint Weierstrass c E Q R → Nat

class WPCurve (c : Coordinate) (E : Type _) (Q : Type _) (R : Type _) 
      [Add Q] [Mul Q] [Sub Q] [Div Q] [GaloisField Q] 
      [Add R] [Mul R] [Sub R] [Div R] [GaloisField R] [PrimeField R]
      [Curve Weierstrass Projective E Q R] [WCurve Projective E Q R] where
  gP : ProjectivePoint Weierstrass Projective E Q R

def witness : (A : Type _) := sorry

instance [inst₁ : Curve Weierstrass Projective E Q R] 
         [inst₂ : WCurve Projective E Q R] [inst₃ : WPCurve Projective E Q R] 
         [BEq Q] : Curve Weierstrass Projective E Q R where
  Point := ProjectivePoint Weierstrass Projective E Q R
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
    let a' := @WCurve.a_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
    let b' := @WCurve.b_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
    let a := a' witness
    let b := b' witness
    match p with
      | (.P x y z) => ((x * x) + (a * z) * z) * x == ((y * y) - (b * z) * z) * z
  inv 
    | .P x y z => .P x (-y) z
  disc _ :=
    let a' := 
      @WCurve.a_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
    let b' :=
      @WCurve.b_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
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
      @WCurve.a_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
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
    let p : ProjectivePoint Weierstrass Projective E Q R := .P x y 1
    let a' := @WCurve.a_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
    let b' := @WCurve.b_ Projective E Q R addq mulq subq div galq addr mulr subr divr galr prr inst₁ inst₂
    let a := a' witness
    let b := b' witness
    if ((x * x) + (a * 1) * 1) * x == ((y * y) - (b * 1) * 1) * 1 then .some p else none
  pointX := sorry
  yx := sorry

end EllipticCurves