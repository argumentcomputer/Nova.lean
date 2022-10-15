import Nova.Util.GaloisField

open GaloisField

inductive Form : Type where
  | Binary
  | Edwards
  | Montgomery
  | Weierstrass

inductive Coordinate : Type where
  | Projective
  | Affine

namespace EllipticCurves

open Form Coordinate

class Curve (f : Form) (c : Coordinate) (Q : Type _) (R : Type _) 
      [GaloisField Q] [GaloisField R] [PrimeField R] where
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

class WCurve (c : Coordinate) (Q : Type _) (R : Type _) 
      [GaloisField Q] 
      [GaloisField R] [PrimeField R]
      [Curve Weierstrass c Q R] where
  a_ : Q
  b_ : Q
  h_ : Nat
  q_ : Nat
  r_ : Nat

open Curve

namespace Weierstrass

variable {Q R : Type _}  [galq : GaloisField Q] 
  [Neg Q] [OfNat Q 4] [OfNat Q 27] [OfNat Q 2] [OfNat Q 3] 
  [galr : GaloisField R] [prr : PrimeField R]

instance [Curve Weierstrass c Q R] [BEq (Point Weierstrass c Q R)] : Add (Point Weierstrass c Q R) where
  add x y := if x == y then dbl x else add x y

instance [Curve Weierstrass c Q R] : OfNat (Point Weierstrass c Q R) 0 where
  ofNat := id

open Nat in
def mulNat [Curve Weierstrass c Q R] (p : Curve.Point Weierstrass c Q R) (n : Nat) : Point Weierstrass c Q R :=
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

def mul' [Curve Weierstrass c Q R] (p : Point Weierstrass c Q R) (n : Int) : Point Weierstrass c Q R :=
  match n with
    | (n : Nat) => mulNat p n
    | (Int.negSucc n) => inv $ mulNat p n

instance [Curve Weierstrass c Q R] : HPow (Point Weierstrass c Q R) Int (Point Weierstrass c Q R) where
  hPow := mul'

instance [Curve Weierstrass c Q R] [BEq (Point Weierstrass c Q R)] : Sub (Point Weierstrass c Q R) where
  sub a b := a + (Curve.inv b)

inductive ProjectivePoint (Q : Type _) (R : Type _) where
  | P : Q → Q → Q → ProjectivePoint Q R

instance prEq [OfNat Q 0] [BEq Q] : BEq (ProjectivePoint Q R) where
  beq p₁ p₂ :=
    match (p₁, p₂) with
      | (.P x y z, .P x' y' z') =>
      z == 0 && z' == 0 || x * z' == x' * z && y * z' == y' * z

namespace ProjectiveCurves

class WPCurve (Q : Type _) (R : Type _) [GaloisField Q] [GaloisField R] [PrimeField R]
      [Curve Weierstrass Projective Q R] where
  gP : ProjectivePoint Q R

instance [PrimeField R] [PrimeField Q] [Curve Weierstrass Projective Q R] [WCurve Projective Q R] [WPCurve Q R] 
         [BEq Q] : Curve Weierstrass Projective Q R where
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
  char _ := WCurve.q_ Projective Q R
  id := .P 0 1 0
  cof _ := WCurve.h_ Projective Q R
  isWellDefined p :=
    let a : Q := WCurve.a_ Projective R
    let b : Q := WCurve.b_ Projective R
    match p with
      | (.P x y z) => ((x * x) + (a * z) * z) * x == ((y * y) - (b * z) * z) * z
  inv 
    | .P x y z => .P x (-y) z
  disc _ :=
    let a : Q := WCurve.a_ Projective R
    let b : Q := WCurve.b_ Projective R
    (((4 * a) * a) * a) + ((27 * b) * a)
  frob
    | .P x y z => .P (galq.frob x) (galq.frob y) (galq.frob z)
  order _ := WCurve.r_ Projective Q R
  dbl
    | (.P x y z) => 
    if z == 0 
    then .P 1 0 1 
    else
    let a : Q := WCurve.a_ Projective R
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
    let a : Q := WCurve.a_ Projective R
    let b : Q := WCurve.b_ Projective R
    if ((x * x) + (a * 1) * 1) * x == ((y * y) - (b * 1) * 1) * 1 then .some p else none

end ProjectiveCurves

namespace AffineCurves

inductive AffinePoint (Q : Type _) (R : Type _) where
  -- affine point
  | A : Q → Q → AffinePoint Q R
  -- infinity point
  | O : AffinePoint Q R
  deriving BEq

class WACurve (Q : Type _) (R : Type _) 
      [GaloisField Q] [GaloisField R] [PrimeField R]
      [Curve Weierstrass Affine Q R] [WCurve Affine Q R] where
  -- curve generator
  gA_ : AffinePoint Q R

instance [Curve Weierstrass Affine Q R] [w : WCurve Affine Q R] [WACurve Q R] [BEq Q] : Curve Weierstrass Affine Q R where
  Point := AffinePoint Q R
  char _ := w.q_
  cof _ := w.h_
  add x y :=
    match (x, y) with
      | (.O, _) => .O
      | (_, .O) => .O
      | (.A x₁ y₁, .A x₂ y₂) =>
        if x₁ == x₂ then .O else
        let l := (y₁ - y₂) / (x₁ - x₂)
        let x₃ := ((l * l) - x₁) - x₂
        let y₃ := (l * (x₁ - x₃)) - y₁
        .A x₃ y₃
  isWellDefined
    | .O => true
    | .A x y => (((x * x) + w.a_) * x) + w.b_ == y * y
  disc _ := (((4 * w.a_) * w.a_) * w.a_) + ((27 * w.b_) * w.b_)
  order _ := w.r_
  dbl
    | .O => .O
    | .A x y =>
      if y == 0 then .O else
      let xx := x * x
      let l := (((xx + xx) + xx) + w.a_) / (y + y)
      let x' := ((l * l) - x) - x
      let y' := (l * (x - x')) - y
      .A x' y'
  id := .O
  inv
    | .O => .O
    | .A x y => .A x (-y)
  frob
    | .O => .O
    | .A x y => .A (GaloisField.frob x) (GaloisField.frob y)
  gen := WACurve.gA_
  point x y :=
    let p := .A x y
    if (((x * x) + w.a_) * x) + w.b_ == y * y then .some p else none


end AffineCurves

end Weierstrass

end EllipticCurves