import Nova.Util.GaloisField

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

class Curve (f : Form) (c : Coordinate) (E : Type _) (Q : Type _) (K : Type) where
  Point : Type
  eqP : BEq Point
  addInst : Add Point
  neqInst : Neg Point
  one : OfNat Point 1
  z : OfNat Point 0
  char : Point → Nat
  cof : Point → Nat
  isWellDefined : Point → Nat
  disc : Point → Q
  order : Point → Nat
  add : Point → Point → Point
  dbl : Point → Point
  id : Point
  inv : Point → Point
  frob : Point → Point
  gen : Point
  point : Q → Q → Point
  pointX : Q → Option Point
  yx : Point → Q → Option Q

open GaloisField

variable {K : Type} [a : Add K] [m : Mul K] [d : Div K] [s : Sub K] [gal : GaloisField K] [pr : PrimeField K]

open Curve

def isEven (n : Nat) : Bool :=
  if n % 2 == 0 then true else false

def mulNat [Curve f c E Q K] (p : Point f c E Q K) (n : Nat) : Point f c E Q K :=
  match h : n with
    | 0 => id
    | (Nat.succ k) =>
      if k == 0 then p
      else
        have h : n / 2 < n := sorry
        let p' := mulNat (dbl p) (n / 2)
        if isEven n then p' else add p p'
    termination_by _ => n

def mul' [Curve f c E Q K] (p : Point f c E Q K) (n : Int) : Point f c E Q K :=
  match n with
    | (n : Nat) => mulNat p n
    | (Int.negSucc n) => inv $ mulNat p n

end EllipticCurves