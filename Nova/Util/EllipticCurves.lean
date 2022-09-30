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
  Point : Form → Coordinate → Type → Type → Type → Type
  char : Point f c E Q K → Nat
  cof : Point f c E Q K → Nat
  isWellDefined : Point f c E Q K → Nat
  disc : Point f c E Q K → Q
  order : Point f c E Q K → Nat
  add : Point f c E Q K → Point f c E Q K → Point f c E Q K
  dbl : Point f c E Q K → Point f c E Q K
  id : Point f c E Q K

end EllipticCurves