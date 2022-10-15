import Nova.Util.EllipticCurves
import YatimaStdLib.Zmod
import Nova.Util.GaloisField
import Nova.Util.RootsOfUnity

namespace Pairing

class Pairing (G₁ : Type _) (G₂ : Type _) (Gₜ : Type _) where
  e : G₁ → G₂ → Gₜ

open EllipticCurves Weierstrass AffineCurves GaloisField Form Coordinate

class ECPairing (q : Nat) (r : Nat) (U : Type _) (V : Type _) (W : Type _)
  [Curve Weiestrass Affine (Zmod q) (Zmod r)]
  [GaloisField (Extension U (Zmod q))]
  [WCurve Affine (Zmod q) (Zmod r)]
  [WACurve (Zmod q) (Zmod r)]
  [Curve (Extension U (Zmod q)) (Zmod r)]
  [IrreducibleMonic U (Zmod q)]
  [GaloisField (Extension V (Extension U (Zmod q)))]
  [IrreducibleMonic V (Extension U (Zmod q))]
  [IrreducibleMonic W (Extension V (Extension U (Zmod q)))]
  [IrreducibleMonic U (Zmod q)]
  [Curve (Extension U (Zmod q)) (Zmod r)]
  [WCurve (Extension U (Zmod q)) (Zmod r)]
  [WACurve (Extension U (Zmod q)) (Zmod r)]

open RootsOfUnity

def GT U V W q r := RootsOfUnity r (Extension W (Extension V (Extension U (Zmod q))))

end Pairing