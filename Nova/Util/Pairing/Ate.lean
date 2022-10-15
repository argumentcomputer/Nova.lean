import Nova.Util.EllipticCurves
import Nova.Util.GaloisField
import Nova.Util.RootsOfUnity
import Nova.Util.Pairing.Pairing

namespace Ate

variable {q r : Nat} (V U W : Type _)

open EllipticCurves Weierstrass AffineCurves GaloisField RootsOfUnity Pairing

variable [Curve (Zmod q) (Zmod r)]
variable [GaloisField (Extension U (Zmod q))]
variable [WCurve (Zmod q) (Zmod r)]
variable [WACurve (Zmod q) (Zmod r)]
variable [Curve (Extension U (Zmod q)) (Zmod r)]
variable [IrreducibleMonic U (Zmod q)]
variable [GaloisField (Extension V (Extension U (Zmod q)))]
variable [IrreducibleMonic V (Extension U (Zmod q))]
variable [IrreducibleMonic W (Extension V (Extension U (Zmod q)))]
variable [WCurve (Extension U (Zmod q)) (Zmod r)]
variable [WACurve (Extension U (Zmod q)) (Zmod r)]
variable [Pairing (AffinePoint (Zmod q) (Zmod r)) (AffinePoint (Extension U (Zmod q)) (Zmod r)) (RootsOfUnity r (Extension W (Extension V (Extension U (Zmod q)))))]

def millerAlgorithmBLS12 [ECPairing q r U V W]
  (x : AffinePoint (Zmod q) (Zmod r)) (y : AffinePoint (Extension U (Zmod q)) (Zmod r)) :
  RootsOfUnity r (Extension W (Extension V (Extension U (Zmod q)))) := sorry

end Ate