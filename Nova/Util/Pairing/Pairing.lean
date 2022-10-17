import Nova.Util.EllipticCurves
import YatimaStdLib.Zmod
import Nova.Util.GaloisField
import Nova.Util.RootsOfUnity

namespace Pairing

class Pairing (G₁ : Type _) (G₂ : Type _) (Gₜ : Type _) where
  e : G₁ → G₂ → Gₜ

open EllipticCurves Weierstrass AffineCurves GaloisField Form Coordinate

class ECPairing (q : Nat) (r : Nat) (U : Type _) (V : Type _) (W : Type _)

open RootsOfUnity

def GT U V W q r := RootsOfUnity r (Extension W (Extension V (Extension U (Zmod q))))

end Pairing