import Nova.Util.EllipticCurves
import Nova.Util.GaloisField

namespace Pairing

class Pairing (G₁ : Type _) (G₂ : Type _) (Gₜ : Type _) where
  e : G₁ → G₂ → Gₜ

end Pairing