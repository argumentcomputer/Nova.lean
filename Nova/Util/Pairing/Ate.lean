import Nova.Util.EllipticCurves
import Nova.Util.GaloisField
import Nova.Util.RootsOfUnity
import Nova.Util.Pairing.Pairing

namespace Ate

variable {q r : Nat} {U V W : Type _}

open EllipticCurves GaloisField RootsOfUnity Pairing

variable [Curve (Zmod q) (Zmod r)]
variable [GaloisField (Extension U (Zmod q))]
variable [Curve (Extension U (Zmod q)) (Zmod r)]
variable [IrreducibleMonic U (Zmod q)]
variable [GaloisField (Extension V (Extension U (Zmod q)))]
variable [IrreducibleMonic V (Extension U (Zmod q))]
variable [IrreducibleMonic W (Extension V (Extension U (Zmod q)))]
variable [Pairing (AffinePoint (Zmod q) (Zmod r)) (AffinePoint (Extension U (Zmod q)) (Zmod r)) (GT U V W q r)]

def millerLoop
  (a : AffinePoint (Zmod q) (Zmod r)) 
  (b : AffinePoint (Extension U (Zmod q)) (Zmod r))
  (l : List Int)
  (pair₁ : (AffinePoint (Extension U (Zmod q)) (Zmod r)) × (GT U V W q r)) :
  (AffinePoint (Extension U (Zmod q)) (Zmod r)) × (GT U V W q r) := sorry

def millerAlgorithmBLS12
  (l : List Int) (a : AffinePoint (Zmod q) (Zmod r)) (b : AffinePoint (Extension U (Zmod q)) (Zmod r)) :
  GT U V W q r :=
    match l with
      | x :: xs => 
        (fun (x, y) => y) $ millerLoop a b xs (if x > 0 then b else cur.inv (Extension U (Zmod q)) (Zmod r) b, _)
      | [] => .U $ .E #[.E #[.E #[1]]]

end Ate