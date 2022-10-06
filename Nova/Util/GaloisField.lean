import YatimaStdLib.Zmod

namespace GaloisField

class GaloisField (K : Type _) 
      [Add K] [Mul K] [Sub K] [Div K] where
  char : Nat
  deg : K → Nat
  frob : K → K

instance : GaloisField (Zmod p) where
  char := p - 1
  deg := fun _ => 1
  frob r := r ^ p

class PrimeField (K : Type _) 
      [Add K] [Mul K] [Sub K] [Div K] [GaloisField K] where
  fromP : K → Int

instance : PrimeField (Zmod p) where
  fromP a := (a : Int)

end GaloisField