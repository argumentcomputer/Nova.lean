namespace GaloisField

class GaloisField (K : Type) 
      [Add K] [Mul K] [Sub K] [Div K] where
  char : K → Nat
  deg : K → Nat
  frob : K → K
  order : K → Nat

class PrimeField (K : Type) 
      [Add K] [Mul K] [Sub K] [Div K] [GaloisField K] where
  fromP : K → Int

end GaloisField