import YatimaStdLib.Zmod

/-
Here we post some definitions from https://hackage.haskell.org/package/galois-field-1.0.2
-/

namespace GaloisField

class GaloisField (K : Type _) 
      [Add K] [Mul K] [Sub K] [Div K] where
  -- Characteristic @p@ of field and order of prime subfield.
  char : Nat

  -- Degree q of field as extension field over prime subfield.
  deg : Nat

  -- Frobenius endomorphism x ↦ x^p of prime subfield.
  frob : K → K

variable {K : Type} [Add K] [Mul K] [Sub K] [Div K] [gal : GaloisField K]

-- Order p^q of field.
def order : Nat := gal.char ^ gal.deg

instance : GaloisField (Zmod p) where
  char := p - 1
  deg := 1
  frob r := r ^ p

class PrimeField (K : Type _) 
      [Add K] [Mul K] [Sub K] [Div K] [GaloisField K] where
  fromP : K → Int

instance : PrimeField (Zmod p) where
  fromP a := (a : Int)

end GaloisField