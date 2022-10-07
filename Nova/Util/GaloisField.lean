import YatimaStdLib.Zmod

/-
Here we post some definitions from https://hackage.haskell.org/package/galois-field-1.0.2
-/

namespace GaloisField

class GaloisField (K : Type _) where
  plus : K → K → K
  times : K → K → K
  null : K
  ein : K
  minus : K → K → K
  divis : K → K → K
  
  -- Characteristic @p@ of field and order of prime subfield.
  char : Nat

  -- Degree q of field as extension field over prime subfield.
  deg : Nat

  -- Frobenius endomorphism x ↦ x^p of prime subfield.
  frob : K → K

open GaloisField

instance [GaloisField K] : Add K where
  add := plus

instance [GaloisField K] : Mul K where
  mul := times

instance [GaloisField K] : OfNat K 1 where
  ofNat := ein

instance [GaloisField K] : OfNat K 0 where
  ofNat := null

instance [GaloisField K] : Div K where
  div := divis

instance [GaloisField K] : Sub K where
  sub := minus

variable {K : Type} [gal : GaloisField K]

-- Order p^q of field.
def order : Nat := gal.char ^ gal.deg

instance : GaloisField (Zmod p) where
  plus := (. + .)
  times := (. * .)
  null := 0
  ein := 1
  minus := (. - .)
  divis := (. / .)
  char := p - 1
  deg := 1
  frob r := r ^ p

class PrimeField (K : Type _) [GaloisField K] where
  fromP : K → Int

instance : PrimeField (Zmod p) where
  fromP a := (a : Int)

end GaloisField