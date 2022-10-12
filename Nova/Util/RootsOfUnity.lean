import Nova.Util.GaloisField

namespace RootsOfUnity

class CyclicSubgroup (G : Type _) where
  g : G

-- n-th roots of unity of Galois fields
inductive RootsOfUnity (n : Nat) (A : Type _) where
  | U : A → RootsOfUnity n A

-- Group operations on roots of unity
instance [Mul A] : Mul (RootsOfUnity n A) where
  mul a b :=
    match (a, b) with
    | (.U x, .U y) => .U $ x * y

instance [OfNat A 1] : OfNat (RootsOfUnity n A) 1 where
  ofNat := .U 1

instance [Div A] : Div (RootsOfUnity n A) where
  div a b :=
    match (a, b) with
    | (.U x, .U y) => .U $ x / y

open GaloisField

variable {K : Type} [gal : GaloisField K] [HPow K Nat K] [BEq K]

-- Cardinality of the subgroup
def cardinality : RootsOfUnity n K → Nat := fun _ => n

-- Cofactor of the subgroup in the group.
def cofactor : RootsOfUnity n K → Nat := 
  let ord := @order K gal
  (fun x => ord 1 / x) ∘ cardinality

-- isUnity checks is a given element of a Galois field is unity
def isUnity (k : K) (n : Nat) : Bool :=
  k ^ n == 1

-- Check if an element is the root of unity.
def isRootOfUnity (r : RootsOfUnity n K) : Bool :=
  match r with
    | .U x => isUnity x $ cardinality r

-- Check if an element is a primitive root of unity.
def isPrimitiveRootOfUnity (r : RootsOfUnity n K) : Bool :=
  match r with
    | .U x =>
        isRootOfUnity r && not (List.any (List.iota $ cardinality r - 1) (isUnity x))

end RootsOfUnity