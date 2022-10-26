-- A helper type class that defines the constants associated with a hash function
class ROConstantsClass (Base : Type _) where
  new : Base

-- A helper type class that defines the behaviour of a hash function 
-- that we use as an RO in the circuit model
class ROCircuitClass (Scalar : Type _) (Base : Type _) [ROConstantsClass Base] where
  new : USize → Base
  absorb : Scalar → Base
  squeeze : USize → Scalar