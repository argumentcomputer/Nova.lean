-- A helper type class that defines the constants associated with a hash function
class ROConstantsClass (G : Type _) where
  new : Base

-- A helper type class that defines the behaviour of a hash function 
-- that we use as an RO in the circuit model
class ROCircuitClass (G : Type _) where
  new : USize → G
  absorb : G → G
  squeeze : USize → G