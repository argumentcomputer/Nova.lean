import Nova.SNARK.R1CS

/--
A helper type class that defines the constants associated with a hash function
-/
class ROConstantsClass (G : Type _) where
  new : Base
  -- TODO: reconsider

/-- A helper type class that defines the behaviour of a hash function 
that we use as an RO in the circuit model
-/
class ROCircuitClass (G : Type _) where
  new : USize → G
  absorb : G → G
  squeeze : USize → G

/--
A class that defines the behaviour of a zkSNARK's prover key
-/
class ProverKey (G : Type _) where
  /--
  Produces a new prover's key
  -/
  proverKey : R1CSGens G → R1CSShape G → G

/--
A class that defines the behaviour of a zkSNARK's verifier key
-/
class VerifierKey (G : Type _) where
  verifierKey : R1CSGens G → R1CSShape G → G

/--
A class that defines the behaviour of a zkSNARK
-/
class RelaxedR1CSSNARK (G : Type _) extends ProverKey G, VerifierKey G where
  /--
  Produces a new SNARK for a relaxed `R1CS`
  -/ 
  prove : G → RelaxedR1CSInstance G → RelaxedR1CSWitness G → Except Error G

  /--
  Verifies a SNARK for a relaxed `R1CS`
  -/
  verify : G → RelaxedR1CSInstance G → Except Error PUnit