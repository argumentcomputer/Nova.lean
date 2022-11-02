import Nova.SNARK.Commitments
import Nova.SNARK.Errors
import Nova.SNARK.R1CS
import YatimaStdLib.Either

-- A helper trait for a step of the incremental computation (i.e., circuit for F)
class StepCircuit (F : Type _) where
-- Return the the number of inputs or outputs of each step
-- (this method is called only at circuit synthesis time)
-- synthesize and output methods are expected to take as
-- input a vector of size equal to arity and output a vector of size equal to arity  
  arity : USize
-- Sythesize the circuit for a computation step and return variable
-- that corresponds to the output of the step z
  synthesise : Array F → Either SynthesisError (Array F)
-- return the output of the step when provided with the step's input
  output : Array F → Array F

structure NovaAugmentedCircuitParams where
  limb_width : USize
  n_limbs : USize
-- A boolean indicating if this is the primary circuit
  is_primary_circuit : Bool

structure TrivialTestCircuit (F : Type _) where
  _p : F

structure NovaAugmentedCircuitInputs (G : Type _) where
  params : G
  i : G
  z₀ : Array G
  zᵢ : Option (Array G)
  U : Option (RelaxedR1CSInstance G)
  u : Option (R1CSInstance G)
  T : Option (Commitment G)

-- The augmented circuit F' in Nova that includes a step circuit F
-- and the circuit for the verifier in Nova's non-interactive folding scheme
structure NovaAugmentedCircuit (G : Type _) where
  params : NovaAugmentedCircuitParams
  inputs : Option (NovaAugmentedCircuitInputs G)
  step_circuit : StepCircuit G