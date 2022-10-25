import Nova.SNARK.Errors
import YatimaStdLib.Either

namespace Circuit

-- A helper trait for a step of the incremental computation (i.e., circuit for F)
class StepCircuit (F : Type _) where
-- Return the the number of inputs or outputs of each step
-- (this method is called only at circuit synthesis time)
-- synthesize and output methods are expected to take as
-- input a vector of size equal to arity and output a vector of size equal to arity  
  arity : F → USize
-- Sythesize the circuit for a computation step and return variable
-- that corresponds to the output of the step z
  synthesise : F → List F → Either (Array F) SynthesisError
-- return the output of the step when provided with the step's input
  output : F → List F → Array F

structure NovaAugmentedCircuitParams where
  limb_width : USize
  n_limbs : USize
-- A boolean indicating if this is the primary circuit
  is_primary_circuit : Bool

structure TrivialTestCircuit (F : Type _) where
  _p : F

end Circuit