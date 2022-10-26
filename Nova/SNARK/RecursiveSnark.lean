import Nova.BellPerson.Solver
import Nova.SNARK.Errors
import Nova.SNARK.PublicParams
import Nova.SNARK.R1CS
import Nova.SNARK.Circuit
import YatimaStdLib.Either

namespace RecursiveSnark

structure RecursiveSnark 
  (G₁ : Type _) (G₂ : Type _) where
  r_W_primary : RelaxedR1CSWitness G₁
  r_U_primary : RelaxedR1CSInstance G₁
  l_w_primary : R1CSWitness G₁
  l_u_primary : R1CSInstance G₁
  r_W_secondary: RelaxedR1CSWitness G₂
  r_U_secondary: RelaxedR1CSInstance G₂
  l_w_secondary : R1CSWitness G₂
  l_u_secondary : R1CSInstance G₂
  i : USize
  zi_primary : Array G₁
  zi_secondary : Array G₂

variable {G₁ G₂ : Type _} [c_primary : StepCircuit G₁] [c_secondary : StepCircuit G₁]
variable [OfNat G₁ 0] [OfNat G₁ 1] [OfNat G₂ 1] [wit : NovaWitness G₁]

-- Create a new `RecursiveSNARK` (or updates the provided `RecursiveSNARK`)
-- by executing a step of the incremental computation
def proof_step
  (pp : PublicParams G₁ G₂)
  (recursive_snark : Option (RecursiveSnark G₁ G₂))
  (z₀_primary : Array G₁)
  (z₀_secondary : Array G₂) : Either Error (RecursiveSnark G₁ G₂) :=
  if z₀_primary.size != pp.F_arity_primary.val || z₀_secondary.size != pp.F_arity_secondary.val
  then .left Error.InvalidInitialInputLength
  else
    match recursive_snark with
      | .none =>
      -- base case for the primary
      let cs_primary : SatisfyingAssignment G₁ := newSatisfyingAssignment
      let inputs_primary : NovaAugmentedCircuitInputs G₁ :=
        NovaAugmentedCircuitInputs.mk 
          pp.r1cs_shape_secondary.digest 
          0 
          z₀_primary
          .none 
          .none 
          .none 
          .none
      let circuit_primary : NovaAugmentedCircuit G₁ :=
        NovaAugmentedCircuit.mk pp.augmented_circuit_params_primary (.some $ inputs_primary) c_primary
      let shape_and_wit : Either Error (R1CSInstance G₁ × R1CSWitness G₁) := 
        wit.r1cs_instance_and_witness pp.r1cs_shape_primary pp.r1cs_gens_primary
      -- TODO: extract (u_primary, w_primary) from shape_and_wit

      -- base case for the secondary
      let cs_secondary : SatisfyingAssignment G₂ := newSatisfyingAssignment
      RecursiveSnark.mk _ _ _ _ _ _ _ _ _ _ _
      | .some _ =>
      RecursiveSnark.mk _ _ _ _ _ _ _ _ _ _ _

-- verify

-- 

end RecursiveSnark