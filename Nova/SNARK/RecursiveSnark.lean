import Nova.BellPerson.Solver
import Nova.SNARK.Errors
import Nova.SNARK.NIFS
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

variable {G₁ G₂ : Type _} [c_primary : StepCircuit G₁] [c_secondary : StepCircuit G₂]
variable [OfNat G₁ 0] [OfNat G₁ 1] [OfNat G₂ 1] [wit : NovaWitness G₁] [wit' : NovaWitness G₂] [OfNat G₂ 0]
variable [Coe USize G₁] [Coe USize G₂]

-- Create a new `RecursiveSNARK` (or updates the provided `RecursiveSNARK`)
-- by executing a step of the incremental computation
def proof_step
  (pp : PublicParams G₁ G₂)
  (recursive_snark : Option (RecursiveSnark G₁ G₂))
  (z₀_primary : Array G₁)
  (z₀_secondary : Array G₂) : Either Error (RecursiveSnark G₁ G₂) := do
  if z₀_primary.size != pp.F_arity_primary.val || z₀_secondary.size != pp.F_arity_secondary.val
  then .left Error.InvalidInitialInputLength
    match recursive_snark with
      | .none =>
      -- base case for the primary
      let cs_primary : SatisfyingAssignment G₁ := newSatisfyingAssignment
      -- TODO: rewrite inputs_primary properly
      let inputs_primary : NovaAugmentedCircuitInputs G₁ :=
        NovaAugmentedCircuitInputs.mk 
          pp.r1cs_shape_primary.digest 
          0 
          z₀_primary
          .none 
          .none 
          .none 
          .none
      let circuit_primary : NovaAugmentedCircuit G₁ :=
        NovaAugmentedCircuit.mk pp.augmented_circuit_params_primary (.some inputs_primary) c_primary
      let (u_primary, w_primary) ← wit.r1cs_instance_and_witness pp.r1cs_shape_primary pp.r1cs_gens_primary
      
      -- base case for the secondary
      let cs_secondary : SatisfyingAssignment G₁ := newSatisfyingAssignment
      -- TODO: rewrite inputs_secondary properly
      let inputs_secondary :=
        NovaAugmentedCircuitInputs.mk 
          pp.r1cs_shape_primary.digest 
          (0 : G₁)
          z₀_primary
          .none
          .none
          (.some u_primary)
          .none
      let circuit_secondary : NovaAugmentedCircuit G₁ := 
        NovaAugmentedCircuit.mk pp.augmented_circuit_params_secondary (.some inputs_secondary) c_primary
      let (u_secondary, w_secondary) ← wit'.r1cs_instance_and_witness pp.r1cs_shape_secondary pp.r1cs_gens_secondary
      let r_W_primary := from_r1cs_witness pp.r1cs_shape_primary w_primary
      let r_U_primary := from_r1cs_instance pp.r1cs_gens_primary u_primary
      let r_W_secondary := default_relaxed_r1cs_witness pp.r1cs_shape_secondary
      let r_U_secondary := default_relaxed_r1cs_instance pp.r1cs_shape_secondary
      let zi_primary := c_primary.output z₀_primary
      let zi_secondary := c_secondary.output z₀_secondary
      if z₀_primary.size != pp.F_arity_primary.val || z₀_secondary.size != pp.F_arity_secondary.val
      then .left Error.InvalidStepOutputLength
      else
      .right $ RecursiveSnark.mk
                r_W_primary 
                r_U_primary 
                w_primary 
                u_primary 
                r_W_secondary 
                r_U_secondary 
                w_secondary
                u_secondary
                1
                zi_primary
                zi_secondary
      | .some r_snark => do
      let (l_u_primary, l_w_primary) ← wit.r1cs_instance_and_witness pp.r1cs_shape_primary pp.r1cs_gens_primary
      let zi_primary := c_primary.output z₀_primary
      let zi_secondary := c_secondary.output z₀_secondary
      let (l_u_secondary, l_w_secondary) ← wit'.r1cs_instance_and_witness pp.r1cs_shape_secondary pp.r1cs_gens_secondary
      let (_, r_U_secondary, r_W_secondary) ← 
        NIFS.prove
          pp.r1cs_gens_secondary
          pp.r1cs_shape_secondary
          r_snark.r_U_secondary
          r_snark.r_W_secondary
          r_snark.l_u_secondary
          r_snark.l_w_secondary
      
      let (_, r_U_primary, r_W_primary) ←
        NIFS.prove
          pp.r1cs_gens_primary
          pp.r1cs_shape_primary
          r_snark.r_U_primary
          r_snark.r_W_primary
          l_u_primary
          l_w_primary
      .right $ RecursiveSnark.mk 
                 r_W_primary
                 r_U_primary
                 l_w_primary
                 l_u_primary
                 r_W_secondary
                 r_U_secondary
                 l_w_secondary
                 l_u_secondary
                 (r_snark.i + 1)
                 zi_primary
                 zi_secondary

-- verify

-- 

end RecursiveSnark