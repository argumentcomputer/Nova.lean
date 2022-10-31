import Nova.SNARK.Circuit
import Nova.SNARK.Commitments
import Nova.SNARK.Constraints
import Nova.SNARK.R1CS

structure PublicParams (G₁ : Type _) (G₂ : Type _) where
  F_arity_primary : USize
  F_arity_secondary : USize
  --ro_consts_primary : ROConstants G₁
  --ro_consts_circuit_primary : ROConstantsCircuit G₂
  
  r1cs_gens_primary : R1CSGens G₁
  r1cs_shape_primary : R1CSShape G₁
  r1cs_shape_padded_primary : R1CSShape G₁
  --ro_consts_secondary : ROConstants G₂
  --ro_consts_circuit_secondary : ROConstantsCircuit G₁
  r1cs_gens_secondary : R1CSGens G₂
  r1cs_shape_secondary  : R1CSShape G₂
  r1cs_shape_padded_secondary : R1CSShape G₂
  augmented_circuit_params_primary : NovaAugmentedCircuitParams
  augmented_circuit_params_secondary : NovaAugmentedCircuitParams

variable {G₁ G₂ : Type _} 
variable [c_primary : StepCircuit G₁] [c_secondary : StepCircuit G₂]
variable [cs : NovaShape G₁] [cs2 : NovaShape G₂]

def setup : PublicParams G₁ G₂ :=
  let F_arity_primary : USize := c_primary.arity
  let F_arity_secondary : USize := c_secondary.arity
  let (r1cs_shape_primary, r1cs_gens_primary) := (cs.r1cs_shape, cs.r1cs_gens)
  let (r1cs_shape_secondary, r1cs_gens_secondary) := (cs2.r1cs_shape, cs2.r1cs_gens)
  let augmented_circuit_params_primary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true
  let augmented_circuit_params_secondary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true
  PublicParams.mk 
    F_arity_primary
    F_arity_secondary 
    r1cs_gens_primary
    r1cs_shape_primary 
    r1cs_shape_primary 
    r1cs_gens_secondary 
    r1cs_shape_secondary
    r1cs_shape_secondary 
    augmented_circuit_params_primary
    augmented_circuit_params_secondary 