import Nova.SNARK.Circuit
import Nova.SNARK.Commitments
import Nova.SNARK.Constraints
import Nova.SNARK.R1CS

open Circuit Commitments R1CS

namespace PublicParams

structure PublicParams 
  (G₁ : Type _) (G₂ : Type _)
  (C₁ : Type _) (C₂ : Type _) where
  F_arity_primary : USize
  F_arity_secondary : USize
  --ro_consts_primary : ROConstants G₁
  --ro_consts_circuit_primary : ROConstantsCircuit G₂
  
  r1cs_gens_primary : R1CSGens G₁
  r1cs_shape_primary : R1CSShape G₁
  r1cs_shape_padded_primary : R1CSShape G₁
  --ro_consts_secondary : ROConstants G₂
  --ro_consts_circuit_secondary : ROConstantsCircuit G₁
  r1cs_gens_secondary : R1CSGens G₁
  r1cs_shape_secondary  : R1CSShape G₁
  r1cs_shape_padded_secondary : R1CSShape G₁
  augmented_circuit_params_primary : NovaAugmentedCircuitParams
  augmented_circuit_params_secondary : NovaAugmentedCircuitParams
  _p_c1 : C₁
  _p_c2 : C₂

def augmented_circuit_params_primary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true

def augmented_circuit_params_secondary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true

-- create a new PublicParams

-- initialise gens for the primary circuit

-- initialise gens for the secondary circuit

end PublicParams