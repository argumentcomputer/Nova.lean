import Nova.SNARK.Circuit
import Nova.SNARK.Commitments
import Nova.SNARK.Constraints
import Nova.SNARK.R1CS

-- A type that holds public parameters of Nova
structure PublicParams (G₁ : Type _) (G₂ : Type _) where
  FArityPrimary : USize
  FAritySecondary : USize
  --ro_consts_primary : ROConstants G₁
  --ro_consts_circuit_primary : ROConstantsCircuit G₂
  
  R1CSGensPrimary : R1CSGens G₁
  R1CSShapePrimary : R1CSShape G₁
  R1CSShapePaddedPrimary : R1CSShape G₁
  --ro_consts_secondary : ROConstants G₂
  --ro_consts_circuit_secondary : ROConstantsCircuit G₁
  R1CSGensSecondary : R1CSGens G₂
  R1CSShapeSecondary  : R1CSShape G₂
  R1CSShapePaddedSecondary : R1CSShape G₂
  AugmentedCircuitParamsPrimary : NovaAugmentedCircuitParams
  AugmentedCircuitParamsSecondary : NovaAugmentedCircuitParams

variable {G₁ G₂ : Type _} 
variable [cPrimary : StepCircuit G₁] [cSecondary : StepCircuit G₂]
variable [cs : NovaShape G₁] [cs2 : NovaShape G₂]

-- Create a new `PublicParams`
def setup : PublicParams G₁ G₂ :=
  let FArityPrimary : USize := cPrimary.arity
  let FAritySecondary : USize := cSecondary.arity
  let (R1CSShapePrimary, R1CSGensPrimary) := (cs.r1cs_shape, cs.r1cs_gens)
  let (R1CSShapeSecondary, R1CSGensSecondary) := (cs2.r1cs_shape, cs2.r1cs_gens)
  let AugmentedCircuitParamsPrimary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true
  let AugmentedCircuitParamsSecondary : NovaAugmentedCircuitParams :=
  NovaAugmentedCircuitParams.mk BN_LIMB_WIDTH BN_N_LIMBS true
  PublicParams.mk 
    FArityPrimary
    FAritySecondary 
    R1CSGensPrimary
    R1CSShapePrimary 
    R1CSShapePrimary 
    R1CSGensSecondary 
    R1CSShapeSecondary
    R1CSShapeSecondary 
    AugmentedCircuitParamsPrimary
    AugmentedCircuitParamsSecondary 