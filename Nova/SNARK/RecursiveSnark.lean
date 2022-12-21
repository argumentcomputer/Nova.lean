import Nova.BellPerson.Solver
import Nova.SNARK.Errors
import Nova.SNARK.NIFS
import Nova.SNARK.PublicParams
import Nova.SNARK.R1CS
import Nova.SNARK.Circuit

structure RecursiveSnark 
  (G₁ : Type _) (G₂ : Type _) where
  rwPrimary : RelaxedR1CSWitness G₁
  ruPrimary : RelaxedR1CSInstance G₁
  lwPrimary : R1CSWitness G₁
  luPrimary : R1CSInstance G₁
  rwSecondary : RelaxedR1CSWitness G₂
  ruSecondary : RelaxedR1CSInstance G₂
  lwSecondary : R1CSWitness G₂
  luSecondary : R1CSInstance G₂
  i : USize
  ziPrimary : Array G₁
  ziSecondary : Array G₂

-- required constraints for Recursive-snark related function
variable {G₁ G₂ : Type _} [Ring G₁] [Ring G₂] [cPrimary : StepCircuit G₁] [cSecondary : StepCircuit G₂]
variable [OfNat G₁ (nat_lit 0)] [OfNat G₁ (nat_lit 1)] [OfNat G₂ (nat_lit 1)] [OfNat G₂ (nat_lit 0)]
variable [Coe Nat G₁] [Coe Nat G₂]
variable [BEq G₁] [BEq G₂]
variable [wit : NovaWitness G₁] [wit' : NovaWitness G₂]
variable [Coe USize G₁] [Coe USize G₂] 
variable [Inhabited G₂] [Inhabited G₁]
variable [ROCircuitClass G₂] [ROCircuitClass G₁]
variable [HPow G₁ G₁ G₁][HPow G₂ G₂ G₂]

open Error

-- Create a new `RecursiveSNARK` (or updates the provided `RecursiveSNARK`)
-- by executing a step of the incremental computation
def proofStep
  (pp : PublicParams G₁ G₂)
  (recursiveSNARK : Option (RecursiveSnark G₁ G₂))
  (z₀Primary : Array G₁)
  (z₀Secondary : Array G₂) : Except Error (RecursiveSnark G₁ G₂) := do
  if z₀Primary.size != pp.FArityPrimary.val || z₀Secondary.size != pp.FAritySecondary.val
  then .error Error.InvalidInitialInputLength
    match recursiveSNARK with
      | .none =>
      -- base case for the primary
      let csPrimary : SatisfyingAssignment G₁ := newSatisfyingAssignment
      -- TODO: rewrite inputs_primary properly in further PRs
      let inputsPrimary : NovaAugmentedCircuitInputs G₁ :=
        NovaAugmentedCircuitInputs.mk 
          pp.R1CSShapePrimary.digest 
          0 
          z₀Primary
          .none 
          .none 
          .none 
          .none
      let circuitPrimary : NovaAugmentedCircuit G₁ :=
        NovaAugmentedCircuit.mk pp.AugmentedCircuitParamsPrimary (.some inputsPrimary) cPrimary
      let (uPrimary, wPrimary) ← wit.R1CSInstanceAndWitness pp.R1CSShapePrimary pp.R1CSGensPrimary
      
      -- base case for the secondary
      let csSecondary : SatisfyingAssignment G₁ := newSatisfyingAssignment
      -- TODO: rewrite inputs_secondary properly in further PRs
      let inputsSecondary :=
        NovaAugmentedCircuitInputs.mk 
          pp.R1CSShapePrimary.digest 
          (0 : G₁)
          z₀Primary
          .none
          .none
          (.some uPrimary)
          .none
      let circuitSecondary : NovaAugmentedCircuit G₁ := 
        NovaAugmentedCircuit.mk pp.AugmentedCircuitParamsSecondary (.some inputsSecondary) cPrimary
      let (uSecondary, wSecondary) ← wit'.R1CSInstanceAndWitness pp.R1CSShapeSecondary pp.R1CSGensSecondary
      let rwPrimary := fromR1CSWitness pp.R1CSShapePrimary wPrimary
      let ruPrimary := fromR1CSInstance pp.R1CSGensPrimary uPrimary
      let rwSecondary := defaultRelaxedR1CSWitness pp.R1CSShapeSecondary
      let ruSecondary := defaultRelaxedR1CSInstance pp.R1CSShapeSecondary
      let zᵢPrimary := cPrimary.output z₀Primary
      let zᵢSecondary := cSecondary.output z₀Secondary
      if z₀Primary.size != pp.FArityPrimary.val || z₀Secondary.size != pp.FAritySecondary.val
      then .error Error.InvalidStepOutputLength
      else
      .ok $ RecursiveSnark.mk
                rwPrimary 
                ruPrimary 
                wPrimary 
                uPrimary 
                rwSecondary 
                ruSecondary 
                wSecondary
                uSecondary
                1
                zᵢPrimary
                zᵢSecondary
      | .some rSNARK => do
      let (luPrimary, lwPrimary) ← wit.R1CSInstanceAndWitness pp.R1CSShapePrimary pp.R1CSGensPrimary
      let zᵢPrimary := cPrimary.output z₀Primary
      let zᵢSecondary := cSecondary.output z₀Secondary
      let (luSecondary, lwSecondary) ← 
        wit'.R1CSInstanceAndWitness
          pp.R1CSShapeSecondary
          pp.R1CSGensSecondary
      let (_, ruSecondary, rwSecondary) ← 
        NIFS.prove
          pp.R1CSGensSecondary
          pp.R1CSShapeSecondary
          rSNARK.ruSecondary
          rSNARK.rwSecondary
          rSNARK.luSecondary
          rSNARK.lwSecondary
      
      let (_, ruPrimary, rwPrimary) ←
        NIFS.prove
          pp.R1CSGensPrimary
          pp.R1CSShapePrimary
          rSNARK.ruPrimary
          rSNARK.rwPrimary
          luPrimary
          lwPrimary
      .ok $ RecursiveSnark.mk 
                 rwPrimary
                 ruPrimary
                 lwPrimary
                 luPrimary
                 rwSecondary
                 ruSecondary
                 lwSecondary
                 luSecondary
                 (rSNARK.i + 1)
                 zᵢPrimary
                 zᵢSecondary

/-
-- Verify the correctness of the `RecursiveSNARK`
def verify
  (self : RecursiveSnark G₁ G₂) (pp : PublicParams G₁ G₂)
  (numSteps : USize) (z₀Primary : Array G₁) 
  (z₀Secondary : Array G₂) : Except Error (Array G₁ × Array G₂)
  :=
  let bad_cases :=
  -- number of steps cannot be zero
    numSteps == 0 ||
  -- check if the provided proof has executed numSteps
    self.i != numSteps ||
  -- check if the (relaxed) R1CS instances have two public outputs
    self.luPrimary.X.size != 2 ||
    self.luSecondary.X.size != 2 || 
    self.ruPrimary.X.size != 2 ||
    self.ruSecondary.X.size != 2
  if bad_cases 
  then .error ProofVerifyError
  else do
  -- check if the output hashes in R1CS instances point to the right running instances
  -- TODO
    let mut hasher :=
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.FArityPrimary
    let mut hasher2 :=
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.FAritySecondary
    for e in z₀Primary do
      sorry
    for e in self.ziPrimary do
      sorry
  -- check the satisfiability of the provided instances
    isSatRelaxed
      pp.R1CSShapePrimary
      pp.R1CSGensPrimary
      self.ruPrimary
      self.rwPrimary
    isSat
      pp.R1CSShapePrimary
      pp.R1CSGensPrimary
      self.luPrimary
      self.lwPrimary
    isSatRelaxed
      pp.R1CSShapeSecondary
      pp.R1CSGensSecondary
      self.ruSecondary
      self.rwSecondary
    isSat
      pp.R1CSShapeSecondary
      pp.R1CSGensSecondary
      self.luSecondary
      self.lwSecondary
  
    pure (self.ziPrimary, self.ziSecondary)
-/