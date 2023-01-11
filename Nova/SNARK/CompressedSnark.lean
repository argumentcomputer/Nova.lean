import Nova.SNARK.Commitments
import Nova.SNARK.NIFS
import Nova.SNARK.PublicParams
import Nova.SNARK.RecursiveSnark
import Nova.SNARK.R1CS
import Nova.SNARK.Typeclasses

/--
A SNARK that proves the knowledge of a valid `RecursiveSNARK`
-/
structure CompressedSnark 
  (G₁ : Type _) (G₂ : Type _) where
  ruPrimary : RelaxedR1CSInstance G₁
  luPrimary : R1CSInstance G₁
  NIFSprimary : NIFS G₁
  fwSnarkPrimary : G₁

  ruSecondary : RelaxedR1CSInstance G₂
  luSecondary : R1CSInstance G₂
  NIFSSecondary : NIFS G₂
  fwSnarkSecondary : G₂

  znPrimary : Array G₁
  znSecondary : Array G₂

variable {G₁ G₂ : Type _} [Ring G₁] [Ring G₂]
variable [Inhabited G₁] [Ring G₁] [BEq G₁] [ROCircuitClass G₁] [RelaxedR1CSSNARK G₁]
variable [Inhabited G₂] [Ring G₂] [BEq G₂] [ROCircuitClass G₂] [RelaxedR1CSSNARK G₂]

/--
Create a new `CompressedSNARK`
-/
def CompressedSnark.prove
  (pp : PublicParams G₁ G₂)
  (recursiveSnark : RecursiveSnark G₁ G₂) : Except Error (CompressedSnark G₁ G₂) := do
  -- fold the primary circuit's instance
  let (nifsPrimary, fuPrimary, fwPrimary) ←
    NIFS.prove
      pp.R1CSGensPrimary
      pp.R1CSShapePrimary
      recursiveSnark.ruPrimary
      recursiveSnark.rwPrimary
      recursiveSnark.luPrimary
      recursiveSnark.lwPrimary
  
  -- fold the secondary circuit's instance
  let (nifsSecondary, fuSecondary, fwSecondary) ←
    NIFS.prove
      pp.R1CSGensSecondary
      pp.R1CSShapeSecondary
      recursiveSnark.ruSecondary
      recursiveSnark.rwSecondary
      recursiveSnark.luSecondary
      recursiveSnark.lwSecondary

  -- produce a prover key for the SNARK
  let pkPrimary :=
    ProverKey.proverKey pp.R1CSGensPrimary pp.R1CSShapePaddedPrimary
  let pkSecondary :=
    ProverKey.proverKey pp.R1CSGensSecondary pp.R1CSShapePaddedSecondary

  -- create SNARKs proving the knowledge of fwPrimary and fwSecondary
  let fwSnarkPrimary ←
    RelaxedR1CSSNARK.prove
      pkPrimary
      fuPrimary
      (fwPrimary.pad pp.R1CSShapePaddedPrimary)
  let fwSnarkSecondary ←
    RelaxedR1CSSNARK.prove
      pkSecondary
      fuSecondary
      (fwSecondary.pad pp.R1CSShapePaddedSecondary)

  pure $ CompressedSnark.mk
           recursiveSnark.ruPrimary
           recursiveSnark.luPrimary
           nifsPrimary
           fwSnarkPrimary
           recursiveSnark.ruSecondary
           recursiveSnark.luSecondary
           nifsSecondary
           fwSnarkSecondary
           recursiveSnark.ziPrimary
           recursiveSnark.ziSecondary