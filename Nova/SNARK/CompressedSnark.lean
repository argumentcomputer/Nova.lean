import Nova.SNARK.Commitments
import Nova.SNARK.NIFS
import Nova.SNARK.R1CS

namespace CompressedSnark

/--
A SNARK that proves the knowledge of a valid `RecursiveSNARK`
-/
structure CompressedSnark 
  (G₁ : Type _) (G₂ : Type _) 
  (S₁ : Type _) (S₂ : Type _) where
  ruPrimary : RelaxedR1CSInstance G₁
  luPrimary : R1CSInstance G₁
  NIFSprimary : NIFS G₁
  fwSnarkPrimary : S₁

  ruSecondary : RelaxedR1CSInstance G₂
  luSecondary : R1CSInstance G₂
  NIFSSecondary : NIFS G₂
  fwSnarkSecondary : S₂

  znPrimary : Array G₁
  znSecondary : Array G₂

end CompressedSnark