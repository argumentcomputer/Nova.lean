import Nova.SNARK.Commitments
import Nova.SNARK.NIFS
import Nova.SNARK.R1CS

namespace CompressedSnark

-- A SNARK that proves the knowledge of a valid `RecursiveSNARK`
structure CompressedSnark 
  (G₁ : Type _) (G₂ : Type _) 
  (S₁ : Type _) (S₂ : Type _) where
  r_U_primary : RelaxedR1CSInstance G₁
  l_u_primary : R1CSInstance G₁
  nifs_primary : NIFS G₁
  f_W_snark_primary : S₁

  r_U_secondary : RelaxedR1CSInstance G₂
  l_u_secondary : R1CSInstance G₂
  nifs_secondary : NIFS G₂
  f_W_snark_secondary : S₂

  zn_primary : Array G₁
  zn_secondary : Array G₂

end CompressedSnark