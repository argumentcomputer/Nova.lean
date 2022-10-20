import Nova.SNARK.R1CS

open R1CS

namespace RecursiveSnark

structure RecursiveSnark 
  (G₁ : Type _) (G₂ : Type _)
  (C₁ : Type _) (C₂ : Type _) where
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
  _p_c1 : C₁
  _p_c2 : C₂

end RecursiveSnark