import Nova.SNARK.Commitments

open Commitments

namespace R1CS

structure RelaxedR1CSInstance (G : Type _) where
  comm_W : Commitment G
  comm_E : Commitment G
  X : Array G
  u : G

structure R1CSInstance (G : Type _) where
  comm_W : Commitment G
  X : Array G

end R1CS