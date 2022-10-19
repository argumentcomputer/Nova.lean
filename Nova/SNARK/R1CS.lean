import Nova.SNARK.Commitments

open Commitments

namespace R1CS

variable (PreprocessedGroupElement : Type _ → Type _)

structure R1CSGens (G : Type _) where
  gens : CommitGens PreprocessedGroupElement G

structure RelaxedR1CSInstance (G : Type _) where
  comm_W : Commitment G
  comm_E : Commitment G
  X : Array G
  u : G

structure R1CSInstance (G : Type _) where
  comm_W : Commitment G
  X : Array G

structure R1CSShape (G : Type _) where
  num_cons : USize
  num_vars : USize
  num_io : USize
  A : Array G
  B : Array G
  C : Array G
  digest : G

end R1CS