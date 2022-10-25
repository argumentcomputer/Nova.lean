import Nova.SNARK.Commitments

open Commitments

namespace R1CS

structure R1CSGens (G : Type _) where
  gens : CommitGens G

structure RelaxedR1CSWitness (G : Type _) where
  W : Commitment G
  E : Commitment G

structure R1CSWitness (G : Type _) where
  W : Commitment G

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

-- Returns the number of constraints in the primary and secondary circuits
def num_constraints (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : USize × USize :=
  (shape₁.num_cons, shape₂.num_cons)

-- Returns the number of variables in the primary and secondary circuits
def num_variables (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : USize × USize :=
  (shape₁.num_vars, shape₂.num_vars)

-- `NovaShape` provides methods for acquiring `R1CSShape` and `R1CSGens` from implementers.
class NovaShape (G : Type _) where
-- Return an appropriate `R1CSShape` struct
  r1cs_shape : R1CSShape G
-- Return an appropriate `R1CSGens` struct
  r1cs_gens : R1CSGens G

end R1CS