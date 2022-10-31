import Nova.SNARK.Commitments
import YatimaStdLib.Either

structure R1CSGens (G : Type _) where
  gens : CommitGens G

structure RelaxedR1CSWitness (G : Type _) where
  W : Array G
  E : Array G

structure R1CSWitness (G : Type _) where
  W : Array G

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

-- Initialises a new RelaxedR1CSInstance from an R1CSInstance
def from_r1cs_instance [OfNat G 1] (gen : R1CSGens G)
                       (inst : R1CSInstance G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk inst.comm_W (Commitment.mk gen.gens._p) inst.X (1 : G)

variable [OfNat G 0] [Coe USize G]

-- Initialises a new RelaxedR1CSWitness from an R1CSWitness
def from_r1cs_witness (S : R1CSShape G) (witness : R1CSWitness G)  : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk witness.W #[0, S.num_cons]

-- Produces a default RelaxedR1CSWitness given an R1CSShape
def default_relaxed_r1cs_witness (s : R1CSShape G) : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk #[0, s.num_vars] #[0, s.num_cons]

-- Produces a default RelaxedR1CSInstance given R1CSGens and R1CSShape
def default_relaxed_r1cs_instance (s : R1CSShape G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk (Commitment.mk 0) (Commitment.mk 0) #[0, s.num_io] 0

-- `NovaShape` provides methods for acquiring `R1CSShape` and `R1CSGens` from implementers.
class NovaShape (G : Type _) where
-- Return an appropriate `R1CSShape` struct
  r1cs_shape : R1CSShape G
-- Return an appropriate `R1CSGens` struct
  r1cs_gens : R1CSGens G

-- Folds an incoming R1CSWitness into the current one
def R1CSWitness.fold (w₂ : R1CSWitness G) (t : Array G) (r : G) : Either Error (RelaxedR1CSWitness G)
  := sorry
-- TODO: complete it

def R1CSInstance.fold (u₂ : R1CSInstance G) (comm_T : Commitment G) (r : G) :  Either Error (RelaxedR1CSInstance G) :=
  sorry
-- TODO: complete it

-- A method to compute a commitment to the cross-term `T` given a
-- Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
def R1CSGens.commit_T (gen : R1CSGens G) (u₁ : RelaxedR1CSInstance G)
                      (w₁ : RelaxedR1CSWitness G) (u₂ : R1CSInstance G) (w₂ : R1CSWitness G) :
                      Either Error (Array G × Commitment G) := sorry
-- TODO: complete it

-- `NovaWitness` provide a method for acquiring an `R1CSInstance` and `R1CSWitness` from implementers.
class NovaWitness (G : Type _) where
  r1cs_instance_and_witness 
    : R1CSShape G 
    → R1CSGens G 
    → Either Error (R1CSInstance G × R1CSWitness G)