import Nova.SNARK.Commitments
import Nova.SNARK.Errors
import YatimaStdLib.Array

open Error

import YatimaStdLib.Array

-- Public parameters for a given R1CS
structure R1CSGens (G : Type _) where
  gens : CommitGens G

-- A type that holds the shape of the R1CS matrices
structure R1CSShape (G : Type _) where
  numCons : USize
  numVars : USize
  numIO : USize
  A : Array (USize × USize × G)
  B : Array (USize × USize × G)
  C : Array (USize × USize × G)
  digest : G
  deriving BEq

-- A type that holds a witness for a given R1CS instance
structure R1CSWitness (G : Type _) where
  W : Array G
  deriving BEq

-- A type that holds an R1CS instance
structure R1CSInstance (G : Type _) where
  commW : Commitment G
  X : Array G
  deriving BEq

-- A type that holds a witness for a given Relaxed R1CS instance
structure RelaxedR1CSWitness (G : Type _) where
  W : Array G
  E : Array G
  deriving BEq

-- A type that holds a Relaxed R1CS instance
structure RelaxedR1CSInstance (G : Type _) where
  commW : Commitment G
  commE : Commitment G
  X : Array G
  u : G
  deriving BEq

-- Returns the number of constraints in the primary and secondary circuits
def numConstraints (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : USize × USize :=
  (shape₁.numCons, shape₂.numCons)

-- Returns the number of variables in the primary and secondary circuits
def numVariables (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : USize × USize :=
  (shape₁.numVars, shape₂.numVars)

-- Initialises a new RelaxedR1CSInstance from an R1CSInstance
def fromR1CSInstance [OfNat G 1] (gen : R1CSGens G)
                       (inst : R1CSInstance G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk inst.commW (Commitment.mk gen.gens._p) inst.X (1 : G)

variable [OfNat G 0] [Coe USize G]

-- Initialises a new RelaxedR1CSWitness from an R1CSWitness
def fromR1CSWitness (S : R1CSShape G) (witness : R1CSWitness G)  : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk witness.W #[0, S.numCons]

-- Produces a default RelaxedR1CSWitness given an R1CSShape
def defaultRelaxedR1CSWitness (s : R1CSShape G) : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk #[0, s.numVars] #[0, s.numCons]

-- Produces a default RelaxedR1CSInstance given R1CSGens and R1CSShape
def defaultRelaxedR1CSInstance (s : R1CSShape G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk (Commitment.mk 0) (Commitment.mk 0) #[0, s.numIO] 0

-- `NovaShape` provides methods for acquiring `R1CSShape` and `R1CSGens` from implementers.
class NovaShape (G : Type _) where
-- Return an appropriate `R1CSShape` struct
  R1CSShape : R1CSShape G
-- Return an appropriate `R1CSGens` struct
  R1CSGens : R1CSGens G

-- Folds an incoming R1CSWitness into the current one
def R1CSWitness.fold [Mul G] [Add G] 
    (w₁ : RelaxedR1CSWitness G) 
    (w₂ : R1CSWitness G) 
    (t : Array G) (r : G) : Except Error (RelaxedR1CSWitness G) :=
    let (w₁, e₁) := (w₁.W, w₁.E)
    let w₂ := w₂.W
    if w₁.size != w₂.size then (.error InvalidWitnessLength) 
    else
      let w := Array.map (fun (a, b) => a + b * r) (Array.zip w₁ w₂)
      let e := Array.map (fun (a, b) => a + b * r) (Array.zip e₁ t)
      .ok $ RelaxedR1CSWitness.mk w e

-- Folds an incoming RelaxedR1CSInstance into the current one
def R1CSInstance.fold {G : Type _} [Mul G] [Add G]
  (u₁ : RelaxedR1CSInstance G) 
  (u₂ : R1CSInstance G) 
  (commT : Commitment G) (r : G) : Except Error (RelaxedR1CSInstance G) :=
  let (x₁, u', commW₁, commE₁) := (u₁.X, u₁.u, u₁.commW, u₁.commE)
  let (x₂, commW₂) := (u₂.X, u₂.commW)
  let commW := (commW₁.comm : G) + ((commW₂.comm : G) * r)
  let commE := commE₁.comm + commT.comm * r
  let u := u' + r
  let x := Array.map (fun (a,b) => a + b * r) (Array.zip x₁ x₂)
  let result :=
    RelaxedR1CSInstance.mk 
      (Commitment.mk commW) 
      (Commitment.mk commE)
      x
      u
  .ok result

def multiplyVec (self : R1CSShape G) (z : Array G) [Mul G] [Add G] : Except Error (Array G × Array G × Array G) :=
  if z.size != self.numIO.val.val + self.numVars.val.val + 1 
  then .error Error.InvalidWitnessLength
  else
    let sparseMatrixVecProduct (M : Array (USize × USize × G)) (numRows : USize) (z : Array G) : Array G :=
      let vals := Array.map 
        (fun i => 
          let (row, col, val) := Array.getD M i (0, 0, 0)
          (row, val * Array.getD z col.val 0)
        ) 
        (Array.iota M.size)
      Array.foldr 
        (fun (r,v) mz => Array.setD mz r.val (v + Array.getD mz r.val 0)) 
        #[0, numRows] 
        vals 
    let Az := sparseMatrixVecProduct self.A self.numCons z
    let Bz := sparseMatrixVecProduct self.B self.numCons z
    let Cz := sparseMatrixVecProduct self.C self.numCons z
    .ok (Az, Bz, Cz)

-- A method to compute a commitment to the cross-term `T` given a
-- Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
def R1CSGens.commitT [Mul G] [Add G] [Sub G] [OfNat G 1] 
  (self : R1CSShape G) (gen : R1CSGens G)
  (u₁ : RelaxedR1CSInstance G) 
  (w₁ : RelaxedR1CSWitness G)
  (u₂ : R1CSInstance G) 
  (w₂ : R1CSWitness G) : Except Error (Array G × Commitment G) := do
  let (az₁, bz₁, cz₁) ← multiplyVec self (Array.join #[w₁.W, #[u₁.u], u₁.X])
  let (az₂, bz₂, cz₂) ← multiplyVec self (Array.join #[w₂.W, #[1], u₂.X])
  let az₁bz₂ :=
    Array.map 
      (fun i => Array.getD az₁ i 0 *  Array.getD bz₂ i 0) 
      (Array.iota az₁.size)
  let az₂bz₁ :=
    Array.map
      (fun i => Array.getD az₂ i 0 *  Array.getD bz₁ i 0) 
      (Array.iota az₂.size)
  let u₁cz₂ :=
    Array.map
      (fun i => u₁.u * Array.getD cz₂ i 0)
      (Array.iota cz₂.size)
  let u₂cz₁ :=
    Array.map
      (fun i => Array.getD cz₁ i 0)
      (Array.iota cz₁.size)
  let t :=
    Array.map (fun (a,b,c,d) => a + b - c - d)
    (Array.zip az₂bz₁
      (Array.zip az₁bz₂
        (Array.zip u₁cz₂ u₂cz₁)))
  let commT := Commitment.mk $
    Array.foldr (. + .) 0 (Array.map (fun (a, b) => a * b) (Array.zip t gen.gens.gens))
  .ok (t, commT)
  -- TODO: complete this sorry in a further PR

-- `NovaWitness` provide a method for acquiring an `R1CSInstance` and `R1CSWitness` from implementers.
class NovaWitness (G : Type _) where
  R1CSInstanceAndWitness 
    : R1CSShape G 
    → R1CSGens G 
    → Except Error (R1CSInstance G × R1CSWitness G)