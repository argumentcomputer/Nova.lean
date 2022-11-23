import Nova.SNARK.Commitments
import Nova.SNARK.Errors
import Nova.SNARK.ShapeCS

import YatimaStdLib.Array
import YatimaStdLib.Monad
import YatimaStdLib.USize

open Error
open Except

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

structure R1CSShapeSerialised where
  numCons : USize
  numVars : USize
  numIO : USize
  A : Array (USize × USize × Array U8)
  B : Array (USize × USize × Array U8)
  C : Array (USize × USize × Array U8)

def compute_digest
  (numCons : USize) (num_vars : USize) (num_io : USize)
  (A : Array (USize × USize × G))
  (B : Array (USize × USize × G))
  (C : Array (USize × USize × G)) : G := sorry

-- Create an object of type `R1CSShape` from the explicitly specified R1CS matrices
open Monad in
def R1CSShape.new [OfNat G (nat_lit 0)]
  (numCons : USize) (numVars : USize) (numIO : USize)
  (A : Array (USize × USize × G))
  (B : Array (USize × USize × G))
  (C : Array (USize × USize × G)) : Except Error (R1CSShape G) := do
  let isValid (M : Array (USize × USize × G)) : Except Error PUnit :=
    let sequenceUnit (i : Nat) : Except Error Unit :=
      let (row, col, _) :=
        Array.getD M i (0,0,0)
      if row >= numCons || col > numIO + numVars
      then .error InvalidIndex
      else .ok ()
    let res' := Array.map sequenceUnit (Array.iota M.size)
    if isError (Array.foldr seqComp (.ok ()) res') 
    then .error InvalidIndex else .ok ()
  let resA := isValid A
  let resB := isValid B
  let resC := isValid C
  if isError resA || isError resB || isError resC
  then .error InvalidIndex
  if numIO % 2 != 0 then .error OddInputLength
  let digest := compute_digest numCons numVars numIO A B C
  let shape := R1CSShape.mk numCons numVars numIO A B C digest
  .ok shape

-- Pads the R1CSShape so that the number of variables is a power of two
-- Renumbers variables to accomodate padded variables
def R1CSShape.pad (self : R1CSShape G) : R1CSShape G :=
  match (self.numVars.nextPowerOfTwo == self.numVars, 
        self.numCons.nextPowerOfTwo == self.numCons) with
    -- check if the provided R1CSShape is already as required
    | (true, true) => self

    -- check if the number of variables are as expected, then
    -- we simply set the number of constraints to the next power of two
    | (true, _) =>
      let numConsPadded := self.numCons.nextPowerOfTwo
      let digest :=
        compute_digest
          numConsPadded
          self.numVars
          self.numIO
          self.A
          self.B
          self.C
      R1CSShape.mk numConsPadded self.numVars self.numVars self.A self.B self.C digest

    -- otherwise, we need to pad the number of variables
    -- and renumber variable accesses
    | (_,_) =>
      let numVarsPadded := self.numVars.nextPowerOfTwo
      let numConsPadded := self.numCons.nextPowerOfTwo
      let applyPad (M : Array (USize × USize × G)) : Array (USize × USize × G) :=
        Array.map
          (fun (r, c, v) => 
            if c >= self.numVars 
            then (r, c + numVarsPadded - self.numVars, v)
            else (r, c, v))
          M
      let A_padded := applyPad self.A
      let B_padded := applyPad self.B
      let C_padded := applyPad self.C
      let digest :=
        compute_digest
          numConsPadded
          numVarsPadded
          self.numIO
          self.A
          self.B
          self.C
      R1CSShape.mk
        numConsPadded
        numVarsPadded
        self.numIO
        A_padded
        B_padded
        C_padded
        digest

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
def fromR1CSInstance [OfNat G (nat_lit 1)] (gen : R1CSGens G)
                       (inst : R1CSInstance G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk inst.commW (Commitment.mk gen.gens._p) inst.X (1 : G)

variable [OfNat G (nat_lit 0)] [Coe USize G]

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
  R1CSShape : ShapeCS G → R1CSShape G
-- Return an appropriate `R1CSGens` struct
  R1CSGens : ShapeCS G → R1CSGens G

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
def R1CSGens.commitT [Mul G] [Add G] [Sub G] [OfNat G (nat_lit 1)] 
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

-- Checks if the Relaxed R1CS instance is satisfiable given a witness and its shape
def isSatRelaxed [Mul G] [Add G] [BEq G] [HPow G G G]
  (self : R1CSShape G) (gen : R1CSGens G)
  (U : RelaxedR1CSInstance G) (W : RelaxedR1CSWitness G) : Except Error Unit := do
  let z := Array.join #[W.W, #[U.u], U.X]
  let (Az, Bz, Cz) ← multiplyVec self z
  if
    W.W.size != self.numVars.val ||
    W.E.size != self.numCons.val ||
    U.X.size != self.numIO.val
  then
        -- verify if Az * Bz = u*Cz + E
    let res_eq : Bool :=
      if
        Az.size != self.numCons.val ||
        Bz.size != self.numCons.val ||
        Cz.size != self.numCons.val
      then false
      else
      let res : USize := 
        Array.foldr 
          (. + .)
          0 $
          Array.map 
            (fun i => 
              if Array.getD Az i 0 * Array.getD Bz i 0 == 
                  U.u * Array.getD Cz i 0 + Array.getD W.E i 0 
              then 0 else 1) 
            (Array.iota self.numCons.val)
      res == 0
      let (commW, commE) := (commit W.W gen.gens, commit W.E gen.gens)
    let res_comm : Bool := U.commW == commW && U.commE == commE
    if res_eq && res_comm then .ok () else .error UnSat
    else .error InvalidInitialInputLength


-- Checks if the R1CS instance is satisfiable given a witness and its shape
def isSat [Mul G] [Add G] [OfNat G (nat_lit 1)] [OfNat G (nat_lit 0)] [BEq G] [HPow G G G]
  (self : R1CSShape G) (gen : R1CSGens G)
  (U : R1CSInstance G) (W : R1CSWitness G) : Except Error Unit := do
  let z := Array.join #[W.W, #[1], U.X]
  let (Az, Bz, Cz) ← multiplyVec self z
  if
    W.W.size != self.numVars.val ||
    U.X.size != self.numIO.val
  then .error InvalidInitialInputLength
  else
    -- verify if Az * Bz = u*Cz
  let resEq : Bool :=
      if
        Az.size != self.numCons.val ||
        Bz.size != self.numCons.val ||
        Cz.size != self.numCons.val
      then false
      else
      let res := Array.foldr (. + .) 0 $
        Array.map
          (fun i => 
            if Array.getD Az i 0 * Array.getD Bz i 0 == Array.getD Cz i 0 
            then 0 else 1) $
          Array.iota self.numCons.val
      res == 0
  let resComm : Bool := U.commW == commit W.W gen.gens
  if resEq && resComm then .ok () else .error UnSat

-- `NovaWitness` provide a method for acquiring an `R1CSInstance` and `R1CSWitness` from implementers.
class NovaWitness (G : Type _) where
  R1CSInstanceAndWitness 
    : R1CSShape G 
    → R1CSGens G 
    → Except Error (R1CSInstance G × R1CSWitness G)