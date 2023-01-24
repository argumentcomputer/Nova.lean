import Nova.SNARK.Commitments
import Nova.SNARK.Errors
import Nova.SNARK.ShapeCS

import YatimaStdLib.Array
import YatimaStdLib.Monad
import YatimaStdLib.Nat
import YatimaStdLib.Ring
import YatimaStdLib.RBMap
import YatimaStdLib.SparseMatrix

open Error
open Except
open SparseMatrix

/-- Public parameters for a given R1CS
-/
structure R1CSGens (G : Type _) where
  gens : CommitGens G

/--
A type that holds the shape of the R1CS matrices
-/
structure R1CSShape (G : Type _) where
  numCons : Nat
  numVars : Nat
  numIO : Nat
  A : SparseMatrix G
  B : SparseMatrix G
  C : SparseMatrix G
  digest : G

structure R1CSShapeSerialised where
  numCons : Nat
  numVars : Nat
  numIO : Nat
  A : SparseMatrix (Array UInt8)
  B : SparseMatrix (Array UInt8)
  C : SparseMatrix (Array UInt8)

open Coe in
def computeDigest [Inhabited G]
  (numCons : Nat) (numVars : Nat) (numIO : Nat)
  (A : SparseMatrix G)
  (B : SparseMatrix G)
  (C : SparseMatrix G) : G :=
  panic! "sorry mate, I need some serialisation, cheers"

open Monad in
/-- Create an object of type `R1CSShape` from the explicitly specified R1CS matrices
-/
def R1CSShape.new [Inhabited G]
  (numCons : Nat) (numVars : Nat) (numIO : Nat)
  (A : SparseMatrix G)
  (B : SparseMatrix G)
  (C : SparseMatrix G) : Except Error (R1CSShape G) := do
  let isValid (M : SparseMatrix G) : Except Error PUnit :=
    let (col,row) := M.dim
    if row >= numCons || col > numIO + numVars
    then .error InvalidIndex
    else .ok ()
  if isError (isValid A) || isError (isValid B) || isError (isValid C)
  then .error InvalidIndex
  if numIO % 2 != 0 then .error OddInputLength
  let digest := computeDigest numCons numVars numIO A B C
  let shape := R1CSShape.mk numCons numVars numIO A B C digest
  .ok shape

open Nat in
/-- Pads the R1CSShape so that the number of variables is a power of two.
Renumbers variables to accomodate padded variables
-/
def R1CSShape.pad (self : R1CSShape G) [Inhabited G] : R1CSShape G :=
  match (Nat.nextPowerOfTwo self.numVars == self.numVars, 
        Nat.nextPowerOfTwo self.numCons == self.numCons) with
    -- check if the provided R1CSShape is already as required
    | (true, true) => self

    -- check if the number of variables are as expected, then
    -- we simply set the number of constraints to the next power of two
    | (true, _) =>
      let numConsPadded := Nat.nextPowerOfTwo self.numCons
      let digest :=
        computeDigest
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
      let numVarsPadded := Nat.nextPowerOfTwo self.numVars
      let numConsPadded := Nat.nextPowerOfTwo self.numCons
      let applyPad (M : SparseMatrix G) : SparseMatrix G :=
        SparseMatrix.mk
          (Std.RBMap.mapKeys
            M.entries
            (fun (r, c) => 
              if c >= self.numVars 
              then (r, c + numVarsPadded - self.numVars)
              else (r, c))
            )
          M.rows
          M.cols
      let aPadded := applyPad self.A
      let bPadded := applyPad self.B
      let cPadded := applyPad self.C
      let digest :=
        computeDigest
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
        aPadded
        bPadded
        cPadded
        digest

-- A type that holds a witness for a given R1CS instance
structure R1CSWitness (G : Type _) where
  W : Array G
  deriving BEq

/-- A type that holds an R1CS instance
-/
structure R1CSInstance (G : Type _) where
  commW : Commitment G
  X : Array G
  deriving BEq

/-- A type that holds a witness for a given Relaxed R1CS instance
-/
structure RelaxedR1CSWitness (G : Type _) where
  W : Array G
  E : Array G
  deriving BEq

/--
Pads the provided witness to the correct length
-/
def RelaxedR1CSWitness.pad [Ring G]
  (self : RelaxedR1CSWitness G) (S : R1CSShape G) : RelaxedR1CSWitness G :=
  let W := self.W ++ #[(0 : G), (S.numVars : G) - (self.W.size : G)]
  let E := self.E ++ #[(0 : G), (S.numCons : G) - (self.E.size : G)]
  RelaxedR1CSWitness.mk W E

/-- A type that holds a Relaxed R1CS instance
-/
structure RelaxedR1CSInstance (G : Type _) where
  commW : Commitment G
  commE : Commitment G
  X : Array G
  u : G
  deriving BEq

/-- Returns the number of constraints in the primary and secondary circuits
-/
def numConstraints (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : Nat × Nat :=
  (shape₁.numCons, shape₂.numCons)

/-- Returns the number of variables in the primary and secondary circuits
-/
def numVariables (shape₁ : R1CSShape G₁) (shape₂ : R1CSShape G₂) : Nat × Nat :=
  (shape₁.numVars, shape₂.numVars)

variable {G : Type _} [Ring G]

/-- Initialises a new RelaxedR1CSInstance from an R1CSInstance
-/
def fromR1CSInstance (gen : R1CSGens G)
                       (inst : R1CSInstance G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk inst.commW (Commitment.mk gen.gens._p) inst.X 1

/-- Initialises a new RelaxedR1CSWitness from an `R1CSWitness`
-/
def fromR1CSWitness (S : R1CSShape G) (witness : R1CSWitness G)  : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk witness.W #[0, S.numCons]

/-- Produces a default RelaxedR1CSWitness given an `R1CSShape`
-/
def defaultRelaxedR1CSWitness (s : R1CSShape G) : RelaxedR1CSWitness G :=
  RelaxedR1CSWitness.mk #[0, s.numVars] #[0, s.numCons]

/-- Produces a default RelaxedR1CSInstance given `R1CSGens` and `R1CSShape`
-/
def defaultRelaxedR1CSInstance (s : R1CSShape G) : RelaxedR1CSInstance G :=
  RelaxedR1CSInstance.mk (Commitment.mk 0) (Commitment.mk 0) #[0, s.numIO] 0

/-- `NovaShape` provides methods for acquiring `R1CSShape` and `R1CSGens` from implementers.
-/
class NovaShape (G : Type _) where
-- Return an appropriate `R1CSShape` struct
  R1CSShape : ShapeCS G → R1CSShape G
-- Return an appropriate `R1CSGens` struct
  R1CSGens : ShapeCS G → R1CSGens G

/-- Folds an incoming R1CSWitness into the current one
-/
def R1CSWitness.fold 
    (w₁ : RelaxedR1CSWitness G) 
    (w₂ : R1CSWitness G) 
    (t : Array G) (r : G) : Except Error (RelaxedR1CSWitness G) :=
    let (w₁, e₁) := (w₁.W, w₁.E)
    let w₂ := w₂.W
    if w₁.size != w₂.size then .error InvalidWitnessLength
    else
      let w := Array.map (fun (a, b) => a + b * r) (Array.zip w₁ w₂)
      let e := Array.map (fun (a, b) => a + b * r) (Array.zip e₁ t)
      .ok $ RelaxedR1CSWitness.mk w e

/-- Folds an incoming RelaxedR1CSInstance into the current one
-/
def R1CSInstance.fold
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

def multiplyVec 
  (self : R1CSShape G) (z : SparseArray G) : Except Error (SparseArray G × SparseArray G × SparseArray G) :=
  if z.size != self.numIO + self.numVars + 1 
  then .error Error.InvalidWitnessLength
  else
    let Az := self.A * z
    let Bz := self.B * z
    let Cz := self.C * z
    .ok (Az, Bz, Cz)

-- A method to compute a commitment to the cross-term `T` given a
-- Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
def R1CSGens.commitT
  (self : R1CSShape G) (gen : R1CSGens G)
  (u₁ : RelaxedR1CSInstance G) 
  (w₁ : RelaxedR1CSWitness G)
  (u₂ : R1CSInstance G) 
  (w₂ : R1CSWitness G) : Except Error (Array G × Commitment G) := do
  let (az₁, bz₁, cz₁) ← multiplyVec self $ Array.toSparse (Array.join #[w₁.W, #[u₁.u], u₁.X])
  let (az₂, bz₂, cz₂) ← multiplyVec self $ Array.toSparse (Array.join #[w₂.W, #[1], u₂.X])
  let az₁bz₂ :=
    Array.map 
      (fun i => Std.RBMap.findD az₁ i 0 * Std.RBMap.findD bz₂ i 0) 
      (Array.iota az₁.size)
  let az₂bz₁ :=
    Array.map
      (fun i => Std.RBMap.findD az₂ i 0 *  Std.RBMap.findD bz₁ i 0) 
      (Array.iota az₂.size)
  let u₁cz₂ :=
    Array.map
      (fun i => u₁.u * Std.RBMap.findD cz₂ i 0)
      (Array.iota cz₂.size)
  let u₂cz₁ :=
    Array.map
      (fun i => Std.RBMap.findD cz₁ i 0)
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
def isSatRelaxed [HPow G G G]
  (self : R1CSShape G) (gen : R1CSGens G)
  (U : RelaxedR1CSInstance G) (W : RelaxedR1CSWitness G) : Except Error Unit := do
  let z := Array.toSparse $ Array.join #[W.W, #[U.u], U.X]
  let (Az, Bz, Cz) ← multiplyVec self z
  if
    W.W.size != self.numVars ||
    W.E.size != self.numCons ||
    U.X.size != self.numIO
  then
        -- verify if Az * Bz = u*Cz + E
    let res_eq : Bool :=
      if
        Az.size != self.numCons ||
        Bz.size != self.numCons ||
        Cz.size != self.numCons
      then false
      else
      let res : Nat := 
        Array.foldr 
          (. + .)
          0 $
          Array.map 
            (fun i => 
              if Std.RBMap.findD Az i 0 * Std.RBMap.findD Bz i 0 == 
                  U.u * Std.RBMap.findD Cz i 0 + Array.getD W.E i 0 
              then 0 else 1) 
            (Array.iota self.numCons)
      res == 0
      let (commW, commE) := (commit W.W gen.gens, commit W.E gen.gens)
    let res_comm : Bool := U.commW == commW && U.commE == commE
    if res_eq && res_comm then .ok () else .error UnSat
    else .error InvalidInitialInputLength


/-- Checks if the R1CS instance is satisfiable given a witness and its shape
-/
def isSat [HPow G G G]
  (self : R1CSShape G) (gen : R1CSGens G)
  (U : R1CSInstance G) (W : R1CSWitness G) : Except Error Unit := do
  let z := Array.toSparse $ Array.join #[W.W, #[1], U.X]
  let (Az, Bz, Cz) ← multiplyVec self z
  if
    W.W.size != self.numVars ||
    U.X.size != self.numIO
  then .error InvalidInitialInputLength
  else
    -- verify if Az * Bz = u*Cz
  let resEq : Bool :=
      if
        Az.size != self.numCons ||
        Bz.size != self.numCons ||
        Cz.size != self.numCons
      then false
      else
      let res := Array.foldr (. + .) 0 $
        Array.map
          (fun i => 
            if Std.RBMap.findD Az i 0 * Std.RBMap.findD Bz i 0 == Std.RBMap.findD Cz i 0 
            then 0 else 1) $
          Array.iota self.numCons
      res == 0
  let resComm : Bool := U.commW == commit W.W gen.gens
  if resEq && resComm then .ok () else .error UnSat

/-- `NovaWitness` provide a method for acquiring an `R1CSInstance` and `R1CSWitness` from implementers.
-/
class NovaWitness (G : Type _) where
  R1CSInstanceAndWitness 
    : R1CSShape G 
    → R1CSGens G 
    → Except Error (R1CSInstance G × R1CSWitness G)