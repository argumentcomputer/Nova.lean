import Nova.SNARK.Constraints
import Nova.SNARK.Commitments
import Nova.SNARK.R1CS
import Nova.SNARK.Typeclasses

-- A SNARK that holds the proof of a step of an incremental computation
structure NIFS (G : Type _) where
  commT : CompressedCommitment G
  _p : G

-- Takes as input a Relaxed R1CS instance-witness tuple `(U1, W1)` and
-- an R1CS instance-witness tuple `(U2, W2)` with the same structure `shape`
-- and defined with respect to the same `gens`, and outputs
-- a folded Relaxed R1CS instance-witness tuple `(U, W)` of the same shape `shape`,
-- with the guarantee that the folded witness `W` satisfies the folded instance `U`
-- if and only if `W1` satisfies `U1` and `W2` satisfies `U2`.
def NIFS.prove [Inhabited G] [Mul G] [Add G] [OfNat G 0] [OfNat G 1] [Coe USize G] [ROCircuitClass G] [Sub G] 
               (gen : R1CSGens G) (s : R1CSShape G) 
               (u₁ : RelaxedR1CSInstance G) (w₁ : RelaxedR1CSWitness G)
               (u₂ : R1CSInstance G) (w₂ : R1CSWitness G) : 
               Except Error (NIFS G × RelaxedR1CSInstance G × RelaxedR1CSWitness G) := do
  let (t, commT) ← R1CSGens.commitT s gen u₁ w₁ u₂ w₂
  let r : G := ROCircuitClass.squeeze NUM_CHALLENGE_BITS
  let u ← R1CSInstance.fold u₁ u₂ commT r
  let w ← R1CSWitness.fold w₁ w₂ t r
  .ok (NIFS.mk (compress commT) default, u, w)