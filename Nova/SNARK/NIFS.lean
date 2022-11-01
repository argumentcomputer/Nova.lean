import Nova.SNARK.Constraints
import Nova.SNARK.Commitments
import Nova.SNARK.R1CS
import Nova.SNARK.Typeclasses

structure NIFS (G : Type _) where
  commT : CompressedCommitment G
  _p : G

-- Takes as input a Relaxed R1CS instance-witness tuple `(U1, W1)` and
-- an R1CS instance-witness tuple `(U2, W2)` with the same structure `shape`
-- and defined with respect to the same `gens`, and outputs
-- a folded Relaxed R1CS instance-witness tuple `(U, W)` of the same shape `shape`,
-- with the guarantee that the folded witness `W` satisfies the folded instance `U`
-- if and only if `W1` satisfies `U1` and `W2` satisfies `U2`.
def NIFS.prove [Inhabited G] [ROCircuitClass G] (gen : R1CSGens G) (s : R1CSShape G) 
               (u₁ : RelaxedR1CSInstance G) (w₁ : RelaxedR1CSWitness G)
               (u₂ : R1CSInstance G) (w₂ : R1CSWitness G) : 
               Either NovaError (NIFS G × RelaxedR1CSInstance G × RelaxedR1CSWitness G) := do
  let (t, comm_T) ← R1CSGens.commit_T gen u₁ w₁ u₂ w₂
  let r : G := ROCircuitClass.squeeze NUM_CHALLENGE_BITS
  let u ← R1CSInstance.fold u₁ u₂ comm_T r
  let w ← R1CSWitness.fold w₁ w₂ t r
  .right (NIFS.mk (compress comm_T) default, u, w)