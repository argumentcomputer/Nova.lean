import Nova.SNARK.Commitments
import Nova.SNARK.R1CS

structure NIFS (G : Type _) where
  commT : CompressedCommitment G
  _p : G

-- Takes as input a Relaxed R1CS instance-witness tuple `(U1, W1)` and
-- an R1CS instance-witness tuple `(U2, W2)` with the same structure `shape`
-- and defined with respect to the same `gens`, and outputs
-- a folded Relaxed R1CS instance-witness tuple `(U, W)` of the same shape `shape`,
-- with the guarantee that the folded witness `W` satisfies the folded instance `U`
-- if and only if `W1` satisfies `U1` and `W2` satisfies `U2`.
def NIFS.prove (gen : R1CSGens G) (s : R1CSShape G) 
               (u₁ : RelaxedR1CSInstance G) (w₁ : RelaxedR1CSWitness G)
               (u₂ : R1CSInstance G) (w₂ : R1CSWitness G) : 
               Either NovaError (NIFS G × RelaxedR1CSInstance G × RelaxedR1CSWitness G) := do
  sorry