namespace Commitments

variable (PreprocessedGroupElement : Type _ → Type _)

structure Commitment (G : Type _) where
  comm : G

structure CommitGens (G : Type _) where
  gens : Array (PreprocessedGroupElement G)
  _p : G

structure CompressedCommitment (C : Type _) where
  comm : C

end Commitments