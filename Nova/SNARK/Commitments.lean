structure Commitment (G : Type _) where
  comm : G

structure CommitGens (G : Type _) where
  gens : Array G
  _p : G

structure CompressedCommitment (C : Type _) where
  comm : C