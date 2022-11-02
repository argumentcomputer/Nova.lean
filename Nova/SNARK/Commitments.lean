structure Commitment (G : Type _) where
  comm : G
  deriving BEq

structure CommitGens (G : Type _) where
  gens : Array G
  _p : G
  deriving BEq

structure CompressedCommitment (C : Type _) where
  comm : C

def compress (c : Commitment G) : CompressedCommitment G :=
  CompressedCommitment.mk c.comm