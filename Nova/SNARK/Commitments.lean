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

def commit [OfNat G 0] [HPow G G G] [Add G]
  (degs : Array G) (gen : CommitGens G) : Commitment G :=
  Commitment.mk $
  Array.foldr (. + .) 0 (Array.map (fun (degree, base) => base ^ degree) (Array.zip degs gen.gens))
-- rewrite it using efficient multiexponentiation