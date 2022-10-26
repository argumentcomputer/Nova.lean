import Nova.SNARK.Commitments

structure NIFS (G : Type _) where
  commT : CompressedCommitment G
  _p : G