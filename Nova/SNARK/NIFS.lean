import Nova.SNARK.Commitments

namespace NIFS

open Commitments

structure NIFS (G : Type _) where
  commT : CompressedCommitment G
  _p : G

end NIFS