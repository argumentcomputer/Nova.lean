import YatimaStdLib.Either

-- Errors returned by Nova
inductive Error : Type where
  -- returned if the supplied row or col in (row,col,val) tuple is out of range
  | InvalidIndex
  -- returned if the supplied input is not even-sized
  | OddInputLength
  -- returned if the supplied input is not of the right length
  | InvalidInputLength
  -- returned if the supplied witness is not of the right length
  | InvalidWitnessLength
  -- returned if the supplied witness is not a satisfying witness 
  -- to a given shape and instance
  | UnSat
  -- returned when the supplied compressed commitment cannot be decompressed
  | DecompressionError
  -- returned if proof verification fails
  | ProofVerifyError
  -- returned if the provided number of steps is zero
  | InvalidNumSteps
  -- returned when an invalid inner product argument is provided
  | InvalidIPA
  -- returned when an invalid sum-check proof is provided
  | InvalidSumcheckProof
  -- returned when the initial input to an incremental computation 
  -- differs from a previously declared arity
  | InvalidInitialInputLength
  -- returned when the step execution produces an output whose
  -- length differs from a previously declared arity
  | InvalidStepOutputLength

open Error in
open Either.Correctness in
def isError (act : Either Error A) : Bool :=
  match act with
    | .left _ => true
    | _         => false

inductive SynthesisError : Type where
  | AssignmentMissing : SynthesisError
  | DivisionByZero : SynthesisError
  | Unsatisfiable : SynthesisError
  | PolynomialDegreeTooLarge : SynthesisError
  | UnexpectedIdentity : SynthesisError
  | IoError : Error → SynthesisError
  | UnconstrainedVariable : SynthesisError