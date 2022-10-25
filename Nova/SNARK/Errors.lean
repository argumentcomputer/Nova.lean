inductive Error : Type where
  | InvalidIndex
  | OddInputLength
  | InvalidInputLength
  | InvalidWitnessLength
  | UnSat
  | DecompressionError
  | ProofVerifyError
  | InvalidNumSteps
  | InvalidIPA
  | InvalidSumcheckProof
  | InvalidInitialInputLength
  | InvalidStepOutputLength

inductive SynthesisError : Type where
  | AssignmentMissing : SynthesisError
  | DivisionByZero : SynthesisError
  | Unsatisfiable : SynthesisError
  | PolynomialDegreeTooLarge : SynthesisError
  | UnexpectedIdentity : SynthesisError
  | IoError : Error → SynthesisError
  | UnconstrainedVariable : SynthesisError