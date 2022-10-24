inductive Errors : Type _ where
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