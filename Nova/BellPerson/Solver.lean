import YatimaStdLib.Bit

structure DensityTracker where
  bv : Array Bit
  total_density : USize

def new_tracker : DensityTracker := DensityTracker.mk #[] 0

def add_element (tr : DensityTracker) : DensityTracker :=
  let new_bv :=  Array.push tr.bv .zero
  DensityTracker.mk new_bv tr.total_density

structure SatisfyingAssignment (G : Type _) where
  a_aux_density : DensityTracker
  b_input_density : DensityTracker
  b_aux_density : DensityTracker
  a : Array G
  b : Array G
  c : Array G
  input_assignment : Array G
  aux_assignment : Array G

def newSatisfyingAssignment [OfNat G 1] : SatisfyingAssignment G :=
  let input_assignment := #[(1 : G)]
  let d := add_element new_tracker
  SatisfyingAssignment.mk
    new_tracker
    d
    new_tracker
    #[]
    #[]
    #[]
    input_assignment
    #[]