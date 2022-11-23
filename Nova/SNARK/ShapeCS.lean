import Nova.BellPerson.Index
import Nova.BellPerson.LinearCombination

inductive NamedObject where
  | Constraint : USize → NamedObject
  | Var : Variable Index → NamedObject
  | Namespace : NamedObject

-- `ShapeCS` is a `ConstraintSystem` for creating `R1CSShape`s for a circuit.
structure ShapeCS (G : Type _) where
  namedObjects : Array (String × NamedObject)
  constraints : Array (LinearCombination G × LinearCombination G × LinearCombination G × String)
  currentNamespace : Array String
  inputs : Array String
  aux : Array String

open NamedObject in
open Index in
def ShapeCS.new : ShapeCS G :=
  ShapeCS.mk #[("ONE", Var ∘ Variable.mk ∘ Input $ 1)] #[] #[] #["ONE"] #[]