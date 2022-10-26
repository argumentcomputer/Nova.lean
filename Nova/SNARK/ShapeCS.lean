import Nova.BellPerson.Index

inductive NamedObject where
  | Constraint : USize → NamedObject
  | Var : Variable Index → NamedObject
  | Namespace : NamedObject

structure ShapeCS (G : Type _) where
  named_objects : Array (String × NamedObject)
  current_namespace : Array String
  inputs : Array String
  aux : Array String