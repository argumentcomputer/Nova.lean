namespace Circuit

/-
class StepCircuit (F : Type _) where
  arity : F → USize
  synthesise : _
  output : Array F
-/

structure NovaAugmentedCircuitParams where
  limb_width : USize
  n_limbs : USize
  is_primary_circuit : Bool

structure TrivialTestCircuit (F : Type _) where
  _p : F

end Circuit