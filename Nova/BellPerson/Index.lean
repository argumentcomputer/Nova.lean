inductive Index : Type _ where
  | Input : USize → Index
  | Aux : USize → Index

structure Variable (A : Type _) where
  var : A 