import Std.Data.HashMap

namespace Polynomial

def Polynomial R := Array R

def Array.join : (Array (Array A)) → Array A :=
  Array.foldr (. ++ .) Array.empty 

instance : Monad Polynomial where
  map := Array.map
  pure := Array.singleton
  bind xs ar := Array.join (Array.map ar xs)

instance : Append (Polynomial A) where
  append := Array.append

variable {A : Type} [Add A] [Mul A] [HPow A Nat A] [OfNat A 0] [Inhabited A]

def mulByConst (a : A) (f : Polynomial A) : Polynomial A :=
  Array.map (fun x => x * a) f

instance : HMul A (Polynomial A) (Polynomial A) where
  hMul := mulByConst

def eval (f : Polynomial A) (a : A) : A :=
  let action (i : Fin f.size) _ :=
    match (i : Nat) with
      | 0 => f[0]
      | (Nat.succ _) => a ^ (i : Nat) * f[i]
  Array.foldr (. + .) 0 (Array.mapIdx f action)

def polAdd (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let action (f₁ : Polynomial A) (f₂ : Polynomial A) := Array.map ( fun (x, y) => x + y) (Array.zip f₁ f₂)
  let zeros n : Polynomial A := (mkArray n 0 : Polynomial A)
  if f.size < g.size
  then
    action (f ++ zeros (g.size - f.size)) g
  else
    if f.size > g.size
    then action f (g ++ zeros (f.size - g.size))
    else action f g

def polMul (f : Polynomial A) (g : Polynomial A) : Polynomial A := do
  let fx <- f;
  let gx <- g;
  return fx * gx 

instance : Add (Polynomial A) where
  add := polAdd

instance : Mul (Polynomial A) where
  mul := polMul

end Polynomial