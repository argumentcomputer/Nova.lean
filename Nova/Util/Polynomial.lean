import Std.Data.HashMap

namespace Polynomial

def Array.join : (Array (Array A)) → Array A :=
  Array.foldr (. ++ .) Array.empty 

def Polynomial R := Array R

instance : Monad Polynomial where
  map := Array.map
  pure := Array.singleton
  bind xs ar := Array.join (Array.map ar xs)

instance : Append (Polynomial A) where
  append := Array.append

variable {A : Type} [Add A] [Mul A] [HPow A Nat A] [OfNat A 0] [Inhabited A] [BEq A]

def dropWhile (p : A → Bool) (f : Polynomial A) : Polynomial A :=
  match f with
    | { data := xs } => Array.mk $ List.dropWhile p xs

def norm (f : Polynomial A) : Polynomial A :=
  dropWhile (fun (x : A) => x == 0) f

def degree (f : Polynomial A) : Nat :=
  Array.size (norm f) - 1

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

def zeros (n : Nat) : Polynomial A := mkArray n 0

def shift (f : Polynomial A) (n : Nat) : Polynomial A :=
  f ++ zeros n

def polAdd (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let action (f₁ : Polynomial A) (f₂ : Polynomial A) := Array.map ( fun (x, y) => x + y) (Array.zip f₁ f₂)
  if f.size < g.size
  then
    action (shift f (g.size - f.size)) g
  else
    if f.size > g.size
    then action f (shift g (f.size - g.size))
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