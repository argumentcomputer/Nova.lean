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

variable {A : Type} [Add A] [Mul A] [HPow A Nat A] [OfNat A 1] [ofnat : OfNat A 0] 
                    [hab : Inhabited A] [eq : BEq A] [Div A] [Neg A]

def dropWhile (p : A → Bool) (f : Polynomial A) : Polynomial A :=
  match f with
    | { data := xs } => Array.mk $ List.dropWhile p xs

def norm (f : Polynomial A) : Polynomial A :=
  Array.reverse $ dropWhile (fun (x : A) => x == 0) (Array.reverse f)

def degree (f : Polynomial A) : Nat :=
  Array.size (norm f) - 1

def isZero (f : Polynomial A) : Bool :=
  if f.size == 1 && f[0] == 0 then true else false

def isMonic (f : Polynomial A) : Bool :=
  let f' := norm f
  if f'[f'.size-1] == 1 then true else false

def lead (f : Polynomial A) : A :=
  let f' := norm f
  f'[f'.size-1] 

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

def polySub (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  polAdd f (Array.map Neg.neg g)

def polMul (f : Polynomial A) (g : Polynomial A) : Polynomial A := do
  let fx <- f
  let gx <- g
  return fx * gx 

instance : Add (Polynomial A) where
  add := polAdd

instance : Mul (Polynomial A) where
  mul := polMul

instance : Sub (Polynomial A) where
  sub := polySub

/-
def polDiv (f : Polynomial A) (g : Polynomial A) 
    {p₁ : f.size > 0} {p₂ : isZero (norm g) == false} : 
    Polynomial A × Polynomial A :=
  let f' := norm f
  let g' := norm g
  let rec helper (x : Polynomial A) (y : Polynomial A) : Polynomial A × Polynomial A :=
    if isZero x && degree x <= degree y 
    then (x, y)
    else
      let t := pure $ (lead x / lead y : A) 
      let y' := y ++ t
      let x' := x - t * y
      helper x' y'
  helper f' g'
-/

end Polynomial