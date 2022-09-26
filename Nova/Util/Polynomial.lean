import Std.Data.HashMap

namespace Polynomial

def Polynomial R := Array R

instance : Append (Polynomial A) where
  append := Array.append

variable {A : Type} [Add A] [Mul A] [HPow A Nat A] [OfNat A 1] [ofnat : OfNat A 0] 
                    [hab : Inhabited A] [eq : BEq A] [Div A] [Neg A]

def dropWhile (p : A → Bool) (f : Polynomial A) : Polynomial A :=
  match f with
    | { data := xs } => Array.mk $ List.dropWhile p xs

def norm (f : Polynomial A) : Polynomial A :=
  dropWhile (fun (x : A) => x == 0) f

def degree (f : Polynomial A) : Nat :=
  Array.size (norm f) - 1

def isZero (f : Polynomial A) : Bool :=
  if f.size == 1 && f[0] == 0 then true else false

def isMonic (f : Polynomial A) : Bool :=
  let f' := norm f
  if f'[f'.size-1] == 1 then true else false

def lead (f : Polynomial A) : A := Array.getD f 0 0

def mulByConst (a : A) (f : Polynomial A) : Polynomial A :=
  Array.map (fun x => x * a) f

instance : HMul A (Polynomial A) (Polynomial A) where
  hMul := mulByConst

def eval (f : Polynomial A) (a : A) : A :=
  let action (i : Fin f.size) _ :=
    match (i : Nat) with
      | 0 => f[0] ^ f.size
      | (Nat.succ _) => a ^ (f.size - i : Nat) * f[i]
  Array.foldr (. + .) 0 (Array.mapIdx f action)

def zeros (n : Nat) : Polynomial A := mkArray n 0

def zero : Polynomial A := #[0]

def shift (f : Polynomial A) (n : Nat) : Polynomial A :=
  f ++ zeros n

def polAdd (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  let action (f₁ : Polynomial A) (f₂ : Polynomial A) := Array.map (fun (x, y) => x + y) (Array.zip f₁ f₂)
  if f.size < g.size
  then
    action (shift f (g.size - f.size)) g
  else
    if f.size > g.size
    then action f (shift g (f.size - g.size))
    else action f g

instance : Add (Polynomial A) where
  add := polAdd

def polySub (f : Polynomial A) (g : Polynomial A) : Polynomial A :=
  polAdd f (Array.map Neg.neg g)

def polMul (f : Polynomial A) : Polynomial A → Polynomial A :=
  Array.foldr (fun x acc => polAdd (mulByConst x f) (zero ++ acc)) (#[] : Polynomial A)

instance : Mul (Polynomial A) where
  mul := polMul

instance : Sub (Polynomial A) where
  sub := polySub

def polDiv (f : Polynomial A) (g : Polynomial A) : 
    Polynomial A × Polynomial A :=
  let f' := norm f
  let g' := norm g
  let rec helper (x : Polynomial A) (y : Polynomial A) (n : Nat) : Polynomial A × Polynomial A :=
    match n with
      | .zero => (x, y)
      | .succ k => 
        let t : Polynomial A := #[lead x / lead y]
        let y' := norm (y + t)
        let x' := norm (x - t * g')
        helper (norm x') (norm y') k
  let (f'', g'') := helper f' g' (degree f')
  (norm f'', norm g'')

end Polynomial