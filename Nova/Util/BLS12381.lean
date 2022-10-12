import Nova.Util.EllipticCurves
import YatimaStdLib.Zmod

namespace BLS12381

def R : Nat := 
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def Q : Nat := 
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

def _a : Zmod Q := 0x0 

def _b : Zmod Q := 0x4

def _h : Nat := 
  0x396c8c005555e1568c00aaab0000aaab

def _q : Nat := 
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def _r : Nat := 
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def _x : Zmod Q := 
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

def _y : Zmod Q :=
  0x8b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

open EllipticCurves Weierstrass

open ProjectiveCurves

instance [Curve (Zmod Q) (Zmod R)] : WCurve (Zmod Q) (Zmod R) where
  a_ := _a
  b_ := _b
  h_ := _h
  q_ := _q
  r_ := _r

def gP : ProjectivePoint (Zmod Q) (Zmod R) := .P _x _y 1

instance [Curve (Zmod Q) (Zmod R)] : WPCurve (Zmod Q) (Zmod R) where
  gP := gP

end BLS12381