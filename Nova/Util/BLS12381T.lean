import Nova.Util.BLS12381
import Nova.Util.GaloisField
import Nova.Util.EllipticCurves

namespace BLS12381T

open GaloisField

inductive U

open BLS12381 in
instance : IrreducibleMonic U (Zmod Q) where
  poly _ := #[1,0,1]

def _h : Nat := 0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5

def _q : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def _r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def _a : Extension U (Zmod Q) := .E #[]

def _b : Extension U (Zmod Q) := .E #[0x4, 0x4]

def _x : Extension U (Zmod Q) := 
  .E #[0x24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
      0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e] 

def _y : Extension U (Zmod Q) := 
  .E #[0xce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
      0x606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be] 

open EllipticCurves Weierstrass AffineCurves Coordinate Form

variable [GaloisField (Extension U (Zmod Q))] [Curve Weierstrass Affine (Extension U (Zmod Q)) (Zmod R)]

instance : WCurve Affine (Extension U (Zmod Q)) (Zmod R) where
  a_ := _a
  b_ := _b
  h_ := _h
  q_ := _q
  r_ := _r

def gA : AffinePoint (Extension U (Zmod Q)) (Zmod R) := .A _x _y

instance : WACurve (Extension U (Zmod Q)) (Zmod R) where
  gA_ := gA

end BLS12381T