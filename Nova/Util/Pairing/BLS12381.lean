import Nova.Util.BLS12381
import Nova.Util.BLS12381T
import Nova.Util.GaloisField
import Nova.Util.Pairing.Pairing

namespace BLS12381

open BLS12381 GaloisField BLS12381T

def xi : Extension U (Zmod Q) :=
  .E #[0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd556,
       0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd555]

inductive V

variable [GaloisField (Extension V (Extension U (Zmod Q)))]

instance : IrreducibleMonic V (Extension V (Extension U (Zmod Q))) where
  poly _ := #[.E #[xi], 0, 0, 1]

inductive W 

variable [GaloisField (Extension W (Extension V (Extension U (Zmod Q))))]

instance : IrreducibleMonic W (Extension W (Extension V (Extension U (Zmod Q)))) where
  poly _ := #[(.E #[0, -1]), 0, 1]

def pol₁ : Extension U (Zmod Q) :=
  .E #[0x1250ebd871fc0a92a7b2d83168d0d727272d441befa15c503dd8e90ce98db3e7b6d194f60839c508a84305aaca1789b6,
      0x89a1c5b46e5110b86750ec6a532348868a84045483c92b7af5af689452eafabf1a8943e50439f1d59882a98eaa0170f]

def pol₂ : Extension U (Zmod Q) :=
  .E #[0x31ee0cf8176faed3d5e214d37e4837b518958ee5c39b2997f01e9ffb9e533bf5cb7335184e4b9b91c232bd7551f5ef,
       0x333fc379662be784e4ed53bc809b8c242cd5c26049b5dbe98b3e9599912e2523dbb28ca5f0764eaa9980581f5dd5f5b]

def pol₃ : Extension U (Zmod Q) :=
  .E #[0x1434ca7627208b631fab9fe851983efa300f78c547c61f10017a080635adb658fcc639b4ed513fdb10cb2a9862a855e3,
      0x129cac1291d7cede0e5c448a7fa1879dd6e1d4579d8748542c3a143f14588050bf3874ac39dc273dff6d6e70dadc272b]

def pol₄ : Extension U (Zmod Q) :=
  .E #[0xf84ad8722c9486446b9d04ee5c12b31ca548f26fc85317fa4ae45dcacca2709ef1851df07d1c7ac4d23a6ebf1a82869,
      0x140766a9b0c7736808ab0e3042aa7be8dd368d5062528949fb7c4413b0f51b6d7989a629b646c3ea8eed395c68774a20]

def pol₅ : Extension U (Zmod Q) :=
  .E #[0xe83a4cf2599c26539d4183cce2597a90179aa3ac63883345c450f5245902578fd4737c27d92fcef5d7122d2718820b5,
      0x14edc37a74f7bc0cc00ab7d3a7f085e28ebb7d2b9ba3b19a9dd51cacb1a07799f497594dbed2f8a2d9b64613f63d53f9]

def pol₆ : Extension U (Zmod Q) :=
  .E #[0x12f6c0f91a404c38fd5629091c63e94df3020950c1adc74636d2cca650f75efe9f15ba1a87a57f85ff69a0640ea93d83,
      0x6ecf38c504bc3b9f13ba96c27fbaa763995b521b26e8bb21f46fb401dc62936b863f0edd45760f665c063e9ba54e90c]

def parameterBin : List Int :=
  [-1,-1, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def parameterHex : Int := -0xd201000000010000

end BLS12381