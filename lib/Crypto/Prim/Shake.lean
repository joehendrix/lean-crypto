import Crypto.ByteVec

@[extern "lean_shake256"]
opaque shake (w:Nat) (input: ByteArray) : ByteVec w
