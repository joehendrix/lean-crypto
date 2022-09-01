import Crypto.ByteVec

@[extern "lean_AES128_ECB"]
opaque aes128Ecb (key: @&ByteVec 16) (v: @&ByteVec 16) : ByteVec 16

@[extern "lean_AES256_ECB"]
opaque aes256Ecb (key: @&ByteVec 32) (v: @&ByteVec 16) : ByteVec 16