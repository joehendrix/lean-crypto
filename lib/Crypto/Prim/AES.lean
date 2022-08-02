import Crypto.ByteVec

@[extern "lean_AES256_ECB"]
opaque aes256Ecb (key: @&ByteVec 32) (v: @&ByteVec 16) : ByteVec 16