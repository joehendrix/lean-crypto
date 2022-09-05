import Crypto.BitVec
import Crypto.ByteVec
import Crypto.Vector
import Crypto.GF2Poly

/-
// Cryptol AES Implementation
// Copyright (c) 2010-2013, Galois Inc.
// www.cryptol.net
// You can freely use this source code for educational purposes.

// This is a fairly close implementation of the FIPS-197 standard:
//   http://csrc.nist.gov/publications/fips/fips197/fips-197.pdf

// Nk: Number of blocks in the key
// Must be one of 4 (AES128), 6 (AES192), or 8 (AES256)
// Aside from this line, no other code below needs to change for
// implementing AES128, AES192, or AES256
module AES where

type AES128 = 4
type AES192 = 6
type AES256 = 8
-/

def ByteVec.toList (v : ByteVec n) : List UInt8 := sorry

class Split (O : Type _) (I : outParam (Type _)) where
  split (i : I) : O

open Split

namespace BitVec

protected
def split {a b : Nat} (x:BitVec (a*b))  : Vector a (BitVec b) := sorry

instance (a b : Nat) : Split (Vector a (BitVec b)) (BitVec (a*b)) where
  split := BitVec.split

end BitVec

namespace ByteVec

instance : GetElem (ByteVec n) Nat UInt8 (λv i => i < n) where
  getElem := sorry


end ByteVec


namespace Vector

instance : GetElem (Vector n α) Nat α (λv i => i < n) where
  getElem := sorry

instance [h:HXor α β γ] : HXor (Vector n α) (Vector n β) (Vector n γ) := sorry

@[specialize]
def foldl {α β} {n:Nat} (f : α → β → α) (init : α) (v:Vector n β) : α :=
  v.data.foldl f init

def joinBV {m n:Nat} (x:Vector m (BitVec n)) : BitVec (m*n) := sorry

protected
def split {a b:Nat} {α:Type _} (x:Vector (a*b) α) : Vector a (Vector b α) := sorry

instance (a b : Nat) : Split (Vector a (Vector b α)) (Vector (a*b) α) where
  split := Vector.split

def toBitVec {m:Nat} (x:Vector m Bool) : BitVec m := sorry

def reverse (x:Vector n α) : Vector n α := sorry

def transpose (x:Vector m (Vector n α)) : Vector n (Vector m α) := sorry

end Vector


-- Nk values
@[reducible]
def aes128 := 4

@[reducible]
def aes192 := 4
def aes256 := 4

/-
type Nk = AES128

// For Cryptol 2.x | x > 0
// NkValid: `Nk -> Bit
// property NkValid k = (k == `AES128) || (k == `AES192) || (k == `AES256)

// Number of blocks and Number of rounds
type Nb = 4
type Nr = 6 + Nk

type AESKeySize  = (Nk*32)

// Helper type definitions
type GF28        = [8]
type State       = [4][Nb]GF28
type RoundKey    = State

type KeySchedule = (RoundKey, [Nr-1]RoundKey, RoundKey)
-/

abbrev GF28 := BitVec 8

abbrev Nb := 4

abbrev Nr (nk:Nat) := 6 + nk

abbrev State := Vector 4 (Vector Nb GF28)

abbrev RoundKey := State

structure KeySchedule (nk:Nat) where
  init : RoundKey
  schedule : Vector (Nr nk - 1) RoundKey
  final : State

/-
// GF28 operations
gf28Add : {n} (fin n) => [n]GF28 -> GF28
gf28Add ps = sums ! 0
  where sums = [zero] # [  p ^ s | p <- ps | s <- sums ]

irreducible = <| x^^8 + x^^4 + x^^3 + x + 1 |>

gf28Mult : (GF28, GF28) -> GF28
gf28Mult (x, y) = pmod(pmult x y) irreducible

gf28Pow : (GF28, [8]) -> GF28
gf28Pow (n, k) = pow k
  where   sq x  = gf28Mult (x, x)
          odd x = x ! 0
          pow i = if i == 0 then 1
                  else if odd i
                       then gf28Mult(n, sq (pow (i >> 1)))
                       else sq (pow (i >> 1))

gf28Inverse : GF28 -> GF28
gf28Inverse x = gf28Pow (x, 254)

gf28DotProduct : {n} (fin n) => ([n]GF28, [n]GF28) -> GF28
gf28DotProduct (xs, ys) = gf28Add [ gf28Mult (x, y) | x <- xs
                                                    | y <- ys ]

gf28VectorMult : {n, m} (fin n) => ([n]GF28, [m][n]GF28) -> [m]GF28
gf28VectorMult (v, ms) = [ gf28DotProduct(v, m) | m <- ms ]

gf28MatrixMult : {n, m, k} (fin m) => ([n][m]GF28, [m][k]GF28) -> [n][k]GF28
gf28MatrixMult (xss, yss) = [ gf28VectorMult(xs, yss') | xs <- xss ]
   where yss' = transpose yss

// The affine transform and its inverse
xformByte : GF28 -> GF28
xformByte b = gf28Add [b, (b >>> 4), (b >>> 5), (b >>> 6), (b >>> 7), c]
   where c = 0x63

xformByte' : GF28 -> GF28
xformByte' b = gf28Add [(b >>> 2), (b >>> 5), (b >>> 7), d] where d = 0x05
// The SubBytes transform and its inverse
SubByte : GF28 -> GF28
SubByte b = xformByte (gf28Inverse b)

SubByte' : GF28 -> GF28
SubByte' b = sbox@b
-/


def subByte' (b:GF28) : GF28 := sorry

def subBytes (state:State) : State :=
  Functor.map subByte' <$> state


def invSubByte (b:GF28) : GF28 := sorry

/-
InvSubByte b = gf28Inverse (xformByte' b)
-/

def invSubBytes (state:State) : State :=
  Functor.map invSubByte <$> state


def shiftRows (state:State) : State := sorry

/-
// The ShiftRows transform and its inverse
ShiftRows : State -> State
ShiftRows state = [ row <<< shiftAmount | row <- state
                                        | shiftAmount <- [0 .. 3]
                  ]
-/

def invShiftRows (state:State) : State := sorry

/-
InvShiftRows state = [ row >>> shiftAmount | row <- state
                                           | shiftAmount <- [0 .. 3]
                     ]
-/

-- The MixColumns transform and its inverse
def mixColumns (state:State) : State := sorry

/-
MixColumns : State -> State
MixColumns state = gf28MatrixMult (m, state)
    where m = [[2, 3, 1, 1],
               [1, 2, 3, 1],
               [1, 1, 2, 3],
               [3, 1, 1, 2]]
-/

def invMixColumns (state:State) : State := sorry

/-
InvMixColumns state = gf28MatrixMult (m, state)
    where m = [[0x0e, 0x0b, 0x0d, 0x09],
               [0x09, 0x0e, 0x0b, 0x0d],
               [0x0d, 0x09, 0x0e, 0x0b],
               [0x0b, 0x0d, 0x09, 0x0e]]
-/


def addRoundKey (rk:RoundKey) (s:State) : State := rk ^^^ s

/-
// Key expansion
Rcon : [8] -> [4]GF28
Rcon i = [(gf28Pow (<| x |>, i-1)), 0, 0, 0]

SubWord : [4]GF28 -> [4]GF28
SubWord bs = [ SubByte' b | b <- bs ]

RotWord : [4]GF28 -> [4]GF28
RotWord [a0, a1, a2, a3] = [a1, a2, a3, a0]
-/

abbrev Byte := GF28

abbrev Word  := Vector 4 Byte

def word (a b c d : Byte) : Word := #v[a,b,c,d]

def subWord (w:Word) : Word := subByte' <$> w

def rotWord (w:Word) : Word := #v[w[1], w[2], w[3], w[0]]

def rcon (j:Nat) : Word := #v[sorry, 0, 0, 0]

--Rcon : [8] -> [4]GF28
--Rcon i = [(gf28Pow (<| x |>, i-1)), 0, 0, 0]

#eval 3 ^ 3

def keyExpansion {nk:Nat} (key : Vector (4*nk) GF28) : Vector (Nb * (Nr nk+1)) Word := Id.run do
  let mut w : Array Word := Array.mkEmpty (Nb * (Nr nk+1))
  -- i = 0
  for i in range 0 nk do
    --   w[i] = word(key[4*i], key[4*i+1], key[4*i+2], key[4*i+3])
    --   i = i+1
    have h0 : 4*i < 4*nk := sorry
    have h1 : 4*i+1 < 4*nk := sorry
    have h2 : 4*i+2 < 4*nk := sorry
    have h3 : 4*i+3 < 4*nk := sorry
    w := w.push #v[key[4*i], key[4*i+1], key[4*i+2], key[4*i+3]]
  for i in rangeH nk (Nb * Nr nk + 1) do
    let mut temp := w[i-1]!
    if i % nk == 0 then
      temp := subWord (rotWord temp) ^^^ rcon (i/nk)
    else
      temp := subWord temp
    w := w.push (w[i-nk]! ^^^ temp)
  pure (Vector.mk w sorry)




/-
NextWord : ([8],[4][8],[4][8]) -> [4][8]
NextWord(i, prev, old) = old ^ mask
   where mask = if i % `Nk == 0
                then SubWord(RotWord(prev)) ^ Rcon (i / `Nk)
                else if (`Nk > 6) && (i % `Nk == 4)
                     then SubWord(prev)
                     else prev
-/

/-
ExpandKeyForever : [Nk][4][8] -> [inf]RoundKey
ExpandKeyForever seed = [ transpose g | g <- groupBy`{4} (keyWS seed) ]

keyWS : [Nk][4][8] -> [inf][4][8]
keyWS seed    = xs
     where xs = seed # [ NextWord(i, prev, old)
                       | i    <- [ `Nk ... ]
                       | prev <- drop`{Nk-1} xs
                       | old  <- xs
                       ]
-/

@[reducible]
def Key (nk:Nat) := BitVec (32*nk)

#print cast

def expandKey {nk:Nat} (key:Key nk) : KeySchedule nk :=
  let h : 32 * nk = nk * 4 * 8 := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
  let key : BitVec (nk * 4 * 8) := cast (congr_arg _ h) key
  let seed : Vector nk (Vector 4 (BitVec 8)) := split (split key)
  sorry

      -- seed = (key.split (nk*4), split (split key)

/-
ExpandKey : [AESKeySize] -> KeySchedule
ExpandKey key = (keys @ 0, keys @@ [1 .. (Nr - 1)], keys @ `Nr)
  where   seed : [Nk][4][8]
          seed = split (split key)
          keys = ExpandKeyForever seed
-/

/-
fromKS : KeySchedule -> [Nr+1][4][32]
fromKS (f, ms, l) = [ formKeyWords (transpose k) | k <- [f] # ms # [l] ]
    where formKeyWords bbs = [ join bs | bs <- bbs ]
-/


-- AES rounds and inverses
def aesRound (rk:RoundKey) (s:State) : State :=
  addRoundKey rk (mixColumns (shiftRows (subBytes s)))

-- AESRound : (RoundKey, State) -> State
--AESRound (rk, s) = AddRoundKey (rk, MixColumns (ShiftRows (SubBytes s)))


-- AES rounds and inverses
def aesInvRound (rk:RoundKey) (s:State) : State :=
  invMixColumns (addRoundKey rk (invSubBytes (invShiftRows s)))

--AESInvRound : (RoundKey, State) -> State
--AESInvRound (rk, s) =
--      InvMixColumns (AddRoundKey (rk, InvSubBytes (InvShiftRows s)))

def aesFinalRound (rk:RoundKey) (s:State) : State :=
  addRoundKey rk (shiftRows (subBytes s))

def aesFinalInvRound (rk:RoundKey) (s:State) : State :=
  addRoundKey rk (invSubBytes (invShiftRows s))

-- Converting a 128 bit message to a State
-- msgToState : [128] -> State
-- msgToState msg = transpose (split (split msg))

def msgToState (msg:BitVec 128) : State :=
  split (split msg)

def stateToMsg (s:State) : BitVec 128 := s.transpose.join.joinBV

/-



// Test runs:

// cryptol> aesEncrypt (0x3243f6a8885a308d313198a2e0370734,   \
//                      0x2b7e151628aed2a6abf7158809cf4f3c)
// 0x3925841d02dc09fbdc118597196a0b32
// cryptol> aesEncrypt (0x00112233445566778899aabbccddeeff,   \
//                      0x000102030405060708090a0b0c0d0e0f)
// 0x69c4e0d86a7b0430d8cdb78070b4c55a
property AESCorrect msg key = aesDecrypt (aesEncrypt (msg, key), key) == msg
-/


/-
sbox : [256]GF28
sbox = [
 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67,
 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59,
 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7,
 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1,
 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05,
 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83,
 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29,
 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b,
 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa,
 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c,
 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc,
 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec,
 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19,
 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee,
 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49,
 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4,
 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6,
 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70,
 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9,
 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e,
 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1,
 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0,
 0x54, 0xbb, 0x16]
-/


-- AES Encryption
def aesEncrypt {nk:Nat} (pt : BitVec 128) (key : Key nk) : BitVec 128 :=
  let { init := kInit, schedule := ks, final := kFinal } := expandKey key
  let state0 := addRoundKey kInit (msgToState pt)
  let s := ks.foldl (λs rk => aesRound rk s) state0
  stateToMsg (aesFinalRound kFinal s)

-- AES Decryption
def aesDecrypt {nk:Nat} (ct : BitVec 128) (key : Key nk) : BitVec 128 :=
  let { init := kInit, schedule := ks, final := kFinal } := expandKey key
  let state0 := addRoundKey kInit (msgToState ct)
  let s := ks.reverse.foldl (λs rk => aesInvRound rk s) state0
  stateToMsg (aesFinalInvRound kFinal s)

@[extern "lean_AES128_ECB"]
opaque aes128Ecb (key: @&ByteVec 16) (v: @&ByteVec 16) : ByteVec 16

@[extern "lean_AES256_ECB"]
opaque aes256Ecb (key: @&ByteVec 32) (v: @&ByteVec 16) : ByteVec 16