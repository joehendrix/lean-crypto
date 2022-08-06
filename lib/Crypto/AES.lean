import Crypto.GF2BV

import Smt.Data.BitVec
import Smt

open GF256

/- ! Utilities -/

def Array.transpose [Inhabited α] (as : Array (Array α)) : Array (Array α) := Id.run do
  let shape := (as.size, as.get! 0 |>.size)
  let mut ret : Array (Array α) := mkArray shape.snd #[]
  for j in [:shape.snd] do
    for i in [:shape.fst] do
      let a := ret.get! j
      ret := ret.set! j (a.push (as.get! i |>.get! j))
  return ret

#eval #[#[1,2,3],#[4,5,6]].transpose.transpose == #[#[1,2,3],#[4,5,6]]

def Array.join (as : Array (Array α)) : Array α := Id.run do
  let mut ret := #[]
  for a in as do
    for x in a do
      ret := ret.push x
  return ret

def Array.bvJoin (bs : Array (BitVec w)) (h : bs.size = n) : BitVec (n * w) :=
  match n with
  | 0   => 0
  | n+1 =>
    let bs' := bs.pop
    have h' : bs'.size = n := by
      have := bs.size_pop
      rw [h, Nat.succ_sub_succ] at this
      assumption
    let res := bs'.bvJoin h'
    have : n < size bs := h ▸ Nat.lt_succ_self n
    have : (n + 1) * w = n*w + w := by simp [Nat.add_mul]
    this ▸ res.append bs[n]

def Array.bvSplit (n : Nat) (b : BitVec (n*w)) : Array (BitVec w) :=
  if h : w = 0 then #[]
  else Id.run do
    let mut ret := #[]
    for i in [:n] do
      have : i * w + (w - 1) - i*w + 1 = w := by
        sorry
      let part : BitVec w := this ▸ b.extract (i*w + (w - 1)) (i*w)
      ret := ret.push part
    return ret

/-! Theory of arrays -/

def SmtArray (α β : Type) :=
  α → β

def SmtArray.select (a : SmtArray α β) (x : α) :=
  a x

def SmtArray.store [DecidableEq α] (a : SmtArray α β) (x : α) (v : β) : SmtArray α β :=
  fun y => if x = y then v else a.select y

def SmtArray.constant (v : β) : SmtArray α β :=
  fun _ => v

instance [Inhabited β] : Inhabited (SmtArray α β) :=
  ⟨SmtArray.constant default⟩

open Lean Smt Translator in
@[smtTranslator]
def translateSmtArray : Translator
  | Expr.const ``SmtArray _ => return Term.symbolT "Array"
  | Expr.app (Expr.app (Expr.const ``SmtArray.select _) _) _ =>
    return Term.symbolT "select"
  | Expr.app (Expr.app (Expr.app (Expr.const ``SmtArray.store _) _) _) _ =>
    return Term.symbolT "store"
  | e@(Expr.app (Expr.app (Expr.app (Expr.const ``SmtArray.constant _) _) _) v) => do
    let kind := smt.solver.kind.get (← getOptions)
    if kind != .cvc5 && kind != .z3 then
      throwError "cannot translate{indentD e}\nconstant arrays are only supported by Z3 and CVC"
    let t ← Meta.inferType e
    return Term.appT
      (Term.mkApp2 (Term.symbolT "as") (Term.symbolT "const") (← applyTranslators! t))
      (← applyTranslators! v)
  | _ => return none

def SmtArray.ofBvMap (f : BitVec w → BitVec w) : SmtArray (BitVec w) (BitVec w) := Id.run do
  let mut ret := default
  for v in List.range (2^w) do
    let v := BitVec.ofNat w v
    ret := ret.store v (f v)
  return ret

/-! AES -/

def keyBlocks := 4
def inputBlocks := 4 -- 4 for AES128
def numRounds := max inputBlocks keyBlocks + 6
def keyBits := keyBlocks * 32

def State := { a : Array (Array GF256) // a.size = 4 ∧ ∀ b, b ∈ a → b.size = inputBlocks }
def RoundKey := State
def KeySchedule := RoundKey × { k : Array RoundKey // k.size + 1 = numRounds } × RoundKey

def GF256.dotProduct (a b : Array GF256) : GF256 :=
  GaloisField2k.addMany (a.zip b |>.map fun (a, b) => a * b)

-- Computable theory of modules over fields would be nicer
def GF256.vectorMul (v : Array GF256) (M : Array (Array GF256)) : Array GF256 :=
  M.map fun row => dotProduct v row

def GF256.matrixMul (M N : Array (Array GF256)) : Array (Array GF256) :=
  M.map fun row => vectorMul row (N.transpose)

def SmtArray.storeBv (a : SmtArray (BitVec 8) (BitVec 8)) (x v : Nat) : SmtArray (BitVec 8) (BitVec 8) :=
  a.store (.ofNat 8 x) (.ofNat 8 v)

-- See also tests/aes/SBox.lean
def sbox : SmtArray (BitVec 8) (BitVec 8) :=
  SmtArray.constant (BitVec.ofNat 8 0) |>.storeBv 0 0x63 |>.storeBv 1 0x7c |>.storeBv 2 0x77 |>.storeBv 3 0x7b
  |>.storeBv 4 0xf2 |>.storeBv 5 0x6b |>.storeBv 6 0x6f |>.storeBv 7 0xc5 |>.storeBv 8 0x30
  |>.storeBv 9 0x1 |>.storeBv 10 0x67 |>.storeBv 11 0x2b |>.storeBv 12 0xfe |>.storeBv 13 0xd7
  |>.storeBv 14 0xab |>.storeBv 15 0x76 |>.storeBv 16 0xca |>.storeBv 17 0x82 |>.storeBv 18 0xc9
  |>.storeBv 19 0x7d |>.storeBv 20 0xfa |>.storeBv 21 0x59 |>.storeBv 22 0x47 |>.storeBv 23 0xf0
  |>.storeBv 24 0xad |>.storeBv 25 0xd4 |>.storeBv 26 0xa2 |>.storeBv 27 0xaf |>.storeBv 28 0x9c
  |>.storeBv 29 0xa4 |>.storeBv 30 0x72 |>.storeBv 31 0xc0 |>.storeBv 32 0xb7 |>.storeBv 33 0xfd
  |>.storeBv 34 0x93 |>.storeBv 35 0x26 |>.storeBv 36 0x36 |>.storeBv 37 0x3f |>.storeBv 38 0xf7
  |>.storeBv 39 0xcc |>.storeBv 40 0x34 |>.storeBv 41 0xa5 |>.storeBv 42 0xe5 |>.storeBv 43 0xf1
  |>.storeBv 44 0x71 |>.storeBv 45 0xd8 |>.storeBv 46 0x31 |>.storeBv 47 0x15 |>.storeBv 48 0x4
  |>.storeBv 49 0xc7 |>.storeBv 50 0x23 |>.storeBv 51 0xc3 |>.storeBv 52 0x18 |>.storeBv 53 0x96
  |>.storeBv 54 0x5 |>.storeBv 55 0x9a |>.storeBv 56 0x7 |>.storeBv 57 0x12 |>.storeBv 58 0x80
  |>.storeBv 59 0xe2 |>.storeBv 60 0xeb |>.storeBv 61 0x27 |>.storeBv 62 0xb2 |>.storeBv 63 0x75
  |>.storeBv 64 0x9 |>.storeBv 65 0x83 |>.storeBv 66 0x2c |>.storeBv 67 0x1a |>.storeBv 68 0x1b
  |>.storeBv 69 0x6e |>.storeBv 70 0x5a |>.storeBv 71 0xa0 |>.storeBv 72 0x52 |>.storeBv 73 0x3b
  |>.storeBv 74 0xd6 |>.storeBv 75 0xb3 |>.storeBv 76 0x29 |>.storeBv 77 0xe3 |>.storeBv 78 0x2f
  |>.storeBv 79 0x84 |>.storeBv 80 0x53 |>.storeBv 81 0xd1 |>.storeBv 82 0x0 |>.storeBv 83 0xed
  |>.storeBv 84 0x20 |>.storeBv 85 0xfc |>.storeBv 86 0xb1 |>.storeBv 87 0x5b |>.storeBv 88 0x6a
  |>.storeBv 89 0xcb |>.storeBv 90 0xbe |>.storeBv 91 0x39 |>.storeBv 92 0x4a |>.storeBv 93 0x4c
  |>.storeBv 94 0x58 |>.storeBv 95 0xcf |>.storeBv 96 0xd0 |>.storeBv 97 0xef |>.storeBv 98 0xaa
  |>.storeBv 99 0xfb |>.storeBv 100 0x43 |>.storeBv 101 0x4d |>.storeBv 102 0x33 |>.storeBv 103 0x85
  |>.storeBv 104 0x45 |>.storeBv 105 0xf9 |>.storeBv 106 0x2 |>.storeBv 107 0x7f |>.storeBv 108 0x50
  |>.storeBv 109 0x3c |>.storeBv 110 0x9f |>.storeBv 111 0xa8 |>.storeBv 112 0x51 |>.storeBv 113 0xa3
  |>.storeBv 114 0x40 |>.storeBv 115 0x8f |>.storeBv 116 0x92 |>.storeBv 117 0x9d |>.storeBv 118 0x38
  |>.storeBv 119 0xf5 |>.storeBv 120 0xbc |>.storeBv 121 0xb6 |>.storeBv 122 0xda |>.storeBv 123 0x21
  |>.storeBv 124 0x10 |>.storeBv 125 0xff |>.storeBv 126 0xf3 |>.storeBv 127 0xd2 |>.storeBv 128 0xcd
  |>.storeBv 129 0xc |>.storeBv 130 0x13 |>.storeBv 131 0xec |>.storeBv 132 0x5f |>.storeBv 133 0x97
  |>.storeBv 134 0x44 |>.storeBv 135 0x17 |>.storeBv 136 0xc4 |>.storeBv 137 0xa7 |>.storeBv 138 0x7e
  |>.storeBv 139 0x3d |>.storeBv 140 0x64 |>.storeBv 141 0x5d |>.storeBv 142 0x19 |>.storeBv 143 0x73
  |>.storeBv 144 0x60 |>.storeBv 145 0x81 |>.storeBv 146 0x4f |>.storeBv 147 0xdc |>.storeBv 148 0x22
  |>.storeBv 149 0x2a |>.storeBv 150 0x90 |>.storeBv 151 0x88 |>.storeBv 152 0x46 |>.storeBv 153 0xee
  |>.storeBv 154 0xb8 |>.storeBv 155 0x14 |>.storeBv 156 0xde |>.storeBv 157 0x5e |>.storeBv 158 0xb
  |>.storeBv 159 0xdb |>.storeBv 160 0xe0 |>.storeBv 161 0x32 |>.storeBv 162 0x3a |>.storeBv 163 0xa
  |>.storeBv 164 0x49 |>.storeBv 165 0x6 |>.storeBv 166 0x24 |>.storeBv 167 0x5c |>.storeBv 168 0xc2
  |>.storeBv 169 0xd3 |>.storeBv 170 0xac |>.storeBv 171 0x62 |>.storeBv 172 0x91 |>.storeBv 173 0x95
  |>.storeBv 174 0xe4 |>.storeBv 175 0x79 |>.storeBv 176 0xe7 |>.storeBv 177 0xc8 |>.storeBv 178 0x37
  |>.storeBv 179 0x6d |>.storeBv 180 0x8d |>.storeBv 181 0xd5 |>.storeBv 182 0x4e |>.storeBv 183 0xa9
  |>.storeBv 184 0x6c |>.storeBv 185 0x56 |>.storeBv 186 0xf4 |>.storeBv 187 0xea |>.storeBv 188 0x65
  |>.storeBv 189 0x7a |>.storeBv 190 0xae |>.storeBv 191 0x8 |>.storeBv 192 0xba |>.storeBv 193 0x78
  |>.storeBv 194 0x25 |>.storeBv 195 0x2e |>.storeBv 196 0x1c |>.storeBv 197 0xa6 |>.storeBv 198 0xb4
  |>.storeBv 199 0xc6 |>.storeBv 200 0xe8 |>.storeBv 201 0xdd |>.storeBv 202 0x74 |>.storeBv 203 0x1f
  |>.storeBv 204 0x4b |>.storeBv 205 0xbd |>.storeBv 206 0x8b |>.storeBv 207 0x8a |>.storeBv 208 0x70
  |>.storeBv 209 0x3e |>.storeBv 210 0xb5 |>.storeBv 211 0x66 |>.storeBv 212 0x48 |>.storeBv 213 0x3
  |>.storeBv 214 0xf6 |>.storeBv 215 0xe |>.storeBv 216 0x61 |>.storeBv 217 0x35 |>.storeBv 218 0x57
  |>.storeBv 219 0xb9 |>.storeBv 220 0x86 |>.storeBv 221 0xc1 |>.storeBv 222 0x1d |>.storeBv 223 0x9e
  |>.storeBv 224 0xe1 |>.storeBv 225 0xf8 |>.storeBv 226 0x98 |>.storeBv 227 0x11 |>.storeBv 228 0x69
  |>.storeBv 229 0xd9 |>.storeBv 230 0x8e |>.storeBv 231 0x94 |>.storeBv 232 0x9b |>.storeBv 233 0x1e
  |>.storeBv 234 0x87 |>.storeBv 235 0xe9 |>.storeBv 236 0xce |>.storeBv 237 0x55 |>.storeBv 238 0x28
  |>.storeBv 239 0xdf |>.storeBv 240 0x8c |>.storeBv 241 0xa1 |>.storeBv 242 0x89 |>.storeBv 243 0xd
  |>.storeBv 244 0xbf |>.storeBv 245 0xe6 |>.storeBv 246 0x42 |>.storeBv 247 0x68 |>.storeBv 248 0x41
  |>.storeBv 249 0x99 |>.storeBv 250 0x2d |>.storeBv 251 0xf |>.storeBv 252 0xb0 |>.storeBv 253 0x54
  |>.storeBv 254 0xbb |>.storeBv 255 0x16

def invSbox : SmtArray (BitVec 8) (BitVec 8) :=
  SmtArray.constant (BitVec.ofNat 8 0) |>.storeBv 0 0x52 |>.storeBv 1 0x9 |>.storeBv 2 0x6a |>.storeBv 3 0xd5
  |>.storeBv 4 0x30 |>.storeBv 5 0x36 |>.storeBv 6 0xa5 |>.storeBv 7 0x38 |>.storeBv 8 0xbf |>.storeBv 9 0x40
  |>.storeBv 10 0xa3 |>.storeBv 11 0x9e |>.storeBv 12 0x81 |>.storeBv 13 0xf3 |>.storeBv 14 0xd7 |>.storeBv 15 0xfb
  |>.storeBv 16 0x7c |>.storeBv 17 0xe3 |>.storeBv 18 0x39 |>.storeBv 19 0x82 |>.storeBv 20 0x9b |>.storeBv 21 0x2f
  |>.storeBv 22 0xff |>.storeBv 23 0x87 |>.storeBv 24 0x34 |>.storeBv 25 0x8e |>.storeBv 26 0x43 |>.storeBv 27 0x44
  |>.storeBv 28 0xc4 |>.storeBv 29 0xde |>.storeBv 30 0xe9 |>.storeBv 31 0xcb |>.storeBv 32 0x54 |>.storeBv 33 0x7b
  |>.storeBv 34 0x94 |>.storeBv 35 0x32 |>.storeBv 36 0xa6 |>.storeBv 37 0xc2 |>.storeBv 38 0x23 |>.storeBv 39 0x3d
  |>.storeBv 40 0xee |>.storeBv 41 0x4c |>.storeBv 42 0x95 |>.storeBv 43 0xb |>.storeBv 44 0x42 |>.storeBv 45 0xfa
  |>.storeBv 46 0xc3 |>.storeBv 47 0x4e |>.storeBv 48 0x8 |>.storeBv 49 0x2e |>.storeBv 50 0xa1 |>.storeBv 51 0x66
  |>.storeBv 52 0x28 |>.storeBv 53 0xd9 |>.storeBv 54 0x24 |>.storeBv 55 0xb2 |>.storeBv 56 0x76 |>.storeBv 57 0x5b
  |>.storeBv 58 0xa2 |>.storeBv 59 0x49 |>.storeBv 60 0x6d |>.storeBv 61 0x8b |>.storeBv 62 0xd1 |>.storeBv 63 0x25
  |>.storeBv 64 0x72 |>.storeBv 65 0xf8 |>.storeBv 66 0xf6 |>.storeBv 67 0x64 |>.storeBv 68 0x86 |>.storeBv 69 0x68
  |>.storeBv 70 0x98 |>.storeBv 71 0x16 |>.storeBv 72 0xd4 |>.storeBv 73 0xa4 |>.storeBv 74 0x5c |>.storeBv 75 0xcc
  |>.storeBv 76 0x5d |>.storeBv 77 0x65 |>.storeBv 78 0xb6 |>.storeBv 79 0x92 |>.storeBv 80 0x6c |>.storeBv 81 0x70
  |>.storeBv 82 0x48 |>.storeBv 83 0x50 |>.storeBv 84 0xfd |>.storeBv 85 0xed |>.storeBv 86 0xb9 |>.storeBv 87 0xda
  |>.storeBv 88 0x5e |>.storeBv 89 0x15 |>.storeBv 90 0x46 |>.storeBv 91 0x57 |>.storeBv 92 0xa7 |>.storeBv 93 0x8d
  |>.storeBv 94 0x9d |>.storeBv 95 0x84 |>.storeBv 96 0x90 |>.storeBv 97 0xd8 |>.storeBv 98 0xab |>.storeBv 99 0x0
  |>.storeBv 100 0x8c |>.storeBv 101 0xbc |>.storeBv 102 0xd3 |>.storeBv 103 0xa |>.storeBv 104 0xf7 |>.storeBv 105 0xe4
  |>.storeBv 106 0x58 |>.storeBv 107 0x5 |>.storeBv 108 0xb8 |>.storeBv 109 0xb3 |>.storeBv 110 0x45 |>.storeBv 111 0x6
  |>.storeBv 112 0xd0 |>.storeBv 113 0x2c |>.storeBv 114 0x1e |>.storeBv 115 0x8f |>.storeBv 116 0xca |>.storeBv 117 0x3f
  |>.storeBv 118 0xf |>.storeBv 119 0x2 |>.storeBv 120 0xc1 |>.storeBv 121 0xaf |>.storeBv 122 0xbd |>.storeBv 123 0x3
  |>.storeBv 124 0x1 |>.storeBv 125 0x13 |>.storeBv 126 0x8a |>.storeBv 127 0x6b |>.storeBv 128 0x3a |>.storeBv 129 0x91
  |>.storeBv 130 0x11 |>.storeBv 131 0x41 |>.storeBv 132 0x4f |>.storeBv 133 0x67 |>.storeBv 134 0xdc |>.storeBv 135 0xea
  |>.storeBv 136 0x97 |>.storeBv 137 0xf2 |>.storeBv 138 0xcf |>.storeBv 139 0xce |>.storeBv 140 0xf0 |>.storeBv 141 0xb4
  |>.storeBv 142 0xe6 |>.storeBv 143 0x73 |>.storeBv 144 0x96 |>.storeBv 145 0xac |>.storeBv 146 0x74 |>.storeBv 147 0x22
  |>.storeBv 148 0xe7 |>.storeBv 149 0xad |>.storeBv 150 0x35 |>.storeBv 151 0x85 |>.storeBv 152 0xe2 |>.storeBv 153 0xf9
  |>.storeBv 154 0x37 |>.storeBv 155 0xe8 |>.storeBv 156 0x1c |>.storeBv 157 0x75 |>.storeBv 158 0xdf |>.storeBv 159 0x6e
  |>.storeBv 160 0x47 |>.storeBv 161 0xf1 |>.storeBv 162 0x1a |>.storeBv 163 0x71 |>.storeBv 164 0x1d |>.storeBv 165 0x29
  |>.storeBv 166 0xc5 |>.storeBv 167 0x89 |>.storeBv 168 0x6f |>.storeBv 169 0xb7 |>.storeBv 170 0x62 |>.storeBv 171 0xe
  |>.storeBv 172 0xaa |>.storeBv 173 0x18 |>.storeBv 174 0xbe |>.storeBv 175 0x1b |>.storeBv 176 0xfc |>.storeBv 177 0x56
  |>.storeBv 178 0x3e |>.storeBv 179 0x4b |>.storeBv 180 0xc6 |>.storeBv 181 0xd2 |>.storeBv 182 0x79 |>.storeBv 183 0x20
  |>.storeBv 184 0x9a |>.storeBv 185 0xdb |>.storeBv 186 0xc0 |>.storeBv 187 0xfe |>.storeBv 188 0x78 |>.storeBv 189 0xcd
  |>.storeBv 190 0x5a |>.storeBv 191 0xf4 |>.storeBv 192 0x1f |>.storeBv 193 0xdd |>.storeBv 194 0xa8 |>.storeBv 195 0x33
  |>.storeBv 196 0x88 |>.storeBv 197 0x7 |>.storeBv 198 0xc7 |>.storeBv 199 0x31 |>.storeBv 200 0xb1 |>.storeBv 201 0x12
  |>.storeBv 202 0x10 |>.storeBv 203 0x59 |>.storeBv 204 0x27 |>.storeBv 205 0x80 |>.storeBv 206 0xec |>.storeBv 207 0x5f
  |>.storeBv 208 0x60 |>.storeBv 209 0x51 |>.storeBv 210 0x7f |>.storeBv 211 0xa9 |>.storeBv 212 0x19 |>.storeBv 213 0xb5
  |>.storeBv 214 0x4a |>.storeBv 215 0xd |>.storeBv 216 0x2d |>.storeBv 217 0xe5 |>.storeBv 218 0x7a |>.storeBv 219 0x9f
  |>.storeBv 220 0x93 |>.storeBv 221 0xc9 |>.storeBv 222 0x9c |>.storeBv 223 0xef |>.storeBv 224 0xa0 |>.storeBv 225 0xe0
  |>.storeBv 226 0x3b |>.storeBv 227 0x4d |>.storeBv 228 0xae |>.storeBv 229 0x2a |>.storeBv 230 0xf5 |>.storeBv 231 0xb0
  |>.storeBv 232 0xc8 |>.storeBv 233 0xeb |>.storeBv 234 0xbb |>.storeBv 235 0x3c |>.storeBv 236 0x83 |>.storeBv 237 0x53
  |>.storeBv 238 0x99 |>.storeBv 239 0x61 |>.storeBv 240 0x17 |>.storeBv 241 0x2b |>.storeBv 242 0x4 |>.storeBv 243 0x7e
  |>.storeBv 244 0xba |>.storeBv 245 0x77 |>.storeBv 246 0xd6 |>.storeBv 247 0x26 |>.storeBv 248 0xe1 |>.storeBv 249 0x69
  |>.storeBv 250 0x14 |>.storeBv 251 0x63 |>.storeBv 252 0x55 |>.storeBv 253 0x21 |>.storeBv 254 0xc |>.storeBv 255 0x7d

-- The SubBytes transform and its inverse
def SubByte (b : GF256) : GF256 :=
  sbox.select b

def InvSubByte (b : GF256) : GF256 :=
  invSbox.select b

def SubBytes (st : State) : State :=
  let arr := st.val.map fun row => row.map SubByte
  ⟨arr, sorry⟩

def InvSubBytes (st : State) : State :=
  let arr := st.val.map fun row => row.map InvSubByte
  ⟨arr, sorry⟩

def rotateArrayLeft {α : Type} (as : Array α) (n : Nat) : Array α :=
  if h : as.size = 0 then as
  else Id.run do
    let mut ret := #[]
    for i in [:as.size] do
      have : (i + n) % as.size < as.size :=
        Nat.mod_lt _ (Nat.zero_lt_of_ne_zero h)
      ret := ret.push as[(i + n) % as.size]
    return ret

def rotateArrayRight {α : Type} (as : Array α) (n : Nat) : Array α :=
  if h : as.size = 0 then as
  else Id.run do
    let mut ret := #[]
    for i in [:as.size] do
      have : (as.size + i - n) % as.size < as.size :=
        Nat.mod_lt _ (Nat.zero_lt_of_ne_zero h)
      ret := ret.push as[(as.size + i - n) % as.size]
    return ret

-- The ShiftRows transform and its inverse
def ShiftRows (st : State) : State := Id.run do
  let rows := st.val
  have h : rows.size = 4 := st.property.left
  -- The GetOp solver should be able to get this automatically
  have : 0 < rows.size := by simp [h]
  have : 1 < rows.size := by simp [h]
  have : 2 < rows.size := by simp [h]
  have : 3 < rows.size := by simp [h]
  ⟨#[rows[0], rotateArrayLeft rows[1] 1,
     rotateArrayLeft rows[2] 2, rotateArrayLeft rows[3] 3],
  sorry⟩

def InvShiftRows (st : State) : State := Id.run do
  let rows := st.val
  have h : rows.size = 4 := st.property.left
  have : 0 < rows.size := by simp [h]
  have : 1 < rows.size := by simp [h]
  have : 2 < rows.size := by simp [h]
  have : 3 < rows.size := by simp [h]
  ⟨#[rows[0], rotateArrayRight rows[1] 1,
     rotateArrayRight rows[2] 2, rotateArrayRight rows[3] 3],
  sorry⟩

-- The MixColumns transform and its inverse
def MixColumns (st : State) : State :=
  ⟨GF256.matrixMul m st.val, sorry⟩
where m :=
  #[#[2, 3, 1, 1],
    #[1, 2, 3, 1],
    #[1, 1, 2, 3],
    #[3, 1, 1, 2]] |>.map fun row => row.map (BitVec.ofNat 8)

def InvMixColumns (st : State) : State :=
 ⟨GF256.matrixMul m st.val, sorry⟩
where m :=
  #[#[0x0e, 0x0b, 0x0d, 0x09],
    #[0x09, 0x0e, 0x0b, 0x0d],
    #[0x0d, 0x09, 0x0e, 0x0b],
    #[0x0b, 0x0d, 0x09, 0x0e]] |>.map fun row => row.map (BitVec.ofNat 8)

-- The AddRoundKey transform
def AddRoundKey (rk : RoundKey) (st : State) : State :=
  -- Cpmponentwise sum
  ⟨rk.val.zipWith st.val fun rowRk rowSt => rowRk.zipWith rowSt (· ^^^ ·), sorry⟩

-- Converting a 128 bit message to a State and back
def msgToState (msg : BitVec 128) : State :=
  let rows := Array.bvSplit 4 (w := 32) msg
  let st := rows.map (Array.bvSplit 4 (w := 8))
  ⟨Array.transpose st, sorry⟩

def State.toMsg (st : State) : BitVec 128 :=
  let v := st.val.transpose.join
  have : v.size = 4 * inputBlocks := sorry
  st.val.transpose.join.bvJoin this

#exit

SubWord : [4]GF28 -> [4]GF28
SubWord bs = [ SubByte' b | b <- bs ]

RotWord : [4]GF28 -> [4]GF28
RotWord [a0, a1, a2, a3] = [a1, a2, a3, a0]

NextWord : ([8],[4][8],[4][8]) -> [4][8]
NextWord(i, prev, old) = old ^ mask
   where mask = if i % `Nk == 0
                then SubWord(RotWord(prev)) ^ Rcon (i / `Nk)
                else if (`Nk > 6) && (i % `Nk == 4)
                     then SubWord(prev)
                     else prev


ExpandKeyForever : [Nk][4][8] -> [inf]RoundKey
ExpandKeyForever seed = [ transpose g | g <- groupBy`{4} (keyWS seed) ]

keyWS : [Nk][4][8] -> [inf][4][8]
keyWS seed    = xs
     where xs = seed # [ NextWord(i, prev, old)
                       | i    <- [ `Nk ... ]
                       | prev <- drop`{Nk-1} xs
                       | old  <- xs
                       ]

ExpandKey : [AESKeySize] -> KeySchedule
ExpandKey key = (keys @ 0, keys @@ [1 .. (Nr - 1)], keys @ `Nr)
  where   seed : [Nk][4][8]
          seed = split (split key)
          keys = ExpandKeyForever seed

fromKS : KeySchedule -> [Nr+1][4][32]
fromKS (f, ms, l) = [ formKeyWords (transpose k) | k <- [f] # ms # [l] ]
    where formKeyWords bbs = [ join bs | bs <- bbs ]

// AES rounds and inverses
AESRound : (RoundKey, State) -> State
AESRound (rk, s) = AddRoundKey (rk, MixColumns (ShiftRows (SubBytes s)))

AESFinalRound : (RoundKey, State) -> State
AESFinalRound (rk, s) = AddRoundKey (rk, ShiftRows (SubBytes s))

AESInvRound : (RoundKey, State) -> State
AESInvRound (rk, s) =
      InvMixColumns (AddRoundKey (rk, InvSubBytes (InvShiftRows s)))
AESFinalInvRound : (RoundKey, State) -> State
AESFinalInvRound (rk, s) = AddRoundKey (rk, InvSubBytes (InvShiftRows s))

// AES Encryption
aesEncrypt : ([128], [AESKeySize]) -> [128]
aesEncrypt (pt, key) = stateToMsg (AESFinalRound (kFinal, rounds ! 0))
  where   (kInit, ks, kFinal) = ExpandKey key
          state0 = AddRoundKey(kInit, msgToState pt)
          rounds = [state0] # [ AESRound (rk, s) | rk <- ks
                                                 | s <- rounds
                              ]

// AES Decryption
aesDecrypt : ([128], [AESKeySize]) -> [128]
aesDecrypt (ct, key) = stateToMsg (AESFinalInvRound (kFinal, rounds ! 0))
  where   (kFinal, ks, kInit) = ExpandKey key
          state0 = AddRoundKey(kInit, msgToState ct)
          rounds = [state0] # [ AESInvRound (rk, s)
                              | rk <- reverse ks
                              | s  <- rounds
                              ]

// Test runs:

// cryptol> aesEncrypt (0x3243f6a8885a308d313198a2e0370734,   \
//                      0x2b7e151628aed2a6abf7158809cf4f3c)
// 0x3925841d02dc09fbdc118597196a0b32
// cryptol> aesEncrypt (0x00112233445566778899aabbccddeeff,   \
//                      0x000102030405060708090a0b0c0d0e0f)
// 0x69c4e0d86a7b0430d8cdb78070b4c55a
property AESCorrect msg key = aesDecrypt (aesEncrypt (msg, key), key) == msg
