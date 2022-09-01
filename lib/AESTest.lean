import Crypto.ByteVec
import Crypto.Prim.AES

namespace Char

def decodeHexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then Except.ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then Except.ok (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then Except.ok (10 + c.toNat - 'A'.toNat)
  else Except.error s!"Could not decode {c} as hexadecimal digit."

end Char

def parseHexByteVec (name:String) (n:Nat) (s:String) : Except String (ByteVec n) := do
  let rec loop (a:ByteArray) (l:List Char) : Except String ByteArray :=
    match l with
    | [] =>
      Except.ok a
    | d0::d1::r => do
      let d0 ← d0.decodeHexDigit
      let d1 ← d1.decodeHexDigit
      let a := a.push (16 * UInt8.ofNat d0 + UInt8.ofNat d1)
      loop a r
    | [_] =>
      Except.error s!"{name} has {l.length} characters when {2*n} expected."
  let r ← loop (ByteArray.mkEmpty n) s.data
  if p:r.size = n then
    Except.ok ⟨r, p⟩
  else
    Except.error s!"{name} has {s.length} characters when {2*n} expected."


def parseHexByteVecIO (name:String) (n:Nat) (s:String) : IO (ByteVec n) := do
  match parseHexByteVec name n s with
  | Except.ok r => pure r
  | Except.error msg => throw (IO.userError msg)

inductive Cipher where
| AES128 : Cipher
| AES256 : Cipher

namespace Cipher
def keylengthBytes
| AES128 => 16
| AES256 => 32

end Cipher

partial def main (args:List String): IO Unit := do
  match args with
  | [testPath] => do
      let h ← IO.FS.Handle.mk testPath IO.FS.Mode.read false

      let mut cipher := Cipher.AES128
      let mut key : ByteArray := ByteArray.empty
      let mut plaintext : ByteVec 16 := ByteVec.zeros _
      repeat
        let ln ← h.getLine
        if ln == "" then
          break
        if ln.takeRight 1 ≠ "\n" then
          throw $ IO.userError s!"Expected line terminator in \"{ln}\""
        let ln := ln.dropRight 1
        match ln.splitOn with
        | "#"::_ =>
          -- Skip
          pure ()
        | [""] =>
          pure ()
        | ["Cipher", "=", cipherStr] =>
          match cipherStr with
          | "AES-128-ECB" =>
            cipher := Cipher.AES128
          | "AES-256-ECB" =>
            cipher := Cipher.AES256
          | _ =>
            throw (IO.userError s!"Unknown cipher {cipherStr}")
        | ["Key", "=", keyStr] => do
          key ← ByteVec.data <$> parseHexByteVecIO "Key" cipher.keylengthBytes keyStr
        | ["Plaintext", "=", plaintextStr] =>
          plaintext ← parseHexByteVecIO "Plaintext" _ plaintextStr
          pure ()
        | ["Ciphertext", "=", str] =>
          let ciphertext ← parseHexByteVecIO "Ciphertext" 16 str
          let encrypted ←
            match cipher with
            | Cipher.AES128 =>
              if p:key.size = 16 then
                pure (aes128Ecb ⟨key,p⟩ plaintext).data
              else
                throw $ IO.userError s!"AES128 requires 128-bit key."
            | Cipher.AES256 =>
              if p:key.size = 32 then
                pure (aes256Ecb ⟨key,p⟩ plaintext).data
              else
                throw $ IO.userError s!"AES256 requires 128-bit key."
          if ciphertext.data ≠ encrypted then
            throw (IO.userError s!"Encrypted block {encrypted} does not match ciphertext {ciphertext}.")
        | _ =>
          throw $ IO.userError s!"Unexpected line \"{ln}\""
  | _ => do
    throw $ IO.userError "Expected test path"