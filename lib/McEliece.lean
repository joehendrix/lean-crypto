import Crypto

-- Creates a vector [0..n)
def byteSequence (n:Nat) : ByteVec n :=
  ⟨ByteArray.sequence n, by admit⟩

def main (args:List String): IO Unit := do
  match args with
  | [reqPath, rspPath] => do
      let mut drbg0 := randombytesInit (byteSequence 48);
      let mut seedArray : Array Seed := #[]
      let fpReq ← IO.FS.Handle.mk reqPath IO.FS.Mode.write false
      for i in [0:10] do
        let (seed, drbg2) := randombytes drbg0 48
        drbg0 := drbg2
        fpReq.putStrLn s!"count = {i}"
        fpReq.putStrLn s!"seed = {seed.toHex}"
        fpReq.putStrLn "pk ="
        fpReq.putStrLn "sk ="
        fpReq.putStrLn "ct ="
        fpReq.putStrLn "ss =\n"
        seedArray := seedArray.push seed
      let fpRsp ← IO.FS.Handle.mk rspPath IO.FS.Mode.write false
      fpRsp.putStrLn $ s!"# kem/{Mceliece348864Ref.name}\n"
      for i in [0:10], seed in seedArray do
        let (key, drbg) ←
              match Mceliece348864Ref.mkCryptoKemKeypair seed with
              | none => throw $ IO.userError "Key generation failed"
              | some p => pure p
        let enc ←
              match Mceliece348864Ref.mkCryptoKemEnc drbg 20 key.pk with
              | none => throw $ IO.userError "Encryption key generation failed."
              | some (enc, _drbg) => pure enc
        match Mceliece348864Ref.cryptoKemDec enc.ct key.sk with
        | none =>
          throw $ IO.userError "crypto_kem_dec failed."
        | some expected =>
          if enc.ss.bytes ≠ expected.bytes then
            throw $ IO.userError "crypto_kem_dec returned bad 'ss' value"
        fpRsp.putStrLn $ s!"count = {i}"
        fpRsp.putStrLn $ s!"seed = {seed.toHex}"
        fpRsp.putStrLn $ s!"pk = {key.pk}"
        fpRsp.putStrLn $ s!"sk = {key.sk}"
        fpRsp.putStrLn $ s!"ct = {enc.ct}"
        fpRsp.putStrLn $ s!"ss = {enc.ss}\n"
      IO.println "Done"
  | _ => do
    throw $ IO.userError "Expected reqPath and rspPath"