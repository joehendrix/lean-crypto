import Crypto

def main (args:List String): IO Unit := do
  match args with
  | [reqPath, rspPath] => do
      randombytesInit (ByteVec.sequence 48);
      let mut seedArray : Array (ByteVec 48) := #[]
      let fpReq ← IO.FS.Handle.mk reqPath IO.FS.Mode.write false
      for i in [0:10] do
        let seed ← randombytes 48;
        fpReq.putStrLn s!"count = {i}"
        fpReq.putStrLn s!"seed = {seed}"
        fpReq.putStrLn "pk ="
        fpReq.putStrLn "sk ="
        fpReq.putStrLn "ct ="
        fpReq.putStrLn "ss =\n"
        seedArray := seedArray.push seed
      let fpRsp ← IO.FS.Handle.mk rspPath IO.FS.Mode.write false
      fpRsp.putStrLn $ s!"# kem/{Mceliece348864Ref.name}\n"
      for i in [0:10], seed in seedArray do
        let key ← Mceliece348864Ref.mkCryptoKemKeypair seed
        let enc ← Mceliece348864Ref.mkCryptoKemEnc key.pk
        let expected := Mceliece348864Ref.cryptoKemDec enc.ct key.sk
        if enc.ss ≠ expected then
          throw $ IO.userError "crypto_kem_dec returned bad 'ss' value"
        fpRsp.putStrLn $ s!"count = {i}"
        fpRsp.putStrLn $ s!"seed = {seed}"
        fpRsp.putStrLn $ s!"pk = {key.pk}"
        fpRsp.putStrLn $ s!"sk = {key.sk}"
        fpRsp.putStrLn $ s!"ct = {enc.ct}"
        fpRsp.putStrLn $ s!"ss = {enc.ss}\n"  
      IO.println "Done"
  | _ => do
    throw $ IO.userError "Expected reqPath and rspPath"