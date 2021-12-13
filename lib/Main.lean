import Crypto

def main : IO Unit := do
  randombytesInit (ByteVec.sequence 48);
  let mut seedArray : Array (ByteVec 48) := #[]
  let fpReq ← openByFd 8;
  for i in [0:10] do
    let seed ← randombytes 48;
    fpReq.putStrLn $ "count = " ++ toString i
    fpReq.putStrLn $ "seed = " ++ toString seed
    fpReq.putStrLn "pk ="
    fpReq.putStrLn "sk ="
    fpReq.putStrLn "ct ="
    fpReq.putStrLn "ss =\n"    
    seedArray := seedArray.push seed
  let fpRsp ← openByFd 9;
--  let fpRsp ← IO.getStdout
  fpRsp.putStrLn $ "# kem/" ++ Mceliece348864Ref.name ++"\n"
  for i in [0:10], seed in seedArray do
    let key ← mkCryptoKemKeypair seed
    let enc ← mkCryptoKemEnc key.pk
    let ss1 ← cryptoKemDec enc.ct key.sk
    if enc.ss ≠ ss1 then
      throw $ IO.userError "crypto_kem_dec returned bad 'ss' value"
    fpRsp.putStrLn $ s!"count = {i}"
    fpRsp.putStrLn $ s!"seed = {seed}"
    fpRsp.putStrLn $ s!"pk = {key.pk}"
    fpRsp.putStrLn $ s!"sk = {key.sk}"
    fpRsp.putStrLn $ s!"ct = {enc.ct}"
    fpRsp.putStrLn $ s!"ss = {ss1}\n"  
  IO.println "Done"