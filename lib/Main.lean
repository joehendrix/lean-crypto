import Ffi

--theorem add_le_add {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
--  Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)

--theorem add_lt_add {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
--  Nat.lt_trans (Nat.add_lt_add_right h₁ c) (Nat.add_lt_add_left h₂ b)

theorem add_le_implies_le_rhs {j k : Nat} : ∀(i : Nat), (h : i + j ≤ k) → j ≤ k
| Nat.succ i, h => add_le_implies_le_rhs i (Nat.le_of_succ_le (Nat.succ_add i j ▸ h))
| 0, h => Nat.zero_add j ▸ h

@[inline] def forFinM {m} [Monad m] (n : Nat) (f : Fin n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ (i:Nat), (p : i ≤ n) → m Unit 
    | 0, p => pure ()
    | i+1, p => do
       let q : n-(i+1) < n := Nat.sub_lt (add_le_implies_le_rhs i p) (Nat.zero_lt_succ _)
       f ⟨n-(i+1), q⟩; loop i (Nat.le_of_succ_le p)
  loop n Nat.le.refl

def main : IO Unit := do
  let seedArray := initSeed ()
  let fpReq ← openByFd 8;
--  let fpReq ← IO.getStdout
  forFinM seedArray.size $ λi => do
    fpReq.putStrLn $ "count = " ++ toString i
    fpReq.putStrLn $ "seed = " ++ toString (seedArray.get i)
    fpReq.putStrLn "pk ="
    fpReq.putStrLn "sk ="
    fpReq.putStrLn "ct ="
    fpReq.putStrLn "ss =\n"    
  let fpRsp ← openByFd 9;
--  let fpRsp ← IO.getStdout
  fpRsp.putStrLn $ "# kem/" ++ Mceliece348864Ref.name ++"\n"
  forFinM seedArray.size $ λi => do
    fpRsp.putStrLn $ "count = " ++ toString i
    let seed := seedArray.get i
    fpRsp.putStrLn $ "seed = " ++ toString seed
    let key ← mkCryptoKemKeypair seed
    fpRsp.putStrLn $ "pk = " ++ toString key.pk
    fpRsp.putStrLn $ "sk = " ++ toString key.sk
    let enc ← mkCryptoKemEnc key.pk
    fpRsp.putStrLn $ "ct = " ++ toString enc.ct
    let ss1 ← cryptoKemDec enc.ct key.sk
    fpRsp.putStrLn $ "ss = " ++ toString ss1 ++ "\n"  
    if enc.ss ≠ ss1 then
      throw $ IO.userError "crypto_kem_dec returned bad 'ss' value"
  IO.println "Done"