import Crypto.Prim.AES
import Crypto.Random.PRNG
import Crypto.Nat
import Crypto.Range
import Crypto.Vector

-- theorem mul_div_lt {i m n:Nat} : i < m * n → (i/n) < m := by admit

def concatByteVec (v : Vector m (ByteVec n)) : ByteVec (m*n) :=
  let r {i} (p : i < m*n) : 0 < n := sorry
  ByteVec.generate (m*n) (λi => (v.get ⟨i.val / n, Nat.mul_div_lt i.isLt⟩).get (Fin.ofNat' i.val (r i.isLt)))

structure DRBG where
  key : ByteVec (256 / 8)
  v : ByteVec (128 / 8)

instance : Inhabited DRBG := ⟨Inhabited.default, Inhabited.default⟩

@[reducible]
def Seed := ByteVec 48

opaque incrementV (v : ByteVec 16) : ByteVec 16 := Id.run do
  let mut v := v
  for i in range 0 15 do
    let j := 15 - i
    let vj := v.get! j
    if vj = 0xff then
      v := v.set! j 0x00
    else
      v := v.add! j 1
      break
  pure v

opaque aes256CtrDrbgUpdate (key : ByteVec 32) (v0 : ByteVec 16) : ByteVec 48 :=
  let g := Vector.iterate 3 incrementV (incrementV v0)
  concatByteVec (aes256Ecb key <$> g)

opaque randombytesInit (s : Seed) : DRBG :=
  let key := ByteVec.generate 32 (λ_ => 0)
  let v   := ByteVec.generate 16 (λ_ => 0)
  let b := aes256CtrDrbgUpdate key v
  let b := ByteVec.generate _ (λi => b.get i ^^^ s.get i)
  { key := b.extractN 0 32, v := b.extractN 32 16 }

private theorem randomBytesTerminates : ∀ n, n ≥ 16 → n - 16 < n := by
  intros n gt
  have n_pos : 0 < n := by
        cases n with
        | zero =>
          contradiction
        | succ x =>
          exact (Nat.zero_lt_succ _)
  apply Nat.sub_lt n_pos (by decide)

def randombytes3 (key : ByteVec 32) (v : ByteVec 16) (a : ByteArray) (n : Nat)
   : ByteArray × ByteVec 16 :=
  if n == 0 then
    (a, v)
  else
    let v := incrementV v
    let b := aes256Ecb key v
    if h : n ≥ 16 then
      have : n - 16 < n := randomBytesTerminates n ‹_›
      randombytes3 key v (a ++ b.data) (n - 16)
    else
      (a ++ b.data.extractN 0 n, v)

--theorem randomBytes3_size2 (key) (v) (a) (n:Nat)
--    : (randombytes3 key v a n).1.size = a.size + n := by admit

theorem randomBytes3_size (key) (v) (a) (n:Nat)
    : (randombytes3 key v a n).1.size = n := by
  admit

namespace DRBG

opaque randombytes (rbg : DRBG) (n : Nat) : ByteVec n × DRBG :=
  let key := rbg.key
  let v := rbg.v
  let p := randombytes3 key v (ByteArray.mkEmpty n) n
  let pr : p.1.size = n := randomBytes3_size key v (ByteArray.mkEmpty n) n
  let b := aes256CtrDrbgUpdate key p.2
  let rbg := { key := b.extractN 0 32, v := b.extractN 32 16 }
  (⟨p.1, pr⟩, rbg)

instance : PRNG DRBG := ⟨DRBG.randombytes⟩

end DRBG