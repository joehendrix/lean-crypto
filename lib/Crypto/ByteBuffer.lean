import Crypto.ByteArray
--import Crypto.UInt8

structure ByteBuffer where
  data : ByteArray
  deriving DecidableEq

namespace ByteBuffer

/-
protected def toString (a:ByteBuffer) : String :=
  a.data.foldl (λs b => s ++ b.toHex) ""

instance : ToString ByteBuffer := ⟨ByteBuffer.toString⟩
-/

protected def fromList (l:List UInt8) : ByteBuffer := ⟨fromList l⟩

protected def append : ByteBuffer → ByteBuffer → ByteBuffer
| ⟨x⟩, ⟨y⟩ => ⟨x ++ y⟩

instance  : Append ByteBuffer where
  append := ByteBuffer.append

end ByteBuffer

syntax "#b[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#b[ $elems,* ]) => `(ByteBuffer.fromList [ $elems,* ])
