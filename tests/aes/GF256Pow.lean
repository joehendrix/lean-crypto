import Smt

import Crypto.GF2BV

open GF2BVPoly GaloisField2k

set_option smt.solver.kind "z3" in
example (x : GF256) : GF256.pow2 8 x = x := by
  extract_def GF256.pow2

  extract_def mul
  specialize_def GaloisField2k.mul [GF256] blocking [@polyMod, @polyMul]
  conv at GF256.pow2.def =>
    intro k x
    rw [ GaloisField2k.mul.GF256.specialization ]
  save

  extract_def polyMod
  specialize_def GF2BVPoly.polyMod [16, 8]
  save

  extract_def polyMul
  specialize_def GF2BVPoly.polyMul [8, 8]
  save

  conv at GaloisField2k.mul.GF256.def =>
    intro a b
    rw [ GF2BVPoly.polyMul.«8».«8».specialization,
      GF2BVPoly.polyMod.«16».«8».specialization ]

  smt_show [
    GF256.pow2,
    GaloisField2k.mul.GF256,
    GF2BVPoly.polyMul.«8».«8»,
    GF2BVPoly.polyMod.«16».«8»
  ] 
    
  sorry
