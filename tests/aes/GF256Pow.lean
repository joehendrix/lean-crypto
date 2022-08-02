import Crypto.GF2BV

import Smt

open GF256 GF2BVPoly

set_option smt.solver.kind "z3" in
example (x : GF256) : pow 256 x = x := by
  extract_def pow
  extract_def mul
  extract_def polyMod
  extract_def polyMul
  save

  specialize_def GF2BVPoly.polyMod [16, 8]
  save

  specialize_def GF2BVPoly.polyMul [8, 8]
  save

  simp (config := {zeta := false}) only
    [ GF2BVPoly.polyMul.«8».«8».specialization
    , GF2BVPoly.polyMod.«16».«8».specialization
    ]
    at GF256.mul.def
  save

  smt_show [
    GF256,
    GF256.irreducible,
    GF256.mul,
    GF256.pow.sq,
    GF256.pow,
    GF2BVPoly.polyMod.«16».«8»,
    GF2BVPoly.polyMul.«8».«8»
   ]

  sorry
