#!/bin/bash
set -ex
lake update
lake build Crypto
lake build Smt:shared
mkdir -p tmp

lake build mceliece
./build/bin/mceliece tmp/kat_kem.req tmp/kat_kem.rsp
cmp --silent tests/mceliece/kat_kem.req.golden tmp/kat_kem.req || echo "Req files are different"
cmp --silent tests/mceliece/kat_kem.rsp.golden tmp/kat_kem.rsp || echo "Rsp files are different"

lake run runTest tests/aes/GF256Pow.lean
lake run runTest tests/aes/SBox.lean