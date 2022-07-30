#!/bin/bash
set -ex
lake update
lake build
mkdir -p tmp

./build/bin/crypto tmp/kat_kem.req tmp/kat_kem.rsp
cmp --silent tests/kat_kem.req.golden tmp/kat_kem.req || echo "Req files are different"
cmp --silent tests/kat_kem.rsp.golden tmp/kat_kem.rsp || echo "Rsp files are different"

lake env lean \
  --load-dynlib=libSmt-Tactic-WHNFConfigurable.so \
  --load-dynlib=libSmt-Tactic-WHNFConfigurableRef.so \
  --load-dynlib=libSmt-Tactic-WHNFSmt.so \
  tests/aes/GF256Pow.lean > tmp/GF256Pow.produced
diff --text --unified --strip-trailing-cr tests/aes/GF256Pow.expected tmp/GF256Pow.produced

lake env lean \
  --load-dynlib=libSmt-Tactic-WHNFConfigurable.so \
  --load-dynlib=libSmt-Tactic-WHNFConfigurableRef.so \
  --load-dynlib=libSmt-Tactic-WHNFSmt.so \
  tests/aes/SBox.lean > tmp/SBox.produced
diff --text --unified --strip-trailing-cr tests/aes/SBox.expected tmp/SBox.produced
