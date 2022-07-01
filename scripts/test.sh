#!/bin/bash
set -ex
lake update
lake build
mkdir -p tmp
./build/bin/crypto tmp/kat_kem.req tmp/kat_kem.rsp
cmp --silent tests/kat_kem.req.golden tmp/kat_kem.req || echo "Req files are different"
cmp --silent tests/kat_kem.rsp.golden tmp/kat_kem.rsp || echo "Rsp files are different"
