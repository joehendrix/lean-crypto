#!/bin/bash
set -ex
lake build
mkdir -p tmp
DYLD_LIBRARY_PATH="deps/openssl-1.1.1l" ./build/bin/ffi 8> tmp/kat_kem.req 9> tmp/kat_kem.rsp
cmp --silent tests/kat_kem.req.golden tmp/kat_kem.req || echo "Req files are different"
cmp --silent tests/kat_kem.rsp.golden tmp/kat_kem.rsp || echo "Rsp files are different"