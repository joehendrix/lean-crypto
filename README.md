# Cryptography in Lean 4

This repo is intended to provide a comprehensive collection of specifications
of cryptographic algorithms in Lean 4.  Each algorithm will have a complete,
executable specification along with test vectors for some validation that the
algorithm is correctly specified.

The repositiory currently contains a complete specification of the
[Classic McEliece](https://classic.mceliece.org/) algorithm on the
``kem/mceliece348864`` parameter set.  It has been
derived from the [Nist Round 3](https://classic.mceliece.org/nist.html)
submission files.  Our [continuous integration](https://github.com/joehendrix/lean-crypto/actions)
validates that the Lean specification produces the same known-answer tests
as the C reference implementation.

The cryptographic library also links in [OpenSSL](https://www.openssl.org/)
and [libkeccak](https://codeberg.org/maandree/libkeccak) so
that we can invoke fast C implementations of AES and SHAKE respectively.

This repository also includes experiments aimed at mapping the cryptographic
specifications into SMT so that we can take advantage of automated constraint
solving to reason about cryptographic specificiations including equivalence
checking and checking correctness properties of specifications.

Plans for the Future
====================

This repository is still in its early stages.  Our next plans are to:

* Write reference specifications of AES and SHAKE that can be validated
  against known answer tests.
* Complete specifications of other Classic Mceliece parameter sets.
