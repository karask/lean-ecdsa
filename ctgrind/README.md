# ctgrind: constant-time check of the compiled code

Runs every secret-dependent operation of the library under
[valgrind](https://valgrind.org/)'s memcheck, with the private key and nonce
bytes marked as *undefined*. memcheck then reports any conditional branch or
memory address in the machine code that depends on them. This covers code
introduced by the Lean compiler, the C compiler and the Lean runtime, not
just the Lean source. Outputs that are public by design (the signature, the
public key, whether a scalar is in range) are marked defined before they are
compared. This is the technique of libsecp256k1's `ctime_tests`.

```sh
sudo apt-get install valgrind   # or your platform's equivalent
./run.sh
```

`run.sh` makes two runs:

1. **The constant-time operations**, which must produce no memcheck errors:
   - public key derivation `d • G`, including the conversion to affine coordinates
   - `k • P` for a public point `P`
   - the ECDSA signing core: `R = k • G`, `r`, `s = k⁻¹(e + r·d)`, the recovery id and the success flag
   - RFC 6979 nonce generation keyed by the private key, including the retry path
   - the range check `k < n`
   - scalar and field arithmetic, including inversion
2. **A positive control** (`--control`), which must produce errors. It runs the variable-time reference arithmetic on the same secrets, and shows that the check detects secret-dependent branches.

This package is separate from the library so that the library has no C or
valgrind dependency. Results apply to the platform, toolchain and compiler
flags the check is run with.

The library passes secret-derived values to `Secp256k1.CT.declassify` where
they become public. Code after those points is outside this check, and is
meant to be reviewed by hand (`grep -rn declassify Secp256k1/`).
