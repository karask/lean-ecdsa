# Project Wycheproof test vectors

Unmodified copies of the secp256k1 ECDSA verification vectors from
[Project Wycheproof](https://github.com/C2SP/wycheproof), `testvectors_v1/`,
commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`:

| File | Signature encoding | Verification mode |
| --- | --- | --- |
| `ecdsa_secp256k1_sha256_test.json` | DER | standard (high-S accepted) |
| `ecdsa_secp256k1_sha256_bitcoin_test.json` | DER | Bitcoin (`requireLowS := true`) |
| `ecdsa_secp256k1_sha256_p1363_test.json` | 64-byte `r ‖ s` | standard |

The vectors are distributed under the Apache License 2.0
(<https://github.com/C2SP/wycheproof/blob/main/LICENSE>).
They are read by `Tests/Wycheproof.lean` when `lake test` runs.
