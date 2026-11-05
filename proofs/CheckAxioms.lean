import Secp256k1Proofs

/-! Run with `lake env lean CheckAxioms.lean`: each theorem should depend only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool` from `native_decide` / `bv_decide`). -/

#print axioms Secp256k1Proofs.toW_add
#print axioms Secp256k1Proofs.smulG_correct
#print axioms Secp256k1Proofs.addOrderOf_G
#print axioms Secp256k1Proofs.publicKey_correct
#print axioms Secp256k1Proofs.signWithNonce_verifies
#print axioms Secp256k1Proofs.sign_verifies
#print axioms Secp256k1Proofs.verifyHash_eq_true_iff
#print axioms Secp256k1Proofs.verify_sign
#print axioms Secp256k1Proofs.recover_signRecoverable
