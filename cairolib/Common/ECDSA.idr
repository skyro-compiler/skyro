module Common.ECDSA

import Common

-- An unverified message
-- This is temporary API
export
data TaintedMessage = MkTaintedMessage Felt

export
tainted : Felt -> TaintedMessage
tainted = MkTaintedMessage

-- Returns the verified message
-- This function is not safe: If the returned value is ignored, Idris is free to eliminate the call to this function altogether.
export %inline
%foreign 
    "imports:starkware.cairo.common.cairo_builtins SignatureBuiltin, starkware.cairo.common.signature verify_ecdsa_signature"
    "linear_implicits:ecdsa_ptr"
    """
    code:
    func Common_ECDSA_verifySignature(ecdsa_ptr, message, public_key, signature_r, signature_s) -> (message, ecdsa_ptr):
       let ecdsa_ptr_ = cast(ecdsa_ptr, SignatureBuiltin*)
       verify_ecdsa_signature{ecdsa_ptr=ecdsa_ptr_}(message, public_key, signature_r, signature_s)
       return (message, cast(ecdsa_ptr_, felt))
    end
    """
verifySignature : (message: TaintedMessage) -> (public_key: Felt) -> (signature_r: Felt) -> (signature_s: Felt) -> Felt
