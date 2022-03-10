module Main
import Cairo

-- Example data from https://www.cairo-lang.org/docs/hello_starknet/signature_verification.html
publicKey : Felt
publicKey = 1628448741648245036800002906075225705100596136133912895015035902954123957052 

messageHash : TaintedMessage
messageHash = tainted $ pedersenHash 4321 0

signature : (Felt, Felt)
signature = (1225578735933442828068102633747590437426782890965066746429241472187377583468, 3568809569741913715045370357918125425757114920266578211811626257903121825123)

%noinline
main : Cairo ()
main = 
  output (verifySignature messageHash publicKey (fst signature) (snd signature))
