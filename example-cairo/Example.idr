-- Import the Cairo prelude
import Cairo
import Data.List

-- Define a datatype
record Account where
  constructor MkAccount
  number: Felt 
  balance: Felt

-- Read from private input (using inline Cairo)
%foreign 
  """
  code:
  func Main_readFromInput(key) -> (result):
      tempvar result
      %{  
          from starkware.cairo.common.math_utils import as_int
          val = program_input[ids.key]
          ids.result = as_int(val, PRIME) % PRIME
      %}
      return (result)
  end
  """
readFromInput : Felt -> Felt

-- Creates an account based on an index into the JSON array in `input.json`
createAccount : Felt -> Account
createAccount index = MkAccount number balance
  where number : Felt
        number = readFromInput index
        balance : Felt
        balance = readFromInput (index + 1) 

-- List of available accounts (we assume there are 3 accounts)
privateAccounts : List Account
privateAccounts = map createAccount [0,2,4] 

-- Define a function which gets a list of accounts and returns the sum of their balances
sumOfBalances : List Account -> Felt
sumOfBalances accounts = sum (map balance accounts)

-- Computes the hash of the account data (no need to pass the pedersen_ptr)
hashOfAccountData : List Account -> Felt
hashOfAccountData accounts = foldl pedersenHash 3 (foldMap (\a => [a.number, a.balance]) accounts)

-- The main entry point:
-- Computes and outputs the hash of the account data
-- together with the sum of the balances
main : Cairo ()
main = do
  output $ hashOfAccountData privateAccounts
  output $ sumOfBalances privateAccounts