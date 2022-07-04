# StorageVars

## Usage
In Idris, a programmer declares only the type of a storage var:
```
balance : StorageSpace [Felt] Felt
```
and registers it on the abi:
```
main = abi ["viewEx"] ["balance"]
```

## Implementation
### Frontend
The `abi` call creates
1. the body implementation
```
balance = MkStorageSpace Main.balance_addr
```

2. an external definition with nomangle data for the ABI
```
  public export 
  %nomangle  #"cairo:{ "type"\:"StorageVar", "name"\:"balance"}"#
  %extern balance_addr: Felt
```

### Backend
On the backend, extracts the ABI information from the %nomangle and
1. Creates a StorageVar ABIItem
which leads to the creation of the `ExtFunDef` with tag `@storage_var`



2. ANFtoCairo replaces `AExtPrim` calls to the external balance_addr with invocations of
```STARKNETINTRINSIC res empty (StorageVarAddr "balance") []```

### Codegen
- Generates the following for the `ExtFunDef`
```
@storage_var
def balance() -> ():
end
```

- Generates the following for the StorageVar Intrinsic
```
STARKNETINTRINSIC res empty (StorageVarAddr "balance") []
``