module Starknet.Integration.ABI

import public Language.Reflection

%language ElabReflection

cairoName : Name
cairoName = NS (MkNS (["Common"])) (UN (Basic "Cairo"))

public export
data ABIEntryType = View | External | Constructor | L1Handler

record NamedElem where
  constructor MkNamedElem
  name : Maybe Name
  type : TTImp

record Constr where
  constructor MkConstr 
  name: Name
  tag: Int
  args: List NamedElem

record TypeDesc where 
  constructor MkTypeDesc 
  name: Name 
  tag: Int 
  constructors : List Constr

-- Todo change name to something else
-- is export neccesary
public export
record AbiEntry where
  constructor MkAbiEntry
  abstract : Bool
  name : Name
  entryType : ABIEntryType
  inputs : List NamedElem
  output : NamedElem

public export %spec sep, ss -- This is required to ensure that the string is fully evaluated.
separate : (sep:String) -> (ss:List String) -> String
separate _ [] = ""
separate _ [s] = s
separate sep (s::ss) = s ++ sep ++ separate sep ss


public export
showName : (n:Name) -> String 
showName (NS (MkNS ns) name) = separate "." (reverse ns) ++ "." ++ show name
showName name = show name

boolToJSON : Bool -> String
boolToJSON True = "true"
boolToJSON False = "false"

mutual
    collectNameAndArgs : (tp: TTImp) -> (String, List String)
    collectNameAndArgs (IVar _ name) = (showName name, Nil)
    collectNameAndArgs (IApp _ f a) = let (n,args) = collectNameAndArgs f in (n, args ++ [namedElemTypeToString a])
    collectNameAndArgs _ = ("Illegal type in NamedElem type", Nil)

    public export
    namedElemTypeToString : (tp: TTImp) -> String
    namedElemTypeToString (IPrimVal _ (PrT IntType)) = #"{"name":"$Primitive.Int", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Int8Type)) = #"{"name":"$Primitive.Int8", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Int16Type)) = #"{"name":"$Primitive.Int16", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Int32Type)) = #"{"name":"$Primitive.Int32", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Int64Type)) = #"{"name":"$Primitive.Int64", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Bits8Type)) = #"{"name":"$Primitive.Bits8", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Bits16Type)) = #"{"name":"$Primitive.Bits16", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Bits32Type)) = #"{"name":"$Primitive.Bits32", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT Bits64Type)) = #"{"name":"$Primitive.Bits64", "args":[] }"#
    namedElemTypeToString (IPrimVal _ (PrT IntegerType)) = #"{"name":"$Primitive.Integer", "args":[] }"#
    namedElemTypeToString (IType _ ) = #"{"name":"$Special.Type", "args":[] }"#
    namedElemTypeToString (IVar _ name) = #"{"name":"\#{showName name}", "args":[] }"#
    namedElemTypeToString tp@(IApp _ f a) = let (n,args) = collectNameAndArgs tp in #"{"name":"\#{n}", "args":[\#{separate "," args}] }"#

    namedElemTypeToString (IPrimVal _ _) = #"{"Illegal type in NamedElem type: IPrimVal"}"#
    namedElemTypeToString (IPi _ _ _ _ _ _ ) = #"{"Illegal type in NamedElem type: IPi"}"#
    namedElemTypeToString (ILam _ _ _ _ _ _ ) = #"{"Illegal type in NamedElem type: ILam"}"#
    namedElemTypeToString (ILet _ _ _ _ _ _ _ ) = #"{"Illegal type in NamedElem type: ILet"}"#
    namedElemTypeToString (ICase _ _ _ _ ) = #"{"Illegal type in NamedElem type: ICase"}"#
    namedElemTypeToString (ILocal _ _ _ ) = #"{"Illegal type in NamedElem type: ILocal"}"#
    namedElemTypeToString (IUpdate _ _ _ ) = #"{"Illegal type in NamedElem type: IUpdate"}"#
    namedElemTypeToString (INamedApp _ _ _ _ ) = #"{"Illegal type in NamedElem type: INamedApp"}"#
    namedElemTypeToString (IAutoApp _ _ _ ) = #"{"Illegal type in NamedElem type: IAutoApp"}"#
    namedElemTypeToString (IWithApp _ _ _ ) = #"{"Illegal type in NamedElem type: IWithApp"}"#
    namedElemTypeToString (ISearch _ _ ) = #"{"Illegal type in NamedElem type: ISearch"}"#
    namedElemTypeToString (IAlternative _ _ _ ) = #"{"Illegal type in NamedElem type: IAlternative"}"#
    namedElemTypeToString (IRewrite _ _ _ ) = #"{"Illegal type in NamedElem type: IRewrite"}"#
    namedElemTypeToString (IBindHere _ _ _ ) = #"{"Illegal type in NamedElem type: IBindHere"}"#
    namedElemTypeToString (IBindVar _ _ ) = #"{"Illegal type in NamedElem type: IBindVar"}"#
    namedElemTypeToString (IAs _ _ _ _ _ ) = #"{"Illegal type in NamedElem type: IAs"}"#
    namedElemTypeToString (IMustUnify _ _ _ ) = #"{"Illegal type in NamedElem type: IMustUnify"}"#
    namedElemTypeToString (IDelayed _ _ _ ) = #"{"Illegal type in NamedElem type: IDelayed"}"#
    namedElemTypeToString (IDelay _ _ ) = #"{"Illegal type in NamedElem type: IDelay"}"#
    namedElemTypeToString (IForce _ _ ) = #"{"Illegal type in NamedElem type: IForce"}"#
    namedElemTypeToString (IQuote _ _ ) = #"{"Illegal type in NamedElem type: IQuote"}"#
    namedElemTypeToString (IQuoteName _ _ ) = #"{"Illegal type in NamedElem type: IQuoteName"}"#
    namedElemTypeToString (IQuoteDecl _ _ ) = #"{"Illegal type in NamedElem type: IQuoteDecl"}"#
    namedElemTypeToString (IUnquote _ _ ) = #"{"Illegal type in NamedElem type: IUnquote"}"#
    namedElemTypeToString (IHole _ _ ) = #"{"Illegal type in NamedElem type: IHole"}"#
    namedElemTypeToString (Implicit _ _ ) = #"{"Illegal type in NamedElem type: Implicit"}"#
    namedElemTypeToString (IWithUnambigNames _ _ _ ) = #"{"Illegal type in NamedElem type: IWithUnambigNames"}"#

-- checkPrim fc IntType = (PrimVal fc IntType, ttype fc)
-- checkPrim fc Int8Type = (PrimVal fc Int8Type, ttype fc)
-- checkPrim fc Int16Type = (PrimVal fc Int16Type, ttype fc)
-- checkPrim fc Int32Type = (PrimVal fc Int32Type, ttype fc)
-- checkPrim fc Int64Type = (PrimVal fc Int64Type, ttype fc)
-- checkPrim fc IntegerType = (PrimVal fc IntegerType, ttype fc)
-- checkPrim fc Bits8Type = (PrimVal fc Bits8Type, ttype fc)
-- checkPrim fc Bits16Type = (PrimVal fc Bits16Type, ttype fc)
-- checkPrim fc Bits32Type = (PrimVal fc Bits32Type, ttype fc)
-- checkPrim fc Bits64Type = (PrimVal fc Bits64Type, ttype fc)
-- checkPrim fc StringType = (PrimVal fc StringType, ttype fc)
-- checkPrim fc CharType = (PrimVal fc CharType, ttype fc)
-- checkPrim fc DoubleType = (PrimVal fc DoubleType, ttype fc)
-- checkPrim fc WorldType = (PrimVal fc WorldType, ttype fc)


%inline
elemToJSON : NamedElem -> String
elemToJSON (MkNamedElem name tp) = #"{ "name":"\#{maybe "" showName name}", "type":\#{namedElemTypeToString tp} }"#

%inline
abiEntryToJSON : AbiEntry -> String
abiEntryToJSON (MkAbiEntry abstract fName entryTp inputs output) = 
  #"{"abstract":\#{boolToJSON abstract}, "type":"\#{entryTypeToString entryTp}", "name":"\#{showName fName}", "inputs":[\#{separate "," (map elemToJSON inputs)}], "output":\#{elemToJSON output}}"#
  where entryTypeToString : ABIEntryType -> String
        entryTypeToString View = "View"
        entryTypeToString External = "External"
        entryTypeToString Constructor = "Constructor"
        entryTypeToString L1Handler = "L1Handler"


%inline
constrToJSON : Constr -> String
constrToJSON (MkConstr name tag elems) = 
  #"{ "name":"\#{showName name}", "tag":\#{show tag}, "elems":[\#{separate "," (map elemToJSON elems)}] }"#


typeDescToJSON : TypeDesc -> String
typeDescToJSON (MkTypeDesc name tag constrs) = 
  #"{ "type":"Type", "name":"\#{showName name}", "constructors":[\#{separate "," (map constrToJSON constrs)}] }"#


%inline
nameToAbiType : Name -> Maybe ABIEntryType
nameToAbiType (NS _ (UN (Basic "View"))) = Just View
nameToAbiType (NS _ (UN (Basic "External"))) = Just External
nameToAbiType (NS _ (UN (Basic "Constructor"))) = Just Constructor
nameToAbiType (NS _ (UN (Basic "L1Handler"))) = Just L1Handler
nameToAbiType _ = Nothing


-- Finds the first `f m =>` and uses `f` to determine the ABIEntryType
-- %inline
findAbiEntryType : TTImp -> Maybe ABIEntryType
findAbiEntryType (IPi _ _ AutoImplicit _ (IApp _ (IVar _ constraintName) m) retType) = nameToAbiType constraintName
findAbiEntryType (IPi _ _ _ _ _ retType) = findAbiEntryType retType
findAbiEntryType _ = Nothing

-- Returns all type Names from a signature
collectTypeNames : (tp: TTImp) -> List Name
collectTypeNames (IPi _ c ExplicitArg _ argType retType) = collectTypeNames argType ++ collectTypeNames retType
collectTypeNames (IVar _ name) = [name]
collectTypeNames (IApp _ f a) = collectTypeNames f ++ collectTypeNames a
collectTypeNames t = []

-- Returns all type Names from a constructor
collectCtrFieldNames : Name -> Elab (List Name)
collectCtrFieldNames consName = do
    [(name, tp)] <- getType consName
        | _ => failAt EmptyFC "consDesc"
    [(_, MkNameInfo $ DataCon _ _)] <- getInfo name
        | _ => failAt EmptyFC ((show name) ++ " is not a data constructor")
    pure $ collectTypeNames tp

-- Returns all field type Names from a data type
collectDataFieldTypeNames : Name -> Elab (List Name)
collectDataFieldTypeNames tpName = do
    [(_, MkNameInfo $ TyCon _ _)] <- getInfo tpName
        | _ => failAt EmptyFC ((show tpName) ++ " is not a type constructor")
    consNames <- getCons tpName
    map concat $ traverse collectCtrFieldNames consNames

collectAllTypeNamesRec : List Name -> List Name -> Elab (List Name)
collectAllTypeNamesRec processedNames [] = pure processedNames
collectAllTypeNamesRec processedNames (newName::rest) = if elem (show newName) (map show processedNames)
    then collectAllTypeNamesRec processedNames rest
    else do
        fieldNames <- collectDataFieldTypeNames newName
        collectAllTypeNamesRec (newName::processedNames) (fieldNames ++ rest)

collectAllTypeNames : List TTImp -> Elab (List Name)
collectAllTypeNames newTypes = collectAllTypeNamesRec [] (concatMap collectTypeNames newTypes)


-- Creates the type for a wrapper function
-- input: View m => Felt -> Felt -> m Felt
-- output: Felt -> Felt -> Cairo Felt

-- todo: rename this to checkedWrapper....

wrapperArgType : (tp: TTImp) -> Elab TTImp
wrapperArgType (IVar _ name) = pure $ IVar EmptyFC name -- todo: ensure name is not a function (if even possible)
wrapperArgType (IApp _ f a) = pure $ IApp EmptyFC !(wrapperArgType f) !(wrapperArgType a)
wrapperArgType (IPrimVal _ (PrT typ)) = pure $ IPrimVal EmptyFC (PrT typ)
wrapperArgType t = do
                 logTerm "ABI" 0 "Unsupported ABI argument type" t
                 failAt (getFC t) "Unsupported ABI function argument"

wrapperRetType : Name -> (tp: TTImp) -> Elab TTImp
wrapperRetType m1 t@(IApp _ (IVar _ m2) a) = if show m1 == show m2
    then pure $ (IApp EmptyFC (IVar EmptyFC cairoName) !(wrapperArgType a))
    else do
       logTerm "ABI" 0 "Unsupported ABI return type" t
       failAt (getFC t) ("ABI functions must return a 'm t' where m is constrained by View m, External m, ...")

-- wrapperRetType _ t@(IPi _ _ _ _ (IType _) retType) = do
--    logTerm "ABI" 0 "Unsupported ABI return type" t
--    failAt (getFC t) "ABI function do not support type parameters"

wrapperRetType m (IPi _ c ExplicitArg n argType retType) = pure $ IPi EmptyFC c ExplicitArg n !(wrapperArgType argType) !(wrapperRetType m retType)
wrapperRetType _ t = do
                 logTerm "ABI" 0 "Unsupported ABI return type" t
                 failAt (getFC t) "ABI function returns must be in a View, External, ... context and type parameters and implicits are not supported"


-- Assumes an implicit `m` at the start as in:
-- {m:Type} -> External m => ... at the start
wrapperType : Maybe Name -> (tp: TTImp) -> Elab TTImp
wrapperType Nothing (IPi _ _ ImplicitArg name _ retType) = wrapperType name retType
wrapperType (Just m1) t@(IPi _ _ AutoImplicit _ (IApp _ (IVar _ constraintName) (IVar _ m2)) retType) = if show m1 == show m2
    then wrapperRetType m1 retType
    else do
        logTerm "ABI" 0 "Illegal ABI function header" t
        failAt (getFC t) ("ABI functions must start with View m, External m, ...")

wrapperType _ t = do
  logTerm "ABI" 0 "Unsupported ABI function type" t
  failAt (getFC t) "ABI functions must start with a Autoimplicit View, External, ... "


abiFnType : (tp: TTImp) -> Elab (List NamedElem, NamedElem)
abiFnType (IPi _ _ ExplicitArg mn argType (IApp _ m ret)) = pure ([MkNamedElem mn argType], MkNamedElem (Just $ UN $ Basic "ret") ret)
abiFnType (IPi _ _ ExplicitArg mn argType retType) = pure $ mapFst (MkNamedElem mn argType ::) !(abiFnType retType)
abiFnType (IApp _ m ret) = pure ([], MkNamedElem (Just $ UN $ Basic "ret") ret)
abiFnType t = do
  logTerm "Illegal signature type" 0 "type" t
  fail "Illegal signature type!"


-- Creates the name for a wrapper function by appending '
wrapperFunctionName : (n: Name) -> Elab Name
wrapperFunctionName (NS _ (UN (Basic n))) = pure $ NS (MkNS ["Wrapper","ABI","Main"]) (UN $ Basic n)
wrapperFunctionName other = assert_total $ idris_crash ("Bad name: " ++ show other)

-- Helper for name Resolution
-- Todo: if it has "." in it use as fully qualified
resolveName : String -> Elab Name
resolveName name = inCurrentNS (UN $ Basic name)

-- Takes a function name and type and creates a wrapper
-- viewEx : View m => Felt -> Felt -> m Felt
--
-- %nomangle "cairo:viewEx'|External|addr:Common.Felt.Felt->value:Common.Felt.Felt->Common.Cairo Builtin.Unit"
-- viewEx' : Felt -> Felt -> Cairo Felt
-- Returns the name and type of the wrapper function
public export
processFunction : String -> Elab AbiEntry
processFunction fName = do
  name <- resolveName fName
  [(fnName, tp)] <- getType name
    | [] => failAt EmptyFC ("Unknown function in entry point: " ++ fName)
    | _ => failAt EmptyFC ("Ambiguous function in entry point: " ++ fName)

  (Just entryTp) <- pure $ findAbiEntryType tp
    | _ => do logTerm "Unknown ABI type!" 0 "" tp
              failAt EmptyFC "Unknown ABI type! Use one of: View, External, Constructor, L1Handler"

  wName <- wrapperFunctionName fnName
  wType <- wrapperType Nothing tp
  (inputs, output) <- abiFnType wType
  let abiEntry = MkAbiEntry False wName entryTp inputs output

  declare [
    IClaim EmptyFC MW Export [NoMangle (Just $ BackendNames [("cairo",abiEntryToJSON abiEntry)])] (MkTy EmptyFC EmptyFC wName wType),
    IDef EmptyFC wName [PatClause EmptyFC (IVar EmptyFC wName) (IVar EmptyFC fnName)]]

  pure abiEntry


namedElems : TTImp -> List NamedElem
namedElems (IPi _ _ _ n argT restT) = MkNamedElem n argT :: namedElems restT
namedElems rest = Nil

-- Creates a constructor descriptor given a constructor name
consDesc : Name -> Elab Constr
consDesc consName = do
  [(name, tp)] <- getType consName
               | _ => failAt EmptyFC "consDesc"
  [(_, MkNameInfo $ DataCon tag arity)] <- getInfo name
    | _ => failAt EmptyFC ((show name) ++ " is not a data constructor")
  pure $ MkConstr consName tag (namedElems tp)

-- Creates a type descriptor given a type name
typeDesc : Name -> Elab TypeDesc
typeDesc tpName = do
  [(_, MkNameInfo $ TyCon tag arity)] <- getInfo tpName
    | _ => failAt EmptyFC ((show tpName) ++ " is not a type constructor")
  consNames <- getCons tpName
  pure $ MkTypeDesc tpName tag !(traverse consDesc consNames)


-- Relocates the given name into the current namespace and appends a '
-- Type declarations are located in the current namespace to ensure,
-- that there are no collisions between type declarations which are
-- generated by `abi` with those which are generated by `contract_interface`
%spec n
typeDeclName : (n: Name) -> Elab Name
typeDeclName (NS _ (UN (Basic n))) = inCurrentNS (UN $ Basic (n ++ "'"))
typeDeclName other = assert_total $ idris_crash ("Bad name: " ++ show other)

-- Generates a declaration for the given type name
-- Input: Main.RecType
--
-- Declaration:
-- %nomangle "Struct;Main.RecType;Main.MkRec,0,valA:Common.Felt.Felt,valB:Common.Felt.Felt"
-- RecType' : Unit
-- RecType' = MkUnit
declareType : Name -> Elab (Maybe Name) 
declareType tpName = do
  tpDesc@(MkTypeDesc _ _ (_::_)) <- typeDesc tpName 
    | _ => pure Nothing -- Ignore types without constructors
  descName <- typeDeclName tpName
  declare [ IClaim EmptyFC MW Public [NoMangle (Just (BackendNames [("cairo",typeDescToJSON tpDesc)]))] (MkTy EmptyFC EmptyFC descName (IVar EmptyFC (UN (Basic "Unit")))),
            IDef EmptyFC descName [PatClause EmptyFC (IVar EmptyFC descName) (IVar EmptyFC (UN (Basic "MkUnit")))]]
  pure $ Just descName

-- Collects all required types and generates a declaration for each type in the ABI entries
declareTypes : List AbiEntry -> Elab (List Name)
declareTypes entries = do
    allNames <- collectAllTypeNames allTypes
    map catMaybes $ traverse declareType allNames
  where allEntries : List NamedElem
        allEntries = concatMap inputs entries ++ map output entries
        allTypes : List TTImp
        allTypes = map type allEntries

{-
namespace StorageVar -- (mit Dollar in Name)
  public export 
  %nomangle  #"cairo:{ "type":"StorageVar", "name":"balance"}"#
  %extern balance: Felt

  WARNING: The order of NoMangle ExternFn matters!
-}
processStorageVar : String -> Elab Name
processStorageVar sv = do
  name <- resolveName sv
  [(svName, tp)] <- getType name
                 | [] => failAt EmptyFC ("Unknown storage var in entry point: " ++ sv)
                 | _ => failAt EmptyFC ("Ambiguous storage var in entry point: " ++ sv)
  externName <- inCurrentNS (UN $ Basic (sv ++ "_addr")) 
  -- This needs to end in "_addr" because because calls to externals ending in "_addr" are replaced by 
  -- STARKNET_INTRINSIC (StorageVar name)
  
  -- check type
  -- NS (MkNS ["StorageVar"]) (UN $ Basic sv)
  declare [ IClaim EmptyFC MW Public [NoInline, NoMangle (Just (BackendNames [("cairo",#"{ "type":"StorageVar", "name":"\#{sv}"}"#)])), ExternFn] (MkTy EmptyFC EmptyFC externName (IVar EmptyFC (UN (Basic "Felt")))) ]
  
  --declare `[balance = MkStorageSpace balance_addr ]
  --declare [IDef EmptyFC svName [PatClause EmptyFC (IVar EmptyFC svName) `(MkStorageSpace ~(IVar EmptyFC externName))]]

  --declare `[balance = fromStorageAddr balance_addr ]
  declare [IDef EmptyFC svName [PatClause EmptyFC (IVar EmptyFC svName) `(fromStorageAddr ~(IVar EmptyFC externName))]]
  pure externName

{-
myEvent : EventDesc [Felt] [Felt, Felt]
--

myEvent = MkEventDesc emptySegment emptySegment

myEvent_event
-}
processEvent : String -> Elab Name
processEvent ev = do 
  name <- resolveName ev
  [(evName, tp)] <- getType name
                 | [] => failAt EmptyFC ("Unknown event in entry point: " ++ ev)
                 | _ => failAt EmptyFC ("Ambiguous event in entry point: " ++ ev)
  externName <- inCurrentNS (UN $ Basic (ev ++ "_event"))
  declare [IClaim EmptyFC MW Public [NoInline, NoMangle (Just (BackendNames [("cairo",#"{ "type":"Event", "name":"\#{ev}"}"#)])), ExternFn] (MkTy EmptyFC EmptyFC externName (IVar EmptyFC (UN (Basic "Felt")))) ]

  -- declare `[myEvent = MkEventDesc (singletonSegment myEvent_event) emptySegment ]
  -- declare [IDef EmptyFC evName [PatClause EmptyFC (IVar EmptyFC evName) `(MkEventDesc (singletonSegment ~(IVar EmptyFC externName)) emptySegment)]]

  -- declare `[myEvent = fromEventId myEvent_event) ]
  declare [IDef EmptyFC evName [PatClause EmptyFC (IVar EmptyFC evName) `(fromEventId ~(IVar EmptyFC externName))]]
  pure externName

-- Declares wrapper functions and generates the ABI description string.
public export %macro
abi : {default [] functions : List String} 
   -> {default [] storageVars : List String} 
   -> {default [] events : List String} 
   -> Elab String
abi {functions} {storageVars} {events} = do
  eventNames <- traverse processEvent events
  svarNames <- traverse processStorageVar storageVars
  entries <- traverse processFunction functions
  typeNames <- declareTypes entries
  let wrapperNames = typeNames ++ map (.name) entries
  let wrapperNamesString = map showName (wrapperNames ++ svarNames ++ eventNames)
  pure (separate ";" wrapperNamesString)




-- in: a -> b -> Cairo c
-- out: a -> b -> Segment
decoderType : TTImp -> Elab TTImp
decoderType (IPi fc cnt ExplicitArg name argTp rest) = (decoderType rest)
decoderType (IApp _ c target) = 
  pure $ IPi EmptyFC MW ExplicitArg Nothing (IVar EmptyFC (UN (Basic "Segment"))) target
decoderType tp = do 
  logTerm "Unable to create encoder type!" 0 "" tp
  failAt EmptyFC "Unable to create encoder type!"


-- in: a -> b -> Cairo c
-- out: a -> b -> Segment
encoderType : TTImp -> Elab TTImp
encoderType (IPi fc cnt ExplicitArg name argTp rest) = pure $ IPi fc cnt ExplicitArg name argTp !(encoderType rest)
encoderType (IApp _ _ _) = pure $ IVar EmptyFC (UN (Basic "Segment"))
encoderType tp = do 
  logTerm "Unable to create encoder type!" 0 "" tp
  failAt EmptyFC "Unable to create encoder type!"


{-
%extern %nomangle {abstract function param types, result type (used for encoder generation)}
fn_selector : Felt
fn_param_decoder : T1 -> T2 -> Segement
fn_result_decoder : Segment -> T
-}
-- Namespace: (NS (MkNS ([ns])) (UN (Basic (name ++ "_selector"))))
contractFunction : String -> Elab AbiEntry
contractFunction fName = do
  name <- resolveName fName
  [(fnName, tp)] <- getType name
    | [] => failAt EmptyFC ("Unknown function in entry point: " ++ fName)
    | _ => failAt EmptyFC ("Ambiguous function in entry point: " ++ fName)

  (Just entryTp) <- pure $ findAbiEntryType tp
    | _ => do logTerm "Unknown ABI type!" 0 "" tp
              failAt EmptyFC "Unknown ABI type! Use one of: View, External, Constructor, L1Handler"

              failAt EmptyFC "Unknown ABI type! Use one of: View, External"
  wType <- wrapperType Nothing tp
  (inputs, output) <- abiFnType wType

  selectorName <- inCurrentNS (UN $ Basic (fName ++ "_selector")) 
  let abiEntry = MkAbiEntry True selectorName entryTp inputs output

  baseName <- inCurrentNS (UN $ Basic fName)
  let abstEntry = MkAbiEntry True baseName entryTp inputs output
  declare [ IClaim EmptyFC MW Public [NoInline, NoMangle (Just $ BackendNames [("cairo",abiEntryToJSON abstEntry)]), ExternFn] (MkTy EmptyFC EmptyFC selectorName (IVar EmptyFC (UN (Basic "Felt")))) ]

  encoderName <- inCurrentNS (UN $ Basic (fName ++ "_encodeParams")) 
  encType <- encoderType wType
  declare [ IClaim EmptyFC MW Public [NoInline,  ExternFn] (MkTy EmptyFC EmptyFC encoderName encType) ]

  --todo: compute correct type: Segment -> Tr
  decoderName <- inCurrentNS (UN $ Basic (fName ++ "_decodeResult")) 
  decType <- decoderType wType
  declare [ IClaim EmptyFC MW Public [NoInline, ExternFn] (MkTy EmptyFC EmptyFC decoderName decType) ]

  pure abiEntry


public export
contract_interface : List String -> Elab ()
contract_interface functionNames = do
  entries <- traverse contractFunction functionNames
  ignore $ declareTypes entries
