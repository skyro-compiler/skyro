module CairoCode.CairoCodeSerializer

import public CairoCode.CairoCode
import Control.Monad.State
import CairoCode.Name

import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect

import Protocol.Hex

%default total

public export
Program : Type
Program = List (CairoName, CairoDef)

%hide Data.String.unlines
||| This definition of unlines is necessary because the default Data.String.unlines
||| consistently appends a newline at the end, meaning `lines . Data.String.unlines`
||| is not identity, but `lines . unlines` is.
unlines : List String -> String
unlines = joinBy "\n"

||| Indentation per level in spaces
indentPerLevel : Nat
indentPerLevel = 2

||| Indent each line of a given string by `n` spaces.
indentLines : (n : Nat) -> String -> String
indentLines n str = unlines $ map (indent n) $ lines str

||| Comma separated serializers
commaSpaceSep : (a -> String) -> List a -> String
commaSpaceSep f xs = joinBy ", " $ map f xs

||| Semicolon and new-line separated serializers
semiNewlineSep : (a -> String) -> List a -> String
semiNewlineSep f xs = joinBy ";\n" $ map f xs

||| Similar to cairoName, but:
||| * Single underscores get doubled
||| * Pre-defined symbols like =(){} are pre-, not postfixed with an underscore
||| * The hex-encoding of other characters - alternatively, we could pad with zeros,
|||   but the maximum value of a Char was not easily discoverable - is prefixed by
|||   a single hex digit representing the length of the encoding - 1.
export
stringToSafe : String -> String
stringToSafe s = concatMap makeSafe (unpack s)
  where makeSafe : Char -> String
        makeSafe '_' = "__"
        -- For readability's sake, we pre-define these names
        makeSafe '.' = "_dot"
        makeSafe '=' = "_eq"
        makeSafe '<' = "_lt"
        makeSafe '>' = "_gt"
        makeSafe '\'' = "_prime"
        makeSafe '(' = "_lpar"
        makeSafe ')' = "_rpar"
        makeSafe '{' = "_lcurl"
        makeSafe '}' = "_rcurl"
        makeSafe '$' = "_dollar"
        makeSafe ' ' = "_space"
        makeSafe c =
          if isAlphaNum c
          then cast c
          else
            let hexRepr = asHex (cast c)
                hexLength = asHex $ cast $ (strLength hexRepr - 1)
            in "_\{hexLength}_\{hexRepr}"

||| Inverse of `stringToSafe`.
-- TODO Augment with Error info?
export
stringFromSafe : String -> Maybe String
stringFromSafe = map pack . fromSafe . unpack
  where fromSafe : List Char -> Maybe (List Char)
        fromSafe [] = Just []
        fromSafe ('_' :: '_' :: xs) = ('_' ::) <$> fromSafe xs

        -- For readability's sake, we pre-define these names
        fromSafe ('_'::'e'::'q'                     :: xs) = ('=' ::)  <$> fromSafe xs
        fromSafe ('_'::'l'::'t'                     :: xs) = ('<' ::)  <$> fromSafe xs
        fromSafe ('_'::'g'::'t'                     :: xs) = ('>' ::)  <$> fromSafe xs
        fromSafe ('_'::'d'::'o'::'t'                :: xs) = ('.' ::)  <$> fromSafe xs
        fromSafe ('_'::'l'::'p'::'a'::'r'           :: xs) = ('(' ::)  <$> fromSafe xs
        fromSafe ('_'::'r'::'p'::'a'::'r'           :: xs) = (')' ::)  <$> fromSafe xs
        fromSafe ('_'::'l'::'c'::'u'::'r'::'l'      :: xs) = ('{' ::)  <$> fromSafe xs
        fromSafe ('_'::'r'::'c'::'u'::'r'::'l'      :: xs) = ('}' ::)  <$> fromSafe xs
        fromSafe ('_'::'s'::'p'::'a'::'c'::'e'      :: xs) = (' ' ::)  <$> fromSafe xs
        fromSafe ('_'::'p'::'r'::'i'::'m'::'e'      :: xs) = ('\'' ::) <$> fromSafe xs
        fromSafe ('_'::'d'::'o'::'l'::'l'::'a'::'r' :: xs) = ('$' ::)  <$> fromSafe xs

        fromSafe ('_'::len::'_'::xs) = do
          len' <- fromHex $ cast len
          let required   : Nat := 1 + cast len'
          let restLength : Nat := length xs
          let (encoded, xs') = splitAt required xs

          guard (required <= restLength)

          -- Keep this reverse in mind - fromHex and asHex are not isomorphic!
          charValue <- fromHexChars $ reverse encoded

          (cast charValue ::) <$> fromSafe (assert_smaller xs xs')

        -- Unknown escaping!
        fromSafe ('_' :: xs) = Nothing
        fromSafe (x   :: xs) = (x ::) <$> fromSafe xs

||| Serialize the constants and constant types,
||| using a Rust-like postfix for identifying the literals.
||| Exported since the Tokens use this as well
export
serializeConst : CairoConst -> String
serializeConst (I   v) = show v
serializeConst (I8  v) = show v ++ "i8"
serializeConst (I16 v) = show v ++ "i16"
serializeConst (I32 v) = show v ++ "i32"
serializeConst (I64 v) = show v ++ "i64"
serializeConst (F   v) = show v ++ "f"
serializeConst (BI  v) = show v ++ "big"
serializeConst (B8  v) = show v ++ "u8"
serializeConst (B16 v) = show v ++ "u16"
serializeConst (B32 v) = show v ++ "u32"
serializeConst (B64 v) = show v ++ "u64"
serializeConst (Str v) = show v
serializeConst (Ch  v) = show v
serializeConst IntType     = "int"
serializeConst Int8Type    = "i8"
serializeConst Int16Type   = "i16"
serializeConst Int32Type   = "i32"
serializeConst Int64Type   = "i64"
serializeConst IntegerType = "Integer"
serializeConst FeltType    = "Felt"
serializeConst Bits8Type   = "u8"
serializeConst Bits16Type  = "u16"
serializeConst Bits32Type  = "u32"
serializeConst Bits64Type  = "u64"
serializeConst StringType  = "String"
serializeConst CharType    = "Char"
serializeConst TypeType    = "Type"

||| String representation of registers:
||| There is no distinction between them appearing on the left-
||| or right-hand side of an instruction, and the levels are always
||| printed as well - the alternative would require an up-sift of `Local`
||| registers to create the appropriate non-assigning definition,
||| combined with subsequent down-sift and recombination when parsing;
||| including double-definition and scope checks - all of which should
||| be left to the actual compiler phases.
serializeReg : CairoReg -> String
serializeReg (Unassigned Nothing       i lvl) = "unassigned \{show i} @\{show lvl}"
serializeReg (Unassigned (Just helper) i lvl) = "unassigned \{show helper} \{show i} @\{show lvl}"
serializeReg (Param      i            )       = "param " ++ show i
serializeReg (CustomReg  n   Nothing  )       = "reg   \{show n}"
serializeReg (CustomReg  n   (Just ty))       = "reg   \{show n} : \{show ty}"
serializeReg (Local      i   lvl      )       = "local \{show i} @\{show lvl}"
serializeReg (Let        i   lvl      )       = "let   \{show i} @\{show lvl}"
serializeReg (Temp       i   lvl      )       = "temp  \{show i} @\{show lvl}"
serializeReg (Const      cst          )       = "const \{serializeConst cst}"
serializeReg (Eliminated Null             )   = "eliminated <null>"
serializeReg (Eliminated Unreachable      )   = "eliminated unreachable"
serializeReg (Eliminated Disjoint         )   = "eliminated disjoint"
serializeReg (Eliminated (Replacement reg))   = "eliminated by \{serializeReg reg}"
serializeReg (Eliminated (Other reason)   )   = "eliminated by \{show reason}"

-- Instructions
mutual
  ||| Serializes the immplicit arguments passed in certain instructions.
  ||| If none are passed, no text is generated (instead of an empty pair of curly braces).
  showLinearArgs : LinearImplicitArgs -> String
  showLinearArgs lins with (null lins)
    showLinearArgs _    | True = ""
    showLinearArgs lins | False = "{" ++ (commaSpaceSep display $ toList lins) ++ "}"
      where display : (LinearImplicit, (CairoReg, CairoReg)) -> String
            display (impl, (source, target)) = "\{implicitName impl}@(\{serializeReg target}) <- \{serializeReg source}"


  ||| Serializes both the Case and ConstCase instructions combined, as their only differences are
  ||| their keyword and their discriminators
  serializeCase : (indentSize : Nat)
                -> (kw : String)
                -> (val : CairoReg)
                -> (displayer: a -> String)
                -> (alternatives : List (a, List CairoInst))
                -> (def : Maybe (List CairoInst))
                -> String
  serializeCase i keyword val displayDisc alts def =
    let doCase : Nat -> String -> List CairoInst -> String
        doCase i label body =
          unlines
            [ indent i "\{label} {"
            , assert_total $ serializeInstrs (i + indentPerLevel) body
            , indent i "}"
            ]
        displayAlt : (a, List CairoInst) -> String
        displayAlt (discriminator, body) = doCase (i + indentPerLevel) "\{displayDisc discriminator} ->" body
        alts' : List String
        alts' = map displayAlt alts
        def' : List String
        def' = maybe [] (singleton . doCase (i + indentPerLevel) "default") def
    in unlines
        ( "\{keyword}(\{serializeReg val}) {"
        :: alts'
        ++ def'
        ++ [ indent i "}" ]
        )

  ||| Serialize the right-hand side of an Operator instruction.
  ||| All instructions either begin with an @ symbol and their attached type,
  ||| or with one of the keywords `cast`, `crash` and `believe_me`.
  -- serializeOp : LinearImplicitArgs -> Vect n CairoReg -> CairoPrimFn n -> String
  serializeOp : LinearImplicitArgs -> List CairoReg -> CairoPrimFn -> String
  serializeOp lins [arg] primfn = case primfn of
    Neg ty       => "@\{serializeConst ty} -\{showLinearArgs lins}(\{serializeReg arg})"
    Cast from to => "cast \{showLinearArgs lins}(\{serializeConst from} -> \{serializeConst to})(\{serializeReg arg})"
    _ => assert_total $ idris_crash "Invalid arity operator"
  serializeOp lins [arg1, arg2] primfn =
    let commonOp : CairoConst -> String -> String
        commonOp ty symbol = "@\{serializeConst ty} \{showLinearArgs lins}(\{serializeReg arg1} \{symbol} \{serializeReg arg2})"
    in case primfn of
      Add ty    => commonOp ty "+"
      Sub ty    => commonOp ty "-"
      Mul ty    => commonOp ty "*"
      Div ty    => commonOp ty "/"
      Mod ty    => commonOp ty "%"
      ShiftL ty => commonOp ty "<<"
      ShiftR ty => commonOp ty ">>"
      BAnd ty   => commonOp ty "&&"
      BOr ty    => commonOp ty "||"
      BXOr ty   => commonOp ty "^"
      LT ty     => commonOp ty "<"
      LTE ty    => commonOp ty "<="
      EQ ty     => commonOp ty "=="
      GTE ty    => commonOp ty ">="
      GT ty     => commonOp ty ">"
      Crash     => "crash @(\{serializeReg arg1})\{showLinearArgs lins}(\{serializeReg arg2})"
      _ => assert_total $ idris_crash "Invalid arity operator"
  serializeOp lins [from, to, arg] BelieveMe = "believe_me \{showLinearArgs lins}(\{serializeReg from} -> \{serializeReg to})(\{serializeReg arg})"
  serializeOp _ _ _ = assert_total $ idris_crash "Invalid Operator signature - non-matching arity of operator and arguments."

  ||| Serialize the given instruction with the specified indentation.
  serializeInst : (indentSize : Nat) -> CairoInst -> String
  serializeInst i = indent i . go
    where leftSide : List CairoReg -> String
          leftSide res = "(\{commaSpaceSep serializeReg res}) = "

          go : CairoInst -> String
          go (ASSIGN     res source  ) = leftSide [res] ++ serializeReg source
          go (MKCONSTANT res constant) = leftSide [res] ++ serializeConst constant
          go (NULL       res         ) = leftSide [res] ++ "<null>"

          go (MKCON      res Nothing    args) = leftSide [res] ++ "new (\{commaSpaceSep serializeReg args})"
          go (MKCON      res (Just tag) args) = leftSide [res] ++ "new @\{show tag} (\{commaSpaceSep serializeReg args})"
          go (PROJECT    res value      idx ) = leftSide [res] ++ "(\{serializeReg value}).\{show idx}"

          go (OP         res lins primfn args) = leftSide [res] ++ serializeOp lins args primfn
          go (CALL       res lins name   args) =
            leftSide  res  ++          "\{show name}\{showLinearArgs lins}(\{commaSpaceSep serializeReg args})"
          go (EXTPRIM    res lins name   args) =
            leftSide  res  ++ "external \{show name}\{showLinearArgs lins}(\{commaSpaceSep serializeReg args})"
          go (STARKNETINTRINSIC res lins intr args) =
            leftSide [res]  ++ "intrinsic \{serializeIntrinsic intr}\{showLinearArgs lins}(\{commaSpaceSep serializeReg args})"
            where serializeIntrinsic : StarkNetIntrinsic -> String
                  serializeIntrinsic (StorageVarAddr n) = "storage \{show n}"
                  serializeIntrinsic (EventSelector  n) = "event \{show n}"
                  serializeIntrinsic (FunctionSelector  n) = "function \{show n}"

          go (MKCLOSURE  res name missing args) =
            leftSide [res] ++ "closure \{show name}(\{joinBy ", " params})"
            where args', missing', params : List String
                  args'    = map serializeReg args
                  missing' = replicate missing "_"
                  params   = args' ++ missing'
          go (APPLY      res lins fun     arg ) =
            leftSide [res] ++ "(\{serializeReg fun})\{showLinearArgs lins}(\{serializeReg arg})"

          go (CASE       val branches def) = serializeCase i "case"       val show           branches def
          go (CONSTCASE  val branches def) = serializeCase i "const_case" val serializeConst branches def

          go (RETURN     res finalLins) = "return \{linAssignments}(\{commaSpaceSep serializeReg res})"
            where linAssignments : String
                  linAssignments = if null finalLins
                                    then ""
                                    else "{" ++ (commaSpaceSep (\(k, v) => "\{implicitName k}@(\{serializeReg v})") $ SortedMap.toList finalLins) ++ "}"

          go (ERROR      res msg) = leftSide [res] ++ "error " ++ show msg

  ||| Serialize the list of instructions, separated by semicolons and newlines.
  serializeInstrs : (indentSize : Nat) -> List CairoInst -> String
  serializeInstrs indent = semiNewlineSep (serializeInst indent)

||| Serialize the tuple structure of a foreign function
serializeTupleStructure : TupleStructure -> String
serializeTupleStructure ReturnValue = "_"
serializeTupleStructure (Tupled tag inners) = "\{show tag}:(\{inners'})"
  where inners' : String
        inners' = assert_total $ commaSpaceSep serializeTupleStructure inners

||| Serialize any potential implicit parameters a function declaration can have.
serializeImplicitParams : SortedMap LinearImplicit CairoReg -> String
serializeImplicitParams lins with (null lins)
  serializeImplicitParams lins | False = "{" ++ (commaSpaceSep (\(k, v) => "\{implicitName k}@(\{serializeReg v})" ) $ SortedMap.toList lins) ++ "}"
  serializeImplicitParams _    | True  = ""

||| Serialize a list of registers, separated by comma and space
serializeRegs : List CairoReg -> String
serializeRegs regs = commaSpaceSep serializeReg regs

||| Serialization of normal and external functions share almost everything.
serializeCommonFun : CairoName -> (tags : Maybe (List String))
                  -> (params : List CairoReg) -> (implicits : SortedMap LinearImplicit CairoReg)
                  -> (rets : List CairoReg) -> (body : List CairoInst) -> String
serializeCommonFun name tags params implicits rets body = unlines (tagLines ++ [functionDefinition, bodyLines, "}"])
  where tagLines : List String
        tagLines = case tags of
          Nothing   => []
          Just tags => map (\tag => "@" ++ tag) tags
        funType : String
        funType = if tags == Nothing then "fun" else "extfun"
        functionDefinition : String
        functionDefinition = "\{funType} \{show name}\{serializeImplicitParams implicits}(\{serializeRegs params}) -> (\{serializeRegs rets}) {"
        bodyLines : String
        bodyLines = serializeInstrs indentPerLevel body

||| Serialize a foreign function definition
serializeForeignDef : CairoName -> (info : ForeignInfo) -> (args : Nat) -> (rets : Nat) -> String
serializeForeignDef name (MkForeignInfo isApStable untupledSig implicits imports code) args rets =
  unlines
    ( "foreign \{show name}{\{commaSpaceSep implicitName implicits}}(\{show args}) -> (\{show rets}) \{stability} \{tupleSig} {"
    :: importLines
    ++ [ code'
      , "}"
      ]
    )
  where stability, tupleSig, code' : String
        stability   = if isApStable then "stable" else "unstable"
        tupleSig    = maybe "<none>" serializeTupleStructure untupledSig
        importLines : List String
        importLines = map (indent indentPerLevel . (++ ";") . show) $ Data.SortedSet.toList imports
        code'       = (indent indentPerLevel "\"\"\"") ++ code ++ "\"\"\""

||| Serialize any top-level definition associated with the given name
serializeDef : (CairoName, CairoDef) -> String
serializeDef (name, def) = case def of
  FunDef         params implicits rets instrs => serializeCommonFun name Nothing     params implicits rets instrs
  ExtFunDef tags params implicits rets instrs => serializeCommonFun name (Just tags) params implicits rets instrs
  ForeignDef info args rets                   => serializeForeignDef name info args rets

||| Entrypoint to the Serializer: Serialize a whole Program structure.
public export
serializeProgram : Program -> String
serializeProgram entries = unlines $ intersperse "" $ map serializeDef $ entries
