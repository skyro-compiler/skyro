module CairoCode.CairoCodeParser

import CairoCode.CairoCodeSerializer
import CairoCode.CairoCodeLexer
import CairoCode.Name
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect

import Text.Parser

%default total

-- Our Rule types
AnyRule : Bool -> Type -> Type
AnyRule consumes ty = Grammar () SkyroToken consumes ty
Rule, OptRule : Type -> Type
Rule = AnyRule True
OptRule = AnyRule False

-- * General, single-token parsers

keywordP : Keyword -> Rule Keyword
keywordP kw = terminal ("Expected keyword " ++ show kw) $
  \tok => case tok of
    KeywordTk kw' => if kw == kw' then Just kw else Nothing
    _ => Nothing

simpleNameP : Rule String
simpleNameP = terminal ("Expected simple name") $
  \tok => case tok of
    Name name => pure name
    _ => Nothing

natP : Rule Nat
natP = terminal ("Expected natural number") $
  \tok => case tok of
    NatNumber num => pure num
    _ => Nothing

intP : Rule Int
intP = terminal ("Expected integral") $
  \tok => case tok of
    NatNumber num => pure $ cast num
    NegNumber num => pure $ cast num
    _ => Nothing

tripleQuotedP : Rule String
tripleQuotedP = terminal ("Expected triple-quoted string") $
  \tok => case tok of
    TripleQuoted text => pure text
    _ => Nothing

-- TODO Unescape?
stringP : Rule String
stringP = terminal ("Expected string") $
  \tok => case tok of
    SingleQuoted text => pure text
    _ => Nothing

||| Either parse a plain name with the value of an implicit,
||| and return the corresponding implicit, or fail fatally.
forcedImplicitP : Rule LinearImplicit
forcedImplicitP = do
  res <- terminal ("Expected implicit name") $
    \tok => case tok of
      Name "output_ptr" => Just $ Right output_builtin
      Name "syscall_ptr" => Just $ Right syscall_builtin
      Name "pedersen_ptr" => Just $ Right pedersen_builtin
      Name "range_check_ptr" => Just $ Right range_check_builtin
      Name "ecdsa_ptr" => Just $ Right ecdsa_builtin
      Name "bitwise_ptr" => Just $ Right bitwise_builtin
      Name unknown_implicit => Just $ Left unknown_implicit
      _ => Nothing

  commit -- We found _some_ name, if it's an unknown one this is a hard error anyway
  case res of
    Left err => fatalError err
    Right val => pure val

tokenP : SkyroToken -> Rule SkyroToken
tokenP tk = terminal ("Expected token " ++ show tk) $
  \tok => if tok == tk then pure tk else Nothing

-- * Combining Parsers

-- TODO These parsers need new versions that:
-- a) parses opening
-- b) Parses inner rule, then:
--    c) Parse separator, Parse next inner rule
--    d) Parse Closing
-- If at step c), after separator, the Closing is encountered
-- We should report it as a failing inner rule - currently,
-- the separator back-tracks, Closing is required, not found,
-- and thus reported, even though the failure was due to a
-- missing inner parser (or an extraneous separator)

commaSepP : {c : Bool} -> AnyRule c a -> AnyRule c (List1 a)
commaSepP = sepBy1 (tokenP Comma)

commaSepOptP : {c : Bool} -> AnyRule c a -> OptRule (List a)
commaSepOptP = sepBy (tokenP Comma)

semiSepP : {c : Bool} -> AnyRule c a -> AnyRule c (List1 a)
semiSepP = sepBy1 (tokenP Semicolon)

bracedP : {c : Bool} -> AnyRule c a -> Rule a
bracedP = between (tokenP OpenBrace) (tokenP CloseBrace)

parenP : {c : Bool} -> AnyRule c a -> Rule a
parenP = between (tokenP OpenParen) (tokenP CloseParen)

-- * Concrete parsers
-- TODO: Cleaner error messages for the combined parsers (e.g. "expected register" when no register-keyword was detected)

-- NOTE: `commit`s as a way to lock in to the current alternative are used liberally, accompanied with a reasoning.

nameP : Rule CairoName
nameP = choice $ the (List _)
  [ Extension <$> simpleNameP
              <*> optional (tokenP Dollar *> intP)
              <*  tokenP Plus
              <*> assert_total nameP
  , do 
      segments <- sepBy1 (tokenP Period) simpleNameP
      pure $ uncurry RawName $ unsnoc segments
  ]

parseConst : Rule CairoConst
parseConst =
  (I <$> intP)
  <|> (Str <$> stringP)
  -- <|> (Ch <$> ) -- TODO Needs unescape in token parser
  <|> do
    res <- terminal ("Expected constant") $
      \tok => case tok of
        ConstantType ty => pure $ Right ty
        OptNumericLit (Right val) => pure $ Right val
        OptNumericLit (Left err) => pure $ Left err
        _ => empty

    commit -- We can commit here - we found a literal, we only fail if it's out of range (which is non-recoverable)
    -- Annotation needed, Idris can't derive the info otherwise for some reason
    case the (Either _ CairoConst) res of
      Left err => fatalError err
      Right val => pure val

-- The keywords are uniquely identifying the register type, thus we commit after them.
parseReg : Rule CairoReg
parseReg = choice $ the (List _)
  [ Unassigned <$  keywordP Unassigned <* commit
               <*> optional stringP
               <*> intP
               <*  tokenP AtSymbol
               <*> intP
  , Param      <$  keywordP Param  <* commit
               <*> intP
  , CustomReg  <$  keywordP Reg <* commit
               <*> stringP
               <*> optional (tokenP Colon *> stringP)
  , Local      <$  keywordP Local <* commit
               <*> intP
               <*  tokenP AtSymbol
               <*> intP
  , Let        <$  keywordP Let <* commit
               <*> intP
               <*  tokenP AtSymbol
               <*> intP
  , Temp       <$  keywordP Temp <* commit
               <*> intP
               <*  tokenP AtSymbol
               <*> intP
  , Const      <$  keywordP Const <* commit
               <*> parseConst
  , Eliminated <$  keywordP Eliminated <* commit
               <*> choice {t=List}
    [ Null        <$  keywordP Null
    , Replacement <$  keywordP By
                  <*> assert_total parseReg
    , Other       <$  keywordP By
                  <*> stringP
    , Unreachable <$ keywordP Unreachable
    , Disjoint    <$ keywordP Disjoint
    ]
  ]

-- TODO Maybe fix malformed instructions and report errors via `act` instead of hard-failing.
parseInst : Rule CairoInst
parseInst = parseNormal <|> parseControlFlow
  where ||| Verify there's only a single value on the left-hand side
        verifySingle : WithBounds (List1 CairoReg) -> String -> OptRule CairoReg
        verifySingle (MkBounded (reg ::: []) _ _  ) _   = pure reg
        verifySingle (MkBounded _            _ bnd) tag = failLoc bnd "\{tag} instruction needs 1 result register"

        ||| Parse the optionally provided linear implicit arguments, or nothing (no empty braces).
        linearArguments : OptRule LinearImplicitArgs
        linearArguments = option empty (fromList <$> (bracedP $ commaSepOptP linearArgument))
          where linearArgument : Rule (LinearImplicit, (CairoReg, CairoReg))
                linearArgument = do
                  impl   <- forcedImplicitP
                  _      <- tokenP AtSymbol
                  target <- parenP parseReg
                  _      <- tokenP ArrowL
                  source <- parseReg

                  pure (impl, (source, target))

        parseNormal : Rule CairoInst
        parseNormal = do
          res <- bounds $ parenP $ commaSepP parseReg

          _ <- tokenP SingleEquals
          commit -- = means we're a normal instruction.

          choice $ the (List _)
            [ do source <- parseReg                          -- (<reg>) = <reg>
                 commit
                 target <- verifySingle res "ASSIGN"
                 pure $ ASSIGN target source
            , do value <- parseConst                         -- (<reg>) = <const>
                 commit
                 target <- verifySingle res "MKCONSTANT"
                 pure $ MKCONSTANT target value
            , do _ <- keywordP Null                          -- (<reg>) = <null>
                 commit
                 target <- verifySingle res "NULL"
                 pure $ NULL target

            -- Constructors and Projections
            , do _ <- keywordP New                           -- (<reg>) = new {@<int>} (<reg>, ...)
                 commit -- new always means constructors
                 tag <- optional (tokenP AtSymbol *> intP)
                 args <- parenP $ commaSepOptP parseReg
                 target <- verifySingle res "MKCON"
                 pure $ MKCON target tag args
            , do value <- parenP parseReg                    -- (<reg>) = (<reg>).<nat>
                 _ <- tokenP Period
                 commit -- . means indexed access
                 idx <- natP
                 target <- verifySingle res "PROJECT"
                 pure $ PROJECT target value idx

            -- Operators
            , do _ <- keywordP Cast                          -- (<reg>) = cast <lin-args> (<const> -> <const>)(<reg>)
                 commit -- cast keyword is explicit
                 lins <- linearArguments
                 primfn <- parenP $ do
                    from <- parseConst
                    _ <- tokenP Arrow
                    to <- parseConst
                    pure $ Cast from to
                 val <- parenP parseReg
                 target <- verifySingle res "Cast Operator"
                 pure $ OP target lins primfn [val]
            , do _ <- keywordP Crash                         -- crash @(<reg>) <lin-args> (<reg>)
                 commit
                 _ <- tokenP AtSymbol
                 type <- parenP parseReg
                 lins <- linearArguments
                 value <- parenP parseReg
                 target <- verifySingle res "Crash Operator"
                 pure $ OP target lins Crash [type, value]
            , do _ <- keywordP BelieveMe                     -- believe_me <lin-args>(<reg> -> <reg>)(<reg>)
                 commit
                 lins <- linearArguments
                 fromTo <- parenP $ do
                    from <- parseReg
                    _ <- tokenP Arrow
                    to <- parseReg
                    pure [from, to]
                 value <- parenP parseReg
                 target <- verifySingle res "BelieveMe Operator"
                 pure $ OP target lins BelieveMe (fromTo ++ [ value ])
            , do _ <- tokenP AtSymbol                        -- @<const> -<lin-args>(<reg>)
                 commit                                      -- @<const> <lin-args>(<reg> <operator> <reg>)
                 type <- parseConst
                 target <- verifySingle res "Negation or binary infix Operator"
                 choice $ the (List _)
                   [ do _ <- tokenP Minus
                        commit
                        lins <- linearArguments
                        value <- parenP parseReg
                        pure $ OP target lins (Neg type) [value]
                   , do lins <- linearArguments
                        parenP $ do
                          arg1 <- parseReg
                          operator <- choice $ the (List _)
                            [ Add    <$ tokenP Plus
                            , Sub    <$ tokenP Minus
                            , Mul    <$ tokenP Mult
                            , Div    <$ tokenP Div
                            , Mod    <$ tokenP Mod
                            , ShiftL <$ tokenP ShiftL
                            , ShiftR <$ tokenP ShiftR
                            , BAnd   <$ tokenP BoolAnd
                            , BOr    <$ tokenP BoolOr
                            , BXOr   <$ tokenP BoolXor
                            , LT     <$ tokenP LessThan
                            , LTE    <$ tokenP LessThanEqual
                            , EQ     <$ tokenP DoubleEquals
                            , GTE    <$ tokenP GreaterThan
                            , GT     <$ tokenP GreaterThanEqual
                            ]
                          arg2 <- parseReg
                          pure $ OP target lins (operator type) [arg1, arg2]
                   ]


            -- Function calls
            , do funName <- nameP
                 lins <- linearArguments
                 args <- parenP $ commaSepOptP parseReg
                 pure $ CALL (forget res.val) lins funName args
            , do _ <- keywordP External
                 commit
                 funName <- nameP
                 lins <- linearArguments
                 args <- parenP $ commaSepOptP parseReg
                 pure $ EXTPRIM (forget res.val) lins funName args
            , do _ <- keywordP Intrinsic
                 commit
                 intr <- keywordP Storage *> pure StorageVarAddr
                     <|> keywordP Event   *> pure EventSelector
                 funName <- nameP
                 lins <- linearArguments
                 args <- parenP $ commaSepOptP parseReg
                 target <- verifySingle res "Starknet Intrinsic"
                 pure $ STARKNETINTRINSIC target lins (intr funName) args

            , do _ <- keywordP Closure
                 commit
                 name <- nameP
                 parenP $ do
                   args <- commaSepOptP parseReg
                   missing <- option 0 $ if length args == 0
                      then map length $ commaSepOptP $ keywordP Underscore -- No previous arguments, no previous ,
                      else (length <$  tokenP Comma
                                   <*> (commaSepP $ keywordP Underscore))
                              <|> pure 0

                   target <- verifySingle res "Closure creation"
                   pure $ MKCLOSURE target name missing args

            , do fun <- parenP parseReg
                 lins <- linearArguments
                 arg <- parenP parseReg
                 target <- verifySingle res "Apply"
                 pure $ APPLY target lins fun arg
            , do _ <- keywordP Error
                 commit
                 msg <- stringP
                 target <- verifySingle res "Error"
                 pure $ ERROR target msg
            ]

        parseCaseCommon : Keyword
                       -> String
                       -> Rule dis
                       -> (CairoReg -> List (dis, List CairoInst) -> Maybe (List CairoInst) -> CairoInst)
                       -> Rule CairoInst
        parseCaseCommon kw name disP con = do
          _ <- keywordP kw
          commit -- The keywords are explicit
          val <- parenP parseReg
          bracedP $ do
            alts <- many $ do
              discriminator <- disP
              commit -- Individually, the case branch has begun, so we can commit.
              _ <- tokenP Arrow
              body <- map forget $ bracedP $ semiSepP $ assert_total parseInst
              pure (discriminator, body)
            def <- optional $ do
              _ <- keywordP Default
              commit
              map forget $ bracedP $ semiSepP $ assert_total parseInst
            -- TODO We don't/in some cases can't check coverage right now, so a default branch is always allowed
            when (null alts && isNothing def) $ fatalError "\{name}: Either one alternative, or the default branch, must be available."

            pure $ con val alts def

        parseControlFlow : Rule CairoInst
        parseControlFlow = choice $ the (List _)
          [ parseCaseCommon Case "Case statement" intP CASE
          , parseCaseCommon ConstCase "Const Case statement" parseConst CONSTCASE
          , do _ <- keywordP Return
               finalLins <- option empty $ bracedP $ commaSepOptP $ do
                 impl <- forcedImplicitP
                 _ <- tokenP AtSymbol
                 register <- parenP parseReg
                 pure (impl, register)
               values <- parenP $ commaSepOptP parseReg
               pure $ RETURN values (fromList finalLins)
          ]

parseTupleSig : Rule (Maybe TupleStructure)
parseTupleSig = do
    _ <- keywordP None
    --commit
    pure Nothing
  <|> (Just <$> parseTupleSig')
  where parseTupleSig' : Rule TupleStructure
        parseTupleSig' = do
            _ <- keywordP Underscore
            --commit
            pure ReturnValue
          <|> do
            tag <- intP
            --commit
            _ <- tokenP Colon
            inners <- parenP $ commaSepOptP (assert_total parseTupleSig')

            pure $ Tupled tag inners

parseImplicitParam : Rule (LinearImplicit, CairoReg)
parseImplicitParam = do
  (,) <$> forcedImplicitP
      <*  tokenP AtSymbol
      <*> parenP parseReg

parseImport : Rule Import
parseImport =
  MkImport <$  keywordP From <* commit
           <*> ((joinBy "." . forget) <$> sepBy1 (tokenP Period) simpleNameP)
           <*  keywordP Import
           <*> simpleNameP
           <*> optional (
             keywordP As
             *> simpleNameP
           )

||| Parser for a CairoDef
parseCairoDef : Rule (CairoName, CairoDef)
parseCairoDef
  = do -- foreign
    _ <- keywordP Foreign
    commit

    name <- nameP
    implicits <- bracedP $ commaSepOptP simpleNameP
    params <- parenP natP
    _ <- tokenP Arrow
    rets <- parenP natP

    foreignInfo <-
      MkForeignInfo
        -- Stability info
        <$> (pure (Stable ==) <*> (keywordP Stable <|> keywordP Unstable))
        -- Tuple signature
        <*> parseTupleSig
        -- The already parsed implicits
        <*> pure (map MKLinearImplicit implicits)
        -- Parse the opening curly brace
        <*  tokenP OpenBrace
        -- Parse the possibly-empty imports
        <*> (fromList <$> many (parseImport <* tokenP Semicolon))
        -- Parse the code
        <*> tripleQuotedP
        -- Parse the finishing curly brace
        <*  tokenP CloseBrace

    -- (MkForeignInfo isApStable untupledSig implicits imports code)
    pure (name, ForeignDef foreignInfo params rets)
  <|> do -- fun
    _ <- keywordP Fun
    commit

    commonFunP FunDef
  <|> do -- extfun
    tags <- many (tokenP AtSymbol *> simpleNameP)
    when (length tags /= 0) $ commit
    _ <- keywordP ExtFun
    commit -- Definitely commit after the extfun keyword

    commonFunP (ExtFunDef tags)
  where commonFunP : (List CairoReg -> SortedMap LinearImplicit CairoReg -> List CairoReg -> List CairoInst -> CairoDef) -> Rule (CairoName, CairoDef)
        commonFunP constructDef = do
          name <- nameP
          implicits <-
            fromList
              <$> (option [] $ bracedP $ commaSepOptP parseImplicitParam)


          params <- parenP $ commaSepOptP parseReg
          _ <- tokenP Arrow
          rets <- parenP $ commaSepOptP parseReg
          body <- forget <$> (bracedP $ semiSepP parseInst)

          pure (name, constructDef params implicits rets body)

parseProgram : Rule Program
parseProgram = forget <$> someTill eof parseCairoDef

-- TODO : Better display alternative-errors, maybe think about using `parseWith`
-- and `act` instead to collect correctable errors instead of bailing early.
-- Code copied from newer version of Parser that has the Show instance included.
export
showError : ParsingError tok -> String
showError (Error s Nothing) = "PARSING ERROR: " ++ s
showError (Error s (Just (MkBounds startLine startCol endLine endCol))) =
  "PARSING ERROR: "
  ++ s
  ++ " @ L\{show startLine}:\{show startCol}-L\{show endLine}:\{show endCol}"

export
parseSkyro' : TokenList -> Either (List1 (ParsingError SkyroToken)) (Program, TokenList)
parseSkyro' = parse parseProgram

export
parseSkyro : String -> Either String Program
parseSkyro program = do
  tokens <- lexSkyro program
  case parseSkyro' tokens of
    Left err => Left $ joinBy ";\n"
                     $ forget
                     $ map showError err
    Right program => Right $ fst program
