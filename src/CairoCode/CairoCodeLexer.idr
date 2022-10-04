module CairoCode.CairoCodeLexer

import CairoCode.CairoCodeSerializer

import Data.String.Extra
import Text.Lexer

%default total

||| Pre-defined Keywords - these can never be used anywhere else!
||| Note that the names of linear implicits are not keywords,
||| though they do act like keywords in their appropriate positions in the syntax.
public export
data Keyword =
  ExtFun
  | Fun
  | Foreign
  | None
  | From
  | Import
  | As
  | Stable
  | Unstable
  | Underscore
  | Null
  -- Reg keywords
  | Unassigned
  | Param
  | Reg
  | Local
  | Let
  | Temp
  | Const
  | Eliminated
  | By
  | Unreachable
  | Disjoint
  -- Instructions
  | New
  | Cast
  | Crash
  | BelieveMe
  | External
  | Intrinsic
  | Storage
  | Event
  | Closure
  | Case
  | ConstCase
  | Default
  | Return
  | Error

export
Eq Keyword where
  ExtFun     == ExtFun     = True
  Fun        == Fun        = True
  Foreign    == Foreign    = True
  None       == None       = True
  From       == From       = True
  Import     == Import     = True
  As         == As         = True
  Stable     == Stable     = True
  Unstable   == Unstable   = True
  Underscore == Underscore = True
  Null       == Null       = True

  Unassigned  == Unassigned  = True
  Param       == Param       = True
  Reg         == Reg         = True
  Local       == Local       = True
  Let         == Let         = True
  Temp        == Temp        = True
  Const       == Const       = True
  Eliminated  == Eliminated  = True
  By          == By          = True
  Unreachable == Unreachable = True
  Disjoint    == Disjoint    = True

  New        == New        = True
  Cast       == Cast       = True
  Crash      == Crash      = True
  BelieveMe  == BelieveMe  = True
  External   == External   = True
  Intrinsic  == Intrinsic  = True
  Storage    == Storage    = True
  Event      == Event      = True
  Closure    == Closure    = True
  Case       == Case       = True
  ConstCase  == ConstCase  = True
  Default    == Default    = True
  Return     == Return     = True
  Error      == Error      = True

  _ == _ = False

export
Show Keyword where
  show ExtFun     = "extfun"
  show Fun        = "fun"
  show Foreign    = "foreign"
  show None       = "<none>"
  show From       = "from"
  show Import     = "import"
  show As         = "as"
  show Stable     = "stable"
  show Unstable   = "unstable"
  show Underscore = "_"
  show Null       = "<null>"

  show Unassigned  = "unassigned"
  show Param       = "param"
  show Reg         = "reg"
  show Local       = "local"
  show Let         = "let"
  show Temp        = "temp"
  show Const       = "const"
  show Eliminated  = "eliminated"
  show By          = "by"
  show Unreachable = "unreachable"
  show Disjoint    = "disjoint"

  show New        = "new"
  show Cast       = "cast"
  show Crash      = "crash"
  show BelieveMe  = "believe_me"
  show External   = "external"
  show Intrinsic  = "intrinsic"
  show Storage    = "storage"
  show Event      = "event"
  show Closure    = "closure"
  show Case       = "case"
  show ConstCase  = "const_case"
  show Default    = "default"
  show Return     = "return"
  show Error      = "error"

||| The tokens that can appear in the Skyro IR:
||| * Punctuation
||| * Operators
||| * Values and Literals
public export
data SkyroToken =
  OpenBrace
  | OpenParen
  | CloseParen
  | CloseBrace
  -- Symbols
  | Comma
  | Colon
  | Semicolon
  | Period
  | AtSymbol
  | DoubleEquals
  | SingleEquals
  | Arrow
  | ArrowL
  -- Operators
  | Plus
  | Minus
  | Mult
  | Div
  | Mod
  | ShiftL
  | ShiftR
  | BoolAnd
  | BoolOr
  | BoolXor
  | LessThanEqual
  | GreaterThan
  | LessThan
  | GreaterThanEqual
  -- Variants
  | Name String
  | Dollar
  | TripleQuoted String
  | SingleQuoted String
  | Character String -- TODO Unescaped Character
  | NatNumber Nat
  | NegNumber Int
  | KeywordTk Keyword
  -- Holds a tagged literal. Types are handled by the constructor below,
  -- Naked integrals by NatNumber and NegNumber, Strings by SingleQuoted
  | OptNumericLit (Either String CairoConst) -- A Left holds the error message for an out-of-range literal
  | ConstantType CairoConst
  | Whitespace

export
Eq SkyroToken where
  OpenBrace            == OpenBrace            = True
  OpenParen            == OpenParen            = True
  CloseParen           == CloseParen           = True
  CloseBrace           == CloseBrace           = True
  Comma                == Comma                = True
  Colon                == Colon                = True
  Semicolon            == Semicolon            = True
  Period               == Period               = True
  AtSymbol             == AtSymbol             = True
  DoubleEquals         == DoubleEquals         = True
  SingleEquals         == SingleEquals         = True
  Arrow                == Arrow                = True
  ArrowL               == ArrowL               = True

  Plus                 == Plus                 = True
  Minus                == Minus                = True
  Mult                 == Mult                 = True
  Div                  == Div                  = True
  Mod                  == Mod                  = True
  ShiftL               == ShiftL               = True
  ShiftR               == ShiftR               = True
  BoolAnd              == BoolAnd              = True
  BoolOr               == BoolOr               = True
  BoolXor              == BoolXor              = True
  LessThanEqual        == LessThanEqual        = True
  GreaterThan          == GreaterThan          = True
  LessThan             == LessThan             = True
  GreaterThanEqual     == GreaterThanEqual     = True

  (Name name1)         == (Name name2)         = name1 == name2
  Dollar               == Dollar               = True
  (TripleQuoted text1) == (TripleQuoted text2) = text1 == text2
  (SingleQuoted text1) == (SingleQuoted text2) = text1 == text2
  (Character  ch1)     == (Character ch2)      = ch1 == ch2
  (NatNumber num1)     == (NatNumber num2)     = num1 == num2
  (NegNumber num1)     == (NegNumber num2)     = num1 == num2
  (KeywordTk kw1)      == (KeywordTk kw2)      = kw1 == kw2
  (OptNumericLit cst1) == (OptNumericLit cst2) = cst1 == cst2
  (ConstantType cst1)  == (ConstantType cst2)  = cst1 == cst2
  Whitespace           == Whitespace           = True
  _                    == _                    = False

export
Show SkyroToken where
  show OpenBrace           = "{"
  show OpenParen           = "("
  show CloseParen          = ")"
  show CloseBrace          = "}"
  show Comma               = ","
  show Colon               = ":"
  show Semicolon           = ";"
  show Period              = "."
  show AtSymbol            = "@"
  show DoubleEquals        = "=="
  show SingleEquals        = "="
  show Arrow               = "->"
  show ArrowL              = "<-"

  show Plus                = "+"
  show Minus               = "-"
  show Mult                = "*"
  show Div                 = "/"
  show Mod                 = "%"
  show ShiftL              = "<<"
  show ShiftR              = ">>"
  show BoolAnd             = "&&"
  show BoolOr              = "||"
  show BoolXor             = "^"
  show LessThan            = "<"
  show LessThanEqual       = "<="
  show GreaterThan         = ">="
  show GreaterThanEqual    = ">"

  show (Name name)         = name
  show Dollar              = "$"
  show (TripleQuoted text) = "\"\"\"" ++ text ++ "\"\"\""
  show (SingleQuoted text) = "\"" ++ text ++ "\""
  show (Character ch)      = show ch
  show (NatNumber num)     = show num
  show (NegNumber num)     = show num
  show (KeywordTk kw)      = show kw
  show (OptNumericLit cst) = either id serializeConst cst
  show (ConstantType cst)  = serializeConst cst
  show Whitespace          = "<space>"

public export
TokenList : Type
TokenList = List (WithBounds SkyroToken)

wordBoundary : Recognise False
wordBoundary = reject (alphaNum <|> is '_')

||| TODO: Can a CairoName possibly start with one of the normal keywords, e.g. 'extfun'?
keywordLexer : TokenMap SkyroToken
keywordLexer =
  let kwLex : String -> Keyword -> (Recognise True, String -> SkyroToken)
      kwLex kw tk = (exact kw <+> wordBoundary, const $ KeywordTk tk)
  in
    [ kwLex "extfun"       ExtFun
    , kwLex "fun"          Fun
    , kwLex "foreign"      Foreign
    , kwLex "<none>"       None
    , kwLex "from"         From
    , kwLex "import"       Import
    , kwLex "stable"       Stable
    , kwLex "unstable"     Unstable
    , kwLex "_"            Underscore
    , kwLex "return"       Return
    , kwLex "error"        Error
    , kwLex "<null>"       Null
    , kwLex "unassigned"   Unassigned
    , kwLex "param"        Param
    , kwLex "reg"          Reg
    , kwLex "local"        Local
    , kwLex "let"          Let
    , kwLex "temp"         Temp
    , kwLex "const"        Const
    , kwLex "eliminated"   Eliminated
    , kwLex "by"           By
    , kwLex "unreachable"  Unreachable
    , kwLex "disjoint"     Disjoint
    , kwLex "new"          New
    , kwLex "cast"         Cast
    , kwLex "crash"        Crash
    , kwLex "believe_me"   BelieveMe
    , kwLex "external"     External
    , kwLex "intrinsic"    Intrinsic
    , kwLex "storage"      Storage
    , kwLex "event"        Event
    , kwLex "closure"      Closure
    , kwLex "case"         Case
    , kwLex "const_case"   ConstCase
    , kwLex "default"      Default
    , kwLex "return"       Return
    , kwLex "error"        Error
    ]

||| The constants are lexed in a more complicated way:
||| They're actually stored as an Either String value, where
||| the String represents the error message if the literal is out of range.
||| This is necessary because the Lexer itself cannot reject after recognizing,
||| and something like "(\d|\d\d|1\d\d|2[0-4]\d|25[0-5])u8" for unsigned 8-bit characters,
||| while it works, is impractical, hideously ugly and non-performant.
|||
||| Instead, the tagged integral literals are cast from String to their type.
||| To check the in-range-ness, we then cast them back to String and compare to the
||| original value (minus the postfix tag): If equal, it's in range, if not, it's out of range.
||| This is legal, because something that parses as a tagged integral literal can under no circumstances
||| be lexed as something different. The actual error reporting happens later on in the Parser stage,
||| meaning it's also possible to report the error as an accumulated one instead of as a hard-fail.
|||
||| Is this elegant? No, not really. Does it work? Yes.
constantLexer : TokenMap SkyroToken
constantLexer =
  let checkRange : Cast a String => Cast String a => String -> String -> Either String a
      checkRange orig x =
        let x'  : a      := cast x
            x'' : String := cast x'
        in if x == x''
          then Right x'
          else Left "Literal is not in range: \{show orig}"
      literal : Cast a String => Cast String a
             => String
             -> (a -> CairoConst)
             -> (Recognise True, String -> SkyroToken)
      literal suffix f =
        ( opt (is '-') <+> digits <+> exact suffix <+> wordBoundary
        , \x => OptNumericLit $ map f
                              $ checkRange x
                              $ dropLast (length suffix) x
        )
  in [ literal "i8"   I8
     , literal "i16"  I16
     , literal "i32"  I32
     , literal "i64"  I64
     , literal "f"    F
     , literal "big"  BI
     , literal "u8"   B8
     , literal "u16"  B16
     , literal "u32"  B32
     , literal "u64"  B64

     , (exact "int"     <+> wordBoundary,      const $ ConstantType IntType)
     , (exact "i8"      <+> wordBoundary,      const $ ConstantType Int8Type)
     , (exact "i16"     <+> wordBoundary,      const $ ConstantType Int16Type)
     , (exact "i32"     <+> wordBoundary,      const $ ConstantType Int32Type)
     , (exact "i64"     <+> wordBoundary,      const $ ConstantType Int64Type)
     , (exact "Integer" <+> wordBoundary,      const $ ConstantType IntegerType)
     , (exact "Felt"    <+> wordBoundary,      const $ ConstantType FeltType)
     , (exact "u8"      <+> wordBoundary,      const $ ConstantType Bits8Type)
     , (exact "u16"     <+> wordBoundary,      const $ ConstantType Bits16Type)
     , (exact "u32"     <+> wordBoundary,      const $ ConstantType Bits32Type)
     , (exact "u64"     <+> wordBoundary,      const $ ConstantType Bits64Type)
     , (exact "String"  <+> wordBoundary,      const $ ConstantType StringType)
     , (exact "Char"    <+> wordBoundary,      const $ ConstantType CharType)
     , (exact "Type"    <+> wordBoundary,      const $ ConstantType TypeType)
     ]

skyroTokens : TokenMap SkyroToken
skyroTokens =
  keywordLexer ++ constantLexer ++
    [ (is '{',                                const OpenBrace)
    , (is '(',                                const OpenParen)
    , (is ')',                                const CloseParen)
    , (is '}',                                const CloseBrace)
    , (is ',',                                const Comma)
    , (is ':',                                const Colon)
    , (is ';',                                const Semicolon)
    , (is '.',                                const Period)
    , (is '@',                                const AtSymbol)
    , (exact "==",                            const DoubleEquals)
    , (is '=',                                const SingleEquals)
    , (exact "->",                            const Arrow)
    , (exact "<-",                            const ArrowL)

    , (is '+',                                const Plus)
    , (is '-',                                const Minus)
    , (is '*',                                const Mult)
    , (is '/',                                const Div)
    , (is '%',                                const Mod)
    , (exact "<<",                            const ShiftL)
    , (exact ">>",                            const ShiftR)
    , (exact "&&",                            const BoolAnd)
    , (exact "||",                            const BoolOr)
    , (is '^',                                const BoolXor)
    , (exact "<=",                            const LessThanEqual)
    , (exact ">=",                            const GreaterThan)
    , (is '<',                                const LessThan)
    , (is '>',                                const GreaterThanEqual)

    , (alpha <+> many (alphaNums <|> is '_'), Name)
    , (is '$',                                const Dollar) -- Used in Name Expressions as the iter-separator
    , (quote (exact "\"\"\"") any,            TripleQuoted . shrink 3)
    , (quote (is '"') any,                    SingleQuoted . shrink 1)
    , (charLit,                               Character . shrink 1)
    , (digits,                                NatNumber . cast)
    , (is '-' <+> digits,                     NegNumber . cast)
    , (spaces,                                const Whitespace)
    ]

||| Remove any whitespace tokens from the list.
||| The tokens are whitespace-aware, while the grammar
||| is not.
processWhitespace : (TokenList, Int, Int, String)
                -> (TokenList, Int, Int, String)
processWhitespace (x, l, c, s) = (filter notWhitespace x, l, c, s)
  where notWhitespace : WithBounds SkyroToken -> Bool
        notWhitespace t = case t.val of
          Whitespace => False
          _ => True

export
lexSkyro : String -> Either String TokenList
lexSkyro input = case processWhitespace $ lex skyroTokens input of
  (list, _, _  , "") => Right list
  (_, line, col, _ ) => Left "Unknown token beginning at \{show line}:\{show col}"
