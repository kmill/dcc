-- | This module is just a straight-forward use of Parsec to parse the
-- decaf language.  The interface takes a list of tokens from
-- 'runScanner' and provides an AST.

module Parser(runDParser) where

import Scanner
import Text.ParserCombinators.Parsec
import CLI
import Control.Applicative hiding ((<|>), many)
import Control.Monad
import AST
import Data.Int

---
--- Main scanner
---

type DParser = GenParser Token DParserState
data DParserState = DParserState {
      parser6035CompatMode :: Bool -- ^ This field doesn't actually do
                                   -- anything.
    }

-- | This is the main function to run the parser.  It either returns a
-- 'DProgram' if it succeeds or a Parsec 'ParseError'.
runDParser :: CompilerOpts
           -> String -- ^ The file name for error messages.
           -> [Token] -- ^ The tokens to parse.
           -> Either ParseError DProgram
runDParser opts fname input
    = runParser dprogram parseState fname input
      where parseState = DParserState
                         { parser6035CompatMode=compatMode opts }

---
--- Helper combinators
---

-- | Matches a token based on its 'TokenType', returning the token.
dtoken :: TokenType -> DParser Token
dtoken tt = dtoken' (\t -> tt == tokenType t) <?> show tt

-- | A combinator which takes a predicate on tokens to determine
-- whether the token matches.
dtoken' :: (Token -> Bool) -> DParser Token
dtoken' p = token showtok tokenPos testtok
    where showtok = show
          testtok t = if p t then Just t else Nothing

-- | Matches tokens which are keywords whose string is the given
-- string.
dkeyword :: String -> DParser Token
dkeyword s = dtoken' (\t -> tokenType t == Keyword && tokenString t == s)
             <?> "\"" ++ s ++ "\""

-- | Matches keyword tokens whose string is one of the given strings.
dkeywords :: [String] -> DParser Token
dkeywords = foldl1 (<|>) . map dkeyword

-- | The following is needed instead of 'lookAhead' because of some
-- kind of annoying bug in Parsec where 'lookAhead' actually fails the
-- entire parse instead of just the current branch of the parse.
tLookAhead :: DParser a -> DParser a
tLookAhead = try . lookAhead

---
--- Punctuation
---

dcomma, dsemi :: DParser ()
dcomma = dkeyword "," >> return ()
dsemi = dkeyword ";" >> return ()

dopenp, dclosep, dopensb, dclosesb, dopenbr, dclosebr :: DParser ()
dopenp = dkeyword "(" >> return ()
dclosep = dkeyword ")" >> return ()
dopensb = dkeyword "[" >> return ()
dclosesb = dkeyword "]" >> return ()
dopenbr = dkeyword "{" >> return ()
dclosebr = dkeyword "}" >> return ()

---
--- Parsers
---

-- | This is the main entry point for parsing a decaf program.
dprogram :: DParser DProgram
dprogram = DProgram <$> getPosition
           <*  header
           <*> many fieldDecl
           <*> many methodDecl
           <* dkeyword "}"
    where header = dkeyword "class" *> identProgram *> dkeyword "{"
          identProgram = dtoken' (\t -> Identifier == tokenType t
                                        && "Program" == tokenString t)
                          <?> "identifier \"Program\""

-- | This matches top-level fields.  It performs three-symbol
-- lookahead so we can get to the method declarations if needed.
fieldDecl :: DParser FieldDecl
fieldDecl = FieldDecl <$> getPosition
            <*> do try $ dtype <* -- three symbol lookahead
                           tLookAhead (ident *> (dsemi <|> dopensb <|> dcomma))
            <*> sepBy1 (arrayVar <|> plainVar) dcomma
            <* dsemi
    where plainVar = PlainVar <$> getPosition <*> try ident
          arrayVar = ArrayVar <$> getPosition
                     <*> do try $ ident <* dopensb -- two symbol lookahead
                     <*> (parseInt64 False <$> (tokenString <$> dtoken IntLiteral))
                     <* dclosesb


-- | This matches method declarations.
methodDecl :: DParser MethodDecl
methodDecl = MethodDecl <$> getPosition
             <*> do try $ MethodReturns <$> dtype
                            <|> MethodVoid <$ dkeyword "void"
             <*> ident
             <*> between dopenp dclosep (arg `sepBy` dcomma)
             <*> block
    where arg = MethodArg <$> dtype <*> ident

-- | This matches a block of code.
block :: DParser Statement
block = Block <$> getPosition
        <* dopenbr
        <*> many varDecl
        <*> many statement
        <* dclosebr

-- | This matches a variable declaration in a block.
varDecl :: DParser VarDecl
varDecl = VarDecl <$> getPosition
          <*> dtype
          <*> sepBy1 ident dcomma
          <* dsemi

-- | This matches a type for a field or a non-@void@ method.
dtype :: DParser DType
dtype = DInt <$ dkeyword "int"
        <|> DBool <$ dkeyword "boolean"   <?> "type"

-- | This matches a statement in a block.
statement :: DParser Statement
statement = ifSt <|> forSt <|> whileSt <|> returnSt
            <|> breakSt <|> continueSt <|> block
            <|> mcall <|> assign
            <?> "statement"
    where assign :: DParser Statement
          assign = AssignSt <$> getPosition
                   <*> location
                   <*> assignOp -- bug: loses "expecting '('"
                   <*> expr <* dsemi
          mcall :: DParser Statement
          mcall = ExprSt
                  <$> (ExprMethod <$> getPosition <*> methodCall)
                  <* dsemi
          ifSt :: DParser Statement
          ifSt = IfSt <$> getPosition
                 <* dkeyword "if"
                 <*> between dopenp dclosep expr
                 <*> block
                 <*> optionMaybe (dkeyword "else" *> block)
          forSt :: DParser Statement
          forSt = ForSt <$> getPosition
                  <* dkeyword "for" <* dopenp
                  <*> ident <* dkeyword "="
                  <*> expr <* dkeyword ";"
                  <*> expr <* dclosep
                  <*> block
          whileSt :: DParser Statement
          whileSt = WhileSt <$> getPosition
                    <* dkeyword "while"
                    <*> between dopenp dclosep expr
                    <*> block
          returnSt :: DParser Statement
          returnSt = ReturnSt <$> getPosition
                     <* dkeyword "return"
                     <*> optionMaybe expr
                     <* dsemi
          breakSt :: DParser Statement
          breakSt = BreakSt <$> getPosition
                    <* dkeyword "break" <* dsemi
          continueSt :: DParser Statement
          continueSt = ContinueSt <$> getPosition
                       <* dkeyword "continue" <* dsemi

-- | This matches an assignment operator, translating the keyword
-- token into the appropriate 'AssignOp'
assignOp :: DParser AssignOp
assignOp = Assign <$ dkeyword "="
           <|> IncAssign <$ dkeyword "+="
           <|> DecAssign <$ dkeyword "-="
           <?> "assignment operator"

-- | This matches a method call, looking ahead two tokens to see if
-- this is actually a method call.  Both normal methods and callout
-- methods are handled by this method.
methodCall :: DParser MethodCall
methodCall = (tLookAhead (ident >> dopenp) *> normalMethod) -- lookahead two
             <|> calloutMethod
    where normalMethod :: DParser MethodCall
          normalMethod = NormalMethod <$> getPosition
                         <*> ident
                         <*> between dopenp dclosep (expr `sepBy` dcomma)
          calloutMethod :: DParser MethodCall
          calloutMethod = CalloutMethod <$> getPosition
                          <* dkeyword "callout" <* dopenp
                          <*> dtoken StringLiteral
                          <*> many (dcomma *> calloutArg)
                          <* dclosep
          calloutArg :: DParser CalloutArg
          calloutArg = CArgString <$> dtoken StringLiteral
                       <|> CArgExpr <$> expr

-- | This matches some location such as a variable or array location.
location :: DParser DLocation
location = doarray <|> doplain
    where doarray = ArrayLocation <$> getPosition
                    -- two token lookahead
                    <*> do try $ ident <* tLookAhead dopensb
                    <*> between dopensb dclosesb expr
          doplain = PlainLocation <$> getPosition
                    <*> ident

-- | This takes a parser @ops@ and a parser @next@ and generates a
-- parser which matches @next + (ops+next)*@.  It /hacks the grammar/
-- and matches @next@ first followed by iteratively trying @ops+next@.
makeBinOp :: DParser Token -> DParser Expr -> DParser Expr
makeBinOp ops next = join $ makeBinOp' <$> getPosition <*> next
    where makeBinOp' pos e1 = (do o <- ops <?> "operator"
                                  e2 <- next
                                  makeBinOp' pos (BinaryOp pos e1 o e2))
                              <|> return e1

-- | Takes a parser @ops@ and a parser @next@ and parses @ops? next@.
makeUnaryOp :: DParser Token -> DParser Expr -> DParser Expr
makeUnaryOp op next = doUnary <|> next
    where doUnary = UnaryOp <$> getPosition
                    <*> (op <?> "unary operator")
                    <*> (makeUnaryOp op next)

-- | This is the parser for decaf expressions.  The general strategy
-- for parsing is that operators become parser generators (which are
-- of type @DParser Expr -> DParser Expr@), and these generators are
-- applied to the @nullary@ parser from high to low precedence, where
-- the @nullary@ parser gives literals, method calls, etc.  This
-- sufficiently /hacks the grammar/ so that order of operations are
-- parsed correctly.
expr :: DParser Expr
expr = foldl (flip id) nullary ops
    where
      nullary :: DParser Expr
      nullary = (ExprMethod <$> getPosition <*> methodCall)
                <|> (LoadLoc <$> getPosition <*> location)
                <|> literal
                <|> between dopenp dclosep expr
      -- | The precedence is from highest to lowest.
      ops :: [DParser Expr -> DParser Expr]
      ops = [ doNegateOp
            , unOps ["!"]
            , binOps ["*", "/", "%"]
            , binOps ["+", "-"]
            , binOps ["<", "<=", ">=", ">"]
            , binOps ["==", "!="]
            , binOps ["&&"]
            , binOps ["||"]
            ]
      unOps, binOps :: [String] -> DParser Expr -> DParser Expr
      unOps = makeUnaryOp . dkeywords
      binOps = makeBinOp . dkeywords
      
      -- | This is a modification of @unOps ["-"]@ so that we first
      -- try to parse the negation as the negative of a number.
      doNegateOp :: DParser Expr -> DParser Expr
      doNegateOp next = try (op *> intParse) <|> negOp
          where negOp = makeUnaryOp op next
                op = dkeyword "-"
                intParse = ExprIntLiteral <$> getPosition
                           <*> (parseInt64 True <$> (tokenString <$> dtoken IntLiteral))


-- | Parses integer, character, and boolean literals.
literal :: DParser Expr
literal = intParse
          <|> (ExprLiteral <$> getPosition
               <*> (dtoken CharLiteral <|> dtoken BooleanLiteral)
               <?> "literal")
    where intParse = ExprIntLiteral <$> getPosition
                     <*> (parseInt64 False <$> (tokenString <$> dtoken IntLiteral))

-- | Parses identifiers.
ident :: DParser Token
ident = dtoken Identifier

-- | Parses a string into an Int64
parseInt64 :: Bool -> String -> Int64
parseInt64 neg s =
    case s of
      ('0':'x':_) -> justRead
      ('0':'b':rest) -> let loop ('0':s') v = loop s' 2*v
                            loop ('1':s') v = loop s' (2*v + (if neg then -1 else 1))
                            loop _ v = v
                        in loop rest 0
      _ -> justRead
    where justRead = read (if neg then '-':s else s)
