module TigerParser where

import Text.Parsec
import Text.Parsec.String (Parser)

import qualified Text.Parsec.Token as Tok
import qualified Text.Parsec.Expr as Ex

import Data.Text hiding (map)

import TigerAbs
import TigerLexer

binary s f assoc ln = Ex.Infix (do
                        reservedOp s 
                        return (\e1 e2 -> OpExp e1 f e2 ln)) assoc

amperCmp ln = Ex.Infix (do
            reservedOp "&"
            return (\e1 e2 -> IfExp e1 e2 (Just (IntExp 0 ln)) ln)) Ex.AssocLeft

pipeCmp ln = Ex.Infix (do
            reservedOp "|"
            return (\e1 e2 -> IfExp e1 (IntExp 1 ln) (Just e2) ln)) Ex.AssocLeft

table ln = [
            [binary "*" TimesOp Ex.AssocLeft ln
            ,binary "/" DivideOp Ex.AssocLeft ln]
            ,
            [binary "+" PlusOp Ex.AssocLeft ln
            ,binary "-" MinusOp Ex.AssocLeft ln]
            ,
            [binary "=" EqOp Ex.AssocNone ln
            ,binary "<>" NeqOp Ex.AssocNone ln
            ,binary "<" LeOp Ex.AssocNone ln
            ,binary ">" GtOp Ex.AssocNone ln
            ,binary "<=" LeOp Ex.AssocNone ln
            ,binary ">=" GeOp Ex.AssocNone ln]
            ,[amperCmp ln]
            ,[pipeCmp ln]
        ]

int :: Parser Exp
int = do
    pos <- gline
    t <- number
    return (IntExp t pos)


v' :: Var -> Parser Var
v' var = (do
            dot
            s <- identifier
            v' (FieldVar var (pack s)))
            <|>
         (do
            e <- brackets expression
            v' (SubscriptVar var e))
            <|> return var


variable :: Parser Var
variable = do
    s <- identifier
    let st = SimpleVar $ pack s
    (v' st)

field :: Parser [Field]
field = 
    commaSep (do
        n <- identifier
        colon
        ty <- identifier 
        return (pack n, Nothing, NameTy (pack ty)))
ftype :: Parser (Maybe Symbol)
ftype = ( do
        ty <- identifier
        return (Just $ pack ty)
        ) <|> return Nothing

mTypo :: Parser (Maybe Symbol)
mTypo = (do
    colon
    ftype) <|> return Nothing

fundec :: Parser (Symbol,[Field], Maybe Symbol, Exp, Pos)
fundec = do
    p <- gline
    reserved "function"
    name <- identifier
    params <- parens field
    m <- mTypo
    symbol "="
    e <- expression
    return (pack $ name, params, m, e, p)
    
functiondec :: Parser Dec
functiondec = do 
        fs <- many1 fundec
        return (FunctionDec fs)

vardec :: Parser Dec
vardec = do
        p <- gline
        reserved "var"
        name <- identifier
        t <- mTypo
        e <- (case t of
            Nothing -> do
                symbol "="
                expression
            Just _ -> do
                symbol ":="
                expression)
        return (VarDec (pack name) Nothing t e p)

namety = do
    t <- identifier
    return (NameTy $ pack t)

rety = do
    f <- braces field 
    return (RecordTy f)
arrty = do
    reserved "array"
    reserved "of"
    id <- identifier
    return (ArrayTy $ pack id)

ty :: Parser Ty
ty = namety <|> rety <|> arrty 

tydec :: Parser (Symbol, Ty, Pos)
tydec = do
        p <- gline
        reserved "type"
        name <- identifier
        symbol "="
        t <- ty
        return (pack name, t, p)

tydecs = do
    dcs <- many1 tydec
    return (TypeDec dcs)

declarations :: Parser Dec
declarations =  functiondec 
                <|> tydecs
                <|> vardec

gline = do
    posSrc <- getPosition
    let (l,c) = (sourceLine posSrc, sourceColumn posSrc)
    return (Simple l c)

varexp :: Parser Exp
varexp = do
    p <- gline
    v <- variable
    return (VarExp v p)

letexp :: Parser Exp
letexp = do
    b <- gline 
    reserved "let"
    dcs <- many1 declarations
    reserved "in"
    b' <- gline
    body <- semiSep1 expression
    e <- gline
    reserved "end"
    if Prelude.length body == 1 then
        return (LetExp dcs (Prelude.head body) (Range b e))
    else
        return (LetExp dcs (SeqExp body b') (Range b e)) 


arrayexp :: Parser Exp
arrayexp = do
    p <- gline
    i <- identifier
    size <- brackets expression
    reserved "of"
    init <- expression
    return (ArrayExp (pack i) size init p)

breakexp = do
        p <- gline
        reserved "break"
        return (BreakExp p)

forexp :: Parser Exp
forexp = do
    p <- gline
    reserved "for"
    i <- identifier 
    symbol ":="
    lo <- expression
    reserved "to"
    hi <- expression
    reserved "do"
    body <- expression
    return (ForExp (pack i) Nothing lo hi body p)

whileexp :: Parser Exp
whileexp = do
    p <- gline
    reserved "while"
    cond <- expression
    reserved "do"
    body <- expression
    return (WhileExp cond body p)

ifexp :: Parser Exp -- Chequear el tema de la assoc del if
ifexp = do
    p <- gline
    reserved "if"
    c <- expression
    reserved "then"
    e <- expression
    (do
       reserved "else"
       ee <- expression
       return (IfExp c e (Just ee) p)
     <|> 
        return (IfExp c e Nothing p))

assignexp :: Parser Exp
assignexp = do  
    p <- gline
    v <- variable
    symbol ":="
    e <- expression
    return (AssignExp v e p)

seqexp :: Parser Exp
seqexp = do
    p <- gline
    es <- parens $ semiSep1 expression
    return (SeqExp es p)

recfld :: Parser (Symbol, Exp)
recfld = do
    i <- identifier
    reservedOp "="
    e <- expression
    return (pack i, e)

recordexp :: Parser Exp
recordexp = do
    p <- gline
    tname <- identifier
    fls <- braces $ commaSep1 recfld
    return (RecordExp fls (pack tname) p)

callexp :: Parser Exp
callexp = do
    p <- gline
    f <- identifier
    args <- parens $ commaSep expression
    return (CallExp (pack f) args p)

stringexp :: Parser Exp
stringexp = do
    p <- gline
    s <- stringLiteral
    return (StringExp s p)

nilexp :: Parser Exp
nilexp = do
    p <- gline
    reserved "nil"
    return (NilExp p)

expression :: Parser Exp
expression = whiteSpace >> parseexp

expression' :: Parser Exp
expression' = 
        try letexp
        <|> try callexp
        <|> try arrayexp
        <|> try recordexp
        <|> try forexp
        <|> try whileexp
        <|> try breakexp
        <|> try ifexp
        <|> try assignexp
        <|> try stringexp
        <|> try nilexp
        <|> varexp
        <|> int
        <|> seqexp 

parseexp :: Parser Exp
parseexp = do
    p <- gline
    try $ Ex.buildExpressionParser (table p) expression'
