module TigerPretty where

import TigerAbs

import Data.Text (unpack)
import Text.PrettyPrint
import Data.List 

-- Sinonimos cortos
ppV = render . prettyVar
ppD = render . prettyDec
ppE = render . prettyExp

tabWidth = 4 

-- sinonimos
colonEquals = text ":=" 

-- Variables
prettyVar (SimpleVar s) = text $ unpack s
prettyVar (FieldVar v s) = prettyVar v <> text "." <> (text $ unpack s)
prettyVar (SubscriptVar v e) = prettyVar v <> (brackets $ prettyExp e)

-- Operaciones
prettyOp PlusOp   = text "+"
prettyOp MinusOp  = text "-"
prettyOp TimesOp  = text "*"
prettyOp DivideOp = text "/"
prettyOp NeqOp    = text "<>"
prettyOp LtOp     = text "<"
prettyOp LeOp     = text "<="
prettyOp GtOp     = text ">"
prettyOp GeOp     = text ">="
prettyOp EqOp     = equals

-- Tipos
prettyTy (NameTy s) = text (unpack s)
prettyTy (RecordTy r) = lbrace <+> prettyField r <+> rbrace 
prettyTy (ArrayTy s) = text "array of" <+> text (unpack s)

-- Records
prettyField r = hsep $ punctuate comma fields 
                    where fields = map (\(s, b, t) -> text (unpack s) <> colon <> prettyTy t) r

-- Declaraciones
prettyDec (VarDec s _ (Just r) e _) = text "var" <+> (text $ unpack s) <> colon <> (text $ unpack r) <+> equals <+> prettyExp e
prettyDec (VarDec s _ Nothing e _) = text "var" <+> (text $ unpack s) <+> colonEquals <+> prettyExp e
prettyDec (TypeDec f) = vcat $ map (\(s, ty, _) -> text "type" <+> (text $ unpack s) <+> equals <+> prettyTy ty) f
prettyDec (FunctionDec f) = vcat $ map functionDec f
    where functionDec (s, f, Just r, e, _) = hang (text "function" <+> (text $ unpack s) <> (parens $ prettyField f) <> 
                                                    colon <> (text $ unpack r) <+> (equals)) tabWidth (prettyExp e)  
          functionDec (s, f, Nothing, e, _) = hang (text "function" <+> (text $ unpack s) <> (parens $ prettyField f) <+> 
                                                    (equals)) tabWidth (prettyExp e)

-- Expresiones
prettyExp (VarExp v _) = prettyVar v
prettyExp (UnitExp _) = text "()"
prettyExp (NilExp _) = text "nil"
prettyExp (IntExp i _) = text $ show i
prettyExp (StringExp s _) = doubleQuotes $ text s
prettyExp (CallExp s args _) = text (unpack s) <> (parens $ hcat $ punctuate (comma <> space) $ map prettyExp args)
prettyExp (OpExp e1 op e2 _) = prettyExp e1 <+> prettyOp op <+> prettyExp e2
prettyExp (SeqExp e _) = parens $ vcat $ punctuate semi (map prettyExp e)
prettyExp (AssignExp v e _) = prettyVar v <+> colonEquals <+> prettyExp e
prettyExp (IfExp e e1 (Just e2) _) = (hang (text "if" <+> prettyExp e <+> text "then") tabWidth (prettyExp e1)) $$ text "else" <+> prettyExp e2
prettyExp (IfExp e e1 Nothing _) = hang (text "if" <+> prettyExp e <+> text "then") tabWidth (prettyExp e1)
prettyExp (WhileExp e e1 _) = hang (text "while" <+> prettyExp e) tabWidth (prettyExp e1)
prettyExp (ForExp s _ e1 e2 e3 _) = hang (text "for" <+> text (unpack s) <+> colonEquals <+> prettyExp e1 <+> text "to" <+> prettyExp e2) tabWidth (prettyExp e3)
prettyExp (LetExp d e _) = text "let" <+> nest tabWidth (vcat (map prettyDec d)) $$ text "in" <+> prettyExp e $$ text "end"
prettyExp (BreakExp _) = text "break"
prettyExp (ArrayExp s e1 e2 _) = text (unpack s) <> brackets (prettyExp e1) <+> text "of" <+> prettyExp e2
prettyExp (RecordExp r n _) = text (unpack n) <> lbrace  <> recordElems r <> rbrace 
    where recordElems r = hsep (punctuate comma (map (\(s,e) -> text (unpack s) <+> equals <+> prettyExp e) r)) 

renderExp = render . prettyExp
