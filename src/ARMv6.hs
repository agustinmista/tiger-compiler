module ARMv6 where

import TigerAbs
import TigerParser
import TigerEscap
import TigerPretty
import TigerSeman
import TigerTips
import TigerPrettyIr
import TigerTrans
import TigerFrame
import TigerCanon
import TigerTemp
import qualified TigerTree as Tree

import qualified Data.Text as T



type Comment = T.Text

type Instruction = (ARMInst, Maybe Comment)

data ARMInst 
    = MoveInst Temp Temp
    | ARMInst ARMInst [Temp] [Temp]
    | LabelInst Temp

data ARMInst
    = ADD   -- ADD Rd, Rn, <Operand2>  
            -- ADD Rd, Rn, #<imm12>
    | SUB   -- SUB Rd, Rn, <Operand2>
            -- SUB Rd, Rn, #<imm12>
    | MUL   -- MUL Rd, Rm, Rs  (Rd=Rm*Rs)
    | SDIV  -- SDIV Rd, Rn, Rm (Rd=Rn/Rm)
    | MOV   -- MOV Rd, <Operand2>
    | CMP   -- CMP Rn, <Operand2> (Rn - Operand2)
    | AND   -- AND Rd, Rn, <Operand2>
    | ORR   -- ORR Rd, Rn, <Operand2>
    | EOR   -- EOR Rd, Rn, <Operand2>
    | BL    -- BL <label>
    | STR   -- STR Rd, [Rn {, #<offset>}]
            -- STR Rd, [Rn, +/-Rm]
            -- STR Rd, [Rn]
    | LDR   -- LDR Rd, [Rn, {, #<offset>}]
            -- LDR Rd, [Rn, +/-Rm]
            -- LDR Rd, [Rn]
    | PUSH  -- PUSH <reglist>
    | POP   -- POP  <reglist>


transStm :: Stm -> [Instruction]
transStm (Move (Temp src) (Temp dst)) = [(MoveInst src dst, Nothing)]
transStm (Move exp1 exp2) = []
transStm (ExpS exp) = transExp exp
transStm (Jump exp lbl) = [(ARMInst BL [lbl] [], Nothing)]
transStm (CJump op te fe tlbl flbl) = undefined 
transStm (Seq s1 s2) = transStm s1 ++ transStm s2
transStm (Label lbl) = [(LabelInst lbl, Nothing)]

transExp = undefined



