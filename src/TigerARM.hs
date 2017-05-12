module TigerARM where

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
    | LabelInst Temp
    | ARMInst ARMOp [Temp] [Temp]

data ARMOp
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
