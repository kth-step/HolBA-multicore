(* generated by Ott 0.33 from: bir.ott *)
(* to compile: Holmake birTheory.uo   *)
(* for interactive use:
  app load ["pred_setTheory","finite_mapTheory","stringTheory","containerTheory","ottLib"];
*)

open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "bir_basic";

open wordsTheory;

Type mmap = ``:(num |-> num)`` (* BIR memory map *)
Type ident = ``:string`` (* Identifier for variable name *)
Type word_one = ``:word1`` (* 1-bit word *)
Type word_eight = ``:word8`` (* 8-bit word *)
Type word_sixteen = ``:word16`` (* 16-bit word *)
Type word_thirtytwo = ``:word32`` (* 32-bit word *)
Type word_sixtyfour = ``:word64`` (* 64-bit word *)
Type word_hundredtwentyeight = ``:word128`` (* 128-bit word *)
val _ = Hol_datatype ` 
bir_imm_t =  (* immediates *)
   Imm1 of word_one
 | Imm8 of word_eight
 | Imm16 of word_sixteen
 | Imm32 of word_thirtytwo
 | Imm64 of word_sixtyfour
 | Imm128 of word_hundredtwentyeight
`;
val _ = Hol_datatype ` 
bir_immtype_t =  (* immediate typing size *)
   Bit1
 | Bit8
 | Bit16
 | Bit32
 | Bit64
 | Bit128
`;
val _ = Hol_datatype ` 
bir_endian_t =  (* endian for memory operations *)
   BEnd_BigEndian
 | BEnd_LittleEndian
 | BEnd_NoEndian
`;
val _ = Hol_datatype ` 
bir_var_t =  (* variable to lookup in environment *)
   BVar of ident
`;
val _ = Hol_datatype ` 
bir_binexp_t =  (* binary expressions *)
   BIExp_And
 | BIExp_Plus
`;
val _ = Hol_datatype ` 
bir_unaryexp_t =  (* unary expressions *)
   BIExp_ChangeSign
 | BIExp_Not
`;
val _ = Hol_datatype ` 
bir_binpred_t =  (* binary predicates *)
   BIExp_Equal
 | BIExp_LessThan
`;
val _ = Hol_datatype ` 
bir_val_t =  (* values for evaluation relation *)
   BVal_Imm of bir_imm_t
 | BVal_Mem of bir_immtype_t => bir_immtype_t => mmap (* address type / value type *)
`;
val _ = Hol_datatype ` 
bir_type_t =  (* general typing *)
   BType_Imm of bir_immtype_t
 | BType_Mem of bir_immtype_t => bir_immtype_t
`;
val _ = Hol_datatype ` 
bir_exp_t =  (* BIR expressions *)
   BExp_Const of bir_imm_t
 | BExp_MemConst of bir_immtype_t => bir_immtype_t => mmap (* address type / value type *)
 | BExp_Den of bir_var_t
 | BExp_BinExp of bir_binexp_t => bir_exp_t => bir_exp_t
 | BExp_UnaryExp of bir_unaryexp_t => bir_exp_t
 | BExp_BinPred of bir_binpred_t => bir_exp_t => bir_exp_t
 | BExp_IfThenElse of bir_exp_t => bir_exp_t => bir_exp_t
 | BExp_Load of bir_exp_t => bir_exp_t => bir_endian_t => bir_immtype_t (* Memory value / Address Value (Imm) / Endian / Type of where to load *)
 | BExp_Store of bir_exp_t => bir_exp_t => bir_endian_t => bir_exp_t (* Memory value / Address Value (Imm) / Endian / Value to store *)
`;
(* Booleans *)

Definition bool2w_def:
  bool2w b = (if b then 1w else 0w):word1
End

Definition bool2b_def:
  bool2b b = Imm1 (bool2w b)
End

Definition birT_def:
  birT = BVal_Imm (Imm1 1w)
End

Definition birF_def:
  birF = BVal_Imm (Imm1 0w)
End

(* Correction Theorems of boolean functions *)
Theorem bool2b_T_eq_birT:
  BVal_Imm (bool2b T) = birT
Proof
  rw [bool2b_def, bool2w_def, birT_def]
QED

Theorem bool2b_F_eq_birF:
  BVal_Imm (bool2b F) = birF
Proof
  rw [bool2b_def, bool2w_def, birF_def]
QED

(* Utility functions *)
Definition bir_dest_bool_val_def:
  (bir_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_dest_bool_val _ = NONE)
End

Definition val_from_imm_option_def:
  (val_from_imm_option NONE = NONE) /\
  (val_from_imm_option (SOME imm) = SOME (BVal_Imm imm))
End


val _ = export_theory ();



