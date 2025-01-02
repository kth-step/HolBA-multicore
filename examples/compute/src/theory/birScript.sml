(* generated by Ott 0.34 from: ../../ott/bir.ott *)
(* to compile: Holmake birTheory.uo   *)
(* for interactive use:
  app load ["pred_setTheory","finite_mapTheory","stringTheory","containerTheory","ottLib"];
*)

open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "bir";

open wordsTheory;
open bitstringTheory numeral_bitTheory;

Type mmap = ``:(num |-> num)`` (* BIR memory map *)
Type ident = ``:string`` (* Identifier *)
Type k = ``:num``

Type word_one = ``:word1``

Type word_eight = ``:word8``

Type word_sixteen = ``:word16``

Type word_thirtytwo = ``:word32``

Type word_sixtyfour = ``:word64``

Type word_hundredtwentyeight = ``:word128``
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
val _ = Hol_datatype ` 
bir_type_t =  (* general typing *)
   BType_Imm of bir_immtype_t
 | BType_Mem of bir_immtype_t => bir_immtype_t
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

(* Utility functions *)
Definition bir_dest_bool_val_def:
  (bir_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_dest_bool_val _ = NONE)
End

Definition val_from_imm_option_def:
  (val_from_imm_option NONE = NONE) /\
  (val_from_imm_option (SOME imm) = SOME (BVal_Imm imm))
End

(* ------ Env ------- *)

Datatype:
  bir_var_environment_t = BEnv (ident -> (bir_val_t option))
End

(* Lookup function *)
Definition bir_env_lookup_def:
  bir_env_lookup (BEnv env) (BVar id) = env id
End

(* Lookup relation *)
Definition bir_env_lookup_rel_def:
  bir_env_lookup_rel (BEnv env) (BVar id) a = (env id = (SOME a)) 
End

(* Empty environment *)
Definition bir_empty_env_def:
  bir_empty_env = BEnv (\x. NONE)
End

(* Update environment *)
(* Slightly differs from original as we don’t check for existence here *)
Definition bir_env_update_def:
  bir_env_update ((BEnv env):bir_var_environment_t) (BVar id) v = BEnv ((id =+ SOME v) env)
End

(* --------- Typing ------- *)

(* Gives the size of an immediate as a number *)
Definition size_of_bir_immtype_def:
  (size_of_bir_immtype Bit1 = 1) /\
  (size_of_bir_immtype Bit8 = 8) /\
  (size_of_bir_immtype Bit16 = 16) /\
  (size_of_bir_immtype Bit32 = 32) /\
  (size_of_bir_immtype Bit64 = 64) /\
  (size_of_bir_immtype Bit128 = 128) 
End

(* Typing function for immediates *)
Definition type_of_bir_imm_def:
  (type_of_bir_imm (Imm1 w) = Bit1) /\
  (type_of_bir_imm (Imm8 w) = Bit8) /\
  (type_of_bir_imm (Imm16 w) = Bit16) /\
  (type_of_bir_imm (Imm32 w) = Bit32) /\
  (type_of_bir_imm (Imm64 w) = Bit64) /\
  (type_of_bir_imm (Imm128 w) = Bit128)
End

(* Typing function for values *)
Definition type_of_bir_val_def:
  (type_of_bir_val (BVal_Imm imm) = (BType_Imm (type_of_bir_imm imm))) /\
  (type_of_bir_val (BVal_Mem aty vty mmap) = (BType_Mem aty vty) )
End

(* Gets the operator for a given binary operation *)
Definition bir_binexp_get_oper_def:
  (bir_binexp_get_oper BIExp_And = word_and) /\
  (bir_binexp_get_oper BIExp_Plus = word_add)
End

(* Gets the operator for a given unary operation *)
Definition bir_unaryexp_get_oper_def:
  (bir_unaryexp_get_oper BIExp_Not = word_1comp) /\
  (bir_unaryexp_get_oper BIExp_ChangeSign = word_2comp)
End

(* Gets the operator for a given binary predicate *)
Definition bir_binpred_get_oper_def:
  (bir_binpred_get_oper BIExp_Equal = $=) /\
  (bir_binpred_get_oper BIExp_LessThan = word_lo)
End

Type bir_var_environment_t = ``:bir_var_environment_t``

Type n = ``:num``
(** definitions *)

(* defns type_of_bir_exp *)
Inductive type_of_bir_exp:
(* defn type_of_bir_exp *)

[Type_BExp_Const:] (! (env:bir_var_environment_t) (bir_imm:bir_imm_t) .
(clause_name "Type_BExp_Const")
 ==> 
( ( type_of_bir_exp env (BExp_Const bir_imm) (BType_Imm  (type_of_bir_imm  bir_imm ) ) )))

[Type_BExp_MemConst:] (! (env:bir_var_environment_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) (mmap:mmap) .
(clause_name "Type_BExp_MemConst")
 ==> 
( ( type_of_bir_exp env (BExp_MemConst bir_immtype1 bir_immtype2 mmap) (BType_Mem bir_immtype1 bir_immtype2) )))

[Type_BExp_Den:] (! (env:bir_var_environment_t) (bir_var:bir_var_t) (bir_val:bir_val_t) .
(clause_name "Type_BExp_Den") /\
(( (bir_env_lookup_rel  env   bir_var   bir_val ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Den bir_var)  (type_of_bir_val  bir_val )  )))

[Type_BExp_BinExp:] (! (env:bir_var_environment_t) (bir_binexp:bir_binexp_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_BinExp") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Imm bir_immtype) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype) )))
 ==> 
( ( type_of_bir_exp env (BExp_BinExp bir_binexp bir_exp1 bir_exp2) (BType_Imm bir_immtype) )))

[Type_BExp_UnaryExp:] (! (env:bir_var_environment_t) (bir_unaryexp:bir_unaryexp_t) (bir_exp:bir_exp_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_UnaryExp") /\
(( ( type_of_bir_exp env bir_exp (BType_Imm bir_immtype) )))
 ==> 
( ( type_of_bir_exp env (BExp_UnaryExp bir_unaryexp bir_exp) (BType_Imm bir_immtype) )))

[Type_BExp_BinPred:] (! (env:bir_var_environment_t) (bir_binpred:bir_binpred_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_BinPred") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Imm bir_immtype) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype) )))
 ==> 
( ( type_of_bir_exp env (BExp_BinPred bir_binpred bir_exp1 bir_exp2) (BType_Imm Bit1) )))

[Type_BExp_IfThenElse:] (! (env:bir_var_environment_t) (bir_exp:bir_exp_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_type:bir_type_t) .
(clause_name "Type_BExp_IfThenElse") /\
(( ( type_of_bir_exp env bir_exp1 bir_type )) /\
( ( type_of_bir_exp env bir_exp2 bir_type )) /\
( ( type_of_bir_exp env bir_exp (BType_Imm Bit1) )))
 ==> 
( ( type_of_bir_exp env (BExp_IfThenElse bir_exp bir_exp1 bir_exp2) bir_type )))

[Type_BExp_Load_NoEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_immtype:bir_immtype_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) .
(clause_name "Type_BExp_Load_NoEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   =   1  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Load bir_exp1 bir_exp2 BEnd_NoEndian bir_immtype) (BType_Imm bir_immtype) )))

[Type_BExp_Load_BigEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_immtype:bir_immtype_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) .
(clause_name "Type_BExp_Load_BigEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Load bir_exp1 bir_exp2 BEnd_BigEndian bir_immtype) (BType_Imm bir_immtype) )))

[Type_BExp_Load_LittleEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_immtype:bir_immtype_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) .
(clause_name "Type_BExp_Load_LittleEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Load bir_exp1 bir_exp2 BEnd_LittleEndian bir_immtype) (BType_Imm bir_immtype) )))

[Type_BExp_Store_NoEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_exp3:bir_exp_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_Store_NoEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( ( type_of_bir_exp env bir_exp3 (BType_Imm bir_immtype) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   =   1  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Store bir_exp1 bir_exp2 BEnd_NoEndian bir_exp3) (BType_Mem bir_immtype1 bir_immtype2) )))

[Type_BExp_Store_BigEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_exp3:bir_exp_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_Store_BigEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( ( type_of_bir_exp env bir_exp3 (BType_Imm bir_immtype) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Store bir_exp1 bir_exp2 BEnd_BigEndian bir_exp3) (BType_Mem bir_immtype1 bir_immtype2) )))

[Type_BExp_Store_LittleEndian:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_exp3:bir_exp_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) (bir_immtype:bir_immtype_t) .
(clause_name "Type_BExp_Store_LittleEndian") /\
(( ( type_of_bir_exp env bir_exp1 (BType_Mem bir_immtype1 bir_immtype2) )) /\
( ( type_of_bir_exp env bir_exp2 (BType_Imm bir_immtype1) )) /\
( ( type_of_bir_exp env bir_exp3 (BType_Imm bir_immtype) )) /\
( (  (  (size_of_bir_immtype  bir_immtype )   MOD   (size_of_bir_immtype  bir_immtype2 )  )   =   0  ) ) /\
( (  (  (size_of_bir_immtype  bir_immtype )   DIV   (size_of_bir_immtype  bir_immtype2 )  )   <=   (2**  (size_of_bir_immtype  bir_immtype1 )  )  ) ))
 ==> 
( ( type_of_bir_exp env (BExp_Store bir_exp1 bir_exp2 BEnd_LittleEndian bir_exp3) (BType_Mem bir_immtype1 bir_immtype2) )))
End
(** definitions *)

(* defns bir_eval_binexp_imm *)
Inductive bir_eval_binexp_imm:
(* defn bir_eval_binexp_imm *)

[Eval_BinExp_Imm_One:] (! (bir_binexp:bir_binexp_t) (word_one:word_one) (word_one':word_one) .
(clause_name "Eval_BinExp_Imm_One")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm1 word_one) (Imm1 word_one') (Imm1  ((bir_binexp_get_oper  bir_binexp )  word_one   word_one' ) ) )))

[Eval_BinExp_Imm_Eight:] (! (bir_binexp:bir_binexp_t) (word_eight:word_eight) (word_eight':word_eight) .
(clause_name "Eval_BinExp_Imm_Eight")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm8 word_eight) (Imm8 word_eight') (Imm8  ((bir_binexp_get_oper  bir_binexp )  word_eight   word_eight' ) ) )))

[Eval_BinExp_Imm_Sixteen:] (! (bir_binexp:bir_binexp_t) (word_sixteen:word_sixteen) (word_sixteen':word_sixteen) .
(clause_name "Eval_BinExp_Imm_Sixteen")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm16 word_sixteen) (Imm16 word_sixteen') (Imm16  ((bir_binexp_get_oper  bir_binexp )  word_sixteen   word_sixteen' ) ) )))

[Eval_BinExp_Imm_Thirtytwo:] (! (bir_binexp:bir_binexp_t) (word_thirtytwo:word_thirtytwo) (word_thirtytwo':word_thirtytwo) .
(clause_name "Eval_BinExp_Imm_Thirtytwo")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm32 word_thirtytwo) (Imm32 word_thirtytwo') (Imm32  ((bir_binexp_get_oper  bir_binexp )  word_thirtytwo   word_thirtytwo' ) ) )))

[Eval_BinExp_Imm_Sixtyfour:] (! (bir_binexp:bir_binexp_t) (word_sixtyfour:word_sixtyfour) (word_sixtyfour':word_sixtyfour) .
(clause_name "Eval_BinExp_Imm_Sixtyfour")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm64 word_sixtyfour) (Imm64 word_sixtyfour') (Imm64  ((bir_binexp_get_oper  bir_binexp )  word_sixtyfour   word_sixtyfour' ) ) )))

[Eval_BinExp_Imm_Hundredtwentyeight:] (! (bir_binexp:bir_binexp_t) (word_hundredtwentyeight:word_hundredtwentyeight) (word_hundredtwentyeight':word_hundredtwentyeight) .
(clause_name "Eval_BinExp_Imm_Hundredtwentyeight")
 ==> 
( ( bir_eval_binexp_imm bir_binexp (Imm128 word_hundredtwentyeight) (Imm128 word_hundredtwentyeight') (Imm128  ((bir_binexp_get_oper  bir_binexp )  word_hundredtwentyeight   word_hundredtwentyeight' ) ) )))
End
(** definitions *)

(* defns bir_eval_unaryexp_imm *)
Inductive bir_eval_unaryexp_imm:
(* defn bir_eval_unaryexp_imm *)

[Eval_UnaryExp_Imm_One:] (! (bir_unaryexp:bir_unaryexp_t) (word_one:word_one) .
(clause_name "Eval_UnaryExp_Imm_One")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm1 word_one) (Imm1  ((bir_unaryexp_get_oper  bir_unaryexp )  word_one ) ) )))

[Eval_UnaryExp_Imm_Eight:] (! (bir_unaryexp:bir_unaryexp_t) (word_eight:word_eight) .
(clause_name "Eval_UnaryExp_Imm_Eight")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm8 word_eight) (Imm8  ((bir_unaryexp_get_oper  bir_unaryexp )  word_eight ) ) )))

[Eval_UnaryExp_Imm_Sixteen:] (! (bir_unaryexp:bir_unaryexp_t) (word_sixteen:word_sixteen) .
(clause_name "Eval_UnaryExp_Imm_Sixteen")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm16 word_sixteen) (Imm16  ((bir_unaryexp_get_oper  bir_unaryexp )  word_sixteen ) ) )))

[Eval_UnaryExp_Imm_Thirtytwo:] (! (bir_unaryexp:bir_unaryexp_t) (word_thirtytwo:word_thirtytwo) .
(clause_name "Eval_UnaryExp_Imm_Thirtytwo")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm32 word_thirtytwo) (Imm32  ((bir_unaryexp_get_oper  bir_unaryexp )  word_thirtytwo ) ) )))

[Eval_UnaryExp_Imm_Sixtyfour:] (! (bir_unaryexp:bir_unaryexp_t) (word_sixtyfour:word_sixtyfour) .
(clause_name "Eval_UnaryExp_Imm_Sixtyfour")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm64 word_sixtyfour) (Imm64  ((bir_unaryexp_get_oper  bir_unaryexp )  word_sixtyfour ) ) )))

[Eval_UnaryExp_Imm_Hundredtwentyeight:] (! (bir_unaryexp:bir_unaryexp_t) (word_hundredtwentyeight:word_hundredtwentyeight) .
(clause_name "Eval_UnaryExp_Imm_Hundredtwentyeight")
 ==> 
( ( bir_eval_unaryexp_imm bir_unaryexp (Imm128 word_hundredtwentyeight) (Imm128  ((bir_unaryexp_get_oper  bir_unaryexp )  word_hundredtwentyeight ) ) )))
End

(* Evaluates a general binary expression with values as parameters *)
Definition bir_eval_binexp_def:
  (bir_eval_binexp binexp (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm imm) =
    (bir_eval_binexp_imm binexp imm1 imm2 imm)) /\
  (bir_eval_binexp _ _ _ _ = F)
End

(* Evaluates a general unary expression with values as parameters *)
Definition bir_eval_unaryexp_def:
  (bir_eval_unaryexp unaryexp (BVal_Imm imm1) (BVal_Imm imm) =
    (bir_eval_unaryexp_imm unaryexp imm1 imm)) /\
  (bir_eval_unaryexp _ _ _ = F)
End

(* Evaluates a binary predicate of two immediates *)
Inductive bir_eval_binpred_imm:
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm1 w1) (Imm1 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm8 w1) (Imm8 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm16 w1) (Imm16 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm32 w1) (Imm32 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm64 w1) (Imm64 w2) ((bir_binpred_get_oper binpred) w1 w2)) /\
  (!binpred w1 w2. 
    bir_eval_binpred_imm binpred (Imm128 w1) (Imm128 w2) ((bir_binpred_get_oper binpred) w1 w2))
End

(* Evaluates a general binary predicate with values as parameters *)
Inductive bir_eval_binpred:
  (!binpred imm1 imm2 b. 
    (bir_eval_binpred_imm binpred imm1 imm2 b) ==>
    (bir_eval_binpred binpred (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm (bool2b b))))
End

(* Evaluates a general ifthenelse expression with values as parameters *)
Inductive bir_eval_ifthenelse:
[~BExp_IfThenElseT:]
  bir_eval_ifthenelse birT (v1:bir_val_t) (v2:bir_val_t) v1 

[~BExp_IfThenElseF:]
  bir_eval_ifthenelse birF v1 v2 v2
End

(* Number to Bitstring *)
Definition n2bs_def:
  (n2bs n Bit1   = Imm1   (n2w n)) /\
  (n2bs n Bit8   = Imm8   (n2w n)) /\
  (n2bs n Bit16  = Imm16  (n2w n)) /\
  (n2bs n Bit32  = Imm32  (n2w n)) /\
  (n2bs n Bit64  = Imm64  (n2w n)) /\
  (n2bs n Bit128 = Imm128 (n2w n))
End

(* Boolean list (vector) to bitstring *)
Definition v2bs_def:
  v2bs v s = n2bs (v2n v) s
End

(* Immediate to number *)
Definition b2n_def:
  (b2n ( Imm1   w ) = w2n w) /\
  (b2n ( Imm8   w ) = w2n w) /\
  (b2n ( Imm16  w ) = w2n w) /\
  (b2n ( Imm32  w ) = w2n w) /\
  (b2n ( Imm64  w ) = w2n w) /\
  (b2n ( Imm128 w ) = w2n w)
End

(* Immediate to bitstring *)
Definition b2v_def:
  (b2v ( Imm1   w ) = w2v w) /\
  (b2v ( Imm8   w ) = w2v w) /\
  (b2v ( Imm16  w ) = w2v w) /\
  (b2v ( Imm32  w ) = w2v w) /\
  (b2v ( Imm64  w ) = w2v w) /\
  (b2v ( Imm128 w ) = w2v w)
End

Definition bitstring_split_aux_def:
  (bitstring_split_aux 0 acc bs = NONE) /\
  (bitstring_split_aux n acc [] = SOME $ REVERSE acc) /\
  (bitstring_split_aux n acc bs =
    bitstring_split_aux n ((TAKE n bs)::acc) (DROP n bs))
Termination
  WF_REL_TAC `measure (\ (_, _, l). LENGTH l)` >>
  simp_tac list_ss []
End

(* Splits a bitstring in chunks of n bits *)
Definition bitstring_split_def:
  bitstring_split n bs = bitstring_split_aux n [] bs
End

Definition is_exp_well_typed_def:
  is_exp_well_typed env exp = ?ty. type_of_bir_exp env exp ty
End

(* Load a value from the mmap at the given address *)
Definition bir_load_mmap_def:
  bir_load_mmap (mmap: num |-> num) a =
      case FLOOKUP mmap a of
        | NONE => 0
        | SOME v => v
End

(* Concatenate multiple bitstrings to a number on the correct number of bits *)
Definition bir_mem_concat_def:
  bir_mem_concat vl rty = v2bs (FLAT vl) rty
End

(* Compute the address modulo the address space *)
Definition bir_mem_addr_def:
  bir_mem_addr aty a = MOD_2EXP (size_of_bir_immtype aty) a
End

(* Computes the number of memory splits we will read *)
Definition bir_number_of_mem_splits_def:
  bir_number_of_mem_splits vty rty aty =
    if ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) then
      if ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) then
          SOME ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty))
      else NONE
    else NONE
End

(* Load a bitstring at the given address from a mmap and pad it *)
Definition bir_load_bitstring_from_mmap_def:
  bir_load_bitstring_from_mmap vty mmap (a:num) =
    fixwidth (size_of_bir_immtype vty) (n2v (bir_load_mmap mmap a))
End
  
(* Load n splits of size vty from mmap starting at addr *) 
Definition bir_load_splits_from_mmap_def:
  bir_load_splits_from_mmap aty vty mmap addr n =
    (MAP (\k. bir_load_bitstring_from_mmap vty mmap (bir_mem_addr aty (addr + k))) (COUNT_LIST n)) 
End

(* Eval an already unpacked load expression *)
Inductive bir_eval_load_from_mem:
[~BEnd_BigEndian:]
  (!aty vty mmap addr rty n.
    (bir_number_of_mem_splits vty rty aty = SOME n)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_BigEndian addr 
      (BVal_Imm (bir_mem_concat (bir_load_splits_from_mmap aty vty mmap addr n) rty)))

[~BEnd_LittleEndian:]
  (!aty vty mmap addr rty n.
    (bir_number_of_mem_splits vty rty aty = SOME n)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_LittleEndian addr
      (BVal_Imm (bir_mem_concat (REVERSE (bir_load_splits_from_mmap aty vty mmap addr n)) rty)))

[~BEnd_NoEndian:]
  (!aty vty mmap addr rty.
    (bir_number_of_mem_splits vty rty aty = SOME 1)
    ==>
    bir_eval_load_from_mem vty rty aty mmap BEnd_NoEndian addr
      (BVal_Imm (bir_mem_concat (bir_load_splits_from_mmap aty vty mmap addr 1) rty)))
End

Definition bir_eval_load_def:
  (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm addr) en rty v = 
    bir_eval_load_from_mem vty rty aty mmap en (b2n addr) v) /\
  (bir_eval_load _ _ _ _ _ = F)
End

(* Add all the bitstrings in the mmap at address a *)
Definition bir_update_mmap_def:
  (bir_update_mmap aty mmap a [] = mmap) /\
  (bir_update_mmap aty mmap a (v::vs) =
    bir_update_mmap aty (FUPDATE mmap ((bir_mem_addr aty a), v2n v)) (SUC a) vs)
End

Inductive bir_eval_store_in_mem:
[~BEnd_BigEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME _) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_BigEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr ll))

[~BEnd_LittleEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME _) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_LittleEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr (REVERSE ll)))

[~BEnd_NoEndian:]
  !vty aty result mmap addr ll.
    (bir_number_of_mem_splits vty (type_of_bir_imm result) aty = SOME 1) /\
    (bitstring_split (size_of_bir_immtype vty) (b2v result) = SOME ll)
    ==>
    bir_eval_store_in_mem vty aty result mmap BEnd_NoEndian addr
      (BVal_Mem aty vty (bir_update_mmap aty mmap addr ll))
End

Definition bir_eval_store_def:
  (bir_eval_store (BVal_Mem aty vty mmap) (BVal_Imm addr) en (BVal_Imm result) v = 
    bir_eval_store_in_mem vty aty result mmap en (b2n addr) v) /\
  (bir_eval_store _ _ _ _ _ = F)
End

(** definitions *)

(* defns bir_eval_exp *)
Inductive bir_eval_exp:
(* defn bir_eval_exp *)

[Eval_BExp_Const:] (! (env:bir_var_environment_t) (bir_imm:bir_imm_t) .
(clause_name "Eval_BExp_Const")
 ==> 
( ( bir_eval_exp env (BExp_Const bir_imm) (BVal_Imm bir_imm) )))

[Eval_BExp_MemConst:] (! (env:bir_var_environment_t) (bir_immtype1:bir_immtype_t) (bir_immtype2:bir_immtype_t) (mmap:mmap) .
(clause_name "Eval_BExp_MemConst")
 ==> 
( ( bir_eval_exp env (BExp_MemConst bir_immtype1 bir_immtype2 mmap) (BVal_Mem bir_immtype1 bir_immtype2 mmap) )))

[Eval_BExp_Den:] (! (env:bir_var_environment_t) (bir_var:bir_var_t) (bir_val:bir_val_t) .
(clause_name "Eval_BExp_Den") /\
(( (bir_env_lookup_rel  env   bir_var   bir_val ) ))
 ==> 
( ( bir_eval_exp env (BExp_Den bir_var) bir_val )))

[Eval_BExp_BinExp:] (! (env:bir_var_environment_t) (bir_binexp:bir_binexp_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_val:bir_val_t) (bir_val1:bir_val_t) (bir_val2:bir_val_t) .
(clause_name "Eval_BExp_BinExp") /\
(( ( bir_eval_exp env bir_exp1 bir_val1 )) /\
( ( bir_eval_exp env bir_exp2 bir_val2 )) /\
( (bir_eval_binexp  bir_binexp   bir_val1   bir_val2   bir_val ) ))
 ==> 
( ( bir_eval_exp env (BExp_BinExp bir_binexp bir_exp1 bir_exp2) bir_val )))

[Eval_BExp_UnaryExp:] (! (env:bir_var_environment_t) (bir_unaryexp:bir_unaryexp_t) (bir_exp:bir_exp_t) (bir_val':bir_val_t) (bir_val:bir_val_t) .
(clause_name "Eval_BExp_UnaryExp") /\
(( ( bir_eval_exp env bir_exp bir_val )) /\
( (bir_eval_unaryexp  bir_unaryexp   bir_val   bir_val' ) ))
 ==> 
( ( bir_eval_exp env (BExp_UnaryExp bir_unaryexp bir_exp) bir_val' )))

[Eval_BExp_BinPred:] (! (env:bir_var_environment_t) (bir_binpred:bir_binpred_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_val:bir_val_t) (bir_val1:bir_val_t) (bir_val2:bir_val_t) .
(clause_name "Eval_BExp_BinPred") /\
(( ( bir_eval_exp env bir_exp1 bir_val1 )) /\
( ( bir_eval_exp env bir_exp2 bir_val2 )) /\
( (bir_eval_binpred  bir_binpred   bir_val1   bir_val2   bir_val ) ))
 ==> 
( ( bir_eval_exp env (BExp_BinPred bir_binpred bir_exp1 bir_exp2) bir_val )))

[Eval_BExp_IfThenElse:] (! (env:bir_var_environment_t) (bir_exp:bir_exp_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_val3:bir_val_t) (bir_val:bir_val_t) (bir_val1:bir_val_t) (bir_val2:bir_val_t) .
(clause_name "Eval_BExp_IfThenElse") /\
(( ( bir_eval_exp env bir_exp bir_val )) /\
( ( bir_eval_exp env bir_exp1 bir_val1 )) /\
( ( bir_eval_exp env bir_exp2 bir_val2 )) /\
( (bir_eval_ifthenelse  bir_val   bir_val1   bir_val2   bir_val3 ) ))
 ==> 
( ( bir_eval_exp env (BExp_IfThenElse bir_exp bir_exp1 bir_exp2) bir_val3 )))

[Eval_BExp_Load:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_endian:bir_endian_t) (bir_immtype:bir_immtype_t) (bir_val:bir_val_t) (bir_val1:bir_val_t) (bir_val2:bir_val_t) .
(clause_name "Eval_BExp_Load") /\
(( ( bir_eval_exp env bir_exp1 bir_val1 )) /\
( ( bir_eval_exp env bir_exp2 bir_val2 )) /\
( (bir_eval_load  bir_val1   bir_val2   bir_endian   bir_immtype   bir_val ) ))
 ==> 
( ( bir_eval_exp env (BExp_Load bir_exp1 bir_exp2 bir_endian bir_immtype) bir_val )))

[Eval_BExp_Store:] (! (env:bir_var_environment_t) (bir_exp1:bir_exp_t) (bir_exp2:bir_exp_t) (bir_endian:bir_endian_t) (bir_exp3:bir_exp_t) (bir_val:bir_val_t) (bir_val1:bir_val_t) (bir_val2:bir_val_t) (bir_val3:bir_val_t) .
(clause_name "Eval_BExp_Store") /\
(( ( bir_eval_exp env bir_exp1 bir_val1 )) /\
( ( bir_eval_exp env bir_exp2 bir_val2 )) /\
( ( bir_eval_exp env bir_exp3 bir_val3 )) /\
( (bir_eval_store  bir_val1   bir_val2   bir_endian   bir_val3   bir_val ) ))
 ==> 
( ( bir_eval_exp env (BExp_Store bir_exp1 bir_exp2 bir_endian bir_exp3) bir_val )))
End
val _ = Hol_datatype ` 
bir_label_t =  (* Label values for jumps *)
   BL_Label of ident
 | BL_Address of bir_imm_t
`;
val _ = Hol_datatype ` 
bir_label_exp_t =  (* Label expressions that may be computed *)
   BLE_Label of bir_label_t
 | BLE_Exp of bir_exp_t
`;
val _ = Hol_datatype ` 
bir_stmt_basic_t =  (* Statements inside a program block *)
   BStmt_Assign of bir_var_t => bir_exp_t
`;
val _ = Hol_datatype ` 
bir_stmt_end_t =  (* Statements at the end of a block *)
   BStmt_Jmp of bir_label_exp_t
 | BStmt_CJmp of bir_exp_t => bir_label_exp_t => bir_label_exp_t
`;
val _ = Hol_datatype ` 
bir_stmt_t =  (* General statement *)
   BStmtB of bir_stmt_basic_t
 | BStmtE of bir_stmt_end_t
`;

(* Block type : a label, basic statements and an end statement *)
Datatype:
  bir_block_t = <|
  bb_label          : bir_label_t;
  bb_statements     : bir_stmt_basic_t list;
  bb_last_statement : bir_stmt_end_t |>
End

(* Program counter : label of the current block and the offset inside the block *)
Datatype:
  bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>
End

Type bir_block_t = ``:bir_block_t``
val _ = Hol_datatype ` 
bir_program_t = 
   BirProgram of bir_block_t list
`;
val _ = Hol_datatype ` 
bir_status_t =  (* Program state *)
   BST_Running (* still running *)
 | BST_TypeError (* execution encountered a type error *)
 | BST_Failed (* execution failed *)
 | BST_JumpOutside of bir_label_t (* execution jumped to unknown label *)
`;

(* Program state *)
Datatype:
  bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t
|>
End

(* Increment a program counter *)
Definition bir_pc_next_def:
  bir_pc_next pc = pc with bpc_index updated_by SUC
End

(* Get the index and block at the given label *)
Definition bir_get_program_block_info_by_label_def:
  bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\(x:bir_block_t). x.bb_label = l) p
End

(* Checks whether a state is still running *)
Definition bir_state_is_terminated_def:
  bir_state_is_terminated st =
  (st.bst_status <> BST_Running)
End

(* Set the program state to Failed *)
Definition bir_state_set_failed_def:
  bir_state_set_failed st =
  (st with bst_status := BST_Failed)
End

(* Set the program state to TypeError *)
Definition bir_state_set_typeerror_def:
  bir_state_set_typeerror st =
  (st with bst_status := BST_TypeError)
End

(* Get the statement of a program at the given program counter *)
Definition bir_get_current_statement_def:
  bir_get_current_statement p pc = 
    case (bir_get_program_block_info_by_label p pc.bpc_label) of 
      | NONE => NONE
      | SOME (_, bl) => if (pc.bpc_index < LENGTH bl.bb_statements) 
                        then SOME (BStmtB (EL (pc.bpc_index) bl.bb_statements)) 
                        else (if pc.bpc_index = LENGTH bl.bb_statements 
                              then SOME (BStmtE bl.bb_last_statement) 
                              else NONE)
End

(* Get all the labels of a program *)
Definition bir_labels_of_program_def:
  bir_labels_of_program (BirProgram p) =
  MAP (\bl. bl.bb_label) p
End

Definition bir_stmts_of_block_def:
  bir_stmts_of_block b = 
    (BStmtE b.bb_last_statement) :: MAP (\bst. (BStmtB bst)) b.bb_statements
End

Definition bir_stmts_of_program_def:
  bir_stmts_of_program (BirProgram blist) = 
  FLAT (MAP (\bl. bir_stmts_of_block bl) blist)
End

(* Return the program counter at the start of the block *)
Definition bir_block_pc_def:
  bir_block_pc l = <| bpc_label := l; bpc_index := 0 |>
End

(* Increment pc in a state if necessary *)
Definition bir_state_next_def:
  bir_state_next st =
     if (bir_state_is_terminated st) then st else st with bst_pc updated_by bir_pc_next
End

(* Jump to a label *)
Definition bir_jmp_to_label_def:
  bir_jmp_to_label p
   (l : bir_label_t) (st : bir_state_t) =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))
End

(* Eval a label expression *)
Definition bir_eval_label_exp_def:
  (bir_eval_label_exp (BLE_Label l) env l' = (l = l')) /\
  (bir_eval_label_exp (BLE_Exp e) env (BL_Address i) = bir_eval_exp env e (BVal_Imm i)) /\
  (bir_eval_label_exp _ _ _ = F)
End

(* Eval a basic statement *)
Definition bir_eval_stmtB_def:
  (bir_eval_stmtB (BStmt_Assign v ex) st st' = 
    (?va. (bir_eval_exp st.bst_environ ex va) 
    /\ (st' = (st with bst_environ := (bir_env_update st.bst_environ v va)))))
End

(* Eval a Jmp statement *)
Definition bir_eval_stmt_jmp_def:
  bir_eval_stmt_jmp p le (st : bir_state_t) st' =
    (?l. bir_eval_label_exp le st.bst_environ l 
    /\ bir_jmp_to_label p l st = st')
End

(* Eval a CJmp statement *)
Definition bir_eval_stmt_cjmp_def:
  bir_eval_stmt_cjmp p ec l1 l2 (st : bir_state_t) st' =
    (if bir_eval_exp st.bst_environ ec birT then 
      bir_eval_stmt_jmp p l1 st st'
    else if bir_eval_exp st.bst_environ ec birF then
      bir_eval_stmt_jmp p l2 st st'
    else F)
End

(* Eval an end statement *)
Definition bir_eval_stmtE_def:
  (bir_eval_stmtE p (BStmt_Jmp le) st st' = bir_eval_stmt_jmp p le st st') /\
  (bir_eval_stmtE p (BStmt_CJmp e l1 l2) st st' = bir_eval_stmt_cjmp p e l1 l2 st st')
End


Type bir_state_t = ``:bir_state_t``

val _ = export_theory ();



