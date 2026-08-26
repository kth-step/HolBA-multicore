open HolKernel boolLib Parse bossLib;

open markerTheory;

open holba_auxiliaryTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open update_sat_spec_arm8Theory;

val _ = new_theory "update_sat_spec_bir";

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_update_sat_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
     BIExp_SignedLessThan
      (BExp_BinExp BIExp_Minus (BExp_UnaryExp BIExp_ChangeSign (BExp_Const (Imm64 2147483647w))) (BExp_Const (Imm64 1w)))
      (BExp_Const (Imm64 pre_x2))``,

  ``BExp_BinPred
     BIExp_SignedLessThan
      (BExp_Const (Imm64 pre_x2))
      (BExp_Const (Imm64 pre_x3))``,

  ``BExp_BinPred
     BIExp_SignedLessOrEqual
      (BExp_Const (Imm64 pre_x2))
      (BExp_Const (Imm64 pre_x1))``,

  ``BExp_BinPred
     BIExp_SignedLessOrEqual
      (BExp_Const (Imm64 pre_x1))
      (BExp_Const (Imm64 pre_x3))``,

  ``BExp_BinPred
     BIExp_SignedLessThan
      (BExp_Den (BVar "R3" (BType_Imm Bit64)))
      (BExp_Const (Imm64 2147483647w))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x3))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x2))``,

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x1))``,                

 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x0))``
];

Definition bspec_update_sat_pre_def:
 bspec_update_sat_pre (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_update_sat_pre_tm
End

val bspec_update_sat_post_or_1_tm = bslSyntax.borl [
  ``BExp_UnaryExp BIExp_Not
       (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
          (BExp_Const (Imm64 pre_x0))
          (BExp_Const (Imm64 0w)))
        (BExp_BinPred BIExp_SignedLessThan
          (BExp_BinExp BIExp_Minus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))
          (BExp_Const (Imm64 pre_x2))))``,

   ``BExp_BinPred BIExp_Equal
       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
       (BExp_Const (Imm64 pre_x2))``
];

val bspec_update_sat_post_or_2_tm = bslSyntax.borl [
  ``BExp_UnaryExp BIExp_Not
       (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
          (BExp_Const (Imm64 pre_x0))
          (BExp_Const (Imm64 0w)))
        (BExp_BinPred BIExp_SignedLessOrEqual
          (BExp_Const (Imm64 pre_x2))
          (BExp_BinExp BIExp_Minus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))))``,

   ``BExp_BinPred BIExp_Equal
       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
       (BExp_BinExp BIExp_Minus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))``
];

val bspec_update_sat_post_or_3_tm = bslSyntax.borl [
  ``BExp_UnaryExp BIExp_Not
       (BExp_BinExp BIExp_And
        (BExp_UnaryExp BIExp_Not
         (BExp_BinPred BIExp_Equal
           (BExp_Const (Imm64 pre_x0))
           (BExp_Const (Imm64 0w))))
        (BExp_BinPred BIExp_SignedLessThan
          (BExp_Const (Imm64 pre_x3))
          (BExp_BinExp BIExp_Plus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))
          ))``,

   ``BExp_BinPred BIExp_Equal
       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
       (BExp_Const (Imm64 pre_x3))``
];

val bspec_update_sat_post_or_4_tm = bslSyntax.borl [
  ``BExp_UnaryExp BIExp_Not
       (BExp_BinExp BIExp_And
        (BExp_UnaryExp BIExp_Not
         (BExp_BinPred BIExp_Equal
           (BExp_Const (Imm64 pre_x0))
           (BExp_Const (Imm64 0w))))
        (BExp_BinPred BIExp_SignedLessOrEqual
          (BExp_BinExp BIExp_Plus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))
          (BExp_Const (Imm64 pre_x3))
          ))``,

   ``BExp_BinPred BIExp_Equal
       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
       (BExp_BinExp BIExp_Plus
            (BExp_Const (Imm64 pre_x1))
            (BExp_Const (Imm64 1w)))``
];

val bspec_update_sat_post_tm = bslSyntax.bandl [
  bspec_update_sat_post_or_1_tm,
  bspec_update_sat_post_or_2_tm,
  bspec_update_sat_post_or_3_tm,
  bspec_update_sat_post_or_4_tm
];

Definition bspec_update_sat_post_def:
 bspec_update_sat_post (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_update_sat_post_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem update_sat_arm8_pre_imp_bspec_pre_thm:
  bir_pre_arm8_to_bir
   (arm8_update_sat_pre pre_x0 pre_x1 pre_x2 pre_x3)
   (bspec_update_sat_pre pre_x0 pre_x1 pre_x2 pre_x3)
Proof
 cheat
QED

Theorem update_sat_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8
  (arm8_update_sat_post pre_x0 pre_x1 pre_x2 pre_x3)
  (\l. bspec_update_sat_post pre_x0 pre_x1 pre_x2 pre_x3) ls
Proof
 cheat
QED

val _ = export_theory ();
