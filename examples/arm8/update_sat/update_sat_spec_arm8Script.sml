open HolKernel boolLib Parse bossLib;

open markerTheory;

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

val _ = new_theory "update_sat_spec_arm8";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition update_sat_init_addr_def:
 update_sat_init_addr : word64 = 0x718w
End

Definition update_sat_end_addr_def:
 update_sat_end_addr : word64 = 0x734w
End

(* -------------- *)
(* ARMv8 contract *)
(* -------------- *)

Definition arm8_update_sat_pre_def:
 arm8_update_sat_pre (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) (s:arm8_state) : bool =
  ((((-(2147483647w : word64)) - (1w : word64)) < pre_x2) /\
  (pre_x2 < pre_x3) /\
  (pre_x2 <= pre_x1) /\
  (pre_x1 <= pre_x3) /\
  (pre_x3 < (2147483647w : word64)) /\
  (pre_x3 = (s.REG 3w)) /\
  (pre_x2 = (s.REG 2w)) /\
  (pre_x1 = (s.REG 1w)) /\
  (pre_x0 = (s.REG 0w)))
End

Definition arm8_update_sat_post_def:
 arm8_update_sat_post (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) (st:arm8_state) : bool =
  (((pre_x0 = (0w : word64)) ==> ((st.REG 0w) = (word_smax pre_x2 (pre_x1 - (1w : word64)) : word64))) /\
  ((pre_x0 <> (0w : word64)) ==> ((st.REG 0w) = (word_smin pre_x3 (pre_x1 + (1w : word64)) : word64))))
End

val _ = export_theory ();
