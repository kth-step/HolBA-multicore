open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory;
open bir_exp_liftingLib bir_typing_expSyntax;
open bir_typing_expTheory;
open bir_extra_expsTheory;
open bir_lifter_general_auxTheory;
open bir_programSyntax bir_interval_expSyntax;
open bir_program_labelsTheory;
open bir_immTheory;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;

open add_regTheory;

val _ = new_theory "add_reg_spec_arm8";

(* whole program *)

Definition add_reg_init_addr_def:
 add_reg_init_addr : word64 = 0x1cw
End

Definition add_reg_end_addr_def:
 add_reg_end_addr : word64 = 0x48w
End

(* loop *)

Definition add_reg_init_loop_addr_def:
 add_reg_loop_init_addr : word64 = 0x20w
End

Definition add_reg_end_loop_addr_def:
 add_reg_loop_end_addr : word64 = 0x40w
End

(* contract *)

val ly_var = ``(m.REG 3w)``;
val lx_var = ``(m.REG 2w)``;

Definition arm8_add_reg_pre_def:
 arm8_add_reg_pre (pre_x : word64) (pre_y : word64) (m : arm8_state) : bool =
  (pre_x >= 0w /\ ^lx_var = pre_x /\ ^ly_var = pre_y)
End

Definition arm8_add_reg_post_def:
 arm8_add_reg_post (pre_x : word64) (pre_y : word64) (m : arm8_state) : bool =
  (pre_x + pre_y = ^ly_var)
End

val _ = export_theory ();
