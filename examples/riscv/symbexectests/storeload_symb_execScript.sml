open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open distribute_generic_stuffTheory;

open storeloadTheory;
open storeload_specTheory;

val _ = new_theory "storeload_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Theorem storeload_prog_vars_thm0 =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_storeload_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_storeload_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) storeload_prog_vars_thm0;
val registervars_tm = listSyntax.mk_list (all_vars, (type_of o hd) all_vars);

Definition storeload_prog_vars_def:
  storeload_prog_vars = ^registervars_tm
End

Definition storeload_birenvtyl_def:
  storeload_birenvtyl = MAP BVarToPair storeload_prog_vars
End

Theorem storeload_prog_vars_thm:
  set storeload_prog_vars = bir_vars_of_program (bir_storeload_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [storeload_prog_vars_thm0, storeload_prog_vars_def]
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_storeload_prog_def
  storeload_init_addr_def [storeload_end_addr_def]
  bspec_storeload_pre_def storeload_birenvtyl_def;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem storeload_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
