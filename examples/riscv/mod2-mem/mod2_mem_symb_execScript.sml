open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open mod2_memTheory mod2_mem_specTheory;

val _ = new_theory "mod2_mem_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition mod2_mem_prog_vars_def:
  mod2_mem_prog_vars = [
   BVar "MEM8" (BType_Mem Bit64 Bit8);
   BVar "x10" (BType_Imm Bit64);
   BVar "x1" (BType_Imm Bit64)
  ]
End

Definition mod2_mem_birenvtyl_def:
  mod2_mem_birenvtyl = MAP BVarToPair mod2_mem_prog_vars
End

Theorem mod2_mem_prog_vars_thm:
  set mod2_mem_prog_vars = bir_vars_of_program (bir_mod2_mem_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_mod2_mem_prog_def, mod2_mem_prog_vars_def] >>
  EVAL_TAC
QED

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_mod2_mem_prog_def
  mod2_mem_init_addr_def [mod2_mem_end_addr_def]
  bspec_mod2_mem_pre_def mod2_mem_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem mod2_mem_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem mod2_mem_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
