open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aesTheory aes_specTheory;

val _ = new_theory "aes_symb_exec";

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = birs_stepLib.patch_lifter_thm bir_aes_riscv_lift_THM;
val _ = birs_stepLib.prepare_program_lookups bir_lift_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_aes_prog_def
  aes_init_addr_def [aes_end_addr_def]
(*  aes_init_addr_def [aes_end1_addr_def,aes_end2_addr_def]*)
(*  aes_init_addr_def [aes_end1_addr_def]*)
  bspec_aes_pre_def aes_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem aes_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem aes_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
