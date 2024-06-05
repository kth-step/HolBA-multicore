open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open isqrtTheory isqrt_propTheory;
open swapTheory swap_symb_transfTheory swap_propTheory;
open mod2Theory mod2_symb_transfTheory mod2_propTheory;
open incrTheory incr_symb_transfTheory incr_propTheory;

fun print_and_check_thm name thm t_concl =
  let
    val _ = print (name ^ ":\n");
    val _ = print "===============================\n";
    val _ = (Hol_pp.print_thm thm; print "\n");
    val _ = if identical (concl thm) t_concl then () else
            raise Fail "print_and_check_thm::conclusion is not as expected"
    val _ = print "\n\n";
  in
    ()
  end;

(* ---- *)
(* swap *)
(* ---- *)

val _ = print_and_check_thm
  "swap RISC-V lift theorem"
  bir_swap_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0w : word64) (32w : word64))
   bir_swap_progbin
   (bir_swap_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "swap BIR contract theorem"
  bspec_cont_swap
  ``bir_cont (bir_swap_prog : 'a bir_program_t)
    bir_exp_true (BL_Address (Imm64 0x00w))
    {BL_Address (Imm64 0x14w)} {}
    (bspec_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
    (\l. if l = BL_Address (Imm64 0x14w)
         then (bspec_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
         else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "swap RISC-V backlifted theorem"
  riscv_cont_swap
  ``riscv_cont
     bir_swap_progbin
     0w {0x14w}
     (riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
     (riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)``;

(* ---- *)
(* incr *)
(* ---- *)
  
val _ = print_and_check_thm
  "incr RISC-V lift theorem"
  bir_incr_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0w : word64) (8w : word64))
   bir_incr_progbin
   (bir_incr_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "incr BIR contract theorem"
  bir_cont_incr
 ``bir_cont (bir_incr_prog : 'a bir_program_t)
  bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_incr_pre pre_x10)
   (\l. if l = BL_Address (Imm64 4w) then (bir_incr_post pre_x10)
        else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "incr RISC-V backlifted theorem"
  riscv_cont_incr
  ``riscv_cont
     bir_incr_progbin
     0w {4w}
     (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)``;

(* ---- *)
(* mod2 *)
(* ---- *)

val _ = print_and_check_thm
  "mod2 RISC-V lift theorem"
  bir_mod2_riscv_lift_THM
  ``
  bir_is_lifted_prog riscv_bmr (WI_end (0w : word64) (8w : word64))
   bir_mod2_progbin
   (bir_mod2_prog : 'observation_type bir_program_t)
  ``;

val _ = print_and_check_thm
  "mod2 BIR contract theorem"
  bir_cont_mod2
 ``bir_cont (bir_mod2_prog : 'a bir_program_t)
  bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 4w)} {} (bir_mod2_pre pre_x10)
   (\l. if l = BL_Address (Imm64 4w) then (bir_mod2_post pre_x10)
        else bir_exp_false)
  ``;

val _ = print_and_check_thm
  "mod2 RISC-V backlifted theorem"
  riscv_cont_mod2
  ``riscv_cont
     bir_mod2_progbin
     0w {4w}
     (riscv_mod2_pre pre_x10) (riscv_mod2_post pre_x10)``;
