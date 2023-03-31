(*
 * Provides some automation to reduce a bir_get_current_statement lookup for
 * programs consisting of bmc_stmt_basic_t 
 *)

structure bir_programLib :> bir_programLib =
struct

open HolKernel Parse boolLib bossLib;
open bir_programTheory;

val is_fun_ty = can Type.dom_rng

(* destructs 'a -> 'b -> 'c to list ['a,'b,'c] *)
fun dest_fun_ty ty =
if not $ is_fun_ty ty then [ty] else
let val (dom,rng) = Type.dom_rng ty
in
  dom::dest_fun_ty rng
end

(*
 * outputs a conjunct theorem that allows to rewrite terms of the shape
 *    bir_get_current_statement prog pc = SOME _
 *)
fun bgcs_bmc_prog_thms prog =
let
  (*
  val prog = ``spinlock_concrete2 blocks unlock_entry``
  val prog = ``BirProgram $ lock lock_addr lock_entry``
  *)
  val lhs_tm = mk_icomb(``bir_get_current_statement``,prog)
    |> (fn tm => mk_icomb(tm,mk_var("pc",``:bir_programcounter_t``)))
  val constructors = TypeBase.constructors_of ``:bmc_stmt_basic_t``
  val thms_BSGen = map (fn constr =>
    let
      (*
      val constr = List.hd constructors
      *)
      val tys = dest_fun_ty $ type_of constr
      val len = length tys
      val arg_tys = List.take(tys,len-1)
      val var_prefix = "x"
      val rhs_tm1 = List.foldl (mk_comb o swap) constr $
        mapi (fn i => fn ty => mk_var(var_prefix ^ Int.toString i, ty)) arg_tys
      val rhs_tm1_ty = type_of rhs_tm1
      val rhs_tm = mk_icomb(``SOME``, mk_icomb(``BSGen``, mk_icomb(``BStmtB``, rhs_tm1)))
      val rhs_tm_ty = type_of rhs_tm
      val eq_comb = mk_icomb(``$=``,lhs_tm)
      val eq_arg_ty = type_of lhs_tm
      val subst = Type.match_type rhs_tm_ty eq_arg_ty
      val eq_tm = mk_comb(eq_comb, Term.inst subst rhs_tm)
      val eq_eval_thm = EVAL eq_tm
      (*
      val eq_eval_thm =
        EVAL ``bir_get_current_statement (spinlock_concrete2 blocks unlock_entry) pc
          = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel``
      *)
    in
      eq_eval_thm
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
      |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
      |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
    end
  ) constructors
  val thm_BSExt = 
    let
      val eq_comb = mk_icomb(``$=``,lhs_tm)
      val eq_arg_ty = type_of lhs_tm
      val out_tm = ``SOME $ BSExt R``
      val out_tm_ty = type_of out_tm
      val subst = Type.match_type out_tm_ty eq_arg_ty
      val eq_tm = mk_comb(eq_comb, Term.inst subst out_tm)
    in
      EVAL eq_tm
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
      |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
      |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
    end
  (*
  EVAL ``bir_get_current_statement (spinlock_concrete2 blocks unlock_entry) pc
    = SOME $ BSGen $ BStmtE x``
  *)
  val thm_BSGenBStmtE = 
    let
      val eq_comb = mk_icomb(``$=``,lhs_tm)
      val eq_arg_ty = type_of lhs_tm
      val out_tm = ``SOME $ BSGen $ BStmtE x``
      val out_tm_ty = type_of out_tm
      val subst = Type.match_type out_tm_ty eq_arg_ty
      val eq_tm = mk_comb(eq_comb, Term.inst subst out_tm)
    in
      EVAL eq_tm
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
      |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
      |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
      |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
    end
in
  LIST_CONJ $ map GEN_ALL $ thm_BSExt :: thm_BSGenBStmtE :: thms_BSGen
end

(*
 * output labels of program
 *)
fun blop_prog_labels_thm prog =
  EVAL $ mk_icomb(``bir_labels_of_program``,prog)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [listTheory.MAP_APPEND]

end
