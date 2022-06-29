open HolKernel Parse boolLib bossLib;
open BasicProvers;
open relationTheory;
open bir_programTheory;
open monadsyntax;
open alistTheory;
open listTheory;
open listRangeTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open stringTheory;
open dep_rewrite;

val _ = new_theory "bir_promising";

Theorem I_EQ_IDABS:
  I = λx. x
Proof
  fs[FUN_EQ_THM]
QED

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val _ = Datatype‘
  mem_msg_t = <|
    loc : bir_val_t;
    val : bir_val_t;
    cid : num
    |>
’;

(* Type of instruction and their arguments. *)
Datatype:
  bir_statement_type_t =
  | BirStmt_Read bir_var_t bir_exp_t ((bir_cast_t # bir_immtype_t) option) bool bool bool
  | BirStmt_Write bir_exp_t bir_exp_t bool bool bool
  | BirStmt_Amo bir_var_t bir_exp_t bir_exp_t bool bool
  | BirStmt_Expr bir_var_t bir_exp_t
  | BirStmt_Fence bir_memop_t bir_memop_t
  | BirStmt_Branch bir_exp_t bir_label_exp_t bir_label_exp_t
  | BirStmt_Generic ('a bir_stmt_t)
  | BirStmt_None
End

(* Default value of memory *)
val mem_default_value_def = Define ‘
  mem_default_value = BVal_Imm (Imm64 0w)
’;

val mem_default_def = Define‘
  mem_default l = <| loc := l; val := mem_default_value; cid := ARB |>
’;

val mem_get_def = Define‘
   mem_get M l 0 = SOME (mem_default l)
   /\
   mem_get M l (SUC t) =
   case oEL t M of
   | SOME $ SOME m => if m.loc = l then SOME m else NONE
   | _ => NONE
’;

Theorem mem_get_PRE:
  0 < t ==> mem_get M l t =
    case oEL (PRE t) M of
   | SOME $ SOME m => if m.loc = l then SOME m else NONE
   | _ => NONE
Proof
  Cases_on `t` >> fs[mem_get_def]
QED

Theorem mem_get_APPEND1:
  !t M M' l. t < LENGTH M + 1
  ==> mem_get (M ++ M') l t = mem_get M l t
Proof
  Cases
  >> rw[AllCaseEqs(),mem_get_def,oEL_THM,rich_listTheory.EL_APPEND1]
  >> qmatch_goalsub_abbrev_tac `EL n M` >> Cases_on `EL n M`
  >> fs[]
QED

Theorem mem_get_APPEND2:
  !t M M' M'' l. LENGTH M + LENGTH M' < t
  ==> mem_get (M ++ M' ++ M'') l t = mem_get (M ++ M'') l (t - LENGTH M')
Proof
  rpt gen_tac >> Cases_on `LENGTH M' = 0` >> fs[]
  >> fs[mem_get_PRE,AllCaseEqs()]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `oEL (PRE t) MMM`
  >> Cases_on `oEL (PRE t) MMM`
  >- (unabbrev_all_tac >> fs[oEL_THM,arithmeticTheory.NOT_LESS])
  >> unabbrev_all_tac
  >> fs[oEL_THM,arithmeticTheory.NOT_LESS]
  >> qmatch_assum_rename_tac `EL _ _ = x` >> Cases_on `x`
  >> gs[rich_listTheory.EL_APPEND1,arithmeticTheory.NOT_LESS,rich_listTheory.EL_APPEND2]
  >> qmatch_goalsub_abbrev_tac `EL m`
  >> qmatch_asmsub_abbrev_tac `EL m'`
  >> `m = m'` by (unabbrev_all_tac >> decide_tac)
  >> fs[]
QED

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
   mem_read M l t =
   case mem_get M l t of
   | SOME m => SOME m.val
   | _ => NONE
’;

Theorem mem_read_APPEND1:
  !t M M' l. t < LENGTH M + 1
  ==> mem_read (M ++ M') l t = mem_read M l t
Proof
  fs[mem_read_def,mem_get_APPEND1]
QED

Theorem mem_read_APPEND2:
  !t M M' M'' l. LENGTH M + LENGTH M' < t
  ==> mem_read (M ++ M' ++ M'') l t = mem_read (M ++ M'') l (t - LENGTH M')
Proof
  fs[mem_read_def,mem_get_APPEND2]
QED

val mem_is_loc_def = Define‘
   mem_is_loc M 0 l = T
   /\
   mem_is_loc M (SUC t) l =
   case oEL t M of
   | SOME $ SOME m => m.loc = l
   | _ => F
’;

Theorem mem_is_loc_PRE:
  0 < t ==> mem_is_loc M t l =
    case oEL (PRE t) M of
   | SOME $ SOME m => m.loc = l
   | _ => F
Proof
  Cases_on `t` >> fs[mem_is_loc_def]
QED

Theorem mem_is_loc_APPEND1:
  !t M M' l. t < LENGTH M + 1
  ==> mem_is_loc (M ++ M') t l = mem_is_loc M t l
Proof
  Cases
  >> rw[AllCaseEqs(),mem_is_loc_def,oEL_THM,rich_listTheory.EL_APPEND1]
  >> qmatch_goalsub_abbrev_tac `EL n M` >> Cases_on `EL n M`
  >> fs[]
QED

Theorem mem_is_loc_APPEND2:
  !t M M' M'' l. LENGTH M + LENGTH M' < t
  ==> mem_is_loc (M ++ M' ++ M'') t l = mem_is_loc (M ++ M'') (t - LENGTH M') l
Proof
  rpt gen_tac >> Cases_on `LENGTH M' = 0` >> fs[]
  >> fs[mem_is_loc_PRE,AllCaseEqs()]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `oEL (PRE t) MMM`
  >> Cases_on `oEL (PRE t) MMM`
  >- (unabbrev_all_tac >> fs[oEL_THM,arithmeticTheory.NOT_LESS])
  >> unabbrev_all_tac
  >> fs[oEL_THM,arithmeticTheory.NOT_LESS]
  >> qmatch_assum_rename_tac `EL _ _ = x` >> Cases_on `x`
  >> gs[rich_listTheory.EL_APPEND1,arithmeticTheory.NOT_LESS,rich_listTheory.EL_APPEND2]
  >> qmatch_goalsub_abbrev_tac `EL m`
  >> qmatch_asmsub_abbrev_tac `EL m'`
  >> `m = m'` by (unabbrev_all_tac >> decide_tac)
  >> fs[]
QED

Theorem mem_get_is_loc:
  !t M l.
    IS_SOME (mem_get M l t) = mem_is_loc M t l
Proof
  Cases
  >> fs [mem_get_def, mem_is_loc_def,EQ_IMP_THM]
  >> rpt gen_tac
  >> BasicProvers.every_case_tac
  >> fs[]
QED

val mem_is_cid_def = Define‘
   mem_is_cid M 0 cid = F
   /\
   mem_is_cid M (SUC t) cid =
   case oEL t M of
   | SOME $ SOME m => m.cid = cid
   | _ => F
’;

Theorem mem_is_cid_PRE:
  0 < t ==> mem_is_cid M t cid =
    case oEL (PRE t) M of
   | SOME $ SOME m => m.cid = cid
   | _ => F
Proof
  Cases_on `t` >> fs[mem_is_cid_def]
QED

Theorem mem_is_cid_APPEND1:
  !t M M' l. t < LENGTH M + 1
  ==> mem_is_cid (M ++ M') t l = mem_is_cid M t l
Proof
  Cases
  >> rw[AllCaseEqs(),mem_is_cid_def,oEL_THM,rich_listTheory.EL_APPEND1]
  >> qmatch_goalsub_abbrev_tac `EL n M` >> Cases_on `EL n M`
  >> fs[]
QED

Theorem mem_is_cid_APPEND2:
  !t M M' M'' l. LENGTH M + LENGTH M' < t
  ==> mem_is_cid (M ++ M' ++ M'') t l = mem_is_cid (M ++ M'') (t - LENGTH M') l
Proof
  rpt gen_tac >> Cases_on `LENGTH M' = 0` >> fs[]
  >> fs[mem_is_cid_PRE,AllCaseEqs()]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `oEL (PRE t) MMM`
  >> Cases_on `oEL (PRE t) MMM`
  >- (unabbrev_all_tac >> fs[oEL_THM,arithmeticTheory.NOT_LESS])
  >> unabbrev_all_tac
  >> fs[oEL_THM,arithmeticTheory.NOT_LESS]
  >> qmatch_assum_rename_tac `EL _ _ = x` >> Cases_on `x`
  >> gs[rich_listTheory.EL_APPEND1,arithmeticTheory.NOT_LESS,rich_listTheory.EL_APPEND2]
  >> qmatch_goalsub_abbrev_tac `EL m`
  >> qmatch_asmsub_abbrev_tac `EL m'`
  >> `m = m'` by (unabbrev_all_tac >> decide_tac)
  >> fs[]
QED


(* is_some_some *)
Definition is_some_some_def:
  is_some_some t M <=> 0 < t /\ t < LENGTH M /\ IS_SOME $ EL (PRE t) M
End

(* Note that this currently does not take into account ARM *)
val mem_read_view_def = Define‘
  mem_read_view (f:fwdb_t) t = if f.fwdb_time = t ∧ ~f.fwdb_xcl then f.fwdb_view else t
’;

(* global variables begin with an underscore *)

Definition is_global_def:
  is_global (BVar str ty) = isPREFIX "_" str
End

(* calculates the views of an expression, with views of global variables are always 0 *)

Definition bir_eval_view_of_exp_def:
  (bir_eval_view_of_exp (BExp_BinExp op e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_BinPred pred e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_UnaryExp op e) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Cast cty e ity) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Den v) viewenv =
    if is_global v then 0
    else case FLOOKUP viewenv v of NONE => 0 | SOME view => view)
/\ (bir_eval_view_of_exp exp viewenv = 0)
End

(* read from global memory if a variable is prefixed with an underscore, else
 * use the usual environment *)

Definition bir_eval_exp_mix_def:
  (bir_eval_exp_mix (BExp_Const n) env g_env = SOME (BVal_Imm n)) /\
  (bir_eval_exp_mix (BExp_MemConst aty vty mmap) env g_env = SOME (BVal_Mem aty vty mmap)) /\
  (bir_eval_exp_mix (BExp_Den v) env g_env =
    if is_global v
    then bir_env_read v g_env
    else bir_env_read v env) /\
  (bir_eval_exp_mix (BExp_Cast ct e ty) env g_env = bir_eval_cast ct (bir_eval_exp_mix e env g_env) ty) /\
  (bir_eval_exp_mix (BExp_UnaryExp et e) env g_env = bir_eval_unary_exp et (bir_eval_exp_mix e env g_env)) /\
  (bir_eval_exp_mix (BExp_BinExp et e1 e2) env g_env = bir_eval_bin_exp et (bir_eval_exp_mix e1 env g_env) (bir_eval_exp_mix e2 env g_env)) /\
  (bir_eval_exp_mix (BExp_BinPred pt e1 e2) env g_env = bir_eval_bin_pred pt (bir_eval_exp_mix e1 env g_env) (bir_eval_exp_mix e2 env g_env)) /\
  (bir_eval_exp_mix (BExp_MemEq e1 e2) env g_env = bir_eval_memeq (bir_eval_exp_mix e1 env g_env) (bir_eval_exp_mix e2 env g_env)) /\
  (bir_eval_exp_mix (BExp_IfThenElse c et ef) env g_env =
    bir_eval_ifthenelse (bir_eval_exp_mix c env g_env) (bir_eval_exp_mix et env g_env) (bir_eval_exp_mix ef env g_env)) /\
  (bir_eval_exp_mix (BExp_Load mem_e a_e en ty) env g_env =
    bir_eval_load (bir_eval_exp_mix mem_e env g_env) (bir_eval_exp_mix a_e env g_env) en ty) /\
  (bir_eval_exp_mix (BExp_Store mem_e a_e en v_e) env g_env =
    bir_eval_store (bir_eval_exp_mix mem_e env g_env) (bir_eval_exp_mix a_e env g_env) en (bir_eval_exp_mix v_e env g_env))
End

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
val bir_eval_exp_view_def = Define‘
  bir_eval_exp_view exp env viewenv genv =
  (bir_eval_exp_mix exp env genv, bir_eval_view_of_exp exp viewenv)
’;


(* statements that operate on mixed global and local expressions
 * adaptations of bir_programTheory and bir_envTheory *)

Definition bir_env_write_mix_def:
  bir_env_write_mix var va env genv =
    if is_global var then
      OPTION_MAP (λgenv. (env,genv)) (bir_env_write var va genv)
    else
      OPTION_MAP (λenv. (env,genv)) (bir_env_write var va env)
End

Definition bir_exec_stmt_assign_mix_def:
  bir_exec_stmt_assign_mix v ex (st : bir_state_t) genv =
    case bir_eval_exp_mix ex st.bst_environ genv of
      | SOME va => (case bir_env_write_mix v va st.bst_environ genv of
                      | SOME (env, genv) => (st with bst_environ := env, genv)
                      | NONE => (bir_state_set_typeerror st, genv)
                    )
      | NONE => (bir_state_set_typeerror st, genv)
End

Definition bir_exec_stmt_assert_mix_def:
  bir_exec_stmt_assert_mix ex (st : bir_state_t) genv =
    case (option_CASE (bir_eval_exp_mix ex st.bst_environ genv) NONE bir_dest_bool_val) of
      | SOME T => (st, genv)
      | SOME F => (st with bst_status := BST_AssertionViolated, genv)
      | NONE => (bir_state_set_typeerror st, genv)
End

Definition bir_exec_stmt_assume_mix_def:
  bir_exec_stmt_assume_mix ex (st : bir_state_t) genv =
    case (option_CASE (bir_eval_exp_mix ex st.bst_environ genv) NONE bir_dest_bool_val) of
      | SOME T => (st, genv)
      | SOME F => (st with bst_status := BST_AssumptionViolated, genv)
      | NONE => (bir_state_set_typeerror st, genv)
End

Definition bir_exec_stmt_observe_mix_def:
  bir_exec_stmt_observe_mix oid ec el obf (st : bir_state_t) genv =
  let
    vol = MAP (\e. bir_eval_exp_mix e st.bst_environ genv) el;
    vobc = option_CASE (bir_eval_exp_mix ec st.bst_environ genv) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T =>   if EXISTS IS_NONE vol then
                    (NONE, (bir_state_set_typeerror st, genv))
                  else
                    (SOME (oid, obf (MAP THE vol)), (st, genv))
    | SOME F =>   if EXISTS IS_NONE vol then
                    (NONE, (bir_state_set_typeerror st, genv))
                  else
                    (NONE, (st, genv))
    | NONE => (NONE, (bir_state_set_typeerror st, genv))
End

Definition bir_exec_stmtB_mix_def:
  (bir_exec_stmtB_mix (BStmt_Assert ex) st genv = (NONE, bir_exec_stmt_assert_mix ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Assume ex) st genv = (NONE, bir_exec_stmt_assume_mix ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Assign v ex) st genv = (NONE, bir_exec_stmt_assign_mix v ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Observe oid ec el obf) st genv = bir_exec_stmt_observe_mix oid ec el obf st genv) /\
  (bir_exec_stmtB_mix (BStmt_Fence mop mos) st genv = (λp. (FST p, (SND p,genv))) (bir_exec_stmt_fence mop mos st))
End

Definition bir_exec_stmtB_mix_def:
  (bir_exec_stmtB_mix (BStmt_Assert ex) st genv = (NONE, bir_exec_stmt_assert_mix ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Assume ex) st genv = (NONE, bir_exec_stmt_assume_mix ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Assign v ex) st genv = (NONE, bir_exec_stmt_assign_mix v ex st genv)) /\
  (bir_exec_stmtB_mix (BStmt_Observe oid ec el obf) st genv = bir_exec_stmt_observe_mix oid ec el obf st genv) /\
  (bir_exec_stmtB_mix (BStmt_Fence mop mos) st genv = (λp. (FST p, (SND p,genv))) (bir_exec_stmt_fence mop mos st))
End

Definition bir_exec_stmt_mix_def:
  (bir_exec_stmt_mix (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st genv =
     let (oo, (st', genv)) = bir_exec_stmtB_mix bst st genv in
     if bir_state_is_terminated st' then (oo, (st',genv)) else (oo, (st' with bst_pc updated_by bir_pc_next, genv))) /\
  (bir_exec_stmt_mix p (BStmtE bst) st genv = (NONE, (bir_exec_stmtE p bst st, genv)))
End

(* theorems that if no global variable containt, we can simply *)



val exp_is_load_def = Define `
  (exp_is_load (BExp_Load _ _ _ _) = T) /\
  (exp_is_load _ = F)
`;

val stmt_generic_step_def = Define`
   stmt_generic_step (BStmtB (BStmt_Assign _ _)) = F
/\ stmt_generic_step (BStmtB (BStmt_Fence _ _)) = F
/\ stmt_generic_step (BStmtE (BStmt_CJmp _ _ _)) = F
/\ stmt_generic_step _ = T
`;

val is_read_def = Define`
   is_read BM_Read = T
/\ is_read BM_Write = F
/\ is_read BM_ReadWrite = T
`;

val is_write_def = Define`
   is_write BM_Read = F
/\ is_write BM_Write = T
/\ is_write BM_ReadWrite = T
`;

(*
(* Checks if the memory expressions from lifted loads and stores
 * refers to regular memory or dummy memory. May look inside casts *)
(* TODO: Clarify *)
val contains_dummy_mem_def = Define`
  (contains_dummy_mem (BExp_Den (BVar mem_name mem_ty)) =
     if mem_name <> "MEM8" (* RISC-V regular memory *)
     then T
     else F) /\
  (contains_dummy_mem (BExp_Load mem_e a_e en ty) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Store mem_e a_e en v_e) =
     contains_dummy_mem mem_e) /\
  (contains_dummy_mem (BExp_Cast cast_ty e imm_ty) =
     contains_dummy_mem e) /\
  (contains_dummy_mem _ = F)
`;
*)

(* Obtains an option type that contains the load arguments
 * needed to apply the read rule (can look inside one cast) *)
Definition get_read_args_def:
  (get_read_args (BExp_Load mem_e a_e en ty) = SOME (a_e, NONE)) /\
  (get_read_args (BExp_Cast cast_ty load_e imm_ty) =
   case get_read_args load_e of
   | SOME (a_e, NONE) => SOME (a_e, SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_read_args _ = NONE)
End

(* Obtains an option type that contains the store arguments
 * needed to apply the fulfil rule *)
Definition get_fulfil_args_def:
  (get_fulfil_args (BExp_IfThenElse cond_e e1 e2) = get_fulfil_args e1) /\
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) = SOME (a_e, v_e)) /\
  (get_fulfil_args _ = NONE)
End

Theorem get_read_fulfil_args_exclusive:
∀e.
  (IS_SOME $ get_read_args e ⇒ get_fulfil_args e = NONE)
∧ (IS_SOME $ get_fulfil_args e ⇒ get_read_args e = NONE)
Proof
  Cases >>
  fs [get_read_args_def, get_fulfil_args_def]
QED

val get_xclb_view_def = Define`
  get_xclb_view (SOME xclb) = xclb.xclb_view
∧ get_xclb_view NONE = 0
`;

val fulfil_atomic_ok_def = Define`
  fulfil_atomic_ok M l cid t_r t_w =
     (mem_is_loc M t_r l ==>
       !t'. (t_r < t' /\ t' < t_w /\ mem_is_loc M t' l) ==> mem_is_cid M t' cid)
`;

Definition env_update_cast64_def:
  env_update_cast64 var (BVal_Imm v) env genv =
    if is_global var then
      OPTION_MAP (λgenv. (env,genv))
        (bir_env_update (bir_var_name var) (BVal_Imm (n2bs (b2n v) Bit64)) (bir_var_type var) genv)
    else
      OPTION_MAP (λenv. (env,genv))
        (bir_env_update (bir_var_name var) (BVal_Imm (n2bs (b2n v) Bit64)) (bir_var_type var) env)
End

val fulfil_update_env_def = Define`
  fulfil_update_env p s xcl =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) =>
        bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 0w)) (bir_var_type var_succ) s.bst_environ
      | _ => NONE
    else SOME s.bst_environ
`;

val fulfil_update_viewenv_def = Define`
  fulfil_update_viewenv p s xcl v_post =
    if xcl
    then
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) => SOME (s.bst_viewenv |+ (var_succ, v_post))
      | _ => NONE
    else SOME s.bst_viewenv
`;

val xclfail_update_env_def = Define`
  xclfail_update_env p s =
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) =>
        bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 1w)) (bir_var_type var_succ) s.bst_environ
      | _ => NONE
`;

val xclfail_update_viewenv_def = Define`
  xclfail_update_viewenv p s =
      case bir_get_current_statement p (bir_pc_next s.bst_pc) of
      | SOME (BStmtB (BStmt_Assign var_succ _)) => SOME (s.bst_viewenv |+ (var_succ, 0))
      | _ => NONE
`;

(* Upon the loading statement that is the first Assign in a lifted
 * Load-type instruction, checks if the block is trying to model
 * an exclusive-load *)
Definition is_xcl_read_def:
  is_xcl_read p pc a_e =
    case bir_get_current_statement p (bir_pc_next pc) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
                       var BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))))) => var = a_e
     | _ => F
End

(* Upon the storing statement that is the first Assign in a lifted
 * Strore-type instruction, checks if the block is trying to model
 * an exclusive-store *)
val is_xcl_write_def = Define‘
  is_xcl_write p pc =
    case bir_get_current_statement p (bir_pc_next (bir_pc_next pc)) of
      SOME (BStmtB (BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))))) => T
     | _ => F
’;

(* properties about exclusive reads and writes *)

Theorem is_xcl_read_thm:
  !p pc a_e. is_xcl_read p pc a_e <=>
    bir_get_current_statement p (bir_pc_next pc) =
      SOME $ BStmtB $ BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
        $ BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
          a_e BEnd_LittleEndian
          (BExp_Const (Imm32 0x1010101w))
Proof
  rw[is_xcl_read_def,EQ_IMP_THM,optionTheory.IS_SOME_EXISTS]
  >> pop_assum mp_tac
  >> rpt (BasicProvers.PURE_TOP_CASE_TAC >> fs[])
QED

Theorem is_xcl_write_thm:
  !p pc. is_xcl_write p pc <=>
    IS_SOME $ bir_get_current_statement p (bir_pc_next $ bir_pc_next pc) /\
    bir_get_current_statement p (bir_pc_next $ bir_pc_next pc) =
      SOME $ BStmtB $ BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
        $ BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))
Proof
  rw[is_xcl_write_def,EQ_IMP_THM,optionTheory.IS_SOME_EXISTS]
  >- (BasicProvers.full_case_tac >> fs[])
  >> pop_assum mp_tac
  >> rpt (BasicProvers.PURE_TOP_CASE_TAC >> fs[])
QED

val is_acq_def = Define‘
  is_acq p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_acq
         | _ => F)
     | _ => F
’;

val is_rel_def = Define‘
  is_rel p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_rel
         | _ => F)
     | _ => F
’;

val is_amo_def = Define‘
  is_amo p pc =
    case bir_get_program_block_info_by_label p pc.bpc_label of
      SOME (i, bb) =>
        (case bb.bb_mc_tags of
         SOME mc_tags => mc_tags.mc_atomic
         | _ => F)
     | _ => F
’;

Definition bir_get_stmt_def:
  bir_get_stmt p pc =
  case bir_get_current_statement p pc of
  | SOME (BStmtB (BStmt_Assign var e)) =>
      if is_amo p pc then
      (case get_read_args e of
       | SOME (a_e, cast_opt) =>
           (case bir_get_current_statement p (bir_pc_next pc) of
           | SOME (BStmtB (BStmt_Assign var' e)) =>
               (case get_fulfil_args e of
               | SOME (a_e', v_e) =>
                   if a_e = a_e'
                   then BirStmt_Amo var a_e v_e (is_acq p pc) (is_rel p pc)
                   else BirStmt_None
               | NONE => BirStmt_None)
           | _ => BirStmt_None)
       | NONE =>
           (case get_fulfil_args e of
            | SOME (a_e, v_e) => BirStmt_None
            | NONE => BirStmt_Expr var e))
      else
       (case get_read_args e of
       | SOME (a_e, cast_opt) => BirStmt_Read var a_e cast_opt (is_xcl_read p pc a_e) (is_acq p pc) (is_rel p pc)
       | NONE =>
           (case get_fulfil_args e of
           | SOME (a_e, v_e) => BirStmt_Write a_e v_e (is_xcl_write p pc) (is_acq p pc) (is_rel p pc)
           | NONE => BirStmt_Expr var e))
  | SOME (BStmtB (BStmt_Fence K1 K2)) => BirStmt_Fence K1 K2
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) => BirStmt_Branch cond_e lbl1 lbl2
  | SOME stmt => BirStmt_Generic stmt
  | NONE => BirStmt_None
End

Theorem bir_get_stmt_read:
∀p pc stmt var a_e cast_opt xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Read var a_e cast_opt xcl acq rel) ⇔
 (∃e.
 bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ ~is_amo p pc
 /\ get_read_args e = SOME (a_e, cast_opt)
 /\ is_xcl_read p pc a_e = xcl
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  gvs [bir_get_stmt_def, AllCaseEqs(),
       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem bir_get_stmt_write:
∀p pc stmt a_e v_e xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Write a_e v_e xcl acq rel) ⇔
 (∃var e. bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ ~is_amo p pc
 /\ get_fulfil_args e = SOME (a_e, v_e)
 /\ is_xcl_write p pc = xcl
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  rw [bir_get_stmt_def,AllCaseEqs()] >>
  eq_tac >>
  rw [get_read_fulfil_args_exclusive]
QED

Theorem bir_get_stmt_amo:
∀p pc var stmt a_e v_e xcl acq rel.
 (bir_get_stmt p pc = BirStmt_Amo var a_e v_e acq rel) ⇔
 (∃e cast_opt var' e'.
    bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ is_amo p pc
 /\ get_read_args e = SOME (a_e, cast_opt)
 /\ bir_get_current_statement p (bir_pc_next pc) = SOME (BStmtB (BStmt_Assign var' e'))
 /\ get_fulfil_args e' = SOME (a_e, v_e)
 /\ is_acq p pc = acq
 /\ is_rel p pc = rel)
Proof
  gvs [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED

Theorem bir_get_stmt_expr:
∀p pc var e.
 (bir_get_stmt p pc = BirStmt_Expr var e) =
 (bir_get_current_statement p pc = SOME (BStmtB (BStmt_Assign var e))
 /\ get_read_args e = NONE
 /\ get_fulfil_args e = NONE)
Proof
  rw [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
  Cases_on ‘is_amo p pc’ >> rw []
QED

Theorem bir_get_stmt_fence:
∀p pc K1 K2.
 (bir_get_stmt p pc = BirStmt_Fence K1 K2) ⇔
 bir_get_current_statement p pc = SOME (BStmtB (BStmt_Fence K1 K2))
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_branch:
∀p pc cond_e lbl1 lbl2.
 (bir_get_stmt p pc = BirStmt_Branch cond_e lbl1 lbl2) ⇔
 bir_get_current_statement p pc = SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2))
Proof
  fs [bir_get_stmt_def,AllCaseEqs()]
QED

Theorem bir_get_stmt_generic:
∀p pc stmt.
 (bir_get_stmt p pc = BirStmt_Generic stmt ⇔
 (bir_get_current_statement p pc = SOME stmt ∧ stmt_generic_step stmt))
Proof
  rpt strip_tac >>
  Cases_on ‘stmt’ >|
  [rename1 ‘BStmtB b’, rename1 ‘BStmtE b’] >>
  (
    Cases_on ‘b’ >>
    gvs [bir_get_stmt_def,stmt_generic_step_def,AllCaseEqs()]
  )
QED

(* FIX THIS???
Theorem bir_get_stmt_none:
∀p pc.
 (bir_get_stmt p pc = BirStmt_None) ⇔
 bir_get_current_statement p pc = NONE \/
Proof
  fs [bir_get_stmt_def,AllCaseEqs(), GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
QED
*)

(* TODO: "Generalising variable "v_pre" in clause #0"? *)
(* core-local steps that don't affect memory *)
val (bir_clstep_rules, bir_clstep_ind, bir_clstep_cases) = Hol_reln`
(* read *)
(!p s s' v a_e xcl acq rel M l (t:num) v_pre v_post v_addr var new_env cid opt_cast.
   bir_get_stmt p s.bst_pc = BirStmt_Read var a_e opt_cast xcl acq rel
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv genv
 ∧ mem_read M l t = SOME v
 ∧ v_pre = MAX (MAX (MAX v_addr s.bst_v_rNew) (if (acq /\ rel) then s.bst_v_Rel else 0))
               (if (acq /\ rel) then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
 ∧ (∀t'. ((t:num) < t' ∧ t' ≤ (MAX v_pre (s.bst_coh l)) /\ is_some_some t' M)
    ⇒ ~(mem_is_loc M t' l))
 ∧ v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
 /\ SOME (new_env,genv') = env_update_cast64 var v (s.bst_environ) genv
 (* TODO: Update viewenv by v_addr or v_post? *)
 ∧ s' = s with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
                  bst_environ := new_env;
                  bst_coh := (λlo. if lo = l
                                   then MAX (s.bst_coh l) v_post
                                   else s.bst_coh(lo));
                  bst_v_rOld := MAX s.bst_v_rOld v_post;
                  bst_v_rNew := if acq then (MAX s.bst_v_rNew v_post) else s.bst_v_rNew;
                  bst_v_wNew := if acq then (MAX s.bst_v_wNew v_post) else s.bst_v_wNew;
                  bst_v_Rel := MAX s.bst_v_Rel (if (rel /\ acq) then v_post else 0);
                  bst_v_CAP := MAX s.bst_v_CAP v_addr;
                  bst_xclb := if xcl
                              then SOME <| xclb_time := t; xclb_view := v_post |>
                              else s.bst_xclb;
                  bst_pc := if xcl
                            then (bir_pc_next o bir_pc_next) s.bst_pc
                            else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M genv [] s' genv')
/\ (* exclusive-failure *)
(!p s s' M a_e v_e acq rel cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e T acq rel
 /\  SOME new_env = xclfail_update_env p s
 /\  SOME new_viewenv = xclfail_update_viewenv p s
 /\  s' = s with <| bst_environ := new_env;
                    bst_viewenv := new_viewenv;
                    bst_xclb := NONE;
                    bst_pc := (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc |>
 ==>
clstep p cid s M genv [] s' genv)

/\ (* fulfil *)
(!p s s' M v a_e xcl acq rel l (t:num) v_pre v_post v_addr v_data v_e cid new_env new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv genv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv genv
 /\ (xcl ==> s.bst_xclb <> NONE /\ fulfil_atomic_ok M l cid (THE s.bst_xclb).xclb_time t)
 /\ MEM t s.bst_prom
 /\ mem_get M l t = SOME <| loc := l; val := v; cid := cid  |>
 (* TODO: Use get_xclb_view or separate conjunct to extract option type? *)
 /\ v_pre = MAX (MAX (MAX (MAX v_addr (MAX v_data (MAX s.bst_v_wNew s.bst_v_CAP)))
                          (if rel
                           then (MAX s.bst_v_rOld s.bst_v_wOld)
                           else 0))
                     (if (xcl /\ acq /\ rel)
                      then s.bst_v_Rel
                      else 0))
                (if xcl
                 then get_xclb_view s.bst_xclb
                 else 0)
 /\ (MAX v_pre (s.bst_coh l) < t)
 /\ v_post = t
 /\ SOME new_env = fulfil_update_env p s xcl
 (* TODO: Update viewenv by v_post or something else? *)
 /\ SOME new_viewenv = fulfil_update_viewenv p s xcl v_post
 /\ s' = s with <| bst_viewenv := new_viewenv;
                   bst_prom updated_by (FILTER (\t'. t' <> t));
                   bst_environ := new_env;
                   bst_coh := (\lo. if lo = l
                                    then MAX (s.bst_coh l) v_post
                                    else s.bst_coh(lo));
                   bst_v_wOld := MAX s.bst_v_wOld v_post;
                   bst_v_CAP := MAX s.bst_v_CAP v_addr;
                   bst_v_Rel := MAX s.bst_v_Rel (if (rel /\ acq) then v_post else 0);
                   bst_v_rNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_rNew v_post) else s.bst_v_rNew;
                   bst_v_wNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_wNew v_post) else s.bst_v_wNew;
                   bst_fwdb := (\lo. if lo = l
                                     then <| fwdb_time := t;
                                             fwdb_view := MAX v_addr v_data;
                                             fwdb_xcl := xcl |>
                                     else s.bst_fwdb(lo));
                   bst_xclb := if xcl
                               then NONE
                               else s.bst_xclb;
                   bst_pc := if xcl
                             then (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc
                             else bir_pc_next s.bst_pc |>
 ==>
  clstep p cid s M genv [t] s' genv)
/\ (* AMO fulfil *)
(!p cid s s' M acq rel var l a_e v_r v_w v_e v_rPre v_rPost v_wPre v_wPost (t_w:num) (t_r :num) new_environ new_viewenv.
   bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel

   (* Get location *)
   /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv genv

   (* Read part *)
   /\ mem_read M l t_r = SOME v_r (* v_r value read *)
   /\ v_rPre = MAX v_addr (
        MAX s.bst_v_rNew
        (if acq /\ rel then (MAX s.bst_v_Rel (MAX s.bst_v_rOld s.bst_v_wOld)) else 0))
   /\ v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r)

   (* register and register view update *)
   /\ SOME (new_environ,genv') = env_update_cast64 var v_r (s.bst_environ) genv
   /\ new_viewenv = FUPDATE s.bst_viewenv (var, v_rPost)

   (* Write part *)
   /\ MEM t_w s.bst_prom
   (* v_w value to write, v_e value expression *)
   /\ (SOME v_w, v_data) = bir_eval_exp_view v_e new_environ new_viewenv genv
   /\ mem_get M l t_w = SOME <| loc := l; val := v_w; cid := cid |>
   /\ v_wPre = MAX v_addr (
        MAX v_data (
        MAX s.bst_v_CAP (
        MAX v_rPost (
        MAX s.bst_v_wNew (
        MAX (if rel then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
             (if (acq /\ rel) then s.bst_v_Rel else 0))))))
   /\ v_wPost = t_w
   /\ MAX v_wPre (s.bst_coh l) < t_w

   (* No writes to memory location between read and write *)
   /\ (!t'. t_r < t' /\ t' < t_w /\ is_some_some t' M ==> mem_is_loc M t' l)

   (* State update *)
   /\ s' = s with <| bst_viewenv := new_viewenv;
                     bst_environ := new_environ;
                     bst_prom    updated_by (FILTER (\t'. t' <> t_w));
                     bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_wPost);
                     bst_v_Rel   updated_by (MAX (if acq /\ rel then v_wPost else 0));
                     bst_v_rOld  updated_by (MAX v_rPost);
                     bst_v_rNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_wNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_CAP   updated_by (MAX v_addr);
                     bst_v_wOld  updated_by (MAX v_wPost);
                     bst_fwdb    updated_by (l =+ <| fwdb_time := t_w;
                                                     fwdb_view := MAX v_addr v_data;
                                                     fwdb_xcl := T |>);
                     bst_pc updated_by (bir_pc_next o bir_pc_next) |>
 ==>
 clstep p cid s M genv [t_w] s' genv'
)
/\ (* fence *)
(!p s s' K1 K2 M cid v.
   bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2
   /\ v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                     bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
                     bst_pc updated_by bir_pc_next |>
==>
  clstep p cid s M genv [] s' genv)
/\ (* branch (conditional jump) *)
(!p s s' M cid v oo s2 v_addr cond_e lbl1 lbl2 stm.
   bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2
    /\ stm = BStmtE (BStmt_CJmp cond_e lbl1 lbl2)
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv genv
    /\ bir_exec_stmt_mix p stm s genv = (oo,(s2,genv'))
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>
==>
  clstep p cid s M genv [] s' genv')
/\ (* register-to-register operation *)
(!p s s' var M cid v v_val e new_env.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e
 /\ (SOME v, v_val) = bir_eval_exp_view e s.bst_environ s.bst_viewenv genv
 /\ NONE = get_read_args e
 /\ NONE = get_fulfil_args e
 /\ SOME (new_env,genv') = env_update_cast64 var v (s.bst_environ) genv
 /\ s' = s with <| bst_environ := new_env;
                   bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                   bst_pc      updated_by bir_pc_next |>
==> clstep p cid s M genv [] s' genv')
/\ (* Other BIR single steps *)
(!p s s' M cid stm oo.
   bir_get_stmt p s.bst_pc = BirStmt_Generic stm
    /\ bir_exec_stmt_mix p stm s genv = (oo,(s',genv'))
==>
  clstep p cid s M genv [] s' genv')
`;


(* core steps *)
val (bir_cstep_rules, bir_cstep_ind, bir_cstep_cases) = Hol_reln`
(* execute *)
(!p cid s M s' prom.
  clstep p cid s M genv prom s' genv'
==>
  cstep p cid s M genv prom s' M genv')

/\ (* promise *)
(!p cid s M s' t msg.
   (msg.cid = cid
   /\ LENGTH M < t
   /\ s' = s with bst_prom updated_by (\pr. pr ++ [t]))
==>
  cstep p cid s M genv [t] s' (M ++ REPLICATE (t - LENGTH M - 1) NONE ++ [SOME msg]) genv)
`;

Theorem cstep_bisim:
  !p cid s M genv prom s' M' genv'.
  cstep p cid s M genv prom s' M' genv'
  ==> (cstep p cid s M genv prom s' M genv' /\ M = M')
    \/ (cstep p cid s M genv [LENGTH M + 1]
        (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))
        (M++[LAST M']) genv
        /\ ?t msg. prom = [t]
        /\ M' = M ++ REPLICATE (t - LENGTH M - 1) NONE ++ [SOME msg]
        )
Proof
  rpt strip_tac >> fs[bir_cstep_cases]
QED

(* core steps seq *)
val (bir_cstep_seq_rules, bir_cstep_seq_ind, bir_cstep_seq_cases) = Hol_reln`
(* seq *)
(!p cid s M s' prom.
  clstep p cid s M genv (prom:num list) s' genv'
==>
  cstep_seq p cid (s, M, genv) (s', M, genv'))

/\ (* write *)
(!p cid s M s' s'' M' t.
  (cstep p cid s M genv [t] s' M' genv' /\ ~(M = M')
  /\ clstep p cid s' M' genv' [t] s'' genv'')
==>
  cstep_seq p cid (s, M, genv) (s'', M', genv''))
`;

val cstep_seq_rtc_def = Define`cstep_seq_rtc p cid = (cstep_seq p cid)^*`

(*
(*
 * properties about cstep, clstep, cstep_seq
 *)

(* the timestamp of a fulfil is coupled to the fulfiled core *)

Theorem cstep_fulfil_to_memory:
  !t p cid s M s'.
  cstep p cid s M [t] s' M
  ==> 0 < t /\ PRE t < LENGTH M /\ (EL (PRE t) M).cid = cid
Proof
  Cases >> rpt gen_tac >> strip_tac
  >> gvs[bir_cstep_cases,bir_clstep_cases,PULL_EXISTS,arithmeticTheory.PRE_SUB1,oEL_THM,oEL_THM,mem_get_def,AllCaseEqs()]
QED

(* memory only ever increases *)

Theorem cstep_seq_IS_PREFIX:
  !p cid sM sM'. cstep_seq p cid sM sM'
  ==> IS_PREFIX (SND sM') (SND sM)
Proof
  ho_match_mp_tac bir_cstep_seq_ind >> rw[]
  >> fs[bir_cstep_cases]
QED

Theorem cstep_seq_rtc_IS_PREFIX:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  ==> IS_PREFIX (SND sM') (SND sM)
Proof
  ntac 2 gen_tac
  >> fs[cstep_seq_rtc_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> rw[]
  >> dxrule_then assume_tac cstep_seq_IS_PREFIX
  >> imp_res_tac rich_listTheory.IS_PREFIX_TRANS
QED

(* a fulfil is only fulfilled once *)

Theorem clstep_fulfil_once:
  !p cid cid' s M t s' s''.
  clstep p cid s M [t] s'
  /\ clstep p cid' s' M [t] s'' ==> F
Proof
  rpt strip_tac
  >> Cases_on `cid = cid'`
  >> gvs[bir_clstep_cases,MEM_FILTER]
QED

Theorem cstep_seq_rtc_fulfil_once:
  !p cid sM2 sM3 s M t s1 cid' t' s4 M4 s5.
  cstep p cid s M genv [t] s1 (SND sM2) genv'
  /\ clstep p cid s1 (SND sM2) [t] (FST sM2) genv'
  /\ cstep_seq_rtc p cid sM2 sM3
  /\ cstep p cid' (FST sM3) (SND sM3) [t'] s4 M4
  /\ clstep p cid' s4 M4 [t'] s5
  ==> t <> t'
Proof
  rpt strip_tac
  >> imp_res_tac cstep_seq_rtc_IS_PREFIX
  >> gvs[bir_cstep_cases]
  >> imp_res_tac clstep_fulfil_once
  >> rpt $ PRED_ASSUM is_forall kall_tac
  >> gvs[rich_listTheory.IS_PREFIX_APPEND]
QED
*)

(* bir_exec_stmt invariants *)

Theorem bir_exec_stmt_BStmtE_BStmt_CJmp_bst_xclb_EQ:
  !p cond_e lbl1 lbl2 s oo s' genv genv'.
  bir_exec_stmt_mix p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s genv = (oo,s', genv')
  ==> s.bst_xclb = s'.bst_xclb /\ genv = genv'
Proof
  EVAL_TAC
  >> rw[AllCaseEqs()]
  >> fs[]
QED

Theorem bir_exec_stmt_stmt_generic_step_bst_xclb_EQ:
  !stm p s oo s' genv genv'.
  bir_exec_stmt_mix p stm s genv = (oo,(s',genv'))
  /\ stmt_generic_step stm
  ==> s.bst_xclb = s'.bst_xclb /\ s.bst_prom = s'.bst_prom /\ genv = genv'
Proof
  Cases >> rpt gen_tac >> strip_tac
  >> (qmatch_asmsub_rename_tac `BStmtE stm`
    ORELSE qmatch_asmsub_rename_tac `BStmtB stm`)
  >> Cases_on `stm`
  >> gs[bir_get_stmt_generic,stmt_generic_step_def,bir_exec_stmt_mix_def,pairTheory.ELIM_UNCURRY,stmt_generic_step_def,bir_exec_stmt_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_exec_stmtB_mix_def,bir_state_is_terminated_def,bir_exec_stmt_assign_mix_def,
    bir_exec_stmtB_mix_def,bir_exec_stmt_assert_mix_def,AllCaseEqs(),
    bir_state_set_typeerror_def,bir_exec_stmt_assume_mix_def,bir_exec_stmt_assume_mix_def,
    bir_exec_stmt_observe_mix_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,
    bir_exec_stmt_jmp_to_label_def,bir_exec_stmtE_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac >> fs[]
QED

Theorem bir_exec_stmt_BStmtE_BStmt_CJmp_bst_prom_EQ:
  !p cond_e lbl1 lbl2 s oo s' genv genv'.
  bir_exec_stmt_mix p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s genv = (oo,(s',genv'))
  ==> s.bst_prom = s'.bst_prom /\ genv = genv'
Proof
  EVAL_TAC
  >> rw[AllCaseEqs()]
  >> fs[]
QED

(* set of promises contains only elements smaller then the memory *)

Theorem clstep_EVERY_LENGTH_bst_prom_inv:
  !p cid s M prom s' genv genv'.
  clstep p cid s M genv prom s' genv'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH M) s.bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH M) s'.bst_prom
Proof
  rw[bir_clstep_cases,bir_get_stmt_generic]
  >> imp_res_tac bir_exec_stmt_BStmtE_BStmt_CJmp_bst_prom_EQ
  >> imp_res_tac bir_exec_stmt_stmt_generic_step_bst_xclb_EQ
  >> fs[]
  >> qhdtm_x_assum `EVERY` mp_tac
  >> fs[EVERY_FILTER]
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem clstep_bst_prom_NOT_EQ:
  !p cid s M t s' genv genv'.
  clstep p cid s M genv [t] s' genv' ==> s.bst_prom <> s'.bst_prom
Proof
  rw[bir_clstep_cases,bir_get_stmt_write]
  >> fs[Once EQ_SYM_EQ,FILTER_NEQ_ID]
QED

Theorem clstep_LENGTH_prom:
  !p cid s M prom s' genv genv'. clstep p cid s M genv prom s' genv'
  ==> prom = [] \/ ?t. prom = [t]
Proof
  rw[bir_clstep_cases]
QED


(* cstep_seq invariant *)

Theorem bir_exec_stmt_jmp_bst_prom:
  !st p lbl. st.bst_prom = (bir_exec_stmt_jmp p lbl st).bst_prom
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

Theorem clstep_bst_prom_EQ:
!p cid st M st' genv genv'.
  clstep p cid st M genv [] st' genv' ==> st.bst_prom = st'.bst_prom
Proof
  rw[bir_clstep_cases]
  >> gvs[bir_state_t_accfupds,bir_exec_stmt_mix_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_bst_prom,bir_get_stmt_def]
  >> (
    fs[AllCaseEqs(),bir_exec_stmt_mix_def,pairTheory.ELIM_UNCURRY,bir_exec_stmt_halt_def]
    >> BasicProvers.every_case_tac
    >> fs[bir_exec_stmtB_mix_def,bir_exec_stmt_assert_mix_def,bir_exec_stmt_assume_mix_def,bir_exec_stmt_observe_mix_def]
    >> BasicProvers.every_case_tac
    >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
  )
  >> qmatch_assum_rename_tac `stmt_generic_step $ BStmtE b`
  >> Cases_on `b`
  >> fs[stmt_generic_step_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_exec_stmt_mix_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> BasicProvers.every_case_tac
  >> gvs[bir_state_set_typeerror_def,CaseEq"option"]
QED

(*
Theorem cstep_seq_bst_prom_EQ:
  !p cid sM sM'. cstep_seq p cid sM sM'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM') (FST sM').bst_prom
    /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac bir_cstep_seq_ind
  >> conj_tac >> rpt gen_tac >> strip_tac
  >- cheat
  >> strip_tac >> conj_asm1_tac
  >- (
    pop_assum mp_tac
    >> gvs[bir_cstep_cases,bir_clstep_cases,rich_listTheory.FILTER_APPEND,EVERY_FILTER, rich_listTheory.FILTER_IDEM]
    >> match_mp_tac EVERY_MONOTONIC
    >> fs[]
  )
  >> gvs[bir_clstep_cases,bir_cstep_cases,bir_state_t_accfupds,bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,bir_state_set_typeerror_def,stmt_generic_step_def,bir_exec_stmt_jmp_bst_prom,rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_IDEM, MEM_FILTER]
  >> fs[Once EQ_SYM_EQ,FILTER_EQ_ID]
  >> qpat_x_assum `EVERY _ _.bst_prom` mp_tac
  >> match_mp_tac EVERY_MONOTONIC
  >> fs[]
QED

Theorem cstep_seq_rtc_bst_prom_EQ:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  /\ EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM) (FST sM).bst_prom
  ==> EVERY (λx. 0 < x /\ x <= LENGTH $ SND sM') (FST sM').bst_prom
    /\ (FST sM).bst_prom = (FST sM').bst_prom
Proof
  fs[GSYM AND_IMP_INTRO,cstep_seq_rtc_def]
  >> ntac 2 gen_tac
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> drule_all cstep_seq_bst_prom_EQ
  >> fs[]
QED
*)

val is_certified_def = Define`
is_certified p cid s M genv = ?s' M' genv'.
  cstep_seq_rtc p cid (s, M, genv) (s', M', genv')
  /\ s'.bst_prom = []
`;

val _ = Datatype `core_t =
  Core num (string bir_program_t) bir_state_t
`;

val get_core_cid = Define‘
   get_core_cid (Core cid p s) = cid
’;

val get_core_prog = Define‘
   get_core_prog (Core cid p s) = p
’;

val get_core_state = Define‘
   get_core_state (Core cid p s) = s
’;



val cores_pc_not_atomic_def = Define`
  cores_pc_not_atomic cores =
    ~?cid p s i bl mc_tags.
     FLOOKUP cores cid = SOME (Core cid p s)
     /\ s.bst_pc.bpc_index <> 0
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, bl)
     /\ bl.bb_mc_tags = SOME mc_tags
     /\ mc_tags.mc_atomic = T
`;

val atomicity_ok_def = Define`
  atomicity_ok cid cores =
    cores_pc_not_atomic (cores \\ cid)
`;

(* system step *)
val (bir_parstep_rules, bir_parstep_ind, bir_parstep_cases) = Hol_reln`
(!p cid s s' M M' cores prom genv genv'.
   (FLOOKUP cores cid = SOME (Core cid p s)
    /\ atomicity_ok cid cores
    /\ cstep p cid s M genv prom s' M' genv'
    /\ is_certified p cid s' M' genv')
==>
   parstep cid cores M genv (FUPDATE cores (cid, Core cid p s')) M' genv')
`;

Theorem bir_exec_stmt_mc_invar:
!stmt prog state oo state' genv genv'.
bir_exec_stmt_mix prog stmt state genv = (oo,state',genv') ==>
(state.bst_viewenv = state'.bst_viewenv) /\
(state.bst_coh = state'.bst_coh) /\
(state.bst_v_rOld = state'.bst_v_rOld) /\
(state.bst_v_wOld = state'.bst_v_wOld) /\
(state.bst_v_rNew = state'.bst_v_rNew) /\
(state.bst_v_wNew = state'.bst_v_wNew) /\
(state.bst_v_CAP = state'.bst_v_CAP) /\
(state.bst_v_Rel = state'.bst_v_Rel) /\
(state.bst_prom = state'.bst_prom) /\
(state.bst_fwdb = state'.bst_fwdb) /\
(state.bst_xclb = state'.bst_xclb) /\
(state.bst_inflight = state'.bst_inflight) /\
(state.bst_counter = state'.bst_counter)
Proof
Cases_on ‘stmt’ >> Cases_on ‘b’ >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
  fs[bir_exec_stmt_mix_def,bir_exec_stmtB_mix_def,pairTheory.ELIM_UNCURRY]
  >~ [`bir_exec_stmt_assign_mix`]
  >- (
    BasicProvers.every_case_tac
    >- fs[AllCaseEqs(),bir_exec_stmt_assign_mix_def,bir_state_t_component_equality,bir_state_set_typeerror_def,bir_eval_exp_mix_def] >>
    qmatch_asmsub_abbrev_tac `FST xx` >> Cases_on `xx` >>
    fs [bir_exec_stmt_assign_mix_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_state_t_component_equality]
  )
  >~ [`bir_exec_stmt_assert_mix`]
  >- (
    BasicProvers.every_case_tac
    >- fs[AllCaseEqs(),bir_exec_stmt_assert_mix_def,bir_state_t_component_equality,bir_state_set_typeerror_def,bir_eval_exp_mix_def] >>
    qmatch_asmsub_abbrev_tac `FST xx` >> Cases_on `xx` >>
    fs [bir_exec_stmt_assert_mix_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_state_t_component_equality]
 )
 >~ [`bir_exec_stmt_assume_mix`]
 >- (
    BasicProvers.every_case_tac
    >- fs[AllCaseEqs(),bir_exec_stmt_assume_mix_def,bir_state_t_component_equality,bir_state_set_typeerror_def,bir_eval_exp_mix_def] >>
    qmatch_asmsub_abbrev_tac `FST xx` >> Cases_on `xx` >>
    fs [bir_exec_stmt_assume_mix_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_state_t_component_equality]
  )
  >~ [`bir_exec_stmt_observe_mix`]
  >- (
    BasicProvers.every_case_tac
    >- fs[AllCaseEqs(),bir_exec_stmt_observe_mix_def,bir_state_t_component_equality,bir_state_set_typeerror_def,bir_eval_exp_mix_def] >>
    qmatch_asmsub_abbrev_tac `FST xx` >> Cases_on `xx` >> fs[] >>
    qmatch_asmsub_abbrev_tac `FST xx` >> Cases_on `xx` >> fs[] >>
    gvs [bir_exec_stmt_observe_mix_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_state_t_component_equality]
  )
  >~ [`bir_exec_stmt_fence`]
  >- (
    BasicProvers.every_case_tac >>
    gvs [bir_exec_stmtB_mix_def, bir_exec_stmt_fence_def]
  )
  >~ [`bir_exec_stmtE prog (BStmt_Jmp _)`]
  >- (
    fs [bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
    >> BasicProvers.every_case_tac
    >> fs[bir_state_t_component_equality]
  )
  >~ [`bir_exec_stmtE prog (BStmt_CJmp _ _ _)`]
  >- (
    fs [bir_exec_stmt_def, bir_exec_stmtE_def, bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def] >>
    BasicProvers.every_case_tac >>
    fs[bir_state_t_component_equality]
  )
  >~ [`bir_exec_stmtE _ (BStmt_Halt _)`]
  >- (
    fs [bir_exec_stmt_def, bir_exec_stmtE_def, bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def,bir_exec_stmt_halt_def] >>
    BasicProvers.every_case_tac >>
    fs[bir_state_t_component_equality]
  )
QED

(* lower index  x  by  k  accord to the bound  b , see lower_EL *)

Definition lower_def:
  lower b (k:num) x = if x < b then x else x - k
End

Theorem lower_zero:
  lower b k 0 = 0 /\ lower b 0 = I
Proof
  fs[lower_def,FUN_EQ_THM]
QED

Definition lower_constraints_def:
  lower_constraints b k (x:num) <=> x < b \/ b + k <= x
End

Theorem lower_constraints_zero:
  0 < b ==> lower_constraints b k 0n
Proof
  fs[lower_constraints_def]
QED

Theorem lower_constraints_ZERO_LESS:
  lower_constraints b k t /\ 0 < t /\ 0 < b
  ==> 0 < lower b k t
Proof
  rw[lower_constraints_def,lower_def]
QED

Theorem lower_inj:
  lower_constraints b k x
  /\ lower_constraints b k y
  ==> (lower b k x = lower b k y <=> x = y)
Proof
  rw[lower_def,EQ_IMP_THM,lower_constraints_def]
QED

(* motivation for defining lower_def *)

Theorem lower_EL:
  !i M M' M''. i < LENGTH M + LENGTH M' + LENGTH M''
  /\ lower_constraints (LENGTH M) (LENGTH M') i
  ==> EL i (M ++ M' ++ M'') = EL (lower (LENGTH M) (LENGTH M') i) (M ++ M'')
Proof
  rw[lower_def,rich_listTheory.EL_APPEND1,lower_constraints_def]
  >> fs[rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS]
QED

Theorem lower_LESS:
  !t b k t'. t < t' /\ lower_constraints b k t /\ lower_constraints b k t'
  ==> lower b k t < lower b k t'
Proof
  rw[lower_def,lower_constraints_def]
QED

Theorem lower_COND:
  !cond b k x y.
  lower_constraints b k x /\ lower_constraints b k y
  ==> (if cond then lower b k x else lower b k y) =
    lower b k (if cond then x else y)
Proof
  Cases >> fs[lower_def,lower_constraints_def]
QED

Theorem lower_COND_zero:
  !cond b k x.
  lower_constraints b k x
  ==> (if cond then lower b k x else 0) = lower b k (if cond then x else 0)
Proof
  Cases >> fs[lower_def,lower_constraints_def]
QED

Theorem lower_MAX:
  !b k x y.
  lower_constraints b k x /\ lower_constraints b k y
  ==> MAX (lower b k x) (lower b k y) = lower b k (MAX x y)
Proof
  rw[lower_def,lower_constraints_def]
  >> fs[arithmeticTheory.NOT_LESS,arithmeticTheory.MAX_DEF]
QED

Theorem lower_constraints_MAX:
  !b k x y.
  lower_constraints b k x /\ lower_constraints b k y
  ==> lower_constraints b k (MAX x y)
Proof
  rw[lower_constraints_def]
  >> fs[arithmeticTheory.NOT_LESS,arithmeticTheory.MAX_DEF]
QED

Theorem lower_constraints_COND:
  !b k x y con.
  lower_constraints b k x /\ lower_constraints b k y
  ==> lower_constraints b k (if con then x else y)
Proof
  rw[lower_constraints_def]
QED

(* increase index  x  by  k  accord to the bound  b  *)

Definition upper_def:
  upper b (k:num) x = if b <= x then x + k else x
End

Theorem upper_EL:
  !i M M' M''.
  i < LENGTH M + LENGTH M''
  ==> EL (upper (LENGTH M) (LENGTH M') i) (M ++ M' ++ M'') = EL i (M ++ M'')
Proof
  rw[upper_def,rich_listTheory.EL_APPEND1]
  >> fs[rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS]
QED

Theorem is_some_some_oEL_upper:
  !t M' M'' k.
  is_some_some t $ M' ++ M''
  ==> is_some_some (upper (LENGTH M' + 1) k t) (M' ++ REPLICATE k NONE ++ M'')
Proof
  Cases
  >> rw[is_some_some_def,oEL_THM,optionTheory.IS_SOME_EXISTS,upper_def,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2]
  >> qmatch_asmsub_abbrev_tac `EL kk`
  >> qmatch_goalsub_abbrev_tac `EL kk'`
  >> `kk = kk'` by (unabbrev_all_tac >> decide_tac)
  >> fs[]
QED

Theorem lower_constraints_upper:
  !t b k. lower_constraints b k (upper b k t)
Proof
  fs[lower_constraints_def,upper_def]
QED

Theorem lower_upper:
  !t b k. lower b k (upper b k t) = t
Proof
  fs[lower_def,upper_def]
QED

Theorem lower_upper_LESS:
  !t b k t'. lower b k t < t' /\ lower_constraints b k t ==> t < upper b k t'
Proof
  rw[lower_def,upper_def,lower_constraints_def]
QED

Theorem lower_upper_LESS_EQ:
  !t b k t'. lower b k t <= t' /\ lower_constraints b k t ==> t <= upper b k t'
Proof
  rw[lower_def,upper_def,lower_constraints_def]
QED

Theorem upper_lower_LESS:
  !t b k t'. t < lower b k t' /\ lower_constraints b k t' ==> upper b k t < t'
Proof
  rw[lower_def,upper_def,lower_constraints_def]
QED

Theorem upper_lower_LESS_EQ:
  !t b k t'. t <= lower b k t' /\ lower_constraints b k t' ==> upper b k t <= t'
Proof
  rw[lower_def,upper_def,lower_constraints_def]
QED

Definition timeshift_def:
  timeshift f s =
    s with <|
      bst_viewenv updated_by (λenv. f o_f env);
      bst_coh := f o s.bst_coh;
      bst_v_rOld := f s.bst_v_rOld;
      bst_v_wOld := f s.bst_v_wOld;
      bst_v_rNew := f s.bst_v_rNew;
      bst_v_wNew := f s.bst_v_wNew;
      bst_v_Rel := f s.bst_v_Rel;
      bst_v_CAP := f s.bst_v_CAP;
      bst_xclb :=
        OPTION_MAP (λx. x with <|
          xclb_time updated_by f; xclb_view updated_by f
        |>) s.bst_xclb;
      bst_fwdb :=
        λl. s.bst_fwdb l with <|
          fwdb_time updated_by f; fwdb_view updated_by f
        |>; (* fwdb_t_accfupds *)
      bst_prom := MAP f s.bst_prom
    |>
End

Theorem timeshift_simps:
  (timeshift f s).bst_pc = s.bst_pc
  /\ (timeshift f s).bst_environ = s.bst_environ
  /\ timeshift I s = s
Proof
  fs[timeshift_def]
  >> fs[FUN_EQ_THM,bir_state_t_component_equality,fwdb_t_component_equality,finite_mapTheory.o_f_id,I_EQ_IDABS]
  >> qmatch_goalsub_rename_tac `s.bst_xclb`
  >> Cases_on `s.bst_xclb`
  >> fs[optionTheory.OPTION_MAP_DEF,xclb_t_component_equality]
  >> rpt $ irule_at Any EQ_REFL
QED

(* initial constraints on the state *)

Definition time_constraints_def:
   time_constraints s b k <=>
      FEVERY (lower_constraints b k o SND) s.bst_viewenv
      /\ (!l. lower_constraints b k $ s.bst_coh(l))
      /\ lower_constraints b k s.bst_v_rOld
      /\ lower_constraints b k s.bst_v_wOld
      /\ lower_constraints b k s.bst_v_rNew
      /\ lower_constraints b k s.bst_v_wNew
      /\ lower_constraints b k s.bst_v_Rel
      /\ lower_constraints b k s.bst_v_CAP
      /\ EVERY (λx. lower_constraints b k x) s.bst_prom
      /\ (IS_SOME s.bst_xclb ==> (λx.
        lower_constraints b k x.xclb_time
        /\ lower_constraints b k x.xclb_view) $ THE s.bst_xclb)
      /\ (!l. lower_constraints b k (s.bst_fwdb l).fwdb_view
          /\ lower_constraints b k (s.bst_fwdb l).fwdb_time)
End

Theorem bir_eval_view_of_exp_lower_constraints:
  !b k viewenv.
  FEVERY (lower_constraints b k o SND) viewenv
  /\ 0 < b
  ==> !a_e. lower_constraints b k $ bir_eval_view_of_exp a_e viewenv
Proof
  rpt gen_tac >> strip_tac
  >> Induct
  >> rw[bir_eval_view_of_exp_def,lower_constraints_zero,lower_constraints_MAX]
  >> BasicProvers.every_case_tac >> fs[lower_constraints_zero]
  >> imp_res_tac FEVERY_FLOOKUP >> fs[]
QED

Theorem bir_eval_view_of_exp_lower_constraints_FUPDATE:
  !b k viewenv var upd.
  FEVERY (lower_constraints b k o SND) viewenv
  /\ 0 < b
  /\ lower_constraints b k upd
  ==> !a_e. lower_constraints b k $ bir_eval_view_of_exp a_e (viewenv |+ (var, upd))
Proof
  rpt gen_tac >> strip_tac
  >> Induct
  >> rw[bir_eval_view_of_exp_def,lower_constraints_zero,lower_constraints_MAX,FLOOKUP_UPDATE]
  >> BasicProvers.every_case_tac >> fs[lower_constraints_zero]
  >> imp_res_tac FEVERY_FLOOKUP >> fs[]
QED

Theorem bir_eval_view_of_exp_lower_constraints':
  !s b k v_e v_data.
  time_constraints s b k
  /\ 0 < b
  /\ bir_eval_view_of_exp v_e s.bst_viewenv = v_data
  ==> lower_constraints b k v_data
Proof
  fs[iffLR time_constraints_def,bir_eval_view_of_exp_lower_constraints]
QED

Theorem bir_eval_view_of_exp_lower_constraints_FUPDATE:
  !b k viewenv v_upd var.
  FEVERY (lower_constraints b k o SND) viewenv
  /\ 0 < b
  /\ lower_constraints b k v_upd
  ==> !a_e. lower_constraints b k $ bir_eval_view_of_exp a_e $ viewenv |+ (var,v_upd)
Proof
  rpt gen_tac >> strip_tac
  >> Induct
  >> rw[bir_eval_view_of_exp_def,lower_constraints_zero,lower_constraints_MAX,FLOOKUP_UPDATE]
  >> BasicProvers.every_case_tac >> fs[lower_constraints_zero]
  >> imp_res_tac FEVERY_FLOOKUP >> fs[]
QED

Theorem bir_eval_view_of_exp_lower_constraints_FUPDATE':
  !s b k v_e v_data var v_upd.
  time_constraints s b k
  /\ 0 < b
  /\ bir_eval_view_of_exp v_e (s.bst_viewenv |+ (var,v_upd)) = v_data
  /\ lower_constraints b k v_upd
  ==> lower_constraints b k v_data
Proof
  fs[iffLR time_constraints_def,bir_eval_view_of_exp_lower_constraints_FUPDATE]
QED

(* under these constraints can we move  lower b k
   out of  bir_eval_view_of_exp  *)

Theorem bir_eval_view_of_exp_lower_o_f:
  !viewenv b k.
  FEVERY (lower_constraints b k o SND) viewenv
  /\ 0 < b
  ==> !a_e v_addr.
    bir_eval_view_of_exp a_e viewenv = v_addr
    ==>
      bir_eval_view_of_exp a_e ((lower b k) o_f viewenv) = lower b k v_addr
Proof
  rpt gen_tac >> strip_tac
  >> Induct
  >> fs[bir_eval_view_of_exp_def,FLOOKUP_o_f,lower_constraints_zero,lower_zero]
  >- (
    rw[arithmeticTheory.MAX_DEF,lower_def]
    >> BasicProvers.every_case_tac >> fs[]
  )
  >- (
    irule lower_MAX
    >> fs[bir_eval_view_of_exp_lower_constraints]
  )
  >- (
    irule lower_MAX
    >> fs[bir_eval_view_of_exp_lower_constraints]
  )
QED

Theorem bir_eval_view_of_exp_lower_o_f_FUPDATE:
  !viewenv b k upd var.
  FEVERY (lower_constraints b k o SND) viewenv
  /\ 0 < b
  /\ lower_constraints b k upd
  ==> !a_e v_addr.
    bir_eval_view_of_exp a_e (viewenv |+ (var,upd)) = v_addr
    ==>
      bir_eval_view_of_exp a_e (lower b k o_f viewenv |+ (var, lower b k upd)) = lower b k v_addr
Proof
  rpt gen_tac >> strip_tac
  >> Induct
  >> fs[bir_eval_view_of_exp_def,FLOOKUP_o_f,lower_constraints_zero,lower_zero,FLOOKUP_UPDATE]
  >- (
    rw[arithmeticTheory.MAX_DEF,lower_def]
    >> BasicProvers.every_case_tac >> fs[]
  )
  >> irule lower_MAX
  >> fs[bir_eval_view_of_exp_lower_constraints_FUPDATE]
QED

(* under these constraints can we move  lower b k
   out of  xclfail_update_viewenv  *)

Theorem xclfail_update_env_timeshift:
  xclfail_update_env p (timeshift f s) = xclfail_update_env p s
Proof
  fs[timeshift_def,bir_state_t_component_equality,xclfail_update_env_def]
QED

Theorem xclfail_update_viewenv_lower_o_f:
  xclfail_update_viewenv p s = SOME viewenv
  ==> xclfail_update_viewenv p (timeshift (lower b k) s)
    = SOME (lower b k o_f viewenv)
Proof
  fs[Once xclfail_update_viewenv_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> rw[timeshift_def,xclfail_update_viewenv_def]
  >> fs[lower_def]
QED

Theorem fulfil_update_env_timeshift:
  !benv p s xcl f . fulfil_update_env p s xcl = SOME benv
  ==> fulfil_update_env p (timeshift f s) xcl = SOME benv
Proof
  Cases >> rpt gen_tac
  >> fs[Once fulfil_update_env_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> rw[timeshift_def,fulfil_update_env_def]
QED

Theorem fulfil_update_viewenv_timeshift:
  !p s xcl t new_viewenv.
  fulfil_update_viewenv p s xcl t = SOME new_viewenv
  ==> fulfil_update_viewenv p (timeshift (lower b k) s) xcl (lower b k t)
    = SOME $ (lower b k) o_f new_viewenv
Proof
  reverse $ rw[Once fulfil_update_viewenv_def]
  >- fs[fulfil_update_viewenv_def,timeshift_def]
  >> BasicProvers.every_case_tac
  >> gvs[fulfil_update_viewenv_def,timeshift_def]
QED

Theorem mem_get_lower:
  !M' k M'' l t x.
  mem_get (M' ++ REPLICATE k NONE ++ M'') l t = SOME x
  ==> mem_get (M' ++ M'') l (lower (LENGTH M' + 1) k t) = SOME x
Proof
  rpt gen_tac
  >> Cases_on `t < LENGTH M' + 1`
  >> gs[mem_get_APPEND1,lower_def]
  >> Cases_on `t < LENGTH M' + k + 1`
  >- (
    Cases_on `t`
    >> gs[mem_get_def,oEL_THM,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS,rich_listTheory.EL_REPLICATE]
  )
  >> gs[arithmeticTheory.NOT_LESS,mem_get_APPEND2]
QED

Theorem mem_get_lower_constraints:
  !M' k M'' l t x.
  mem_get (M' ++ REPLICATE k NONE ++ M'') l t = SOME x
  ==> lower_constraints (LENGTH M' + 1) k t
Proof
  rpt strip_tac
  >> Cases_on `t < LENGTH M' + 1`
  >> gs[mem_get_APPEND1,lower_constraints_def]
  >> Cases_on `t < LENGTH M' + k + 1`
  >- (
    Cases_on `t`
    >> gs[mem_get_def,oEL_THM,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS,rich_listTheory.EL_REPLICATE]
  )
  >> gs[arithmeticTheory.NOT_LESS,mem_get_APPEND2]
QED

Theorem mem_get_mem_is_loc_mem_is_cid:
  !t M l x. 0 < t /\
  mem_get M l t = SOME x ==> mem_is_loc M t x.loc /\ mem_is_cid M t x.cid
Proof
  rpt strip_tac
  >> gs[mem_get_PRE,mem_is_loc_PRE,mem_is_cid_PRE,AllCaseEqs()]
QED

Theorem bir_exec_stmtB_mix_timeshift:
  !b s s' genv genv' oo f.
  bir_exec_stmtB_mix b (timeshift f s) genv
  = (FST $ bir_exec_stmtB_mix b s genv,
      timeshift f $ FST $ SND $ bir_exec_stmtB_mix b s genv,
      SND $ SND $ bir_exec_stmtB_mix b s genv)
Proof
  Cases
  >> rw[bir_exec_stmtB_mix_def,bir_exec_stmt_assign_mix_def,bir_exec_stmt_observe_mix_def,bir_exec_stmt_assume_mix_def,bir_exec_stmt_fence_def,timeshift_simps,bir_exec_stmt_assert_mix_def]
  >> BasicProvers.every_case_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,timeshift_def,bir_state_set_typeerror_def,bir_state_t_component_equality]
QED

Theorem bir_exec_stmtE_mix_timeshift:
  !e p s s' f.
  bir_exec_stmtE p e s = s'
  ==> bir_exec_stmtE p e (timeshift f s) = timeshift f s'
Proof
  Cases
  >> rw[bir_exec_stmtE_def,bir_exec_stmt_halt_def,bir_exec_stmt_jmp_def,bir_exec_stmt_cjmp_def,timeshift_simps]
  >> BasicProvers.every_case_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,timeshift_def,bir_state_set_typeerror_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem bir_exec_stmt_mix_timeshift:
  !e p s s' genv genv' oo f.
  bir_exec_stmt_mix p e (timeshift f s) genv
    = (FST $ bir_exec_stmt_mix p e s genv,
      timeshift f $ FST $ SND $ bir_exec_stmt_mix p e s genv,
      SND $ SND $ bir_exec_stmt_mix p e s genv)
Proof
  Cases
  >> rw[bir_exec_stmt_mix_def,bir_exec_stmtE_mix_timeshift,pairTheory.ELIM_UNCURRY]
  >> fs[bir_exec_stmtB_mix_timeshift]
  >> fs[bir_state_is_terminated_def,timeshift_def]
QED


Theorem mem_read_lower:
  !M' k M'' l t x.
  mem_read (M' ++ REPLICATE k NONE ++ M'') l t = SOME x
  ==> mem_read (M' ++ M'') l (lower (LENGTH M' + 1) k t) = SOME x
Proof
  rpt gen_tac
  >> Cases_on `t`
  >> rw[mem_read_def,mem_get_lower,AllCaseEqs(),PULL_EXISTS]
  >> imp_res_tac mem_get_lower
  >> fs[]
QED

Theorem mem_is_loc_REPLICATE_lower_constraints:
  !t k M M' l.
  mem_is_loc (M ++ REPLICATE k NONE ++ M') t l
  ==> lower_constraints (LENGTH M + 1) k t
Proof
  spose_not_then assume_tac
  >> gs[DISJ_EQ_IMP,lower_constraints_def,arithmeticTheory.NOT_LESS,arithmeticTheory.NOT_LESS_EQUAL,mem_is_loc_PRE,oEL_THM]
  >> BasicProvers.every_case_tac
  >> gvs[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.LESS_OR_EQ,arithmeticTheory.ADD1,rich_listTheory.EL_REPLICATE]
QED

Theorem mem_is_loc_lower':
  !t k M' M'' l.
  lower_constraints (LENGTH M' + 1) k t
  ==> mem_is_loc (M' ++ M'') (lower (LENGTH M' + 1) k t) l
    = mem_is_loc (M' ++ REPLICATE k NONE ++ M'') t l
Proof
  rpt gen_tac
  >> Cases_on `t < LENGTH M' + 1`
  >> gs[mem_is_loc_APPEND1,lower_def]
  >> Cases_on `t < LENGTH M' + k + 1`
  >- (
    Cases_on `t`
    >> gs[mem_is_loc_def,oEL_THM,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS,rich_listTheory.EL_REPLICATE,lower_constraints_def]
  )
  >> gs[arithmeticTheory.NOT_LESS,mem_is_loc_APPEND2]
QED

Theorem mem_is_loc_lower:
  !t k M' M'' l.
  mem_is_loc (M' ++ REPLICATE k NONE ++ M'') t l
  <=> (mem_is_loc (M' ++ M'') (lower (LENGTH M' + 1) k t) l
        /\ lower_constraints (LENGTH M' + 1) k t)
Proof
  rw[EQ_IMP_THM]
  >> metis_tac[mem_is_loc_REPLICATE_lower_constraints,mem_is_loc_lower']
QED

Theorem mem_is_cid_REPLICATE_lower_constraints:
  !t k M M' l.
  mem_is_cid (M ++ REPLICATE k NONE ++ M') t l
  ==> lower_constraints (LENGTH M + 1) k t
Proof
  Cases
  >> spose_not_then assume_tac
  >> gs[DISJ_EQ_IMP,lower_constraints_def,arithmeticTheory.NOT_LESS,arithmeticTheory.NOT_LESS_EQUAL,mem_is_cid_def,oEL_THM]
  >> BasicProvers.every_case_tac
  >> gvs[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.LESS_OR_EQ,arithmeticTheory.ADD1,rich_listTheory.EL_REPLICATE]
QED

Theorem mem_is_cid_lower':
  !t k M' M'' l.
  lower_constraints (LENGTH M' + 1) k t
  ==> mem_is_cid (M' ++ M'') (lower (LENGTH M' + 1) k t) l
    = mem_is_cid (M' ++ REPLICATE k NONE ++ M'') t l
Proof
  rpt gen_tac
  >> Cases_on `t < LENGTH M' + 1`
  >> gs[mem_is_cid_APPEND1,lower_def]
  >> Cases_on `t < LENGTH M' + k + 1`
  >- (
    Cases_on `t`
    >> gs[mem_is_cid_def,oEL_THM,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,arithmeticTheory.NOT_LESS,rich_listTheory.EL_REPLICATE,lower_constraints_def]
  )
  >> gs[arithmeticTheory.NOT_LESS,mem_is_cid_APPEND2]
QED

Theorem mem_is_cid_lower:
  !t k M' M'' l.
  mem_is_cid (M' ++ REPLICATE k NONE ++ M'') t l
  <=> (mem_is_cid (M' ++ M'') (lower (LENGTH M' + 1) k t) l
        /\ lower_constraints (LENGTH M' + 1) k t)
Proof
  rw[EQ_IMP_THM]
  >> metis_tac[mem_is_cid_REPLICATE_lower_constraints,mem_is_cid_lower']
QED

Theorem mem_read_APPEND_NONE_lower_constraints:
  !t M' k M'' l v.
  mem_read (M' ++ REPLICATE k NONE ++ M'') l t = SOME v
  ==> lower_constraints (LENGTH M' + 1) k t
Proof
  Cases
  >> fs[mem_read_def,lower_constraints_def,mem_get_PRE]
  >> spose_not_then assume_tac
  >> gs[AllCaseEqs(),oEL_THM,DISJ_EQ_IMP,arithmeticTheory.NOT_LESS,arithmeticTheory.ADD1,arithmeticTheory.NOT_LESS_EQUAL,rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,rich_listTheory.EL_REPLICATE]
QED

Theorem clstep_DROP_NONE:
  !p cid s M genv prom s' genv'.
  clstep p cid s M genv prom s' genv'
  ==> !M' k M''. M = (M' ++ REPLICATE k NONE ++ M'')
    /\ time_constraints s (LENGTH M' + 1) k
  ==>
    clstep p cid (timeshift (lower (LENGTH M' + 1) k) s) (M' ++ M'') genv (MAP (lower (LENGTH M' + 1) k) prom) (timeshift (lower (LENGTH M' + 1) k) s') genv'
Proof
  ho_match_mp_tac bir_clstep_ind
  >> conj_tac
  (* read *)
  >- (
    rpt strip_tac
    >> qpat_x_assum `v_pre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_post = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> fs[]
    >> irule_at Any $ cj 1 bir_clstep_rules
    >> fs[]
    >> drule_then (irule_at Any) mem_read_lower
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` $ assume_tac o GSYM
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> drule_at Any $
      Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL]
      bir_eval_view_of_exp_lower_o_f
    >> disch_then $ drule_at_then Any assume_tac
    >> fs[]
    >> qmatch_asmsub_abbrev_tac `lower b k`
    >> imp_res_tac mem_read_APPEND_NONE_lower_constraints
    >> `lower_constraints b k v_addr` by (
      unabbrev_all_tac
      >> qpat_x_assum `_ = v_addr` $ fs o single o GSYM
      >> drule_then irule bir_eval_view_of_exp_lower_constraints
      >> fs[]
    )
    >> conj_tac
    (* ~mem_is_loc *)
    >- (
      gen_tac
      >> fs[timeshift_def,mem_is_loc_lower,AC DISJ_ASSOC DISJ_COMM]
      >> qmatch_goalsub_rename_tac `lower b k t < t'`
      >> qmatch_goalsub_abbrev_tac `lower b k t < t' /\ disj /\ _`
      >> strip_tac
      >> first_x_assum $ qspec_then `upper b k t'` mp_tac
      >> qunabbrev_tac `b`
      >> fs[lower_upper,lower_upper_LESS,lower_upper_LESS_EQ,is_some_some_oEL_upper,lower_constraints_upper]
      >> disch_then irule
      >> unabbrev_all_tac
      >> gs[iffLR time_constraints_def,lower_MAX,lower_COND_zero,upper_lower_LESS_EQ,lower_constraints_COND,lower_constraints_zero,upper_lower_LESS_EQ,lower_zero,lower_constraints_MAX]
    )
    >> fs[bir_state_t_component_equality,timeshift_def]
    >> `lower_constraints (LENGTH M' + 1) k (mem_read_view (s.bst_fwdb l) t)` by (
      fs[time_constraints_def,mem_read_view_def]
      >> irule lower_constraints_COND
      >> gs[]
    )
    >> `lower_constraints b k v_post` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> gs[iffLR time_constraints_def]
    )
    >> `lower_constraints b k v_pre` by (
      unabbrev_all_tac
      >> gs[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero,iffLR time_constraints_def]
    )
    >> conj_tac
    (* FLOOKUP_UPDATE *)
    >- (
      unabbrev_all_tac
      >> rpt $ AP_TERM_TAC ORELSE AP_THM_TAC
      >> simp[mem_read_view_def]
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> gs[iffLR time_constraints_def,lower_zero]
      >> rpt $ AP_TERM_TAC ORELSE AP_THM_TAC
      >> irule COND_CONG
      >> fs[iffLR time_constraints_def,lower_inj]
    )
    >> qmatch_goalsub_abbrev_tac `mem_read_view lower_bst_fwdb (lower b k t)`
    >> qmatch_goalsub_abbrev_tac `MAX (lower b k _) lower_v_post`
    >> `mem_read_view lower_bst_fwdb (lower b k t)
      = lower b k $ mem_read_view (s.bst_fwdb l) t` by (
      qunabbrev_tac `lower_bst_fwdb`
      >> simp[mem_read_view_def]
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_COND]
      >> irule_at Any COND_CONG
      >> gs[EQ_IMP_THM,iffLR time_constraints_def]
      >> strip_tac
      >> irule $ iffLR lower_inj
      >> goal_assum $ drule_at Any
      >> fs[iffLR time_constraints_def]
    )
    >> `lower_v_post = lower b k v_post` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> gs[iffLR time_constraints_def,lower_zero]
    )
    >> gs[combinTheory.o_DEF,FUN_EQ_THM,iffLR time_constraints_def,lower_zero,GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
    >> conj_tac (* nested if-MAX-if *)
    >- (
      unabbrev_all_tac
      >> irule COND_CONG
      >> fs[combinTheory.o_DEF,FUN_EQ_THM,iffLR time_constraints_def,lower_zero,GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
    )
    >> conj_tac (* nested if-MAX-if *)
    >- (
      unabbrev_all_tac
      >> irule COND_CONG
      >> fs[combinTheory.o_DEF,FUN_EQ_THM,iffLR time_constraints_def,lower_zero,GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
    )
    >> conj_tac (* nested if-MAX *)
    >- (
      dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> `!a b c. b = c ==> MAX a b = MAX a c` by fs[arithmeticTheory.MAX_DEF]
      >> pop_assum $ irule_at Any
      >> irule_at Any COND_CONG
      >> unabbrev_all_tac
      >> fs[iffLR time_constraints_def,lower_zero,GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
    )
    (* nested OPTION_MAP-if *)
    >> BasicProvers.every_case_tac
    >> fs[]
  )
  >> conj_tac
  (* xcl fail *)
  >- (
    rpt strip_tac
    >> gvs[]
    >> irule_at Any $ cj 2 bir_clstep_rules
    >> imp_res_tac $ GSYM xclfail_update_viewenv_lower_o_f
    >> fs[timeshift_simps,xclfail_update_env_timeshift]
    >> simp[timeshift_def,bir_state_t_component_equality,timeshift_def]
  )
  >> conj_tac
  (* write *)
  >- (
    rpt strip_tac
    >> qpat_x_assum `v_pre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> gvs[]
    >> irule_at Any $ cj 3 bir_clstep_rules
    >> rpt $ qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> fs[timeshift_simps]
    >> irule_at Any $ GSYM fulfil_update_env_timeshift
    >> qpat_x_assum `SOME _ = fulfil_update_env _ _ _` $ irule_at Any
    >> drule_then assume_tac mem_get_lower_constraints
    >> irule_at Any $ GSYM fulfil_update_viewenv_timeshift
    >> qpat_x_assum `SOME _ = fulfil_update_viewenv _ _ _ _` $ irule_at Any
    >> drule_then (irule_at Any) mem_get_lower
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> fs[timeshift_def,bir_eval_exp_view_def]
    >> drule_at Any $
      Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL]
      bir_eval_view_of_exp_lower_o_f
    >> disch_then (fn thm =>
      drule_at_then Any assume_tac thm
      >> rev_drule_at_then Any assume_tac thm)
    >> fs[bir_state_t_component_equality,rich_listTheory.FILTER_MAP,MEM_MAP_f,combinTheory.o_DEF]
    >> qmatch_goalsub_abbrev_tac `lower b k`
    >> qmatch_goalsub_abbrev_tac `MAP _ l1 = MAP _ l2`
    >> `l1 = l2` by (
      unabbrev_all_tac
      >> fs[time_constraints_def,EVERY_MEM]
      >> rw[rich_listTheory.FILTER_EQ]
      >> fs[lower_inj]
    )
    >> pop_assum $ fs o single
    >> qmatch_goalsub_abbrev_tac `xcl ==> Atomic`
    >> `xcl ==> Atomic` by (
      rw[Abbr`Atomic`,fulfil_atomic_ok_def]
      >> fs[fulfil_atomic_ok_def]
      >> qmatch_assum_abbrev_tac `A ==> _`
      >> `A` by (
        Cases_on`s.bst_xclb` >- fs[]
        >> unabbrev_all_tac
        >> irule $ iffRL mem_is_loc_lower
        >> gvs[time_constraints_def]
      )
      >> qpat_x_assum `A ==> _` mp_tac
      >> fs[mem_is_loc_lower,mem_is_cid_lower]
      >> Cases_on `s.bst_xclb` >> fs[]
      >> disch_then $ qspec_then `upper b k t'` mp_tac
      >> unabbrev_all_tac
      >> fs[lower_upper,lower_upper_LESS,upper_lower_LESS,lower_constraints_upper]
    )
    >> pop_assum $ fs o single
    >> `lower_constraints b k v_addr /\ lower_constraints b k v_data` by (
      rw[]
      >> drule_then irule $ SIMP_RULE (srw_ss()) [combinTheory.o_DEF] bir_eval_view_of_exp_lower_constraints
      >> fs[Abbr`b`]
    )
    >> rpt $ qpat_x_assum `_ = bir_eval_view_of_exp _ _` $ assume_tac o GSYM
    >> fs[lower_LESS,lower_COND,iffLR time_constraints_def,lower_MAX,lower_constraints_MAX,lower_constraints_COND]
    >> conj_tac
    >- (irule lower_LESS >> fs[Abbr`v_pre`])
    >> conj_tac
    >- (irule lower_LESS >> fs[Abbr`v_pre`])
    >> conj_tac
    >- (irule lower_LESS >> fs[Abbr`v_pre`,iffLR time_constraints_def])
    >> conj_tac
    >- (irule lower_LESS >> fs[Abbr`v_pre`,iffLR time_constraints_def])
    >> conj_tac
    >- (
      (* containing 0 *)
      qspecl_then [`k`,`b`] (ONCE_REWRITE_TAC o single o GSYM) $ GEN_ALL $ cj 1 lower_zero
      >> qunabbrev_tac `b`
      >> fs[lower_MAX,lower_COND,lower_constraints_MAX,lower_constraints_zero,iffLR time_constraints_def]
      >> irule lower_LESS
      >> fs[Abbr`v_pre`,lower_constraints_COND,lower_constraints_MAX,lower_MAX,lower_zero,iffLR time_constraints_def,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero]
    )
    >> conj_tac
    >- (
      (* containing 0 *)
      qspecl_then [`k`,`b`] (ONCE_REWRITE_TAC o single o GSYM) $ GEN_ALL $ cj 1 lower_zero
      >> qunabbrev_tac `b`
      >> fs[lower_MAX,lower_COND,lower_constraints_MAX,lower_constraints_zero,iffLR time_constraints_def]
      >> irule lower_LESS
      >> fs[Abbr`v_pre`,lower_constraints_COND,lower_constraints_MAX,lower_MAX,lower_zero,iffLR time_constraints_def,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero]
    )
    >> conj_tac
    (* get_xclb_view *)
    >- (
      qspecl_then [`k`,`b`] (ONCE_REWRITE_TAC o single o GSYM) $ GEN_ALL $ cj 1 lower_zero
      >> Cases_on `s.bst_xclb`
      >> gs[get_xclb_view_def]
      >- (
        qunabbrev_tac `b`
        >> fs[lower_LESS,lower_constraints_zero,lower_constraints_zero]
      )
      >> dep_rewrite.DEP_REWRITE_TAC[lower_COND,lower_LESS,lower_constraints_COND,lower_constraints_zero]
      >> unabbrev_all_tac
      >> fs[time_constraints_def,lower_COND,lower_LESS,lower_constraints_COND,lower_constraints_zero]
    )
    >> conj_tac
    >- (
      (* containing 0 *)
      qspecl_then [`k`,`b`] (ONCE_REWRITE_TAC o single o GSYM) $ GEN_ALL $ cj 1 lower_zero
      >> qunabbrev_tac `b`
      >> fs[lower_LESS,lower_COND,iffLR time_constraints_def,lower_MAX,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero,lower_zero]
    )
    >> conj_tac
    >- (
      gs[combinTheory.o_DEF,FUN_EQ_THM,iffLR time_constraints_def,lower_zero,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> rw[GSYM lower_MAX]
    )
    (* OPTION_MAP equality *)
    >> simp[Once COND_RAND]
  )
  >> conj_tac
  (* amo *)
  >- (
    rpt strip_tac
    >> qpat_x_assum `v_rPre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_rPost = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> qpat_x_assum `v_wPre = _` $ assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]
    >> gvs[]
    >> irule_at Any $ cj 4 bir_clstep_rules
    >> rpt $ qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` $ assume_tac o GSYM
    >> drule_then (irule_at Any) mem_read_lower
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> drule_at Any $
      Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL]
      bir_eval_view_of_exp_lower_o_f
    >> disch_then (fn thm =>
      drule_at_then Any assume_tac thm
      >> rev_drule_at_then Any assume_tac thm)
    >> drule_then (irule_at Any) mem_get_lower
    >> qmatch_goalsub_abbrev_tac `lower b k`
    >> imp_res_tac mem_read_APPEND_NONE_lower_constraints
    >> `lower_constraints b k $ mem_read_view (s.bst_fwdb l) t_r` by (
      fs[time_constraints_def,mem_read_view_def]
      >> irule lower_constraints_COND
      >> gs[]
    )
    >> `lower_constraints b k v_addr` by (
      rw[]
      >> irule $ SIMP_RULE (srw_ss()) [PULL_FORALL] bir_eval_view_of_exp_lower_constraints
      >> fs[Abbr`b`]
    )
    >> `lower_constraints b k v_rPost` by (
      unabbrev_all_tac
      >> fs[lower_constraints_MAX,time_constraints_def,lower_constraints_COND,lower_constraints_zero]
      >> dep_rewrite.DEP_REWRITE_TAC[lower_constraints_MAX,time_constraints_def,lower_constraints_COND]
      >> fs[lower_constraints_zero]
    )
    >> `lower_constraints b k v_data` by (
      drule_then irule bir_eval_view_of_exp_lower_constraints_FUPDATE'
      >> fs[Abbr`b`]
      >> rpt $ goal_assum $ drule_at Any
    )
    >> `lower_constraints b k v_wPre /\ lower_constraints b k v_rPre` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[lower_constraints_MAX,lower_constraints_COND]
      >> fs[lower_constraints_zero,time_constraints_def]
    )
    >> gs[timeshift_def,bir_state_t_component_equality,rich_listTheory.FILTER_MAP,MEM_MAP_f,combinTheory.o_DEF]
    >> qmatch_goalsub_abbrev_tac `MAP _ l1 = MAP _ l2`
    >> `l1 = l2` by (
      unabbrev_all_tac
      >> fs[time_constraints_def,EVERY_MEM]
      >> rw[rich_listTheory.FILTER_EQ]
      >> fs[lower_inj]
    )
    >> pop_assum $ fs o single
    >> `lower_constraints b k t_w` by fs[time_constraints_def,EVERY_MEM]
    >> conj_tac
    >- (
      rpt strip_tac
      >> qmatch_asmsub_rename_tac `t' < lower b k t_w`
      >> first_x_assum $ qspec_then `upper b k t'` mp_tac
      >> unabbrev_all_tac
      >> gs[lower_upper_LESS,upper_lower_LESS,is_some_some_oEL_upper,mem_is_loc_lower,lower_upper]
    )
    >> qmatch_goalsub_abbrev_tac `mem_read_view lower_bst_fwdb $ lower b k t_r`
    >> `mem_read_view lower_bst_fwdb $ lower b k t_r
      = lower (LENGTH M' + 1) k (mem_read_view (s.bst_fwdb l) t_r)` by (
      unabbrev_all_tac
      >> simp[mem_read_view_def]
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_COND]
      >> irule_at Any COND_CONG
      >> gs[EQ_IMP_THM,iffLR time_constraints_def]
      >> strip_tac
      >> irule $ iffLR lower_inj
      >> goal_assum $ drule_at Any
      >> fs[iffLR time_constraints_def]
    )
    >> `0 < b` by fs[Abbr`b`]
    >> qmatch_goalsub_abbrev_tac `_ |+ (var,lower_v_rPost)`
    >> `lower_v_rPost = lower b k v_rPost` by (
      unabbrev_all_tac
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero]
      >> gs[iffLR time_constraints_def,lower_zero,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero]
    )
    >> `bir_eval_view_of_exp v_e (lower b k o_f s.bst_viewenv |+ (var,lower_v_rPost))
      = lower b k $ bir_eval_view_of_exp v_e (s.bst_viewenv |+ (var,v_rPost))` by (
      fs[]
      >> dep_rewrite.DEP_REWRITE_TAC $ single $ SIMP_RULE (srw_ss()) [PULL_FORALL] bir_eval_view_of_exp_lower_o_f_FUPDATE
      >> unabbrev_all_tac
      >> gs[iffLR time_constraints_def,lower_LESS]
    )
    >> ntac 2 $ pop_assum $ fs o single
    >> unabbrev_all_tac
    >> gs[iffLR time_constraints_def,lower_MAX,lower_COND_zero,lower_COND,lower_LESS,pairTheory.ELIM_UNCURRY,combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero]
    >> rpt $ irule_at Any lower_LESS
    >> gs[iffLR time_constraints_def,lower_MAX,lower_COND_zero,lower_COND,lower_LESS,pairTheory.ELIM_UNCURRY,combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM,lower_constraints_MAX,lower_constraints_COND,lower_constraints_zero,lower_zero]
    >> conj_tac
    >- (
      dep_rewrite.DEP_REWRITE_TAC[lower_COND_zero,lower_COND,lower_MAX,lower_constraints_COND,lower_constraints_MAX]
      >> fs[iffLR time_constraints_def,lower_constraints_zero]
    )
    >> conj_tac
    >- (
      dep_rewrite.DEP_REWRITE_TAC[lower_COND_zero,lower_COND,lower_MAX,lower_constraints_COND,lower_constraints_MAX]
      >> fs[iffLR time_constraints_def,lower_constraints_zero]
    )
    >> rw[FUN_EQ_THM]
    (*
      (* FLOOKUP_UPDATE *)
      unabbrev_all_tac
      >> rpt $ AP_TERM_TAC ORELSE AP_THM_TAC
      >> simp[mem_read_view_def]
      >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_constraints_COND,lower_constraints_MAX,lower_constraints_zero]
      >> gs[iffLR time_constraints_def,lower_zero]
    *)
  )
  >> conj_tac
  (* fence *)
  >- (
    rpt strip_tac >> gvs[]
    >> irule_at Any $ cj 5 bir_clstep_rules
    >> fs[timeshift_def,bir_state_t_component_equality]
    >> dep_rewrite.DEP_REWRITE_TAC[GSYM lower_MAX,GSYM lower_COND,lower_zero,lower_constraints_zero,lower_constraints_MAX,lower_constraints_COND]
    >> fs[time_constraints_def]
  )
  >> conj_tac
  (* branch *)
  >- (
    rpt strip_tac >> gvs[]
    >> irule_at Any $ cj 6 bir_clstep_rules
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> drule_at Any $
      Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL]
      bir_eval_view_of_exp_lower_o_f
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> disch_then $ drule_then assume_tac
    >> fs[Ntimes timeshift_def 3,bir_exec_stmt_mix_timeshift]
    >> fs[bir_state_t_component_equality,timeshift_def]
    >> irule $ GSYM lower_MAX
    >> qpat_x_assum `_ = v_addr` $ fs o single o GSYM
    >> drule_then (irule_at Any) bir_eval_view_of_exp_lower_constraints
    >> fs[time_constraints_def]
  )
  >> conj_tac
  (* expr *)
  >- (
    rpt strip_tac >> gvs[]
    >> irule_at Any $ cj 7 bir_clstep_rules >> fs[]
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` $ assume_tac o GSYM
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` $ assume_tac o GSYM
    >> fs[timeshift_simps,bir_eval_exp_view_def]
    >> imp_res_tac $ cj 1 $ iffLR time_constraints_def
    >> drule_at Any $
      Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL]
      bir_eval_view_of_exp_lower_o_f
    >> disch_then $ drule_at_then Any assume_tac
    >> fs[bir_state_t_component_equality,timeshift_def]
  )
  (* generic *)
  >- (
    rpt strip_tac >> gvs[]
    >> irule_at Any $ cj 8 bir_clstep_rules >> fs[]
    >> fs[timeshift_simps,bir_exec_stmt_mix_timeshift]
  )
QED

Theorem cstep_seq_DROP_NONE:
  !p cid sys1 sys2.
  cstep_seq p cid sys1 sys2
  ==> !s M k M' genv s' M'' genv'.
    sys1 = (s, M ++ (REPLICATE k NONE) ++ M', genv)
    /\ sys2 = (s', M'', genv')
  ==>
  ?s''. cstep_seq p cid (s, M ++ M', genv) (s'', M ++ DROP (LENGTH M + k) M'', genv')
  /\ s''.bst_prom
    = MAP (λx. if x < LENGTH M then x else x - LENGTH M - k) s'.bst_prom
Proof
  ho_match_mp_tac bir_cstep_seq_ind
  >> conj_tac >> ntac 2 (rpt gen_tac >> strip_tac)
  >> gvs[rich_listTheory.DROP_APPEND1]
  >> qmatch_goalsub_abbrev_tac `MAP f`
  >- (
    dsimp[bir_cstep_seq_cases]
    >> qmatch_asmsub_rename_tac `clstep _ _ _ _ _ prom _ _`
    >> CONV_TAC $ RESORT_EXISTS_CONV rev
    >> qexists_tac `MAP f prom`
    >> fs[]
  )
QED

Theorem is_certified_NONE_is_certified:
  !s' s t M p cid msg genv.
  s' = s with bst_prom updated_by (\pr. pr ++ [t])
  /\ LENGTH M < t
  /\ is_certified p cid s'
    (M ++ REPLICATE (t - (LENGTH M + 1)) NONE ++ [SOME msg]) genv
  /\ msg.cid = cid
  ==>
    is_certified p cid
      (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))
      (M ++ [SOME msg]) genv
Proof
  rpt strip_tac
  >> fs[is_certified_def,cstep_seq_rtc_def]
  >> CONV_TAC $ RESORT_EXISTS_CONV rev
  >> qexists_tac `genv`
  >> qexists_tac `M ++ [SOME msg] ++ DROP (SUC t) M'`
  >> cheat
  >> fs[arithmeticTheory.NRC_RTC]
QED

Theorem parstep_bisim:
  !cid cores M genv cores' M' genv'.
  parstep cid cores M genv cores' M' genv'
  ==>
    parstep cid cores M genv cores' M genv'
    \/ parstep cid cores M genv
        (FUPDATE cores (cid,
          Core cid
            (get_core_prog $ THE $ FLOOKUP cores cid)
            ((get_core_state $ THE $ FLOOKUP cores cid) with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))
            ))
        (M++[LAST M']) genv
Proof
  rpt strip_tac
  >> dxrule_then strip_assume_tac $ iffLR bir_parstep_cases
  >> drule_then strip_assume_tac cstep_bisim
  >- (
    disj1_tac
    >> fs[bir_parstep_cases]
    >> rpt $ goal_assum $ drule_at Any
    >> fs[]
  )
  >> disj2_tac
  >> fs[FLOOKUP_UPDATE,get_core_state,get_core_prog,bir_parstep_cases]
  >> rpt $ goal_assum $ drule_at Any
  >> fs[bir_cstep_cases]


QED

val _ = export_theory();