(*
  Promising Semantics for multicore BIR
*)

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

val _ = new_theory "bir_promising";

(* message type, represents a store of the form ⟨loc ≔ val⟩_tid *)
val _ = Datatype‘
  mem_msg_t = <|
    loc : bir_val_t;
    val : bir_val_t;
    cid : num
    |>
’;

(* type abbreviation for abstract and concrete programs *)
Type proga_t = ``:(('a list) # num list) bmc_program_t``
Type progc_t = ``:(mem_msg_t) proga_t``

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
   | SOME m => if m.loc = l then SOME m else NONE
   | NONE => NONE
’;

(*
  mem_read M l t returns the value at address l at time t, if it exists
  NB. at time 0 all addresses have a default value
 *)
val mem_read_def = Define‘
   mem_read M l t =
   case mem_get M l t of
   | SOME m => SOME m.val
   | NONE => NONE
’;


Theorem mem_read_zero:
  !M l. mem_read M l 0 = SOME $ BVal_Imm $ Imm64 0w
Proof
  fs[mem_read_def,mem_get_def,mem_default_value_def,mem_default_def]
QED

val mem_is_loc_def = Define‘
   mem_is_loc M 0 l = T
   /\
   mem_is_loc M (SUC t) l =
   case oEL t M of
   | SOME m => m.loc = l
   | NONE => F
’;

Theorem mem_get_is_loc:
  !M t l.
    IS_SOME (mem_get M l t) = mem_is_loc M t l
Proof
  Cases_on ‘t’ >|
  [
    fs [mem_get_def, mem_is_loc_def]
    ,
    fs [mem_get_def, mem_is_loc_def] >>
    rpt gen_tac >>
    rename1 ‘oEL t M’ >>
    Cases_on ‘oEL t M’ >|
    [
      fs []
      ,
      fs [] >>
      CASE_TAC >>
      (fs [])
    ]
  ]
QED

Theorem mem_is_loc_append:
  !t M M'. t <= LENGTH M
  ==> mem_is_loc (M ++ M') t l = mem_is_loc M t l
Proof
  Cases
  >> fs[mem_is_loc_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND1]
QED

Theorem mem_get_SOME:
  !l t M msg.
    mem_get M l t = SOME msg
    ==>
    l = msg.loc
Proof
  Cases_on ‘t’
  >> fs[mem_get_def, mem_default_def]
  >> rpt strip_tac
  >> Cases_on ‘oEL n M’
  >> gvs[]
QED

Theorem mem_get_mem_read:
  !M l t v.
    mem_read M l t = SOME v
    ==>
    ?m. mem_get M l t = SOME m /\ m.val = v
Proof
  Induct_on ‘t’ >- fs[mem_read_def, mem_get_def]
  >> rpt strip_tac
  >> fs[mem_read_def, mem_get_def]
  >> Cases_on ‘oEL t M’
  >- fs[]
  >> Cases_on ‘x.loc = l’ >- fs[]
  >> fs[]
QED

Theorem mem_get_mem_read_imp:
  !M l t m. mem_get M l t = SOME m ==> mem_read M l t = SOME m.val
Proof
  fs[mem_read_def]
QED

Theorem mem_get_LENGTH:
  !t M l v. mem_get M l t = SOME v ==> t <= LENGTH M
Proof
  Cases >> rw[mem_get_def,listTheory.oEL_THM]
QED

Theorem mem_get_append:
  !t M M' l msg.
    t <= LENGTH M ==> mem_get (M++M') l t = mem_get M l t
Proof
  rpt strip_tac
  >> Cases_on ‘t’
  >> fs[mem_get_def] (* discharges 0 case, SUC remains *)
  >> fs[listTheory.oEL_THM, rich_listTheory.EL_APPEND1]
QED

Theorem mem_read_some:
  !M l t v.
    mem_read M l t = SOME v ==> t <= LENGTH M \/ (t = 0 /\ v = mem_default_value)
Proof
  Induct_on ‘t’
  >> rpt strip_tac
  >> fs[mem_read_def,mem_get_def]
  >> Cases_on ‘oEL t M’
  >> fs[listTheory.oEL_EQ_EL, listTheory.oEL_def]
QED

Theorem mem_read_append:
  !t M M' l msg.
    t <= LENGTH M ==> mem_read (M++M') l t = mem_read M l t
Proof
  fs[mem_read_def,mem_get_append]
QED

Theorem mem_read_LENGTH:
  !t M l v. mem_read M l t = SOME v ==> t <= LENGTH M
Proof
  Cases >> rw[mem_read_some,mem_read_def,AllCaseEqs()]
  >> imp_res_tac mem_get_LENGTH
QED

val mem_is_cid_def = Define‘
   mem_is_cid M 0 cid = F
   /\
   mem_is_cid M (SUC t) cid =
   case oEL t M of
   | SOME m => m.cid = cid
   | NONE => F
’;

Theorem mem_read_mem_is_loc:
  !t M l l' v. 0 < t /\ mem_read M l t = SOME v /\ mem_is_loc M t l' ==> l = l'
Proof
  Cases
  >> rw[mem_read_def,mem_is_loc_def,mem_get_def]
  >> gs[AllCaseEqs()]
QED

Theorem mem_is_cid_append:
  !t M M' cid. t <= LENGTH M ==> mem_is_cid (M ++ M') t cid = mem_is_cid M t cid
Proof
  Cases >> rpt gen_tac >> fs[mem_is_cid_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND1]
QED

Theorem mem_read_mem_is_loc_imp:
  !t l M msg. mem_read M l t = SOME msg ==> mem_is_loc M t l
Proof
  Cases >> fs[mem_is_loc_def,mem_read_def,mem_get_def,AllCaseEqs(),PULL_EXISTS]
QED

Theorem mem_get_mem_is_cid:
  !t M l msg cid.
  mem_get M l t = SOME msg
  /\ mem_is_cid M t cid
  ==> msg.cid = cid /\ msg.loc = l
Proof
  Cases >> csimp[mem_get_def,mem_is_cid_def,AllCaseEqs(),PULL_EXISTS]
QED

(* Note that this currently does not take into account ARM *)
val mem_read_view_def = Define‘
  mem_read_view (f:fwdb_t) t = if f.fwdb_time = t ∧ ~f.fwdb_xcl then f.fwdb_view else t
’;

val bir_eval_view_of_exp = Define‘
  (bir_eval_view_of_exp (BExp_BinExp op e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_BinPred pred e1 e2) viewenv =
   MAX (bir_eval_view_of_exp e1 viewenv) (bir_eval_view_of_exp e2 viewenv))
/\ (bir_eval_view_of_exp (BExp_UnaryExp op e) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Cast cty e ity) viewenv =
    bir_eval_view_of_exp e viewenv)
/\ (bir_eval_view_of_exp (BExp_Den v) viewenv =
    case FLOOKUP viewenv v of NONE => 0 | SOME view => view)
/\ (bir_eval_view_of_exp exp viewenv = 0)
’;

(* bir_eval_exp_view behaves like bir_eval_exp except it also computes
   the view of the expression
   Analogue of ⟦-⟧_m in the paper, except instead of a combined environment m
   of type Reg -> Val # View we unfold it into two mappings
   env : Reg -> Val and viewenv : Reg -> View
   This is so as not to change the definition of bir_eval_exp
*)
val bir_eval_exp_view_def = Define‘
  bir_eval_exp_view exp env viewenv =
  (bir_eval_exp exp env, bir_eval_view_of_exp exp viewenv)
’;

val exp_is_load_def = Define `
  (exp_is_load (BExp_Load _ _ _ _) = T) /\
  (exp_is_load _ = F)
`;

val get_xclb_view_def = Define`
  get_xclb_view (SOME xclb) = xclb.xclb_view
∧ get_xclb_view NONE = 0
`;

val fulfil_atomic_ok_def = Define`
  fulfil_atomic_ok M l cid t_r t_w =
     (mem_is_loc M t_r l ==>
       !t'. (t_r < t' /\ t' < t_w /\ mem_is_loc M t' l) ==> mem_is_cid M t' cid)
`;

Theorem fulfil_atomic_ok_append:
  !M M' l cid t t'.
  t' <= LENGTH M /\ t <= LENGTH M
  ==> fulfil_atomic_ok (M ++ M') l cid t t'
  = fulfil_atomic_ok M l cid t t'
Proof
  rpt strip_tac
  >> fs[fulfil_atomic_ok_def,mem_is_loc_append,mem_is_cid_def,mem_is_cid_append]
  >> rw[EQ_IMP_THM]
  >> first_x_assum irule
  >> gs[mem_is_loc_append]
QED

val env_update_cast64_def = Define‘
  env_update_cast64 varname (BVal_Imm v) vartype env =
    bir_env_update varname (BVal_Imm (n2bs (b2n v) Bit64)) vartype env
’;

Definition bmc_exec_general_stmt_def:
  bmc_exec_general_stmt p stm s =
  case stm of
  | BStmtB $ BMCStmt_Assert e
    => SOME $ bir_exec_stmtB (BStmt_Assert e) s
  | BStmtB $ BMCStmt_Assume e
    => SOME $ bir_exec_stmtB (BStmt_Assume e) s
  | BStmtE $ BStmt_Jmp e
  (* hack until observations are expressed by a put statement *)
    => SOME $ bir_exec_stmtE p (BStmt_Jmp e) s
  | BStmtE $ BStmt_Halt e
    => SOME $ bir_exec_stmtE p (BStmt_Halt e) s
  | _ => NONE
End

Theorem bir_exec_stmt_jmp_to_label_mc_invar:
  !p pc s.
  (bir_exec_stmt_jmp_to_label p pc s).bst_viewenv = s.bst_viewenv /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_coh     = s.bst_coh /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_rOld  = s.bst_v_rOld /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_wOld  = s.bst_v_wOld /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_rNew  = s.bst_v_rNew /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_wNew  = s.bst_v_wNew /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_CAP   = s.bst_v_CAP /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_v_Rel   = s.bst_v_Rel /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_prom    = s.bst_prom /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_fwdb    = s.bst_fwdb /\
  (bir_exec_stmt_jmp_to_label p pc s).bst_xclb    = s.bst_xclb
Proof
  fs[bir_exec_stmt_jmp_to_label_def,COND_RAND]
QED

Theorem bmc_exec_general_stmt_mc_invar:
  !s s' stm p.
  bmc_exec_general_stmt p stm s = SOME s' ==>
  s.bst_viewenv = s'.bst_viewenv /\
  s.bst_coh     = s'.bst_coh /\
  s.bst_v_rOld  = s'.bst_v_rOld /\
  s.bst_v_wOld  = s'.bst_v_wOld /\
  s.bst_v_rNew  = s'.bst_v_rNew /\
  s.bst_v_wNew  = s'.bst_v_wNew /\
  s.bst_v_CAP   = s'.bst_v_CAP /\
  s.bst_v_Rel   = s'.bst_v_Rel /\
  s.bst_prom    = s'.bst_prom /\
  s.bst_fwdb    = s'.bst_fwdb /\
  s.bst_xclb    = s'.bst_xclb
Proof
  ntac 2 gen_tac >> ntac 2 Induct
  >> rpt gen_tac >> strip_tac
  >> fs[bmc_exec_general_stmt_def,bir_exec_stmtB_def,pairTheory.ELIM_UNCURRY,AllCaseEqs()]
  >> fs[pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_exec_stmtB_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_exec_stmt_assign_def,bir_exec_stmt_assert_def,bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_halt_def]
  >> gvs[]
QED

Theorem bir_exec_stmt_cjmp_mc_invar':
  !s cond_e lbl1 lbl2 p s'.
  bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s = s' ==>
  s.bst_viewenv = s'.bst_viewenv /\
  s.bst_coh     = s'.bst_coh /\
  s.bst_v_rOld  = s'.bst_v_rOld /\
  s.bst_v_wOld  = s'.bst_v_wOld /\
  s.bst_v_rNew  = s'.bst_v_rNew /\
  s.bst_v_wNew  = s'.bst_v_wNew /\
  s.bst_v_CAP   = s'.bst_v_CAP /\
  s.bst_v_Rel   = s'.bst_v_Rel /\
  s.bst_prom    = s'.bst_prom /\
  s.bst_fwdb    = s'.bst_fwdb /\
  s.bst_xclb    = s'.bst_xclb
Proof
  rpt gen_tac >> strip_tac
  >> fs[bir_exec_stmt_cjmp_def,pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def]
  >> gvs[]
QED

Theorem bir_exec_stmt_cjmp_mc_invar =
  GSYM $ SIMP_RULE (srw_ss()) [] bir_exec_stmt_cjmp_mc_invar'

(* success value for a store *)
Definition v_succ_def:
  v_succ = Imm64 0w
End

(* failure value for a store *)
Definition v_fail_def:
  v_fail = Imm64 1w
End

Definition fulfil_update_env_def:
  fulfil_update_env var_succ xcl env =
  if xcl then
    bir_env_update (bir_var_name var_succ) (BVal_Imm v_succ)
      (bir_var_type var_succ) env
  else SOME env
End

Definition fulfil_update_viewenv_def:
  fulfil_update_viewenv var_succ xcl v_post viewenv =
  SOME $ if xcl then viewenv |+ (var_succ,v_post) else viewenv
End

Definition xclfail_update_env_def:
  xclfail_update_env var_succ env =
    bir_env_update (bir_var_name var_succ) (BVal_Imm v_fail)
      (bir_var_type var_succ) env
End

Definition xclfail_update_viewenv_def:
  xclfail_update_viewenv var_succ viewenv = SOME $ viewenv |+ (var_succ,0n)
End

(* reading at time stamp  t  at location  l  from memory  M  would not see a
   memory update that is out of scope wrt  to  *)
Definition latest_t_def:
  latest_t l M (t:num) to =
  !t'. t < t' /\ t' <= to ==> ~(mem_is_loc M t' l)
End

Theorem latest_t_append:
  !t l M M' to.
  latest_t l M t to /\ to <= LENGTH M
  ==> latest_t l (M ++ M') t to
Proof
  rw[latest_t_def]
  >> first_x_assum drule
  >> fs[mem_is_loc_append]
QED

Theorem latest_t_dec:
  !l M t to to'.
  latest_t l M t to /\ to' <= MAX t to ==> latest_t l M t to'
Proof
  rw[latest_t_def]
QED

Theorem latest_t_trans:
  !l M t to to'.
  latest_t l M t to /\ latest_t l M to to' ==> latest_t l M t to'
Proof
  rw[latest_t_def]
  >> ntac 2 $ first_x_assum $ drule_at_then Any assume_tac
  >> fs[GSYM arithmeticTheory.NOT_LESS]
  >> qmatch_assum_rename_tac `~A ==> B`
  >> Cases_on `A` >> fs[]
QED

Theorem latest_t_append_eq:
  !t l M M' to.
    to <= LENGTH M ==> latest_t l (M ++ M') t to = latest_t l M t to
Proof
  rw[latest_t_def,mem_is_loc_append]
QED


(* function that can be reused in abstract models, e.g. like
   s' = (bir_state_fulful_view_updates s t loc v_addr v_data acq rel xcl) s'
   enforcing only some updates
*)
Definition bir_state_fulful_view_updates_def:
  bir_state_fulful_view_updates s t loc v_addr v_data acq rel xcl = λs'. s' with <|
    bst_coh    updated_by (loc =+ t);
    bst_v_wOld := MAX s.bst_v_wOld t;
    bst_v_CAP  := MAX s.bst_v_CAP v_addr;
    bst_v_Rel  := MAX s.bst_v_Rel (if (rel /\ acq) then t else 0);
    bst_v_rNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_rNew t) else s.bst_v_rNew;
    bst_v_wNew := if (rel /\ acq /\ xcl) then (MAX s.bst_v_wNew t) else s.bst_v_wNew;
    bst_fwdb   updated_by (loc =+ <| fwdb_time := t; fwdb_view := MAX v_addr v_data; fwdb_xcl := xcl |>);
    bst_xclb   := if xcl then NONE else s.bst_xclb;
  |>
End

Definition bir_state_read_view_updates_def:
  bir_state_read_view_updates s t loc v_addr v_post acq rel xcl = λs'. s' with <|
    bst_coh    updated_by (loc =+ MAX (s.bst_coh loc) v_post);
    bst_v_rOld := MAX s.bst_v_rOld v_post;
    bst_v_rNew := if acq then (MAX s.bst_v_rNew v_post) else s.bst_v_rNew;
    bst_v_wNew := if acq then (MAX s.bst_v_wNew v_post) else s.bst_v_wNew;
    bst_v_Rel  := MAX s.bst_v_Rel (if (rel /\ acq) then v_post else 0);
    bst_v_CAP  := MAX s.bst_v_CAP v_addr;
    bst_xclb   := if xcl
                then SOME <| xclb_time := t; xclb_view := v_post |>
                else s.bst_xclb
  |>
End

Definition is_read_def:
  is_read BM_Read = T /\
  is_read BM_ReadWrite = T /\
  is_read _ = F
End

Definition is_write_def:
  is_write BM_ReadWrite = T /\
  is_write BM_Write = T /\
  is_write _ = F
End

Definition fence_updates_def:
  fence_updates K1 K2 s =
    let v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
    in
      s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
             |>
End

Definition remove_prom_def:
  remove_prom prom = FILTER (λt. ~MEM t prom)
End

(* core-local steps that don't affect memory *)
Inductive clstep:
(* read *)
(!p s s' v a_e xcl acq rel M l (t:num) v_pre v_post v_addr var new_env cid opt_cast.
    bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel
 /\ s.bst_status = BST_Running
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ mem_read M l t = SOME v
 /\ v_pre = MAX (MAX (MAX v_addr s.bst_v_rNew) (if (acq /\ rel) then s.bst_v_Rel else 0))
               (if (acq /\ rel) then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
 /\ latest_t l M t $ MAX v_pre (s.bst_coh l)
 /\ v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 (* TODO: Update viewenv by v_addr or v_post? *)
 /\ s' = (bir_state_read_view_updates s t l v_addr v_post acq rel xcl s)
          with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
                  bst_environ := new_env;
                  bst_pc updated_by bir_pc_next |>
 ==>
  clstep p cid s M [] s')

/\ (* exclusive-failure *)
(!p s s' M var_succ a_e v_e acq rel cid new_env new_viewenv.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e T acq rel
 /\ s.bst_status = BST_Running
 /\  SOME new_env = xclfail_update_env var_succ s.bst_environ
 /\  SOME new_viewenv = xclfail_update_viewenv var_succ s.bst_viewenv
 /\  s' = s with <| bst_environ := new_env;
                    bst_viewenv := new_viewenv;
                    bst_xclb := NONE;
                    bst_pc updated_by bir_pc_next |>
 ==>
clstep p cid s M [] s')

/\ (* fulfil *)
(!p s s' M v var_succ a_e xcl acq rel l (t:num) v_pre v_post v_addr v_data v_e cid new_env new_viewenv.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel
 /\ s.bst_status = BST_Running
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
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
 /\ SOME new_env = fulfil_update_env var_succ xcl s.bst_environ
 (* TODO: Update viewenv by v_post or something else? *)
 /\ SOME new_viewenv = fulfil_update_viewenv var_succ xcl v_post s.bst_viewenv
 /\ s' = (bir_state_fulful_view_updates s t l v_addr v_data acq rel xcl s)
           with <| bst_viewenv := new_viewenv;
                   bst_prom updated_by (remove_prom [t]);
                   bst_environ := new_env;
                   bst_pc updated_by bir_pc_next |>
 ==>
  clstep p cid s M [t] s')

/\ (* AMO fulfil *)
(!p cid s s' M acq rel var l a_e v_r v_w v_e v_rPre v_rPost v_wPre v_wPost (t_w:num) (t_r :num) new_environ new_viewenv.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel
   /\ s.bst_status = BST_Running
   (* Get location *)
   /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
   (* Read part *)
   /\ mem_read M l t_r = SOME v_r (* v_r value read *)
   /\ v_rPre = MAX v_addr (
        MAX s.bst_v_rNew
        (if acq /\ rel then (MAX s.bst_v_Rel (MAX s.bst_v_rOld s.bst_v_wOld)) else 0))
   /\ v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r)
   (* register and register view update *)
   /\ SOME new_environ = env_update_cast64 (bir_var_name var) v_r (bir_var_type var) (s.bst_environ)
   /\ new_viewenv = FUPDATE s.bst_viewenv (var, v_rPost)
   (* Write part *)
   /\ MEM t_w s.bst_prom
   (* v_w value to write, v_e value expression *)
   /\ (SOME v_w, v_data) = bir_eval_exp_view v_e new_environ new_viewenv
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
   /\ t_r < t_w
   (* No writes to memory location between read and write *)
   /\ (!t'. t_r < t' /\ t' < t_w ==> mem_is_loc M t' l)
   (* State update *)
   /\ s' = s with <| bst_viewenv := new_viewenv;
                     bst_environ := new_environ;
                     bst_prom updated_by (remove_prom [t_w]);
                     bst_coh     updated_by (l =+ v_wPost);
                     bst_v_Rel   updated_by (MAX (if acq /\ rel then v_wPost else 0));
                     bst_v_rOld  updated_by (MAX v_rPost);
                     bst_v_rNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_wNew  updated_by (MAX (if acq then (if rel then v_wPost else v_rPost)else 0));
                     bst_v_CAP   updated_by (MAX v_addr);
                     bst_v_wOld  updated_by (MAX v_wPost);
                     bst_fwdb    updated_by (l =+ <| fwdb_time := t_w;
                                                     fwdb_view := MAX v_addr v_data;
                                                     fwdb_xcl := T |>);
                     bst_pc updated_by bir_pc_next |>
 ==>
 clstep p cid s M [t_w] s')

/\ (* fence *)
(!p s s' K1 K2 M cid.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Fence K1 K2
   /\ s.bst_status = BST_Running
   /\ s' = fence_updates K1 K2 (s with bst_pc updated_by bir_pc_next)
==>
  clstep p cid s M [] s')

/\ (* branch (conditional jump) *)
(!p s s' M cid v s2 v_addr cond_e lbl1 lbl2.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2
   /\ s.bst_status = BST_Running
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
    /\ s2 = bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>
==>
  clstep p cid s M [] s')

/\ (* register-to-register operation *)
(!p s s' var M cid v v_val e new_env.
  bir_get_current_statement p s.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assign var e
 /\ s.bst_status = BST_Running
 /\ (SOME v, v_val) = bir_eval_exp_view e s.bst_environ s.bst_viewenv
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 /\ s' = s with <| bst_environ := new_env;
                   bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                   bst_pc      updated_by bir_pc_next |>
==> clstep p cid s M [] s')

/\ (* Other BIR single steps *)
(!p s s' M cid stm.
  bir_get_current_statement p s.bst_pc = SOME $ BSGen stm
    /\ bmc_exec_general_stmt p stm s = SOME s'
    /\ s.bst_status = BST_Running
==>
  clstep p cid s M [] s')

/\ (* external functionality *)
(!p s s' M cid R.
  bir_get_current_statement p s.bst_pc = SOME $ BSExt R
    /\ R (s,(M,prom)) s'
    /\ s.bst_status = BST_Running
    (* well-formedness of ext functionality *)
    /\ (!l. s.bst_coh l <= s'.bst_coh l)
    /\ s'.bst_prom = remove_prom prom s.bst_prom
    /\ (set prom) SUBSET (set s.bst_prom)
    /\ EVERY (λt. t <= LENGTH M /\ ?l. mem_is_loc M t l
      /\ s.bst_coh l < t /\ t <= s'.bst_coh l) prom
    /\ MEM s'.bst_pc.bpc_label (bir_labels_of_program p)
==>
  clstep p cid s M prom s')
End


(* core steps *)
Inductive cstep:
(* execute *)
(!p cid s M s' prom.
  clstep p cid s M prom s'
==>
  cstep p cid s M prom s' M)

/\ (* promise *)
(!p cid s M s' t msg.
   msg.cid = cid
   /\ t = LENGTH M + 1
   /\ s' = s with bst_prom updated_by (\pr. pr ++ [t])
==>
  cstep p cid s M [t] s' (M ++ [msg]))
End

(* core steps seq *)
Inductive cstep_seq:
(* seq *)
(!p cid s M s' prom.
  clstep p cid s M (prom:num list) s'
==>
  cstep_seq p cid (s, M) (s', M))

/\ (* write *)
(!p cid s M s' s'' M' t.
  (cstep p cid s M [t] s' M' /\ ~(M = M')
  /\ clstep p cid s' M' [t] s'')
==>
  cstep_seq p cid (s, M) (s'', M'))
End

Definition cstep_seq_rtc_def:
  cstep_seq_rtc p cid = RTC $ cstep_seq p cid
End

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

Definition is_certified_def:
  is_certified p cid s M = ?s' M'.
    cstep_seq_rtc p cid (s, M) (s', M')
    /\ s'.bst_prom = []
End

val _ = Datatype `core_t =
  Core num (('a, 'shared_state_t) bir_generic_program_t) bir_state_t
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
    ~?cid p s i bl.
     FLOOKUP cores cid = SOME (Core cid p s)
     /\ s.bst_pc.bpc_index <> 0
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, BBlock_Stmts bl)
`;

val atomicity_ok_def = Define`
  atomicity_ok cid cores =
    cores_pc_not_atomic (cores \\ cid)
`;

(* system step *)
Inductive parstep:
(!p cid s s' M M' cores prom.
   FLOOKUP cores cid = SOME (Core cid p s)
    /\ cstep p cid s M prom s' M'
    /\ is_certified p cid s' M'
==>
   parstep cid cores M (FUPDATE cores (cid, Core cid p s')) M')
End

val _ = export_theory();
