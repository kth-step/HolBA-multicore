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
  bir_eval_exp_view exp env viewenv ext =
  (bir_eval_exp exp env ext, bir_eval_view_of_exp exp viewenv)
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
    => SOME (bir_exec_stmtE p (BStmt_Jmp e) s, SND s)
  | BStmtE $ BStmt_Halt e
    => SOME (bir_exec_stmtE p (BStmt_Halt e) s,SND s)
  | _ => NONE
End

Theorem bmc_exec_general_stmt_mc_invar:
  !s s' stm p.
  bmc_exec_general_stmt p stm s = SOME s' ==>
  (FST s).bst_viewenv = (FST s').bst_viewenv /\
  (FST s).bst_coh     = (FST s').bst_coh /\
  (FST s).bst_v_rOld  = (FST s').bst_v_rOld /\
  (FST s).bst_v_wOld  = (FST s').bst_v_wOld /\
  (FST s).bst_v_rNew  = (FST s').bst_v_rNew /\
  (FST s).bst_v_wNew  = (FST s').bst_v_wNew /\
  (FST s).bst_v_CAP   = (FST s').bst_v_CAP /\
  (FST s).bst_v_Rel   = (FST s').bst_v_Rel /\
  (FST s).bst_prom    = (FST s').bst_prom /\
  (FST s).bst_fwdb    = (FST s').bst_fwdb /\
  (FST s).bst_xclb    = (FST s').bst_xclb
Proof
  ntac 2 Cases >> ntac 2 Induct
  >> rpt gen_tac >> strip_tac
  >> fs[bmc_exec_general_stmt_def,bir_exec_stmtB_def,pairTheory.ELIM_UNCURRY,AllCaseEqs()]
  >> fs[pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_exec_stmtB_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_exec_stmt_assign_def,bir_exec_stmt_assert_def,bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_halt_def]
  >> gvs[]
QED

Theorem bir_exec_stmt_cjmp_mc_invar':
  !s cond_e lbl1 lbl2 p s'.
  bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s = s' ==>
  (FST s).bst_viewenv = s'.bst_viewenv /\
  (FST s).bst_coh     = s'.bst_coh /\
  (FST s).bst_v_rOld  = s'.bst_v_rOld /\
  (FST s).bst_v_wOld  = s'.bst_v_wOld /\
  (FST s).bst_v_rNew  = s'.bst_v_rNew /\
  (FST s).bst_v_wNew  = s'.bst_v_wNew /\
  (FST s).bst_v_CAP   = s'.bst_v_CAP /\
  (FST s).bst_v_Rel   = s'.bst_v_Rel /\
  (FST s).bst_prom    = s'.bst_prom /\
  (FST s).bst_fwdb    = s'.bst_fwdb /\
  (FST s).bst_xclb    = s'.bst_xclb
Proof
  PairCases >> rpt gen_tac >> strip_tac
  >> fs[bir_exec_stmt_cjmp_def,pairTheory.ELIM_UNCURRY,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def]
  >> gvs[]
QED

Theorem bir_exec_stmt_cjmp_mc_invar =
  GSYM $ SIMP_RULE (srw_ss()) [] bir_exec_stmt_cjmp_mc_invar'

Definition fulfil_update_env_def:
  fulfil_update_env p s =
    case bir_get_current_statement p s.bst_pc of
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ F _ _
      => SOME s.bst_environ
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ T _ _
      => bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 0w))
          (bir_var_type var_succ) s.bst_environ
    | _ => NONE
End

Definition fulfil_update_viewenv_def:
  fulfil_update_viewenv p s v_post =
    case bir_get_current_statement p s.bst_pc of
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ T _ _
      => SOME (s.bst_viewenv |+ (var_succ, v_post))
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ F _ _
      => SOME s.bst_viewenv
    | _ => NONE
End

Definition xclfail_update_env_def:
  xclfail_update_env p s =
    case bir_get_current_statement p s.bst_pc of
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ T _ _
      => bir_env_update (bir_var_name var_succ) (BVal_Imm (Imm64 1w)) (bir_var_type var_succ) s.bst_environ
    | _ => NONE
End

Definition xclfail_update_viewenv_def:
  xclfail_update_viewenv p s =
    case bir_get_current_statement p s.bst_pc of
    | SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ _ _ T _ _
        => SOME (s.bst_viewenv |+ (var_succ, 0))
    | _ => NONE
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

(* core-local steps that don't affect memory *)
Inductive clstep:
(* read *)
(!p s s' v a_e xcl acq rel M l (t:num) v_pre v_post v_addr var new_env cid opt_cast ext tp.
    bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel
 /\ s.bst_status = BST_Running
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv ext
 /\ mem_read M l t = SOME v
 /\ v_pre = MAX (MAX (MAX v_addr s.bst_v_rNew) (if (acq /\ rel) then s.bst_v_Rel else 0))
               (if (acq /\ rel) then (MAX s.bst_v_rOld s.bst_v_wOld) else 0)
 /\ latest_t l M t $ MAX v_pre (s.bst_coh l)
 /\ v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 (* TODO: Update viewenv by v_addr or v_post? *)
 /\ s' = s with <| bst_viewenv updated_by (\env. FUPDATE env (var, v_post));
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
  clstep p cid tp (s,ext) M [] (s',ext))

/\ (* exclusive-failure *)
(!p s s' M var_succ a_e v_e acq rel cid new_env new_viewenv ext tp.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e T acq rel
 /\ s.bst_status = BST_Running
 /\  SOME new_env = xclfail_update_env p s
 /\  SOME new_viewenv = xclfail_update_viewenv p s
 /\  s' = s with <| bst_environ := new_env;
                    bst_viewenv := new_viewenv;
                    bst_xclb := NONE;
                    bst_pc := (bir_pc_next o bir_pc_next o bir_pc_next) s.bst_pc |>
 ==>
clstep p cid tp (s,ext) M [] (s',ext))

/\ (* fulfil *)
(!p s s' M v var_succ a_e xcl acq rel l (t:num) v_pre v_post v_addr v_data v_e cid new_env new_viewenv ext tp.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel
 /\ s.bst_status = BST_Running
 /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv ext
 /\ (SOME v, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv ext
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
 /\ SOME new_env = fulfil_update_env p s
 (* TODO: Update viewenv by v_post or something else? *)
 /\ SOME new_viewenv = fulfil_update_viewenv p s v_post
 /\ s' = s with <| bst_viewenv := new_viewenv;
                   bst_prom updated_by (FILTER (\t'. t' <> t));
                   bst_environ := new_env;
                   bst_coh     updated_by (l =+ v_post);
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
  clstep p cid tp (s,ext) M [t] (s',ext))

/\ (* AMO fulfil *)
(!p cid s s' M acq rel var l a_e v_r v_w v_e v_rPre v_rPost v_wPre v_wPost (t_w:num) (t_r :num) new_environ new_viewenv ext tp.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel
   /\ s.bst_status = BST_Running
   (* Get location *)
   /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv ext
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
   /\ (SOME v_w, v_data) = bir_eval_exp_view v_e new_environ new_viewenv ext
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
                     bst_prom    updated_by (FILTER (\t'. t' <> t_w));
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
                     bst_pc updated_by (bir_pc_next o bir_pc_next) |>
 ==>
 clstep p cid tp (s,ext) M [t_w] (s',ext))

/\ (* fence *)
(!p s s' K1 K2 M cid v ext tp.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Fence K1 K2
   /\ s.bst_status = BST_Running
   /\ v = MAX (if is_read K1 then s.bst_v_rOld else 0) (if is_write K1 then s.bst_v_wOld else 0)
   /\ s' = s with <| bst_v_rNew := MAX s.bst_v_rNew (if is_read K2 then v else 0);
                     bst_v_wNew := MAX s.bst_v_wNew (if is_write K2 then v else 0);
                     bst_pc updated_by bir_pc_next |>
==>
  clstep p cid tp (s,ext) M [] (s',ext))

/\ (* branch (conditional jump) *)
(!p s s' M cid v s2 v_addr cond_e lbl1 lbl2 ext tp.
   bir_get_current_statement p s.bst_pc
    = SOME $ BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2
   /\ s.bst_status = BST_Running
    /\ (SOME v, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv ext
    /\ s2 = bir_exec_stmt_cjmp p cond_e lbl1 lbl2 (s,ext)
    /\ s' = s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>
==>
  clstep p cid tp (s,ext) M [] (s',ext))

/\ (* register-to-register operation *)
(!p s s' var M cid v v_val e new_env ext tp.
  bir_get_current_statement p s.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assign var e
 /\ s.bst_status = BST_Running
 /\ (SOME v, v_val) = bir_eval_exp_view e s.bst_environ s.bst_viewenv ext
 /\ SOME new_env = env_update_cast64 (bir_var_name var) v (bir_var_type var) (s.bst_environ)
 /\ s' = s with <| bst_environ := new_env;
                   bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                   bst_pc      updated_by bir_pc_next |>
==> clstep p cid tp (s,ext) M [] (s',ext))

/\ (* Other BIR single steps *)
(!p s s' M cid stm ext ext' tp.
  bir_get_current_statement p s.bst_pc = SOME $ BSGen stm
    /\ bmc_exec_general_stmt p stm (s,ext) = SOME (s',ext')
    /\ s.bst_status = BST_Running
==>
  clstep p cid tp (s,ext) M [] (s',ext))

/\ (* external functionality *)
(!p s s' M cid ext ext' tp R.
  bir_get_current_statement p s.bst_pc = SOME $ BSExt R
    /\ R (s,(tp,M),ext) (s',ext')
    /\ s.bst_status = BST_Running
==>
  clstep p cid tp (s,ext) M [] (s',ext'))
End


(* core steps *)
Inductive cstep:
(* execute *)
(!p cid s M s' prom tp.
  clstep p cid tp s M prom s'
==>
  cstep p cid tp s M prom s' M)

/\ (* promise *)
(!p cid s M s' t msg tp.
   (msg.cid = cid
   /\ t = LENGTH M + 1
   /\ FST s' = (FST s) with bst_prom updated_by (\pr. pr ++ [t]))
   /\ SND s = SND s'
==>
  cstep p cid tp s M [t] s' (M ++ [msg]))
End

(* core steps seq *)
Inductive cstep_seq:
(* seq *)
(!p cid s M s' prom tp.
  clstep p cid tp s M (prom:num list) s'
==>
  cstep_seq p cid tp (s, M) (s', M))

/\ (* write *)
(!p cid s M s' s'' M' t tp.
  (cstep p cid tp s M [t] s' M' /\ ~(M = M')
  /\ clstep p cid tp s' M' [t] s'')
==>
  cstep_seq p cid tp (s, M) (s'', M'))
End

Definition cstep_seq_rtc_def:
  cstep_seq_rtc p cid tp = RTC $ cstep_seq p cid tp
End

(* cstep_seq invariant *)

Theorem bir_exec_stmt_jmp_bst_prom:
  !st ext p lbl. st.bst_prom = (bir_exec_stmt_jmp p lbl (st,ext)).bst_prom
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

Definition is_certified_def:
  is_certified p cid tp s M = ?s' M'.
    cstep_seq_rtc p cid tp (s, M) (s', M')
    /\ (FST s').bst_prom = []
End

val _ = Datatype `core_t =
  Core num (('a, 'ext_state_t, 'shared_state_t) bir_generic_program_t) bir_state_t
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
     /\ bir_get_program_block_info_by_label p s.bst_pc.bpc_label = SOME (i, BBlock_Stmts bl)
     /\ bl.bb_mc_tags = SOME mc_tags
     /\ mc_tags.mc_atomic = T
`;

val atomicity_ok_def = Define`
  atomicity_ok cid cores =
    cores_pc_not_atomic (cores \\ cid)
`;

(* system step *)
Inductive parstep:
(!p cid s s' ext ext' M M' cores prom tp.
   FLOOKUP cores cid = SOME (Core cid p s)
    /\ atomicity_ok cid cores
    /\ tp = FRANGE $ get_core_state o_f (cores \\ cid)
    /\ cstep p cid tp (s,ext) M prom (s',ext') M'
    /\ is_certified p cid tp (s',ext') M'
==>
   parstep cid cores ext M (FUPDATE cores (cid, Core cid p s')) ext' M')
End

val _ = export_theory();
