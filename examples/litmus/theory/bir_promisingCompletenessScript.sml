(* This file will probably be deleted *)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory finite_mapTheory;
open bir_promisingTheory bir_programTheory;

val _ = new_theory "bir_promisingCompleteness"

(********** DEFINITIONS **********)
Definition MAXL_def:
  MAXL [] = 0
  /\
  MAXL (x::xs) = MAX x (MAXL xs)
End

Definition sim_time_def:
  sim_time i j v =
  if v < i \/ j < v then v
  else if v = i then j
  else PRE v
End

Definition sim_view_def:
  sim_view i j v v' =
  ?l. v = MAXL l /\ v' = MAXL (MAP (sim_time i j) l)
End

Definition sim_coh_def:
  sim_coh i j coh coh' =
  !l. sim_view i j (coh l) (coh' l)
End

Definition sim_view_opt_def:
  sim_view_opt i j NONE NONE = T
  /\
  sim_view_opt i j (SOME v) NONE = F
  /\
  sim_view_opt i j NONE (SOME v') = F
  /\
  sim_view_opt i j (SOME v) (SOME v') = sim_view i j v v'
End

Definition sim_viewenv_def:
  sim_viewenv i j viewenv viewenv' =
  !r. sim_view_opt i j (FLOOKUP viewenv r) (FLOOKUP viewenv' r)
End

Definition sim_fwdb_def:
  sim_fwdb i j fwdb fwdb' =
  !l. (fwdb' l).fwdb_time = sim_time i j (fwdb l).fwdb_time /\
      (sim_view i j ((fwdb l).fwdb_view) ((fwdb' l).fwdb_view)) /\
      ((fwdb l).fwdb_xcl = (fwdb' l).fwdb_xcl)
End

Definition sim_prom_def:
  sim_prom i j prom = MAP (sim_time i j) $ FILTER (\p. i <> p) prom
End

(* TODO: Fix memory simulation relation *)

Definition sim_memory_def:
  sim_memory i j Ms Mz = T
End

Definition sim_def:
  sim i j (s, Ms) (z, Mz) = (
  i <> 0 /\ i <= j /\ i <= LENGTH Mz /\
  s.bst_pc = z.bst_pc /\
  s.bst_environ = z.bst_environ /\
  s.bst_status = z.bst_status /\
  z.bst_prom = sim_prom i j s.bst_prom /\
  sim_memory i j Ms Mz /\
  sim_viewenv i j s.bst_viewenv z.bst_viewenv /\
  sim_coh i j s.bst_coh z.bst_coh /\
  sim_view i j s.bst_v_rOld z.bst_v_rOld /\
  sim_view i j s.bst_v_wOld z.bst_v_wOld /\
  sim_view i j s.bst_v_rNew z.bst_v_rNew /\
  sim_view i j s.bst_v_wNew z.bst_v_wNew /\
  sim_view i j s.bst_v_CAP  z.bst_v_CAP /\
  sim_view i j s.bst_v_Rel  z.bst_v_Rel /\
  sim_fwdb i j s.bst_fwdb   z.bst_fwdb
  (* TODO: bst_xclb *)
  )
End

(********** THEOREM **********)
Theorem MAX_MAXL:
  !l l'. MAX (MAXL l) (MAXL l') = MAXL (l ++ l')
Proof
  rpt gen_tac >>
  Induct_on ‘l’ >> (fs [MAXL_def]) >>
  (METIS_TAC [MAXL_def, MAX_ASSOC])
QED

Theorem MAXL_APPEND:
  !l l'. MAXL (l ++ l') = MAXL (l' ++ l)
Proof
  rpt gen_tac >>
  Induct_on ‘l’ >> (fs [MAXL_def]) >>
  gen_tac >>
  fs [GSYM MAX_MAXL, MAXL_def] >>
  METIS_TAC [MAX_COMM, MAX_ASSOC]
QED

Theorem SNOC_MAXL:
  !x xs. MAXL (SNOC x xs) = MAX x (MAXL xs)
Proof
  rpt gen_tac >>
  Induct_on ‘xs’ >> (fs [MAXL_def]) >>
  METIS_TAC [MAX_ASSOC, MAX_COMM]
QED

Theorem sim_view0:
  !i j.
    sim_view i j 0 0
Proof
  rpt gen_tac >>
  fs [sim_view_def] >>
  Q.EXISTS_TAC ‘[]’ >>
  fs [MAXL_def]
QED

Theorem sim_view_time:
  !i j t.
    sim_view i j t (sim_time i j t)
Proof
  rpt strip_tac >>
  fs [sim_view_def] >>
  Q.EXISTS_TAC ‘[t]’ >>
  fs [MAXL_def]
QED

Theorem sim_view_MAX:
  !i j v v' w w'.
    sim_view i j v v' /\ sim_view i j w w'
    ==> sim_view i j (MAX v w) (MAX v' w')
Proof
  rpt strip_tac >>
  fs [sim_view_def, MAXL_def] >>
  Q.EXISTS_TAC ‘l ++ l'’ >> fs [MAX_MAXL]
QED

Theorem sim_viewenv_FDOM:
  !i j viewenv viewenv'.
    sim_viewenv i j viewenv viewenv' ==> FDOM viewenv = FDOM viewenv'
Proof
  rpt strip_tac >>
  fs [sim_viewenv_def, pred_setTheory.EXTENSION] >>
  gen_tac >>
  rename1 ‘x IN (FDOM viewenv)’ >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  Cases_on ‘FLOOKUP viewenv x’ >> Cases_on ‘FLOOKUP viewenv' x’ >>
  (fs [FLOOKUP_DEF, sim_view_opt_def])
QED

Theorem sim_viewenv_FUPDATE_sim_view:
  !i j viewenv viewenv' v v' var.
    sim_viewenv i j viewenv viewenv' /\ sim_view i j v v' ==>
    sim_viewenv i j (viewenv |+ (var, v)) (viewenv' |+ (var, v'))
Proof
  fs [sim_viewenv_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  CASE_TAC >>
  fs [sim_view_opt_def]
QED

Theorem sim_time_bijective:
  !i j t t'.
    t = t' <=> sim_time i j t = sim_time i j t'
Proof
  rpt gen_tac >> eq_tac >> fs [sim_time_def]
QED

Theorem sim_fwdb_mem_read_view:
  !i j fwdb fwdb' l t.
    sim_fwdb i j fwdb fwdb' ==>
    sim_view i j (mem_read_view (fwdb l) t) (mem_read_view (fwdb' l) (sim_time i j t))
Proof
  rpt strip_tac >>
  fs [mem_read_view_def, sim_fwdb_def] >>
  first_x_assum (qspec_then ‘l’ assume_tac) >>
  fs [] >>
  Cases_on ‘(fwdb l).fwdb_xcl’ >|
  [
    fs [sim_view_time]
    ,
    fs [] >>
    rpt CASE_TAC >>
    METIS_TAC [sim_time_bijective, sim_view_time]
  ]
QED

(* bir_exec_stmt only touch bst_status, bst_environ and bst_pc *)
Theorem bir_exec_stmt_noninterference:
  !prog stmt P oo P' Q.
    bir_exec_stmt prog stmt P = (oo, P') /\
    P.bst_status = Q.bst_status /\ P.bst_pc = Q.bst_pc /\ P.bst_environ = Q.bst_environ
    ==>
    bir_exec_stmt prog stmt Q = (oo, Q with <| bst_status := P'.bst_status ; bst_environ := P'.bst_environ; bst_pc := P'.bst_pc |>)
Proof
  rpt strip_tac >>
  fs [bir_state_t_component_equality] >>
  Cases_on ‘stmt’ >|
  [
    rename1 ‘BStmtB stmtB’ >>
    fs [bir_exec_stmt_def] >>
    Cases_on ‘stmtB’ >>
    (fs [bir_exec_stmtB_def, bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
         bir_exec_stmt_assume_def, bir_exec_stmt_observe_def, bir_exec_stmt_fence_def] >>
     rpt (gvs [bir_state_set_typeerror_def, bir_state_t_component_equality, bir_state_is_terminated_def] >>
          FULL_CASE_TAC))
    ,
    rename1 ‘BStmtE stmtE’ >>
    fs [bir_exec_stmt_def] >>
    Cases_on ‘stmtE’ >>
    rpt (gvs [bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_state_set_typeerror_def, bir_state_t_component_equality,
              bir_state_is_terminated_def, bir_exec_stmt_jmp_to_label_def, bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_def, bir_exec_stmt_halt_def] >>
         FULL_CASE_TAC)
  ]
QED

(* bir_exec_stmt only touch bst_status, bst_environ and bst_pc *)
Theorem bir_exec_stmt_invar:
  !prog stmt S oo S'.
    bir_exec_stmt prog stmt S = (oo, S') ==>
    bir_exec_stmt prog stmt S = (oo, S with <| bst_status := S'.bst_status ; bst_environ := S'.bst_environ; bst_pc := S'.bst_pc |>)
Proof
  rpt strip_tac >>
  irule bir_exec_stmt_noninterference >>
  HINT_EXISTS_TAC >>
  fs []
QED

Theorem sim_viewenv_bir_eval_view_of_exp:
  !i j viewenv viewenv' e.
    sim_viewenv i j viewenv viewenv' ==>
    sim_view i j (bir_eval_view_of_exp e viewenv) (bir_eval_view_of_exp e viewenv')
Proof
  rpt strip_tac >>
  fs [] >>
  Induct_on ‘e’ >|
  [ (* Const *)
    fs [bir_eval_view_of_exp_def, sim_view0]
    , (* MemConst *)
    fs [bir_eval_view_of_exp_def, sim_view0]
    , (* Den *)
    fs [bir_eval_view_of_exp_def, sim_view0] >>
    gen_tac >>
    CASE_TAC >> CASE_TAC >> 
    (
    gvs [sim_view_opt_def, sim_view_opt_def, sim_view0, sim_viewenv_def] >>
    qpat_x_assum ‘!r. sim_view_opt _ _ _ _’ (qspec_then ‘b’ assume_tac) >>
    rfs [sim_view_opt_def]
    )
    , (* Cast *)
    fs [bir_eval_view_of_exp_def, sim_view0]
    , (* Unary *)
    fs [bir_eval_view_of_exp_def, sim_view0]
    , (* BinExp *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
    , (* BinPred *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
    , (* MemEq *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
    , (* IfThenElse *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
    , (* Load *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
    , (* Store *)
    fs [bir_eval_view_of_exp_def, sim_view0, sim_view_MAX]
  ]
QED

Triviality sim_view_if:
  !i j v w v' w'.
    (sim_view i j v w /\ sim_view i j v' w') ==>
    (!P. sim_view i j (if P then v else v') (if P then w else w'))
Proof
  METIS_TAC []
QED

val irule_sim_view = map irule [sim_view_MAX, sim_view_if, sim_viewenv_bir_eval_view_of_exp, sim_viewenv_FUPDATE_sim_view]

(* clstep that do NOT touch promises *)
Theorem X:
  !p cid s M l z s' i j M'.
    clstep p cid s M l s' /\ sim i j (s,M) (z,M') /\ is_certified p cid s' M
    ==> ?z'. clstep p cid z M' (MAP (sim_time i j) l) z' /\ sim i j (s',M) (z',M') 
Proof
  rpt strip_tac >>
  Q.REFINE_EXISTS_TAC ‘<| bst_pc := z_pc'; bst_environ := z_environ';
                          bst_status := z_status'; bst_viewenv := z_viewenv';
                          bst_coh := z_coh'; bst_v_rOld := z_v_rOld'; bst_v_wOld := z_v_wOld';
                          bst_v_rNew := z_v_rNew'; bst_v_wNew := z_v_wNew';
                          bst_v_CAP := z_v_CAP'; bst_v_Rel := z_v_Rel'; bst_prom := z_prom';
                          bst_fwdb := z_fwdb'; bst_xclb := z_xclb';
			  bst_inflight := z.bst_inflight; bst_counter := z.bst_counter |>’ >>
  gvs [clstep_cases, clstep_cases, sim_def, bir_eval_exp_view_def, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] >|
  [ (* READ *)
    fs [bir_state_t_component_equality] >>
    rename1 ‘mem_read M l t = SOME v’ >>
    Q.LIST_EXISTS_TAC [‘v’, ‘l’, ‘sim_time i j t’] >>
    fs [] >>
    conj_tac >|
    [ (* TODO: Trivial? mem_read M' l (sim_time i j t) = SOME v *)
      cheat
      ,
      conj_tac >|
      [
          (* TODO: Difficult! stupid read rule for time stamps, need invariant *)
          cheat
          , (* Just sim_view stuff *)
          fs [sim_fwdb_mem_read_view, sim_coh_def] >>
          imp_res_tac sim_fwdb_mem_read_view >>
          rpt conj_tac >>
          rpt (
            rpt gen_tac >>
            FIRST irule_sim_view >>
            rpt conj_tac >> fs [sim_view0]
            )
        ]
    ]
    , (* WRITE XCLFAIL*)
    fs [xclfail_update_env_def, xclfail_update_viewenv_def] >>
    rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
    gvs [bir_state_t_component_equality] >>
    rpt (FULL_CASE_TAC >> fs[]) >>
    rpt $ qpat_x_assum ‘_ |+ _ = _’ $ assume_tac o GSYM >>
    gvs [sim_viewenv_FUPDATE_sim_view, sim_view0]
    , (* TODO: WRITE *)
    cheat
    , (* TODO:  AMO *)
    cheat
    , (* FENCE *)
    fs [bir_state_t_component_equality] >>
    conj_tac >>
    rpt (
      FIRST irule_sim_view >> 
      conj_tac >> fs [sim_view0]
      )
    , (* BRANCH *)
    fs [] >>
    rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
    drule_all bir_exec_stmt_noninterference >>
    drule_all bir_exec_stmt_invar >>
    rpt strip_tac >>
    fs [] >>
    gvs [sim_view_MAX, bir_state_t_component_equality, sim_viewenv_bir_eval_view_of_exp]
    , (* EXPR *)
    fs [bir_state_t_component_equality, bir_eval_exp_view_def] >>
    rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
    fs [] >>
    fs [sim_viewenv_FUPDATE_sim_view, sim_viewenv_bir_eval_view_of_exp]
    , (* Generic *)
    drule_all bir_exec_stmt_noninterference >>
    drule_all bir_exec_stmt_invar >>
    rpt strip_tac >>
    gvs [bir_state_t_component_equality]
  ] 
QED

val _ = export_theory ()
