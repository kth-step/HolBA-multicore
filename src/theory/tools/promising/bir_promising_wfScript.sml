open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;
open bir_programTheory;
open bir_valuesTheory;
open bir_expTheory;
open finite_mapTheory;

val _ = new_theory "bir_promising_wf";

Theorem bir_exec_stmt_jmp_bst_eq:
  !s p lbl.
     (bir_exec_stmt_jmp p lbl s).bst_v_rNew = s.bst_v_rNew
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_rOld = s.bst_v_rOld
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_wNew = s.bst_v_wNew
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_wOld = s.bst_v_wOld
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_Rel  = s.bst_v_Rel
  /\ (bir_exec_stmt_jmp p lbl s).bst_viewenv  = s.bst_viewenv
  /\ (!l. (bir_exec_stmt_jmp p lbl s).bst_coh l = s.bst_coh l)
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

Definition latest_def:
  latest l 0 M = 0
  /\ latest l (SUC t) M =
  case oEL t M of
    SOME msg =>
      if l = msg.loc then SUC t else latest l t M
  | _ => latest l t M
End

Definition well_formed_fwdb_def:
 well_formed_fwdb l M coh_t fwd <=>
   fwd.fwdb_time <= latest l coh_t M
    /\ fwd.fwdb_view <= fwd.fwdb_time
    /\ (0 < fwd.fwdb_time ==> fwd.fwdb_view < fwd.fwdb_time)
    /\ ?v. mem_read M l fwd.fwdb_time = SOME v
End

Definition well_formed_xclb_def:
  well_formed_xclb M coh xclb <=>
    xclb.xclb_time <= LENGTH M
    /\ !l. mem_is_loc M xclb.xclb_time l
    /\ 0 < xclb.xclb_time
    ==> xclb.xclb_time <= latest l (coh l) M
      /\ xclb.xclb_view <= coh l
End

Definition well_formed_viewenv_def:
  well_formed_viewenv viewenv M =
  !var v. FLOOKUP viewenv var = SOME v
  ==>
  v <= LENGTH M
End

Definition well_formed_def:
  well_formed cid M s <=>
    well_formed_viewenv s.bst_viewenv M
    /\ (!l. s.bst_coh(l) <= LENGTH M)
     /\ s.bst_v_rNew <= LENGTH M
     /\ s.bst_v_rOld <= LENGTH M
     /\ s.bst_v_wNew <= LENGTH M
     /\ s.bst_v_wOld <= LENGTH M
     /\ s.bst_v_CAP <= LENGTH M
     /\ s.bst_v_Rel <= LENGTH M
     /\ (!l. well_formed_fwdb l M (s.bst_coh(l)) (s.bst_fwdb(l)))
     /\ (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M s.bst_coh xclb)
     /\ EVERY (λt. t <= LENGTH M) s.bst_prom
     /\ EVERY ($< 0) s.bst_prom
     /\ ALL_DISTINCT s.bst_prom
     /\ (!t msg.
           (oEL t M = SOME msg
            /\ msg.cid = cid
            /\ s.bst_coh(msg.loc) < t)
           ==>
           MEM (SUC t) s.bst_prom)
End

Definition well_formed_cores_def:
  well_formed_cores cores M <=>
    !cid p s. FLOOKUP cores cid = SOME $ Core cid p s
      ==> well_formed cid M s
End

Theorem latest_bound:
!l t M.
  latest l t M <= t
Proof
  Induct_on ‘t’ >> fs[latest_def]
  >> rpt strip_tac
  >> ‘latest l t M <= t’ by fs[]
  >> Cases_on ‘oEL t M’
  >> Cases_on ‘l = x.loc’
  >> fs[]
QED

Theorem latest_exact:
!l t M msg.
  mem_get M l t = SOME msg
  ==>
  latest l t M = t
Proof
  Cases_on ‘t’
  >> rpt strip_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL n M’
  >- fs[mem_get_def]
  >> ‘x = msg’ by fs[mem_get_def]
  >> ‘l = msg.loc’ by (drule mem_get_SOME >> fs[])
  >> gvs[]
QED

Theorem latest_exact':
!t l M msg.
  mem_read M l t = SOME msg
  ==>
  latest l t M = t
Proof
  Cases >> rw[mem_read_def]
  >> fs[AllCaseEqs()]
  >> drule_then irule latest_exact
QED

Theorem latest_sound:
  !l t M. ?msg.
            mem_get M l (latest l t M) = SOME msg
            /\ msg.loc = l
Proof
  Induct_on ‘t’ >- fs[latest_def, mem_get_def, mem_default_def]
  >> rpt strip_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL t M’
  >> fs[]
  >> Cases_on ‘l = x.loc’ >- fs[mem_get_def]
  >> fs[]
QED

Theorem latest_is_latest:
  !l t M t' msg.
    latest l t M <= t' /\ t' <= t
    /\ mem_get M l t' = SOME msg
    ==>
    t' = latest l t M
Proof
  Induct_on ‘t’ >- fs[latest_def]
  >> rpt strip_tac
  >> qspecl_then [‘l’, ‘SUC t’, ‘M’] assume_tac latest_sound
  >> Cases_on ‘t' = SUC t’ >- fs[latest_exact]
  >> ‘t' <= t’ by decide_tac
  >> fs[latest_def]
  >> Cases_on ‘oEL t M’
  >> Cases_on ‘l = x.loc’
  >> fs[]
QED

Theorem latest_monotonicity:
!l M t1 t2.
  t1 <= t2 ==> latest l t1 M <= latest l t2 M
Proof
  rpt strip_tac
  >> ‘?msg.mem_get M l (latest l t2 M) = SOME msg /\ msg.loc = l’
    by fs[latest_sound]
  >> ‘latest l t1 M <= t1’ by fs[latest_bound]
  >> ‘latest l t2 M <= t2’ by fs[latest_bound]
  >> Cases_on ‘t1 <= latest l t2 M’
  >| [fs[]
      ,
      ‘latest l t2 M < t1’ by decide_tac
      >> ‘?msg.mem_get M l (latest l t1 M) = SOME msg /\ msg.loc = l’
        by fs[latest_sound]
      >> spose_not_then assume_tac
      >> ‘latest l t2 M <= latest l t1 M’ by decide_tac
      >> ‘latest l t1 M <= t2’ by decide_tac
      >> ‘latest l t1 M = latest l t2 M’
         by (irule latest_is_latest >> fs[])
      >> fs[]]
QED

Theorem latest_spec:
  !l t M l1.
    (l1 = latest l t M)
    ==>
    (?msg.
      mem_get M l l1 = SOME msg
      /\ msg.loc = l
      /\
      !t'. l1 < t' /\ t' <= t
           ==>
           mem_get M l t' = NONE)
Proof
  rpt strip_tac
  >> qspecl_then [‘l’, ‘t’, ‘M’] assume_tac latest_sound
  >> fs[]
  >> rpt strip_tac
  >> spose_not_then assume_tac
  >> Cases_on ‘mem_get M l t'’ >- fs[]
  >> ‘latest l t' M = t'’ by fs[latest_exact]
  >> ‘latest l t' M <= latest l t M’ by fs[latest_monotonicity]
  >> rw[]
QED

Theorem latest_idempotency:
  !l t M.
    latest l (latest l t M) M = latest l t M
Proof
  rpt strip_tac
  >> ‘?msg. mem_get M l (latest l t M) = SOME msg /\ msg.loc = l’
    by fs[latest_sound]
  >> fs[latest_exact]
QED

Theorem latest_max:
!l M t1 t2.
   latest l t1 M <= latest l (MAX t1 t2) M
   /\ latest l t2 M <= latest l (MAX t1 t2) M
Proof
  fs[latest_monotonicity]
QED

Theorem latest_APPEND:
  !t l M M'. t <= LENGTH M
  ==> latest l t (M ++ M') = latest l t M
Proof
  Induct >> rw[latest_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND1]
QED

Theorem clstep_preserves_wf_fwdb:
  !p cid s M prom s'.
  (!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l))
  /\ clstep p cid s M prom s'
  ==>
  (!l. well_formed_fwdb l M (s'.bst_coh l) (s'.bst_fwdb l))
Proof
  rpt strip_tac
  >> fs[clstep_cases]
  >> fs[well_formed_fwdb_def, latest_def]
  >~ [`BMCStmt_Load`]
  >- (
    Cases_on ‘l = l'’ >> fs[]
    >> ‘(s.bst_fwdb l').fwdb_time ≤ latest l' (s.bst_coh l') M’ by fs[]
    >> suff_tac “latest l' (s.bst_coh l') M <=
                latest l'
                        (MAX (s.bst_coh l')
                        (MAX
                          (MAX
                          (MAX (MAX v_addr s.bst_v_rNew)
                            (if acq ∧ rel then s.bst_v_Rel else 0))
                          (if acq ∧ rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                          (mem_read_view (s.bst_fwdb l') t))) M” >- fs[]
    >> fs[latest_max]
  )
  >~ [`BMCStmt_Store`]
  >- (
    Cases_on ‘l = l'’ >> fs[combinTheory.APPLY_UPDATE_THM]
    >> drule_then (assume_tac o GSYM) latest_exact
    >> ‘mem_read M l' v_post = SOME v’ by fs[mem_read_def]
    >> ‘latest l' v_post M <= latest l' v_post M’ suffices_by fs[]
    >> fs[latest_max]
  )
  >~ [`BMCStmt_Amo`]
  >- (
    Cases_on ‘l = l'’
    >- (
      EVAL_TAC
      >> ‘mem_read M l t_w = SOME v_w’ by fs[mem_read_def]
      >> fs[]
      >> ‘t_w = latest l t_w M’  by fs[latest_exact]
      >> ‘latest l' t_w M <= latest l' t_w M’
         suffices_by gvs[]
      >> fs[latest_max]
    )
    >> EVAL_TAC
    >> fs[]
    >> ‘?v.mem_read M l (s.bst_fwdb l).fwdb_time = SOME v’ by fs[]
    >> qexists_tac ‘v’
    >> ‘?m. mem_get M l (s.bst_fwdb l).fwdb_time = SOME m /\ m.val = v’ by fs[mem_get_mem_read]
    >> fs[]
  )
  >~ [`BStmt_CJmp`]
  >- fs[bir_exec_stmt_cjmp_mc_invar]
  >~ [`bmc_exec_general_stmt`]
  >- drule_then (fs o single) bmc_exec_general_stmt_mc_invar
QED

Theorem well_formed_fwdb_coh:
  !l M s. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l)
  ==> (s.bst_fwdb l).fwdb_time <= s.bst_coh l
Proof
  rw[well_formed_fwdb_def]
  >> irule arithmeticTheory.LESS_EQ_TRANS
  >> irule_at Any latest_bound
  >> goal_assum drule
QED

Theorem well_formed_xclb_bst_coh_update:
  !M s xclb v_post l.
    well_formed_xclb M s.bst_coh xclb
    /\ s.bst_coh l < v_post
    ==> well_formed_xclb M s.bst_coh(|l |-> v_post|) xclb
Proof
  rw[well_formed_xclb_def,combinTheory.APPLY_UPDATE_THM]
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> IF_CASES_TAC
  >> gvs[]
  >> irule arithmeticTheory.LESS_EQ_TRANS
  >> goal_assum drule
  >> fs[latest_monotonicity]
QED

Theorem bir_eval_view_of_exp_wf:
!a_e env viewenv M v_addr.
 well_formed_viewenv viewenv M
 /\ v_addr = bir_eval_view_of_exp a_e viewenv
 ==>
 v_addr <= LENGTH M
Proof
  fs[well_formed_viewenv_def]
  >> Induct_on ‘a_e’
  >> fs[bir_eval_view_of_exp_def]
  >> rpt strip_tac
  >- (Cases_on ‘FLOOKUP viewenv b’ >- fs[]
      >> first_assum drule >> fs[])
  >> first_assum drule
  >> last_assum drule >> fs[]
QED

Theorem mem_read_view_wf_fwdb:
!l M coh_t fwd t.
well_formed_fwdb l M coh_t fwd
/\ t <= LENGTH M
==>
mem_read_view fwd t <= LENGTH M
Proof
  rpt strip_tac
  >> fs[mem_read_view_def, well_formed_fwdb_def]
  >> CASE_TAC
  >> gvs[]
QED

Theorem bir_eval_view_of_exp_bound:
  !a_e s M.
    well_formed_viewenv s.bst_viewenv M
    ==>
    (bir_eval_view_of_exp a_e s.bst_viewenv) <= LENGTH M
Proof
  metis_tac[bir_eval_view_of_exp_wf]
QED

Theorem well_formed_viewenv_UPDATE:
  !s M v_val var.
  well_formed_viewenv s.bst_viewenv M
  /\ v_val <= LENGTH M
  ==> well_formed_viewenv (s.bst_viewenv |+ (var,v_val)) M
Proof
  rw[well_formed_viewenv_def,FLOOKUP_UPDATE]
  >> BasicProvers.FULL_CASE_TAC
  >> fs[] >> res_tac
QED

Theorem bir_eval_exp_view_bound:
  !l a_e s M v_addr.
    well_formed_viewenv s.bst_viewenv M
    /\ (SOME l, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv
    ==>
    v_addr <= LENGTH M
Proof
  fs[bir_eval_exp_view_def, bir_eval_view_of_exp_bound]
QED

Theorem clstep_preserves_wf_xclb:
  !p cid s M prom s'.
    (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M s.bst_coh xclb)
    /\ (!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l))
    /\ (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M s.bst_coh xclb)
    /\ clstep p cid s M prom s'
    ==> (!xclb. s'.bst_xclb = SOME xclb ==> well_formed_xclb M s'.bst_coh xclb)
Proof
  rw[clstep_cases] >> fs[]
  >~ [`BStmt_CJmp`]
  >- fs[bir_exec_stmt_cjmp_mc_invar]
  >~ [`bmc_exec_general_stmt`]
  >- drule_then (fs o single) bmc_exec_general_stmt_mc_invar
  >~ [`BMCStmt_Load`]
  >- (
    qmatch_asmsub_abbrev_tac `<|xclb_time:=_;xclb_view:=v_post|>`
    >> Cases_on `xcl` >> gvs[]
    >~ [`SOME (_:xclb_t)`]
    >- (
      imp_res_tac mem_read_LENGTH
      >> simp[well_formed_xclb_def]
      >> rpt gen_tac >> strip_tac
      >> drule_all_then (fs o single) mem_read_mem_is_loc
      >> qmatch_asmsub_rename_tac `mem_is_loc M t l`
      >> first_x_assum $ qspec_then `l` strip_assume_tac
      >> Cases_on `(s.bst_fwdb l).fwdb_time = t /\ ~(s.bst_fwdb l).fwdb_xcl`
      >- (
        irule arithmeticTheory.LESS_EQ_TRANS
        >> gvs[well_formed_fwdb_def]
        >> goal_assum drule
        >> fs[latest_max]
      )
      >> rev_drule_then (ONCE_REWRITE_TAC o single o GSYM) latest_exact'
      >> irule latest_monotonicity
      >> qunabbrev_tac `v_post`
      >> simp[arithmeticTheory.MAX_DEF,mem_read_view_def]
    )
    >> fs[well_formed_xclb_def]
    >> rpt gen_tac >> strip_tac
    >> first_x_assum $ drule_all_then strip_assume_tac
    >> qmatch_goalsub_abbrev_tac `COND cond' _ _`
    >> Cases_on `cond'` >> gvs[]
    >> irule arithmeticTheory.LESS_EQ_TRANS
    >> goal_assum drule
    >> fs[latest_max]
  )
  >~ [`BMCStmt_Store`]
  >- (rpt strip_tac >> fs[well_formed_xclb_bst_coh_update])
  >~ [`BMCStmt_Amo`]
  >- (rpt strip_tac >> fs[well_formed_xclb_bst_coh_update])
QED

Theorem clstep_preserves_wf:
!p cid s M prom s'.
  well_formed cid M s
  /\ clstep p cid s M prom s'
==>
  well_formed cid M s'
Proof
  rpt strip_tac
  >> fs[well_formed_def]
  >> drule_at_then (Pat `clstep _ _ _ _ _`) assume_tac clstep_preserves_wf_fwdb
  >> drule_at (Pat `clstep _ _ _ _ _`) clstep_preserves_wf_xclb
  >> gs[]
  >> disch_then kall_tac (* removes wf_xclb *)
  >> fs[clstep_cases]
  >~ [`BMCStmt_Load`]
  >- (
    ‘v_addr <= LENGTH M’
     by (fs[bir_eval_exp_view_def]
         >> drule bir_eval_view_of_exp_wf
         >> fs[])
    >> fs[well_formed_viewenv_def]
    >> irule_at Any mem_read_view_wf_fwdb
    >> map_every qexists_tac [‘l’,‘s.bst_coh l’]
    >> gvs[]
    >> imp_res_tac mem_read_LENGTH
    >> Cases_on ‘acq /\ rel’
    >- (
      rw[]
      >> Cases_on ‘var' = var’
      >> gvs[FLOOKUP_DEF, FLOOKUP_UPDATE]
      >> irule mem_read_view_wf_fwdb
      >> fs[]
      >> qexists_tac ‘s.bst_coh l’ >> qexists_tac ‘l’
      >> fs[]
    )
    >> asm_rewrite_tac[]
    >> conj_tac
    >~ [`FLOOKUP (_ |+ _)`]
    >- (
      simp[FLOOKUP_UPDATE]
      >> ntac 2 $ first_x_assum $ qspec_then `l` mp_tac
      >> asm_rewrite_tac[]
      >> ntac 2 strip_tac
      >> rpt gen_tac
      >> BasicProvers.FULL_CASE_TAC
      >> gvs[]
      >> rw[mem_read_view_def]
      >> fs[well_formed_fwdb_def]
    )
    >> rw[mem_read_view_def]
    >> ntac 2 $ first_x_assum $ qspec_then `l` mp_tac
    >> gvs[well_formed_fwdb_def]
  )
  >~ [`BMCStmt_Store`,`xclfail_update_env`]
  >- (
    gvs[xclfail_update_env_def,xclfail_update_viewenv_def,AllCaseEqs(),well_formed_viewenv_def,FLOOKUP_UPDATE]
    >> rw[] >> gvs[] >> metis_tac[]
  )
  >~ [`BMCStmt_Store`]
  >- (
    conj_tac
    >- (
      gvs[well_formed_viewenv_def,fulfil_update_viewenv_def,AllCaseEqs(),FLOOKUP_UPDATE,listTheory.EVERY_MEM]
      >> rw[] >> gvs[] >> metis_tac[]
    )
    >> conj_tac
    >- (
      gen_tac
      >> fs[listTheory.EVERY_MEM]
      >> first_assum drule
      >> first_assum $ qspec_then `l` mp_tac
      >> first_x_assum $ qspec_then `l'` mp_tac
      >> first_assum $ qspec_then `l` mp_tac
      >> first_x_assum $ qspec_then `l'` mp_tac
      >> fs[well_formed_fwdb_def,combinTheory.APPLY_UPDATE_THM]
      >> rpt strip_tac
      >> rw[]
    )
    >> conj_tac
    >- (fs[listTheory.EVERY_MEM] >> first_assum drule >> rw[well_formed_fwdb_def])
    >> conj_tac
    >- (fs[listTheory.EVERY_MEM] >> first_assum drule >> rw[well_formed_fwdb_def])
    >> conj_asm1_tac
    >- (
      drule_then rev_drule bir_eval_exp_view_bound
      >> fs[listTheory.EVERY_MEM]
    )
    >> conj_tac
    >- (fs[listTheory.EVERY_MEM] >> first_assum drule >> rw[])
    >> conj_tac >- rw[listTheory.MEM_FILTER]
    >> conj_tac >- fs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- fs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- fs[listTheory.FILTER_ALL_DISTINCT]
    >> gvs[combinTheory.APPLY_UPDATE_THM]
    >> rw[]
    >> first_x_assum drule
    >> fs[]
    >> rw[listTheory.MEM_FILTER]
    >> spose_not_then assume_tac
    >> Cases_on `v_post`
    >> gs[mem_read_def,mem_get_def]
  )
  >~ [`BMCStmt_Amo`]
  >- (
    irule_at Any mem_read_view_wf_fwdb
    >> map_every qexists_tac [‘l’,‘s.bst_coh l’]
    >> drule_then (irule_at Any) well_formed_viewenv_UPDATE
    >> imp_res_tac mem_get_LENGTH
    >> drule_then (rev_drule_then assume_tac) bir_eval_exp_view_bound
    >> imp_res_tac mem_read_LENGTH
    >> asm_rewrite_tac[]
    >> conj_asm1_tac
    >- (
      rw[] >> gvs[]
      >> irule arithmeticTheory.LESS_EQ_TRANS
      >> irule_at Any arithmeticTheory.LESS_IMP_LESS_OR_EQ
      >> goal_assum drule
      >> fs[]
    )
    >> rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
    >> gs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> first_x_assum drule
    >> gvs[]
    >> spose_not_then assume_tac
    >> Cases_on `t_w`
    >> gs[mem_read_def,mem_get_def]
  )
  >~ [`BMCStmt_Fence`]
  >- rw[]
  >~ [`BStmt_CJmp`]
  >- (
    drule_then (rev_drule_then assume_tac) bir_eval_exp_view_bound
    >> fs[bir_exec_stmt_cjmp_mc_invar]
  )
  >~ [`bmc_exec_general_stmt`]
  >- drule_then (fs o single) bmc_exec_general_stmt_mc_invar
  >~ [`BMCStmt_Assign`]
  >- (
    drule_then irule well_formed_viewenv_UPDATE
    >> drule_all bir_eval_exp_view_bound
    >> fs[]
  )
QED

Theorem well_formed_append:
  !cid M s msg. well_formed cid M s
  ==> well_formed_viewenv s.bst_viewenv (M ++ [msg]) /\
    (!l. s.bst_coh l <= LENGTH M + 1) /\
    (!l. well_formed_fwdb l (M ++ [msg]) (s.bst_coh l) (s.bst_fwdb l)) /\
    (!xclb.
        s.bst_xclb = SOME xclb ==>
        well_formed_xclb (M ++ [msg]) s.bst_coh xclb) /\
    EVERY (λt. t <= LENGTH M + 1) s.bst_prom
Proof
  rpt gen_tac >> strip_tac
  >> fs[well_formed_def]
  >> conj_tac
  >- (
    fs[well_formed_viewenv_def] >> rpt strip_tac
    >> first_x_assum drule >> fs[]
  )
  >> conj_tac
  >- (
    qx_gen_tac `l`
    >> last_x_assum $ qspec_then `l` mp_tac
    >> fs[]
  )
  >> conj_tac
  >- (
    qx_gen_tac `l`
    >> qpat_x_assum `!l. well_formed_fwdb _ _ _ _` $ qspec_then `l` assume_tac
    >> fs[well_formed_fwdb_def]
    >> imp_res_tac mem_read_LENGTH
    >> last_x_assum $ qspec_then `l` assume_tac
    >> fs[mem_read_append,latest_APPEND]
  )
  >> conj_tac
  >- (
    fs[well_formed_xclb_def,PULL_FORALL]
    >> gen_tac >> qx_gen_tac `l` >> strip_tac
    >> `xclb.xclb_time <= LENGTH M` by fs[well_formed_xclb_def]
    >> fs[] >> strip_tac
    >> drule_then (fs o single) mem_is_loc_append
    >> first_x_assum $ drule_then strip_assume_tac
    >> last_x_assum $ qspec_then `l` assume_tac
    >> fs[latest_APPEND]
  )
  >> rev_drule_at_then (Pat `EVERY`) irule listTheory.EVERY_MEM_MONO
  >> fs[]
QED

Theorem well_formed_promise_other:
  !cid M s msg. well_formed cid M s
  /\ msg.cid <> cid
  ==> well_formed cid (M ++ [msg]) s
Proof
  rpt strip_tac
  >> simp[well_formed_def]
  >> drule_then (fs o single) well_formed_append
  >> fs[well_formed_def]
  >> qx_gen_tac `t` >> rw[]
  >> Cases_on `t = LENGTH M`
  >- gs[listTheory.oEL_THM,rich_listTheory.EL_APPEND2]
  >> qmatch_asmsub_rename_tac `oEL t (M ++ _) = SOME msg'`
  >> `oEL t M = SOME msg'` by (
    gs[listTheory.oEL_THM,arithmeticTheory.NOT_NUM_EQ,rich_listTheory.EL_APPEND1]
  )
  >> first_x_assum drule
  >> fs[]
QED

Theorem well_formed_promise_self:
  !cid M s msg. well_formed cid M s
  /\ cid = msg.cid
  ==> well_formed cid (M ++ [msg])
        (s with bst_prom updated_by (λpr. pr ++ [LENGTH M + 1]))
Proof
  rpt strip_tac
  >> simp[well_formed_def]
  >> drule_then (fs o single) well_formed_append
  >> fs[well_formed_def]
  >> conj_tac
  >- (
    rw[listTheory.ALL_DISTINCT_APPEND]
    >> spose_not_then assume_tac
    >> fs[listTheory.EVERY_MEM]
    >> res_tac
    >> fs[]
  )
  >> qx_gen_tac `t` >> rw[]
  >> Cases_on `t = LENGTH M`
  >> gs[]
  >> qmatch_asmsub_rename_tac `oEL t (M ++ _) = SOME msg'`
  >> `oEL t M = SOME msg'` by (
    gs[listTheory.oEL_THM,arithmeticTheory.NOT_NUM_EQ,rich_listTheory.EL_APPEND1]
  )
  >> first_x_assum drule
  >> fs[]
QED

Theorem cstep_preserves_wf:
!p cid s M prom s' M'.
  well_formed cid M s
  /\ cstep p cid s M prom s' M'
  ==> well_formed cid M' s'
Proof
  rw[cstep_cases]
  >- (drule_all_then irule clstep_preserves_wf)
  >> fs[well_formed_promise_self]
QED

Theorem cstep_seq_preserves_wf:
!p cid s M s' M'.
  well_formed cid M s
  /\ cstep_seq p cid (s,M) (s',M')
  ==> well_formed cid M' s'
Proof
  rw[cstep_seq_cases]
  >> TRY $ drule_all_then assume_tac cstep_preserves_wf
  >> drule_all clstep_preserves_wf
  >> fs[]
QED

Theorem cstep_seq_rtc_preserves_wf:
  !p cid s M s' M'.
  well_formed cid M s
  /\ cstep_seq_rtc p cid (s,M) (s',M')
  ==> well_formed cid M' s'
Proof
  qsuff_tac `
    !p cid sM sM'.
    cstep_seq_rtc p cid sM sM'
    ==> well_formed cid (SND sM) (FST sM)
    ==> well_formed cid (SND sM') (FST sM')
  `
  >- (
    fs[pairTheory.FORALL_PROD,pairTheory.LAMBDA_PROD,pairTheory.ELIM_UNCURRY,AND_IMP_INTRO]
    >> metis_tac[]
  )
  >> ntac 2 gen_tac
  >> REWRITE_TAC[cstep_seq_rtc_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[pairTheory.FORALL_PROD,pairTheory.LAMBDA_PROD,pairTheory.ELIM_UNCURRY]
  >> rpt strip_tac
  >> drule_all_then assume_tac cstep_seq_preserves_wf
  >> fs[]
QED

Theorem parstep_preserves_wf:
!cid cores M cores' M'.
  well_formed_cores cores M
  /\ parstep cid cores M cores' M'
  ==> well_formed_cores cores' M'
Proof
  rw[parstep_cases]
  >> fs[well_formed_cores_def,FLOOKUP_UPDATE]
  >> rw[]
  >- (
    first_x_assum $ drule_then assume_tac
    >> drule_all_then irule cstep_preserves_wf
  )
  >> first_x_assum $ drule_then assume_tac
  >> fs[cstep_cases,well_formed_promise_other]
QED

(* init state *)

Theorem wf_init_state:
  !cid p. well_formed cid [] $ bmc_state_init p
Proof
  fs[bir_init_progTheory.bmc_state_init_def,well_formed_def,well_formed_viewenv_def,well_formed_fwdb_def,mem_read_def,listTheory.oEL_THM,mem_get_def]
QED

Definition init_def:
  init cores =
    !cid p s. FLOOKUP cores cid = SOME $ Core cid p s
    ==> s = bmc_state_init p
End

Theorem wf_init:
  !cores. init cores ==> well_formed_cores cores []
Proof
  rw[well_formed_cores_def,init_def]
  >> first_x_assum $ drule_then $ fs o single
  >> fs[wf_init_state]
QED

val _ = export_theory ();
