(*
 Well-formedness and its preservation for promising multicore semantics
*)

open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;
open bir_programTheory;
open bir_valuesTheory;
open bir_expTheory;
open finite_mapTheory;
open bir_init_progTheory;

val _ = new_theory "bir_promising_wf";

(* move to promising *)

Theorem mem_get_mem_is_loc:
  !t M l l' msg.
  mem_get M l t = SOME msg /\ mem_is_loc M t l' /\ 0 < t ==> l = l'
Proof
  Cases >> csimp[mem_get_def,mem_is_loc_def,listTheory.oEL_THM,AllCaseEqs()]
QED

Theorem mem_get_eq:
  !t M l l' msg msg'.
  mem_get M l t = SOME msg
  /\ mem_get M l' t = SOME msg'
  /\ 0 < t
  ==> l = l' /\ msg = msg'
Proof
  Cases >> fs[mem_get_def,AllCaseEqs(),listTheory.oEL_THM]
QED

Theorem bmc_exec_general_stmt_exists:
  !stm p s s'.
  bmc_exec_general_stmt p stm s = SOME s'
  <=> ?e e'.
  stm = BStmtB $ BMCStmt_Assert e /\ bir_exec_stmt_assert e s = s'
  \/ stm = BStmtB $ BMCStmt_Assume e' /\ bir_exec_stmt_assume e' s = s'
  \/ (?e. stm = BStmtE $ BStmt_Halt e /\ bir_exec_stmt_halt e s = s')
  \/ ?e. stm = BStmtE $ BStmt_Jmp e /\ bir_exec_stmt_jmp p e s = s'
Proof
  Cases
  >> rw[bmc_exec_general_stmt_def,AllCaseEqs(),EQ_IMP_THM]
  >> fs[bir_exec_stmtB_def,bir_exec_stmtE_def]
QED

Theorem bir_exec_stmt_jmp_bst_eq:
  !s p lbl.
     (bir_exec_stmt_jmp p lbl s).bst_environ    = s.bst_environ
  /\ (bir_exec_stmt_jmp p lbl s).bst_viewenv    = s.bst_viewenv
  /\ (!l. (bir_exec_stmt_jmp p lbl s).bst_coh l = s.bst_coh l)
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_rNew     = s.bst_v_rNew
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_rOld     = s.bst_v_rOld
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_wNew     = s.bst_v_wNew
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_wOld     = s.bst_v_wOld
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_CAP      = s.bst_v_CAP
  /\ (bir_exec_stmt_jmp p lbl s).bst_v_Rel      = s.bst_v_Rel
  /\ (bir_exec_stmt_jmp p lbl s).bst_prom       = s.bst_prom
  /\ (bir_exec_stmt_jmp p lbl s).bst_fwdb       = s.bst_fwdb
  /\ (bir_exec_stmt_jmp p lbl s).bst_xclb       = s.bst_xclb
Proof
  rw[bir_exec_stmt_jmp_def]
  >> CASE_TAC
  >> fs[bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> CASE_TAC
  >> fs[]
QED

(* return the first element from list 'M' satisfying P given index *)
Definition latestP_def:
  latestP P 0 M = 0
  /\ latestP P (SUC t) M =
  case oEL t M of
    SOME msg =>
      if P msg then SUC t else latestP P t M
  | _ => latestP P t M
End

Definition latest_def:
  latest l = latestP (λmsg. l = msg.loc)
End

Definition latest_core_def:
  latest_core l cid = latestP (λmsg. msg.loc = l /\ msg.cid = cid)
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
     /\ EVERY (λt. mem_is_cid M t cid) s.bst_prom
     /\ ALL_DISTINCT s.bst_prom
     /\ (!t msg.
           (oEL t M = SOME msg
            /\ msg.cid = cid
            /\ s.bst_coh(msg.loc) < t)
           ==>
           MEM (SUC t) s.bst_prom)
     /\ (!t l msg.
      mem_get M l t = SOME msg /\ ~MEM t s.bst_prom /\ msg.cid = cid
      ==> t <= s.bst_coh l)
End

(* well-formed external block relation *)
Definition wf_ext_fwdb_def:
  wf_ext_fwdb p cid s M =
    !R s' prom. bir_get_current_statement p s.bst_pc = SOME $ BSExt R
    /\ R (s,(M,prom)) s'
    /\ (!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l))
    ==> (!l. well_formed_fwdb l M (s'.bst_coh l) (s'.bst_fwdb l))
End

Definition wf_ext_xclb_def:
  wf_ext_xclb p cid s M =
    !R s' prom. bir_get_current_statement p s.bst_pc = SOME $ BSExt R
    /\ R (s,(M,prom)) s'
    /\ (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M s.bst_coh xclb)
    ==> (!xclb. s'.bst_xclb = SOME xclb ==> well_formed_xclb M s'.bst_coh xclb)
End

Definition wf_ext_def:
  wf_ext p cid s M =
    !R s' prom. bir_get_current_statement p s.bst_pc = SOME $ BSExt R
    /\ R (s,(M,prom)) s'
    /\ well_formed cid M s ==> well_formed cid M s'
End

Definition wf_ext_p_def:
  wf_ext_p p cid = !M s. wf_ext p cid s M
End

Definition well_formed_cores_def:
  well_formed_cores cores M <=>
    !cid p s. FLOOKUP cores cid = SOME $ Core cid p s
      ==> well_formed cid M s
End

Definition well_formed_ext_cores_def:
  well_formed_ext_cores cores <=>
    !cid p s. FLOOKUP cores cid = SOME $ Core cid p s
      ==> wf_ext_p p cid
End

Theorem latestP_bound:
  !P t M. latestP P t M <= t
Proof
  Induct_on ‘t’ >> fs[latestP_def]
  >> rpt strip_tac
  >> ‘latestP P t M <= t’ by fs[]
  >> Cases_on ‘oEL t M’
  >> Cases_on ‘P x’
  >> fs[]
QED

Theorem latest_bound:
  !l t M. latest l t M <= t
Proof
  fs[latest_def,latestP_bound]
QED

Theorem latestP_zero:
  !P M. latestP P 0 M = 0
Proof
  fs[latestP_def]
QED

Definition mem_getP_def:
  mem_getP P default M 0 = SOME default /\
  mem_getP P default M (SUC t) =
    case oEL t M of
      NONE => NONE
    | SOME m => if P m then SOME m else NONE
End

Theorem mem_getP_mem_get:
  !t M l. mem_getP (λx. l = x.loc) (mem_default l) M t = mem_get M l t
Proof
  Cases >> rw[mem_get_def,mem_getP_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem latestP_exact:
!P t M msg default.
  mem_getP P default M t = SOME msg
  ==> latestP P t M = t
Proof
  Cases_on ‘t’
  >> rpt strip_tac
  >> fs[latestP_def,mem_getP_def]
  >> rpt CASE_TAC
  >> fs[]
QED

Theorem latest_exact:
!l t M msg.
  mem_get M l t = SOME msg
  ==> latest l t M = t
Proof
  rpt strip_tac
  >> fs[latest_def,GSYM mem_getP_mem_get]
  >> drule_then irule latestP_exact
QED

Theorem mem_get_latestP_exact:
  !t M l m cid.
    mem_get M l t = SOME m
    /\ m.loc = l /\ m.cid = cid
    ==> latestP (λmsg. msg.loc = l ∧ msg.cid = cid) t M = t
Proof
  Cases
  >> rpt strip_tac
  >> irule latestP_exact
  >> fs[GSYM mem_getP_mem_get,mem_getP_def]
  >> qmatch_asmsub_rename_tac `oEL n M`
  >> Cases_on `oEL n M`
  >> gs[]
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

Theorem latestP_sound:
  !default P t M. P default ==> ?msg.
            mem_getP P default M (latestP P t M) = SOME msg
            /\ P msg
Proof
  Induct_on ‘t’ >- fs[latestP_def,mem_getP_def]
  >> rpt strip_tac
  >> fs[latestP_def]
  >> CASE_TAC
  >> fs[]
  >> qmatch_asmsub_abbrev_tac `oEL t M = SOME x`
  >> Cases_on ‘P x’ >- fs[mem_getP_def]
  >> fs[]
QED

Theorem latest_sound:
  !l t M. ?msg.
            mem_get M l (latest l t M) = SOME msg
            /\ msg.loc = l
Proof
  rw[GSYM mem_getP_mem_get,latestP_sound,latest_def]
  >> qmatch_goalsub_abbrev_tac `mem_getP P (mem_default l) M (latestP _ t M)`
  >> qspecl_then [`mem_default l`,`P`,`t`,`M`] mp_tac latestP_sound
  >> impl_tac >- fs[Abbr`P`,mem_default_def]
  >> fs[]
QED

Theorem latestP_is_latestP:
  !t P default M t' msg.
    latestP P t M <= t' /\ t' <= t
    /\ mem_getP P default M t' = SOME msg
    /\ P default
    ==> t' = latestP P t M
Proof
  Induct_on ‘t’ >- fs[latestP_def]
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `mem_getP P default M t'`
  >> qspecl_then [`default`,‘P’, ‘SUC t’, ‘M’] assume_tac latestP_sound
  >> gs[]
  >> Cases_on ‘t' = SUC t’
  >- (imp_res_tac latestP_exact >> gvs[])
  >> ‘t' <= t’ by decide_tac
  >> fs[latestP_def]
  >> BasicProvers.every_case_tac
  >> gs[]
  >> first_x_assum drule_all
  >> fs[]
QED

Theorem latest_is_latest:
  !l t M t' msg.
    latest l t M <= t' /\ t' <= t
    /\ mem_get M l t' = SOME msg
    ==>
    t' = latest l t M
Proof
  rpt strip_tac
  >> fs[latest_def,GSYM mem_getP_mem_get]
  >> drule latestP_is_latestP
  >> rpt $ disch_then drule
  >> fs[mem_default_def]
QED

Theorem latestP_monotonicity:
  !P M t1 t2. t1 <= t2 ==> latestP P t1 M <= latestP P t2 M
Proof
  Induct_on `t2`
  >> rw[latestP_def]
  >> CASE_TAC
  >> fs[]
  >- (
    dxrule_then strip_assume_tac $ iffLR arithmeticTheory.LESS_OR_EQ
    >> fs[]
    >> simp[latestP_def]
  )
  >> rw[]
  >- (
    irule arithmeticTheory.LESS_EQ_TRANS
    >> irule_at Any latestP_bound
    >> fs[]
  )
  >> dxrule_then strip_assume_tac $ iffLR arithmeticTheory.LESS_OR_EQ
  >> fs[]
  >> simp[latestP_def]
QED

Theorem latest_monotonicity:
  !l M t1 t2.
    t1 <= t2 ==> latest l t1 M <= latest l t2 M
Proof
  fs[latest_def,latestP_monotonicity]
QED

Theorem latestP_spec:
  !P default t M l1.
    l1 = latestP P t M
    /\ P default
    ==>
    ?msg.
      mem_getP P default M l1 = SOME msg
      /\ P msg
      /\
      !t'. l1 < t' /\ t' <= t
           ==>
           mem_getP P default M t' = NONE
Proof
  rpt strip_tac
  >> qspecl_then [`default`,‘P’, ‘t’, ‘M’] assume_tac latestP_sound
  >> spose_not_then strip_assume_tac
  >> gs[]
  >> Cases_on ‘mem_getP P default M t'’ >- fs[]
  >> qpat_x_assum `_:num < _` mp_tac
  >> fs[arithmeticTheory.NOT_LESS]
  >> drule_then mp_tac latestP_exact
  >> disch_then $ PURE_ONCE_REWRITE_TAC o single o GSYM
  >> fs[latestP_monotonicity]
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
  REWRITE_TAC[latest_def,GSYM mem_getP_mem_get]
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `mem_getP P def`
  >> drule_then (qspec_then `def` mp_tac) latestP_spec
  >> impl_tac
  >- fs[Abbr`P`,Abbr`def`,mem_default_def]
  >> fs[]
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

Theorem latestP_max:
!P M t1 t2.
   latestP P t1 M <= latestP P (MAX t1 t2) M
   /\ latestP P t2 M <= latestP P (MAX t1 t2) M
Proof
  rpt strip_tac
  >> irule latestP_monotonicity
  >> fs[arithmeticTheory.MAX_DEF]
QED

Theorem latest_max:
!l M t1 t2.
   latest l t1 M <= latest l (MAX t1 t2) M
   /\ latest l t2 M <= latest l (MAX t1 t2) M
Proof
  fs[latestP_monotonicity,latest_def]
QED

Theorem latestP_APPEND:
  !t P M M'. t <= LENGTH M
  ==> latestP P t (M ++ M') = latestP P t M
Proof
  Induct >> rw[latestP_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND1]
QED

Theorem latest_APPEND:
  !t l M M'. t <= LENGTH M
  ==> latest l t (M ++ M') = latest l t M
Proof
  fs[latest_def,latestP_APPEND]
QED

Theorem latestP_mem_get:
  !P t M m l.
    mem_get M l (latestP P t M) = SOME m /\ 0 < latestP P t M
    /\ (!m. P m ==> m.loc = l) ==> P m
Proof
  Induct_on `t` >> rw[mem_get_def,latestP_def]
  >> BasicProvers.every_case_tac
  >> gs[]
  >~ [`mem_get M l (SUC t) = _`]
  >- gs[mem_get_def]
  >> first_x_assum drule_all
  >> fs[]
QED

Theorem latest_t_latest_is_lowest:
  !t t' to l M.
  latest_t l M t to /\ t <= t' /\ t' <= to ==> latest l t' M = latest l t M
Proof
  ntac 2 gen_tac
  >> Induct_on `t' - t`
  >> rw[]
  >- (dxrule_all arithmeticTheory.LESS_EQUAL_ANTISYM >> fs[])
  >> Cases_on `t'` >> fs[]
  >> CONV_TAC $ LAND_CONV $ ONCE_REWRITE_CONV[latest_def]
  >> ONCE_REWRITE_TAC[cj 2 latestP_def]
  >> fs[GSYM latest_def]
  >> `~mem_is_loc M (SUC n) l` by fs[latest_t_def]
  >> fs[mem_is_loc_def]
  >> BasicProvers.every_case_tac
  >> fs[]
  >> first_x_assum irule
  >> qhdtm_x_assum `latest_t` $ irule_at Any
  >> fs[]
QED

Theorem well_formed_fwdb_time_LEQ_mem:
  !cid M s l. well_formed cid M s ==> (s.bst_fwdb l).fwdb_time <= LENGTH M
Proof
  rw[well_formed_fwdb_def,well_formed_def]
  >> qmatch_goalsub_rename_tac `s.bst_fwdb l`
  >> ntac 2 $ first_x_assum $ qspec_then `l` strip_assume_tac
  >> irule arithmeticTheory.LESS_EQ_TRANS
  >> qpat_x_assum `_.bst_coh _ <= _` $ irule_at Any
  >> irule arithmeticTheory.LESS_EQ_TRANS
  >> qpat_x_assum `_ <= latest _ _ _` $ irule_at Any
  >> fs[latest_bound]
QED

Theorem clstep_preserves_wf_fwdb:
  !p cid s M prom s'.
  (!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l))
  /\ wf_ext_fwdb p cid s M
  /\ clstep p cid s M prom s'
  ==>
  (!l. well_formed_fwdb l M (s'.bst_coh l) (s'.bst_fwdb l))
Proof
  rpt strip_tac
  >> fs[clstep_cases]
  >> fs[well_formed_fwdb_def, bir_state_read_view_updates_def,
    bir_state_fulful_view_updates_def,fence_updates_def]
  >~ [`BMCStmt_Load`]
  >- (
    qmatch_asmsub_abbrev_tac `latest_t l' M t _`
    >> qmatch_goalsub_abbrev_tac `s.bst_fwdb l`
    >> ‘(s.bst_fwdb l').fwdb_time ≤ latest l' (s.bst_coh l') M’ by fs[]
    >> Cases_on ‘l = l'’ >> fs[combinTheory.APPLY_UPDATE_THM]
    >> suff_tac “latest l' (s.bst_coh l') M <=
                latest l'
                        (MAX (s.bst_coh l')
                        (MAX
                          (MAX
                          (MAX (MAX v_addr s.bst_v_rNew)
                            (if acq ∧ rel then s.bst_v_Rel else 0))
                          (if acq ∧ rel then MAX s.bst_v_rOld s.bst_v_wOld else 0))
                          (mem_read_view (s.bst_fwdb l') t))) M”
    >- fs[AC arithmeticTheory.MAX_ASSOC arithmeticTheory.MAX_COMM]
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
      fs[combinTheory.APPLY_UPDATE_THM]
      >> ‘mem_read M l t_w = SOME v_w’ by fs[mem_read_def]
      >> gs[]
      >> ‘t_w = latest l t_w M’  by fs[latest_exact]
      >> gs[]
    )
    >> fs[combinTheory.APPLY_UPDATE_THM]
  )
  >~ [`BStmt_CJmp`]
  >- fs[bir_exec_stmt_cjmp_mc_invar]
  >~ [`bmc_exec_general_stmt`]
  >- (
    drule_then assume_tac bmc_exec_general_stmt_mc_invar
    >> fs[]
  )
  >~ [`BSExt R`]
  >- (
    gvs[wf_ext_fwdb_def,well_formed_fwdb_def,COND_RAND]
    >> first_x_assum drule
    >> fs[]
  )
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

Theorem well_formed_xclb_time_leq_coh:
  !M s l cid.
    well_formed cid M s
    /\ IS_SOME s.bst_xclb
    /\ IS_SOME $ mem_read M l (THE s.bst_xclb).xclb_time
    /\ 0 < (THE s.bst_xclb).xclb_time
    ==> (THE s.bst_xclb).xclb_time <= s.bst_coh l
Proof
  rw[well_formed_def,well_formed_xclb_def,combinTheory.APPLY_UPDATE_THM,optionTheory.IS_SOME_EXISTS,FORALL_AND_THM,IMP_CONJ_THM]
  >> imp_res_tac mem_read_mem_is_loc_imp
  >> irule arithmeticTheory.LESS_EQ_TRANS
  >> irule_at Any latest_bound
  >> first_x_assum $ irule_at Any
  >> gs[]
QED

Theorem well_formed_xclb_bst_coh_update:
  !M s xclb v_post l.
    well_formed_xclb M s.bst_coh xclb
    /\ s.bst_coh l <= v_post
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
    bir_eval_view_of_exp a_e s.bst_viewenv <= LENGTH M
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
    /\ wf_ext_xclb p cid s M
    /\ clstep p cid s M prom s'
    ==> (!xclb. s'.bst_xclb = SOME xclb ==> well_formed_xclb M s'.bst_coh xclb)
Proof
  rw[clstep_cases] >> fs[fence_updates_def]
  >~ [`BStmt_CJmp`]
  >- fs[bir_exec_stmt_cjmp_mc_invar]
  >~ [`bmc_exec_general_stmt`]
  >- (
    drule_then assume_tac bmc_exec_general_stmt_mc_invar
    >> fs[]
  )
  >~ [`BMCStmt_Load`]
  >- (
    fs[bir_state_read_view_updates_def,combinTheory.APPLY_UPDATE_THM]
    >> qmatch_asmsub_abbrev_tac `<|xclb_time:=_;xclb_view:=v_post|>`
    >> Cases_on `xcl` >> gvs[]
    >~ [`SOME (_:xclb_t)`]
    >- (
      imp_res_tac mem_read_LENGTH
      >> simp[well_formed_xclb_def,combinTheory.APPLY_UPDATE_THM]
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
    >> fs[well_formed_xclb_def,combinTheory.APPLY_UPDATE_THM]
    >> rpt gen_tac >> strip_tac
    >> first_x_assum $ drule_all_then strip_assume_tac
    >> qmatch_goalsub_abbrev_tac `COND cond' _ _`
    >> Cases_on `cond'` >> gvs[]
    >> irule arithmeticTheory.LESS_EQ_TRANS
    >> goal_assum drule
    >> fs[latest_max]
  )
  >~ [`BMCStmt_Store`]
  >- (
    rpt strip_tac >>
    fs[well_formed_xclb_bst_coh_update,bir_state_fulful_view_updates_def]
  )
  >~ [`BMCStmt_Amo`]
  >- (rpt strip_tac >> fs[well_formed_xclb_bst_coh_update])
  >~ [`BSExt R`]
  >- (
    gs[wf_ext_xclb_def,COND_RAND]
    >> first_x_assum drule
    >> fs[]
  )
QED

Theorem clstep_preserves_wf:
  !p cid s M prom s'.
  well_formed cid M s
  /\ wf_ext p cid s M
  /\ clstep p cid s M prom s'
==>
  well_formed cid M s'
Proof
  rpt strip_tac
  >> drule_at_then (Pat `clstep`) assume_tac clstep_preserves_wf_fwdb
  >> drule_at (Pat `clstep`) clstep_preserves_wf_xclb
  >> gs[clstep_cases]
  >~ [`BSExt R`]
  >- (
    fs[wf_ext_def,COND_RAND]
    >> rw[]
    >> first_x_assum drule >> fs[]
    >> simp[well_formed_def]
  )
  >> gs[wf_ext_def,wf_ext_fwdb_def,wf_ext_xclb_def,well_formed_def,
    bir_state_fulful_view_updates_def,bir_state_read_view_updates_def,
    combinTheory.APPLY_UPDATE_THM,fence_updates_def,remove_prom_def]
  >~ [`BMCStmt_Load var a_e opt_cast xcl acq rel`]
  >- (
    disch_then kall_tac (* removes wf_xclb *)
    >> qmatch_asmsub_rename_tac
      `(SOME l,v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv`
    >> ‘v_addr <= LENGTH M’
     by (fs[bir_eval_exp_view_def]
         >> drule bir_eval_view_of_exp_wf
         >> fs[])
    >> fs[well_formed_viewenv_def]
    >> irule_at Any mem_read_view_wf_fwdb
    >> map_every qexists_tac [‘l’,‘s.bst_coh l’]
    >> gvs[]
    >> imp_res_tac mem_read_LENGTH
    >> `mem_read_view (s.bst_fwdb l) t ≤ LENGTH M` by (
      irule mem_read_view_wf_fwdb
      >> qpat_x_assum `!l. well_formed_fwdb _ _ (s.bst_coh l) _` $ irule_at Any
      >> fs[]
    )
    >> Cases_on `acq /\ rel`
    >- (rw[] >> gvs[FLOOKUP_DEF, FLOOKUP_UPDATE,AllCaseEqs()])
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
      >> simp[arithmeticTheory.MAX_DEF]
    )
    >> rpt strip_tac
    >> BasicProvers.FULL_CASE_TAC
    >> gns[]
    >> BasicProvers.FULL_CASE_TAC
    >> gns[]
  )
  >~ [`BMCStmt_Store`,`xclfail_update_env`]
  >- (
    gvs[xclfail_update_env_def,xclfail_update_viewenv_def,AllCaseEqs(),well_formed_viewenv_def,FLOOKUP_UPDATE]
    >> rw[] >> gvs[] >> res_tac
  )
  >~ [`BMCStmt_Store`,`fulfil_update_env`]
  >- (
    disch_then kall_tac (* removes wf_xclb *)
    >> conj_tac
    >- (
      gvs[well_formed_viewenv_def,fulfil_update_viewenv_def,AllCaseEqs(),FLOOKUP_UPDATE,listTheory.EVERY_MEM]
      >> rw[] >> gvs[] >> metis_tac[]
    )
    >> conj_tac
    >- (
      gen_tac
      >> qmatch_goalsub_rename_tac `l = l'`
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
    >> conj_tac >- fs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- fs[listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac
    >- (
      gvs[combinTheory.APPLY_UPDATE_THM]
      >> rw[]
      >> first_x_assum drule
      >> fs[]
      >> rw[listTheory.MEM_FILTER]
      >> spose_not_then assume_tac
      >> Cases_on `v_post`
      >> gs[mem_read_def,mem_get_def]
    )
    >> dsimp[listTheory.MEM_FILTER]
    >> drule_then assume_tac mem_get_eq
    >> rw[]
    >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ
    >> irule arithmeticTheory.LESS_EQ_LESS_TRANS
    >> qpat_x_assum `_.bst_coh _ < _` $ irule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Amo`]
  >- (
    disch_then kall_tac (* removes wf_xclb *)
    >> irule_at Any mem_read_view_wf_fwdb
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
    >> conj_tac >- rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac >- rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac >- rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac >- rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac >- gs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- gs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- gs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
    >> conj_tac >- simp[listTheory.FILTER_ALL_DISTINCT]
    >> conj_tac >- (
      rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER,listTheory.FILTER_ALL_DISTINCT]
      >> gs[listTheory.EVERY_MEM,listTheory.MEM_FILTER]
      >> first_x_assum drule
      >> gvs[]
      >> spose_not_then assume_tac
      >> Cases_on `t_w`
      >> gs[mem_read_def,mem_get_def]
    )
    >> dsimp[listTheory.MEM_FILTER]
    >> drule_then assume_tac mem_get_eq
    >> rw[]
    >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ
    >> irule arithmeticTheory.LESS_EQ_LESS_TRANS
    >> qpat_x_assum `_.bst_coh _ < _` $ irule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Fence`]
  >- rw[]
  >~ [`BStmt_CJmp`]
  >- (
    disch_then kall_tac (* removes wf_xclb *)
    >> drule_then (rev_drule_then assume_tac) bir_eval_exp_view_bound
    >> fs[bir_exec_stmt_cjmp_mc_invar]
  )
  >~ [`bmc_exec_general_stmt`]
  >- (
    disch_then kall_tac (* removes wf_xclb *)
    >> drule_then assume_tac bmc_exec_general_stmt_mc_invar
    >> fs[]
  )
  >~ [`BMCStmt_Assign`]
  >- (
    drule_then irule well_formed_viewenv_UPDATE
    >> drule_all_then irule bir_eval_exp_view_bound
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
  >> conj_tac
  >- (
    fs[listTheory.EVERY_MEM] >> rw[]
    >> res_tac
    >> fs[mem_is_cid_append]
  )
  >> conj_tac
  >- (
    qx_gen_tac `t` >> rw[]
    >> Cases_on `t = LENGTH M`
    >- gs[listTheory.oEL_THM,rich_listTheory.EL_APPEND2]
    >> qmatch_asmsub_rename_tac `oEL t (M ++ _) = SOME msg'`
    >> `oEL t M = SOME msg'` by (
      gs[listTheory.oEL_THM,arithmeticTheory.NOT_NUM_EQ,rich_listTheory.EL_APPEND1]
    )
    >> first_x_assum drule
    >> fs[]
  )
  >> qx_gen_tac `t` >> rw[]
  >> Cases_on `t = LENGTH M`
  >> imp_res_tac mem_get_LENGTH
  >> fs[mem_get_append]
  >> dxrule_then strip_assume_tac $ iffLR arithmeticTheory.LESS_OR_EQ
  >> gs[mem_get_append,mem_get_def,listTheory.oEL_THM,GSYM arithmeticTheory.ADD1,rich_listTheory.EL_APPEND2]
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
    conj_tac
    >- (
      fs[listTheory.EVERY_MEM] >> rw[]
      >> res_tac
      >> fs[mem_is_cid_append]
    )
    >> simp[GSYM arithmeticTheory.ADD1,mem_is_cid_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND2]
  )
  >> conj_tac
  >- (
    rw[listTheory.ALL_DISTINCT_APPEND]
    >> spose_not_then assume_tac
    >> fs[listTheory.EVERY_MEM]
    >> res_tac
    >> fs[]
  )
  >> conj_tac
  >- (
    qx_gen_tac `t` >> rw[]
    >> Cases_on `t = LENGTH M`
    >> gs[]
    >> qmatch_asmsub_rename_tac `oEL t (M ++ _) = SOME msg'`
    >> `oEL t M = SOME msg'` by (
      gs[listTheory.oEL_THM,arithmeticTheory.NOT_NUM_EQ,rich_listTheory.EL_APPEND1]
    )
    >> first_x_assum drule
    >> fs[]
  )
  >> qx_gen_tac `t` >> rw[]
  >> Cases_on `t <= LENGTH M`
  >> gs[mem_get_append,arithmeticTheory.NOT_LESS_EQUAL]
  >> qmatch_asmsub_rename_tac `mem_get _ _ t`
  >> Cases_on `t`
  >> fs[mem_get_def,listTheory.oEL_THM]
QED

Theorem cstep_preserves_wf:
!p cid s M prom s' M'.
  well_formed cid M s
  /\ wf_ext_p p cid
  /\ cstep p cid s M prom s' M'
  ==> well_formed cid M' s'
Proof
  rw[cstep_cases]
  >- (
    drule_at_then Any irule clstep_preserves_wf
    >> fs[wf_ext_p_def]
  )
  >> fs[well_formed_promise_self]
QED

Theorem cstep_seq_preserves_wf:
!p cid s M s' M'.
  well_formed cid M s
  /\ wf_ext_p p cid
  /\ cstep_seq p cid (s,M) (s', M')
  ==> well_formed cid M' s'
Proof
  rw[cstep_seq_cases]
  >- (
    drule_at_then Any irule clstep_preserves_wf
    >> fs[wf_ext_p_def]
  )
  >> qmatch_asmsub_rename_tac `clstep p cid s'' M' [t] s'`
  >> drule_at_then Any irule clstep_preserves_wf
  >> drule_at_then Any (irule_at Any) cstep_preserves_wf
  >> fs[wf_ext_p_def]
QED

Theorem cstep_seq_rtc_preserves_wf:
  !p cid s M s' M'.
  well_formed cid M s
  /\ wf_ext_p p cid
  /\ cstep_seq_rtc p cid (s,M) (s',M')
  ==> well_formed cid M' s'
Proof
  qsuff_tac `
    !p cid sM sM'.
    cstep_seq_rtc p cid sM sM'
    ==> well_formed cid (SND sM) (FST sM)
    ==> wf_ext_p p cid
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

Theorem parstep_preserves_prog_cid:
!cid p cid' cores M cores' M' cid'' s.
  parstep cid cores M cores' M'
  /\ FLOOKUP cores cid' = SOME $ Core cid'' p s
  ==> ?s'. FLOOKUP cores cid' = SOME $ Core cid'' p s'
Proof
  fs[parstep_cases,PULL_EXISTS]
QED

Theorem cstep_seq_NRC_wf =
  Ho_Rewrite.REWRITE_RULE[arithmeticTheory.RTC_eq_NRC,cstep_seq_rtc_def,PULL_EXISTS]
  cstep_seq_rtc_preserves_wf

Theorem parstep_preserves_wf:
!cid cores M cores' M'.
  well_formed_cores cores M
  /\ well_formed_ext_cores cores
  /\ parstep cid cores M cores' M'
  ==> well_formed_cores cores' M'
Proof
  rw[parstep_cases]
  >> fs[well_formed_cores_def,well_formed_ext_cores_def,FLOOKUP_UPDATE]
  >> rw[]
  >> ntac 2 $ first_x_assum $ drule_then strip_assume_tac
  >- drule_all_then irule cstep_preserves_wf
  >> fs[cstep_cases,well_formed_promise_other,well_formed_ext_cores_def]
QED

Theorem parstep_preserves_wf_ext_cores:
!cid cores M cores' M'.
  well_formed_ext_cores cores
  /\ parstep cid cores M cores' M'
  ==> well_formed_ext_cores cores'
Proof
  rw[parstep_cases,well_formed_ext_cores_def]
  >> gvs[FLOOKUP_UPDATE,COND_RATOR,COND_RAND,COND_EXPAND_OR]
QED

(* init state *)

Theorem wf_init_state:
  !cid p. well_formed cid [] $ bmc_state_init p
Proof
  fs[bir_init_progTheory.bmc_state_init_def,well_formed_def,well_formed_viewenv_def,well_formed_fwdb_def,mem_read_def,listTheory.oEL_THM,mem_get_def]
  >> Cases >> fs[mem_get_def,listTheory.oEL_THM]
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

(* lifting reflexive-transitive pre-post conditions to cstep_seq *)

Theorem cstep_transitive_cstep_seq:
  !p cid R.
  reflexive R /\ transitive R
  /\ (!s M prom s' M'. cstep p cid s M prom s' M' ==> R (s,M) (s',M'))
  /\ (!s M prom s'. clstep p cid s M prom s' ==> R (s,M) (s',M))
  ==> !sM sM'. cstep_seq p cid sM sM' ==> R sM sM'
Proof
  rpt gen_tac >> strip_tac
  >> rpt PairCases >> strip_tac
  >> fs[cstep_seq_cases]
  >> res_tac
  >> dxrule_then irule $ iffLR relationTheory.transitive_def
  >> rpt $ goal_assum drule
QED

Theorem cstep_transitive_cstep_seq_rtc:
  !p cid R.
  reflexive R /\ transitive R
  /\ (!s M prom s' M'. cstep p cid s M prom s' M' ==> R (s,M) (s',M'))
  /\ (!s M prom s'. clstep p cid s M prom s' ==> R (s,M) (s',M))
  ==> !sM sM'. cstep_seq_rtc p cid sM sM' ==> R sM sM'
Proof
  rpt gen_tac >> strip_tac
  >> reverse $ qsuff_tac `!sM sM'. cstep_seq p cid sM sM' ==> R sM sM'`
  >- (
    match_mp_tac cstep_transitive_cstep_seq
    >> asm_rewrite_tac[]
  )
  >> rpt $ PRED_ASSUM is_forall kall_tac >> strip_tac
  >> fs[cstep_seq_rtc_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[relationTheory.reflexive_def,relationTheory.transitive_def]
  >> rpt Cases >> strip_tac
  >> first_x_assum $ dxrule_then assume_tac
  >> first_x_assum irule
  >> rpt $ goal_assum drule
QED

(* properties *)

Theorem clstep_coh_mono:
  !p cid s M prom s' l.
  clstep p cid s M prom s' ==> s.bst_coh l <= s'.bst_coh l
Proof
  rw[clstep_cases]
  >> fs[bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,combinTheory.APPLY_UPDATE_THM,bmc_exec_general_stmt_exists,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_halt_def,bir_state_set_typeerror_def,AllCaseEqs(),fence_updates_def]
  >> rw[] >> fs[]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem cstep_coh_mono:
  !p cid s M prom s' M' l.
  cstep p cid s M prom s' M' ==> s.bst_coh l <= s'.bst_coh l
Proof
  rw[cstep_cases] >> fs[]
  >> drule clstep_coh_mono >> fs[]
QED

Theorem cstep_seq_rtc_coh_mono:
  !p cid sM sM' l. cstep_seq_rtc p cid sM sM'
  ==> (FST sM).bst_coh l <= (FST sM').bst_coh l
Proof
  ntac 2 gen_tac
  >> fs[GSYM PULL_FORALL]
  >> ho_match_mp_tac cstep_transitive_cstep_seq_rtc
  >> rw[relationTheory.reflexive_def,pairTheory.LAMBDA_PROD,relationTheory.transitive_def,pairTheory.FORALL_PROD]
  >- (
    qmatch_goalsub_rename_tac `_.bst_coh l`
    >> ntac 2 $ first_x_assum $ qspec_then `l` assume_tac
    >> irule arithmeticTheory.LESS_EQ_TRANS
    >> rpt $ goal_assum drule
  )
  >> imp_res_tac cstep_coh_mono
  >> imp_res_tac clstep_coh_mono
  >> fs[]
QED

Theorem cstep_seq_NRC_coh_mono =
  Ho_Rewrite.REWRITE_RULE[arithmeticTheory.RTC_eq_NRC,cstep_seq_rtc_def,PULL_EXISTS]
  cstep_seq_rtc_coh_mono

(* monotony of memory *)

Theorem cstep_mem_mono:
  !p cid s M prom s' M' P.
  cstep p cid s M prom s' M'
  ==> LENGTH M <= LENGTH M' /\ IS_PREFIX M' M
Proof
  rw[rich_listTheory.IS_PREFIX_APPEND,cstep_cases] >> fs[]
QED

Theorem cstep_seq_mem_mono:
  !p cid s M s' M'.
  cstep_seq p cid (s,M) (s',M')
  ==> LENGTH M <= LENGTH M' /\ IS_PREFIX M' M
Proof
  rpt gen_tac >> strip_tac
  >> fs[cstep_seq_cases]
  >> drule_then irule cstep_mem_mono
QED

Theorem cstep_seq_rtc_mem_mono:
  !p cid sM sM'. cstep_seq_rtc p cid sM sM'
  ==> LENGTH $ SND sM <= LENGTH $ SND sM' /\ IS_PREFIX (SND sM') (SND sM)
Proof
  ntac 2 gen_tac
  >> fs[GSYM PULL_FORALL]
  >> ho_match_mp_tac cstep_transitive_cstep_seq_rtc
  >> rw[relationTheory.reflexive_def,pairTheory.LAMBDA_PROD,relationTheory.transitive_def,pairTheory.FORALL_PROD]
  >- (
    irule rich_listTheory.IS_PREFIX_TRANS
    >> rpt $ goal_assum drule
  )
  >> fs[cstep_cases]
QED

Theorem cstep_seq_NRC_mem_mono =
  Ho_Rewrite.REWRITE_RULE[arithmeticTheory.RTC_eq_NRC,cstep_seq_rtc_def,PULL_EXISTS]
  cstep_seq_rtc_mem_mono

(* promset decreases monotonically *)

Theorem cstep_seq_prom_subset:
  !p cid s M s' M'.
  cstep_seq p cid (s,M) (s',M')
  ==> (set s'.bst_prom) SUBSET (set s.bst_prom)
Proof
  rw[cstep_seq_cases,cstep_cases]
  >- (
    gvs[clstep_cases,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,listTheory.LIST_TO_SET_FILTER,pred_setTheory.INTER_SUBSET,fence_updates_def,remove_prom_def]
    >~ [`BStmt_CJmp`]
    >- (
      fs[bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def]
      >> BasicProvers.every_case_tac
      >> fs[bir_state_set_typeerror_def]
    )
    >~ [`BSGen stmt`]
    >- (
      fs[bmc_exec_general_stmt_exists,bir_exec_stmtB_def,bir_exec_stmtE_def,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_halt_def]
      >> BasicProvers.every_case_tac
      >> gvs[bir_state_set_typeerror_def]
    )
  )
  >> gs[clstep_cases,listTheory.LIST_TO_SET_FILTER,pred_setTheory.INTER_SUBSET,bir_state_fulful_view_updates_def,pred_setTheory.UNION_OVER_INTER,remove_prom_def]
  >> fs[pred_setTheory.INTER_DEF]
  >> fs[COND_RAND,listTheory.LIST_TO_SET_FILTER,pred_setTheory.INTER_SUBSET,pred_setTheory.UNION_OVER_INTER]
  >> fs[pred_setTheory.INTER_DEF]
QED

Theorem cstep_seq_rtc_prom_subset:
  !p cid sM sM'.
  cstep_seq_rtc p cid sM sM'
  ==> (set (FST sM').bst_prom) SUBSET (set (FST sM).bst_prom)
Proof
  ntac 2 gen_tac
  >> fs[GSYM PULL_FORALL,cstep_seq_rtc_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> fs[pairTheory.FORALL_PROD]
  >> rw[]
  >> irule pred_setTheory.SUBSET_TRANS
  >> drule_then (irule_at Any) cstep_seq_prom_subset
  >> goal_assum drule
QED

Theorem cstep_seq_NRC_prom_subset =
  Ho_Rewrite.REWRITE_RULE[arithmeticTheory.RTC_eq_NRC,cstep_seq_rtc_def,PULL_EXISTS]
  cstep_seq_rtc_prom_subset

Theorem remove_prom_empty:
  !prom prom'. prom = remove_prom prom' prom
    /\ (set prom') SUBSET (set prom) ==> prom' = []
Proof
  rw[listTheory.FILTER_EQ_ID,remove_prom_def,DISJ_EQ_IMP]
  >> spose_not_then assume_tac
  >> fs[listTheory.NOT_NULL_MEM,GSYM listTheory.NULL_EQ,listTheory.EVERY_MEM,pred_setTheory.SUBSET_DEF]
  >> ntac 2 res_tac
QED

Theorem COND_COND_eq:
  !P x x' y y'.
  (COND P x y) = COND P x' y' <=> (P ==> x = x') /\ (~P ==> y = y')
Proof
  Cases >> fs[]
QED

Theorem MAX_MAX_eq:
  !a b c. MAX a b = MAX a c <=> (a < b \/ a < c) ==> b = c
Proof
  fs[arithmeticTheory.MAX_DEF] >> BasicProvers.every_case_tac >> fs[]
  >> fs[arithmeticTheory.LESS_OR_EQ,arithmeticTheory.NOT_LESS]
QED

Theorem MAX_MAX_eq':
  !a b c. MAX a b = MAX c b <=> (b < a \/ b < c) ==> a = c
Proof
  fs[arithmeticTheory.MAX_DEF] >> BasicProvers.every_case_tac >> fs[]
  >> fs[arithmeticTheory.LESS_OR_EQ,arithmeticTheory.NOT_LESS]
QED

Theorem cstep_seq_is_clstep:
  !p cid s1 M1 s2 M2 t.
  cstep_seq p cid (s1,M1) (s2,M2)
  /\ well_formed cid M1 s1
  /\ MEM t s1.bst_prom
  /\ ~MEM t s2.bst_prom
  ==> ?prom. clstep p cid s1 M1 prom s2 /\ ~NULL prom /\ M1 = M2
Proof
  rpt gen_tac >> strip_tac
  >> gs[cstep_cases,cstep_seq_cases]
  >- (
    goal_assum drule
    >> gvs[clstep_cases,bir_state_read_view_updates_def,fence_updates_def,bir_exec_stmt_cjmp_mc_invar,remove_prom_def,listTheory.MEM_FILTER]
    >> imp_res_tac bmc_exec_general_stmt_mc_invar
    >> gvs[listTheory.NOT_NULL_MEM,COND_RAND,listTheory.MEM_FILTER]
    >> goal_assum drule
  )
  >> qmatch_asmsub_rename_tac `LENGTH M1 + 1`
  >> qmatch_asmsub_rename_tac `MEM t s1.bst_prom`
  >> `t <= LENGTH M1` by fs[well_formed_def,listTheory.EVERY_MEM]
  >> gvs[clstep_cases,bir_state_fulful_view_updates_def,remove_prom_def,listTheory.FILTER_APPEND_DISTRIB,listTheory.MEM_FILTER]
  >> gvs[COND_RAND,listTheory.MEM_FILTER]
QED

(* in the certifying trace there exists the step where a promise is discharged *)

Theorem is_certified_promise_disch:
  !cid M s p t.
  is_certified p cid s M
  /\ MEM t s.bst_prom
  ==>
    ?n m sM2 sM3 sM4. NRC (cstep_seq p cid) m (s,M) sM2
    /\ cstep_seq p cid sM2 sM3
    /\ NRC (cstep_seq p cid) n sM3 sM4
    /\ MEM t (FST sM2).bst_prom
    /\ ~MEM t (FST sM3).bst_prom
    /\ NULL (FST sM4).bst_prom
Proof
  rpt strip_tac
  >> fs[is_certified_def,cstep_seq_rtc_def]
  >> dxrule_then strip_assume_tac arithmeticTheory.RTC_NRC
  >> qmatch_asmsub_rename_tac `NRC (cstep_seq p cid) n (s,M) (s',M')`
  >> Cases_on `0 < n` >> gvs[]
  >> Cases_on `!m. m <= n ==> !s'' M''.
    NRC (cstep_seq p cid) m (s,M) (s'',M'')
    /\ NRC (cstep_seq p cid) (n - m) (s'',M'') (s',M')
    ==> MEM t s''.bst_prom`
  >- (first_x_assum $ drule_at Any >> fs[])
  >> PRED_ASSUM is_neg $ mp_tac o SIMP_RULE std_ss [NOT_FORALL_THM]
  >> qho_match_abbrev_tac `(?m. P' m) ==> _`
  >> disch_then assume_tac
  >> dxrule_then strip_assume_tac arithmeticTheory.WOP
  >> qmatch_asmsub_rename_tac `P' m`
  >> `0 < m /\ m <= n` by (
    unabbrev_all_tac
    >> fs[] >> Cases_on `m` >> gvs[]
  )
  >> `PRE m < m` by decide_tac
  >> unabbrev_all_tac
  >> Cases_on `m` >> gs[DISJ_EQ_IMP,arithmeticTheory.NRC_SUC_RECURSE_LEFT]
  >> rpt $ goal_assum drule
  >> fs[]
  >> first_x_assum irule
  >> qmatch_asmsub_rename_tac `cstep_seq p cid z (s'',M'')`
  >> PairCases_on `z`
  >> fs[]
  >> goal_assum $ dxrule_at Any
  >> dxrule_at (Pat `NRC`) $
    Ho_Rewrite.REWRITE_RULE[PULL_EXISTS] $ iffRL $ cj 2 arithmeticTheory.NRC
  >> disch_then dxrule
  >> qmatch_goalsub_rename_tac `NRC _ (SUC $ n - SUC n')`
  >> `SUC $ n - SUC n' = n - n'` by decide_tac
  >> fs[]
QED

Theorem is_certified_promises:
  !cid M s p l t msg.
  is_certified p cid s M
  /\ well_formed cid M s
  /\ wf_ext_p p cid
  /\ MEM t s.bst_prom
  /\ mem_get M l t = SOME msg /\ msg.cid = cid
  ==> s.bst_coh l < t
Proof
  spose_not_then strip_assume_tac
  >> qmatch_asmsub_rename_tac `MEM t s.bst_prom`
  >> `t <= LENGTH M` by fs[well_formed_def,listTheory.EVERY_MEM]
  >> drule_all_then strip_assume_tac is_certified_promise_disch
  >> qmatch_asmsub_rename_tac `cstep_seq p cid sM2 sM3`
  >> PairCases_on `sM2` >> PairCases_on `sM3`
  >> rev_drule_at_then (Pat `NRC`) assume_tac cstep_seq_NRC_wf
  >> drule_all_then assume_tac cstep_seq_NRC_wf
  >> fs[arithmeticTheory.NOT_LESS]
  >> dxrule_then (drule_all_then strip_assume_tac) cstep_seq_is_clstep
  >> qmatch_asmsub_rename_tac `NRC (cstep_seq p cid) m (s,M) (s1,M1)`
  >> qspecl_then [`p`,`cid`,`(s,M)`,`(s1,M1)`,`m`] assume_tac cstep_seq_NRC_mem_mono
  >> gvs[clstep_cases,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bmc_exec_general_stmt_exists,bir_exec_stmt_assume_def,bir_exec_stmt_assert_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_halt_def,fence_updates_def]
  >> qmatch_asmsub_rename_tac `_.bst_coh l`
  >> qspecl_then [`p`,`cid`,`(s,M)`,`(s1,M1)`,`l`,`m`] assume_tac cstep_seq_NRC_coh_mono
  >~ [`BSExt R`]
  >- (
    gs[listTheory.MEM_FILTER,remove_prom_def,listTheory.EVERY_MEM,rich_listTheory.IS_PREFIX_APPEND,bir_exec_stmt_jmp_to_label_mc_invar]
    >> first_x_assum $ drule_then strip_assume_tac
    >> gs[mem_is_loc_append]
    >> `0 < t` by fs[well_formed_def,listTheory.EVERY_MEM]
    >> drule_all_then (fs o single) mem_get_mem_is_loc
  )
  >> gvs[listTheory.MEM_FILTER,remove_prom_def]
  >> gvs[rich_listTheory.IS_PREFIX_APPEND,mem_get_append]
  >> fs[mem_get_append]
  >> drule_then (rev_drule_then assume_tac) mem_get_eq
  >> gvs[]
  >> BasicProvers.every_case_tac
  >> gvs[]
  >> fs[listTheory.EVERY_MEM]
  >> first_x_assum $ drule_then assume_tac
  >> gs[mem_is_loc_append]
  >> drule_then (rev_drule_then assume_tac) mem_get_mem_is_loc
  >> gvs[]
QED

Theorem is_certified_promises':
  !cid M s p l t msg.
  is_certified p cid s M
  /\ well_formed cid M s
  /\ wf_ext_p p cid
  ==>
  EVERY (λt. !l. mem_get M l t = SOME msg /\ msg.cid = cid ==> s.bst_coh l < t) s.bst_prom
Proof
  fs[listTheory.EVERY_MEM]
  >> rpt strip_tac
  >> drule_all_then irule is_certified_promises
QED

val _ = export_theory ();
