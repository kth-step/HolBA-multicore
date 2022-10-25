open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;
open bir_programTheory;
open bir_valuesTheory;
open bir_expTheory;
open finite_mapTheory;

val _ = new_theory "bir_promising_wf";

Theorem MAX_LE[simp]:
  MAX a b <= c <=> a <= c /\ b <= c
Proof
  rw[arithmeticTheory.MAX_DEF,EQ_IMP_THM]
QED

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

Theorem mem_get_LENGTH:
  !t M l v. mem_get M l t = SOME v ==> t <= LENGTH M
Proof
  Cases >> rw[mem_get_def,listTheory.oEL_THM]
QED

Theorem mem_read_LENGTH:
  !t M l v. mem_read M l t = SOME v ==> t <= LENGTH M
Proof
  Cases >> rw[mem_read_some,mem_read_def,AllCaseEqs()]
  >> imp_res_tac mem_get_LENGTH
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
 well_formed_fwdb l M coh_t fwd =
   (fwd.fwdb_time <= latest l coh_t M
    /\ fwd.fwdb_view < fwd.fwdb_time
    /\ ?v. mem_read M l fwd.fwdb_time = SOME v)
End
(*
Definition well_formed_xclb_def:
  well_formed_xclb M coh_t xclb =
  (xclb.xclb_time <= latest xclb.xclb_loc coh_t M
   /\ xclb.xclb_view <= coh_t
   /\ ?v. mem_read M xclb.xclb_loc xclb.xclb_time = SOME v)
End
*)

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
(*     /\ (!xclb. s.bst_xclb = SOME xclb ==> well_formed_xclb M (s.bst_coh(xclb.loc) xclb)) *)
     /\ (!t. MEM t s.bst_prom ==> t <= LENGTH M)
     /\ (!t msg.
           (oEL t M = SOME msg
            /\ msg.cid = cid
            /\ s.bst_coh(msg.loc) < t)
           ==>
           MEM (SUC t) s.bst_prom)
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
>|
[ (* read *)
Cases_on ‘l = l'’
>| [
‘(s.bst_fwdb l').fwdb_time ≤ latest l' (s.bst_coh l') M’ by fs[]
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
,
fs[]
],
  (* write *)
  Cases_on ‘l = l'’
  >| [
    ‘mem_read M l' v_post = SOME v’ by fs[mem_read_def]
    >> fs[]
    >> ‘v_post = latest l' v_post M’ by fs[latest_exact]
    >> ‘latest l' v_post M <= latest l' (MAX (s.bst_coh l') v_post) M’ suffices_by fs[]
    >> fs[latest_max]
    , fs[]
  ]
  , (* amo *)
  Cases_on ‘l = l'’
  >| [
      EVAL_TAC
      >> ‘mem_read M l t_w = SOME v_w’ by fs[mem_read_def]
      >> fs[]
      >> ‘t_w = latest l t_w M’  by fs[latest_exact]
      >> ‘latest l' t_w M <= latest l' (MAX (s.bst_coh l') t_w) M’
         suffices_by gvs[]
      >> fs[latest_max]
      ,
      EVAL_TAC
      >> fs[]
      >> ‘?v.mem_read M l (s.bst_fwdb l).fwdb_time = SOME v’ by fs[]
      >> qexists_tac ‘v’
      >> ‘?m. mem_get M l (s.bst_fwdb l).fwdb_time = SOME m /\ m.val = v’ by fs[mem_get_mem_read]
      >> fs[]
    ]
  ,
  (* branch *)
  drule bir_exec_stmt_mc_invar >> strip_tac >> fs[]
  ,
  (* generic *)
  drule bir_exec_stmt_mc_invar >> strip_tac >> fs[]
]
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
mem_read_view fwd t ≤ LENGTH M
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

Theorem clstep_preserves_wf:
!p cid s M prom s'.
  well_formed cid M s
  /\ clstep p cid s M prom s'
==>
  well_formed cid M s'
Proof
  rpt strip_tac
  >> fs[well_formed_def]
  >> drule_then imp_res_tac clstep_preserves_wf_fwdb
  >> fs[clstep_cases]
  >~ [`BirStmt_Read`]
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
  >~ [`BirStmt_Write`,`xclfail_update_env`]
  >- (
    gvs[xclfail_update_env_def,xclfail_update_viewenv_def,AllCaseEqs(),well_formed_viewenv_def,FLOOKUP_UPDATE]
    >> rw[] >> gvs[] >> metis_tac[]
  )
  >~ [`BirStmt_Write`]
  >- (
    conj_tac
    >- (
      gvs[well_formed_viewenv_def,fulfil_update_viewenv_def,AllCaseEqs(),FLOOKUP_UPDATE]
      >> rw[] >> gvs[] >> metis_tac[]
    )
    >> conj_tac
    >- (
      gen_tac
      >> first_assum drule
      >> first_assum $ qspec_then `l` mp_tac
      >> first_x_assum $ qspec_then `l'` mp_tac
      >> first_assum $ qspec_then `l` mp_tac
      >> first_x_assum $ qspec_then `l'` mp_tac
      >> rw[well_formed_fwdb_def]
    )
    >> conj_tac
    >- (first_assum drule >> rw[well_formed_fwdb_def])
    >> conj_tac
    >- (first_assum drule >> rw[well_formed_fwdb_def])
    >> conj_asm1_tac
    >- (
      drule_then rev_drule bir_eval_exp_view_bound
      >> fs[]
    )
    >> conj_tac
    >- (first_assum drule >> rw[])
    >> conj_tac >- rw[listTheory.MEM_FILTER]
    >> rw[]
    >> first_x_assum $ drule_then $ drule_at_then Any assume_tac
    >> gvs[]
    >> rw[listTheory.MEM_FILTER]
    >> spose_not_then assume_tac
    >> Cases_on `v_post`
    >> gs[mem_read_def,mem_get_def]
  )
  >~ [`BirStmt_Amo`]
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
    >> rw[combinTheory.APPLY_UPDATE_THM,listTheory.MEM_FILTER]
    >> first_x_assum $ drule
    >> gvs[]
    >> spose_not_then assume_tac
    >> Cases_on `t_w`
    >> gs[mem_read_def,mem_get_def]
  )
  >~ [`BirStmt_Fence`]
  >- rw[]
  >~ [`BirStmt_Branch`]
  >- (
    drule_then (rev_drule_then assume_tac) bir_eval_exp_view_bound
    >> gvs[bir_exec_stmt_def,bir_exec_stmtE_def,bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,GSYM bir_exec_stmt_jmp_bst_prom,bir_exec_stmt_jmp_bst_eq]
  )
  >~ [`BirStmt_Generic`]
  >- (
    drule_then strip_assume_tac bir_exec_stmt_mc_invar
    >> gvs[]
  )
  >~ [`BirStmt_Expr`]
  >- (
    drule_then irule well_formed_viewenv_UPDATE
    >> drule_all bir_eval_exp_view_bound
    >> fs[]
  )
QED

val _ = export_theory ();
