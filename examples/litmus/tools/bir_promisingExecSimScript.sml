open HolKernel Parse boolLib bossLib BasicProvers;
open bir_promisingTheory bir_promisingExecTheory bir_programTheory;

open listTheory;
open arithmeticTheory;
(*
open listTheory arithmeticTheory;
open bir_expTheory;
open numeralTheory arithmeticTheory;
open pred_setTheory;
open prim_recTheory
*)

val _ = new_theory "bir_promisingExecSim";

(****************************************
 * THEOREM: EL_SNOC2
 *
 * DESCRIPTION:
 *   Self-explanatory. TODO: maybe add to rich_listTheory
 *)
Theorem EL_SNOC2:
  ∀x l.
    EL (LENGTH l) (SNOC x l) = x
Proof
  Induct_on ‘l’ >>
  (asm_rewrite_tac [LENGTH, SNOC, EL, HD, TL])
QED

Triviality IS_SOME_NONE:
  !x.
  IS_SOME x = (x <> NONE)
Proof
  Cases_on ‘x’ >> fs []
QED

Triviality MEM_ZIP_memory_timestamp0:
  ∀m M.
    ~MEM (m, 0) (ZIP (M, [1 .. LENGTH M]))
Proof
  Induct_on ‘M’ using SNOC_INDUCT >>
  (fs [listRangeTheory.listRangeINC_def, oEL_def, rich_listTheory.ZIP_SNOC, GENLIST])
QED

Triviality MEM_ZIP_memory_timestamp:
  ∀m t M.
    MEM (m, SUC t) (ZIP (M, [1 .. LENGTH M])) = (oEL t M = SOME m)
Proof
  Induct_on ‘M’ using SNOC_INDUCT >|
  [
    fs [listRangeTheory.listRangeINC_def, oEL_def]
    ,
    fs [GENLIST, listRangeTheory.listRangeINC_def, rich_listTheory.ZIP_SNOC, oEL_THM] >>
    simp [ADD1] >>
    rpt gen_tac >>
    eq_tac >|
    [
      rpt strip_tac >>
      (fs [EL_SNOC, EL_SNOC2])
      ,
      rpt strip_tac >>
      ‘t < LENGTH M \/ t = LENGTH M’ by (fs []) >>
      (fs [EL_SNOC, EL_SNOC2])
    ]
  ]
QED



(* UNUSED *)
Theorem MAP_PARTIAL_rwr:
  ∀f xs.
  MAP_PARTIAL f xs = MAP THE (FILTER IS_SOME (MAP f xs))
Proof
  Induct_on ‘xs’ >|
  [
    simp [MAP_PARTIAL_def]
    ,
    simp [MAP_PARTIAL_def] >>
    rpt gen_tac >> CASE_TAC >>
    (simp [])
  ]
QED

Theorem MEM_MAP_PARTIAL:
  ∀x f xs.
  MEM x (MAP_PARTIAL f xs) = MEM (SOME x) (MAP f xs)
Proof
  simp [MAP_PARTIAL_rwr] >>
  Induct_on ‘xs’ >|
  [
    simp []
    ,
    simp [] >>
    rpt gen_tac >> CASE_TAC >|
    [
      rename1 ‘IS_SOME (f h)’ >> Cases_on ‘f h’ >>
      (fs [])
      ,
      fs []
    ]
  ]
QED

Triviality EVERY_oEL:
  ∀P l.
  EVERY P l ⇔ ∀x n. oEL n l = SOME x ⇒ P x 
Proof
  fs [EVERY_EL, oEL_THM]
QED

Theorem mem_every_thm:
  ∀P M.
  mem_every P M = ∀m t. oEL t M = SOME m ⇒ P (m, SUC t)
Proof
  fs [mem_every_def, EVERY_MEM] >>
  rpt gen_tac >> eq_tac >|
  [
    rpt strip_tac >>
    fs [MEM_ZIP_memory_timestamp]
    ,
    rpt strip_tac >>
    rename1 ‘P e’ >>
    Cases_on ‘e’ >>
    rename1 ‘P (m, t)’ >>
    Cases_on ‘t’ >>
    (fs [MEM_ZIP_memory_timestamp0, MEM_ZIP_memory_timestamp])
  ]
QED

Theorem mem_filter_thm:
∀P M m t.
  MEM (m, SUC t) (mem_filter P M) = (P (m, SUC t) ∧ oEL t M = SOME m)
Proof
  fs [MEM_ZIP_memory_timestamp, mem_filter_def, MEM_FILTER]
QED                           

(* Replace this *)
Theorem mem_get_0_SOME_thm:
  !M l m.
    mem_get M l 0 = SOME m <=> m = mem_default l
Proof
  fs [mem_get_def, EQ_SYM_EQ]
QED

Theorem mem_get_SUC_SOME_thm:
  !M l t m.
    mem_get M l (SUC t) = SOME m <=> oEL t M = SOME m /\ m.loc = l
Proof
  fs [mem_get_def, CaseEq"option"]
QED

Theorem IS_SOME_mem_get_0_thm:
  ∀M l.
    IS_SOME (mem_get M l 0)
Proof
  fs [mem_get_def]
QED

Theorem mem_get_mem_read:
  !M l t m.
  mem_get M l t = SOME m ==> mem_read M l t = SOME m.val
Proof
  Cases_on ‘t’ >>
  (fs [mem_get_def, mem_default_def, mem_read_def])
QED

Theorem mem_is_loc_correctness:
  !M t l.
    mem_is_loc M (SUC t) l <=> ?m. oEL t M = SOME m /\ m.loc = l
Proof
  fs [mem_is_loc_def] >>
  rpt gen_tac >>
  Cases_on ‘oEL t M’ >> (fs [])
QED

Theorem mem_is_cid_correctness:
  !M t cid.
    mem_is_cid M (SUC t) cid <=> ?m. oEL t M = SOME m /\ m.cid = cid
Proof
  fs [mem_is_cid_def] >>
  rpt gen_tac >>
  Cases_on ‘oEL t M’ >> (fs [])
QED

Theorem mem_atomic_correctness:
  !M l cid t_r t_w.
    mem_atomic M l cid t_r t_w = fulfil_atomic_ok M l cid t_r t_w
Proof
  fs [mem_atomic_def, fulfil_atomic_ok_def, mem_every_thm] >>
  rpt gen_tac >>
  eq_tac >|
  [
    rpt strip_tac >>
    Cases_on ‘t'’ >|
    [
      fs []
      ,
      fs [mem_is_loc_correctness, mem_is_cid_correctness] >>
      LAST_X_ASSUM drule >>
      fs []
    ]
    ,
    rpt strip_tac >>
    rename1 ‘t_r < SUC t’ >>
    ‘mem_is_loc M (SUC t) l’ by (fs [mem_is_loc_correctness]) >>
    ‘mem_is_cid M (SUC t) cid’ by (fs [mem_is_cid_correctness]) >>
    LAST_X_ASSUM drule >>
    gs [mem_is_cid_correctness]
  ]
QED


Theorem MEM_readable_thm:
  ∀m t M v_max l.
    MEM (m, t) (mem_readable M l v_max)
    = (mem_get M l t = SOME m ∧
       ∀t'. t < t' ∧ t' ≤ v_max ⇒ ~mem_is_loc M t' l)
Proof
  rpt gen_tac >>
  eq_tac >|
  [
    rewrite_tac [mem_readable_def, mem_every_thm, mem_filter_thm, MEM_FILTER] >>
    fs [] >>
    rpt strip_tac >|
    [
      fs [mem_get_def, mem_default_def]
      ,
      Cases_on ‘t'’ >|
      [
        fs []
        ,
        fs [mem_is_loc_correctness] >>
        FIRST_X_ASSUM drule >>
        fs []
      ]
      ,
      Cases_on ‘t’ >|
      [
        fs [MEM, mem_filter_def, MEM_ZIP_memory_timestamp0, MEM_FILTER]
        ,
        fs [mem_filter_thm, mem_get_def]
      ]
      ,
      Cases_on ‘t'’ >|
      [
        fs []
        ,
        fs [mem_is_loc_correctness] >>
        FIRST_X_ASSUM drule >>
        fs []
      ]
    ]
    ,
    rewrite_tac [mem_readable_def, mem_every_thm, mem_filter_thm, MEM_FILTER] >>
    fs [] >>
    rpt strip_tac >|
    [
      FIRST_X_ASSUM drule >>
      fs [mem_is_loc_correctness]
      ,
      Cases_on ‘t’ >|
      [
        fs [mem_get_def]
        ,
        fs [mem_get_SUC_SOME_thm, mem_filter_thm]
      ]
    ]
  ]
QED

(*
 ***********************************************************
 * Soundness proof of executable core-local step
 ************************************************************)

Theorem eval_clstep_read_soundness:
  ∀p cid M s s' var e acq rel xcl cast.
    bir_get_stmt p s.bst_pc = BirStmt_Read var e cast acq rel xcl ⇒
    MEM s' (eval_clstep_read s M var e acq rel xcl) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac
  >> fs [clstep_cases, eval_clstep_read_def, bir_state_t_component_equality, bir_eval_exp_view_def]
  >> Cases_on ‘bir_eval_exp e s.bst_environ’
  >- (fs [CaseEq"option"])
  >> fs [CaseEq"option"]
  (* MEM s' (MAP_PARTIAL (λ(msg,t). state option) (mem_readable M x (MAX ...)) *)
  >> fs [MEM_MAP_PARTIAL, MEM_MAP]
  >> rename1 ‘MEM x' (mem_readable _ _ _)’
  >> Cases_on ‘x'’
  >> fs [MEM_readable_thm]
  >> rename1 ‘mem_get M l t = SOME msg’
  >> Q.EXISTS_TAC ‘msg.val’ >> Q.EXISTS_TAC ‘t’
  >> fs [mem_get_mem_read, MAXL_def, ifView_def, combinTheory.UPDATE_def]
  >> rw []
  >> (
  fs []
  (* Fix the MAX parts if needed. *)
  >> METIS_TAC [MAX_ASSOC, MAX_COMM]
  )
QED                                   

Theorem eval_clstep_fulfil_soundness:
  ∀p s s' a_e v_e xcl acq rel cid M.
    bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ⇒
    MEM s' (eval_clstep_fulfil p cid s M a_e v_e xcl acq rel) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_fulfil_def] >>
  (* Get pairs from bir_eval_exp_view *)
  Cases_on ‘bir_eval_exp_view v_e s.bst_environ s.bst_viewenv’ >>
  Cases_on ‘bir_eval_exp_view a_e s.bst_environ s.bst_viewenv’ >>
  rename1 ‘bir_eval_exp_view v_e s.bst_environ s.bst_viewenv = (v_opt,v_data)’ >>
  rename1 ‘bir_eval_exp_view a_e s.bst_environ s.bst_viewenv = (l_opt,v_addr)’ >>
  (* Removes NONE cases *)
  (Cases_on ‘l_opt’ >> Cases_on ‘v_opt’ >> fs []) >> 
  (* Removes MEM, MAP_PARTIONAL, MAP, and FILTER *)
  fs [MEM_MAP_PARTIAL, MEM_MAP, MEM_FILTER] >>
  (* Removes NONE cases *)
  (Cases_on ‘fulfil_update_env p s xcl’ >> Cases_on ‘fulfil_update_viewenv p s xcl v_post’ >> fs []) >>
  (* At this point we have no big case splits (except rel acq xcl) *)
  (* Simplify assumptions *)
  Cases_on ‘xcl’ >|
  [
    (* xcl = T *)
    Cases_on ‘s.bst_xclb’ >- (fs []) >>
    fs [clstep_cases, MAXL_def, ifView_def, bir_state_t_component_equality, combinTheory.UPDATE_def] >>
    fs [mem_atomic_correctness] >>
    Q.EXISTS_TAC ‘[v_post]’ >>
    rw [MAX_COMM, EQ_SYM_EQ]
    ,
    (* xcl = F *)
    fs [clstep_cases, MAXL_def, ifView_def, bir_state_t_component_equality, combinTheory.UPDATE_def] >>
    Q.EXISTS_TAC ‘v_post’ >>
    fs [MAX_COMM, EQ_SYM_EQ]
  ]
QED

Theorem eval_clstep_xclfail_soundness:
  ∀p s s' a_e v_e xcl acq rel cid M.
    bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ⇒
    MEM s' (eval_clstep_xclfail p cid s xcl) ⇒ ?l. clstep p cid s M l s'
Proof
  Cases_on ‘xcl’ >|
  [
    fs [eval_clstep_xclfail_def, clstep_cases] >>
    Cases_on ‘xclfail_update_env p s’ >- (fs []) >>
    Cases_on ‘xclfail_update_viewenv p s’ >- (fs []) >>
    rpt strip_tac >>
    Q.EXISTS_TAC ‘[]’ >>
    fs [bir_state_t_component_equality]
    ,
    fs [eval_clstep_xclfail_def]
  ]
QED

Theorem eval_clstep_amofulfil_soundness:
  ∀p s var a_e v_e acq rel s' cid M.
    bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel ==>
    MEM s' (eval_clstep_amofulfil cid s M var a_e v_e acq rel) ==>
    ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_amofulfil_def] >>
  Cases_on ‘bir_eval_exp_view a_e s.bst_environ s.bst_viewenv’ >>
  rename1 ‘(l_opt, v_addr)’ >>
  Cases_on ‘l_opt’ >- (fs[]) >>
  rename1 ‘(SOME l, v_addr)’ >>
  fs [] >>
  fs [LIST_BIND_def, MEM_FLAT] >>
  rename1 ‘MEM s' state_list’ >>
  fs [MEM_MAP] >>
  rename1 ‘MEM x (mem_readable M l _)’ >>
  Cases_on ‘x’ >>
  rename1 ‘MEM (m_r, t_r) (mem_readable M l _)’ >>
  fs [MEM_readable_thm] >>
  Cases_on ‘env_update_cast64 (bir_var_name var) m_r.val (bir_var_type var) s.bst_environ’ >- (gs []) >>
  rename1 ‘SOME new_environ’ >>
  fs [] >>
  Cases_on ‘bir_eval_exp_view v_e new_environ
            (s.bst_viewenv |+ (var, MAX (MAXL [v_addr; s.bst_v_rNew;
                                               ifView (acq /\ rel) s.bst_v_Rel;
                                               ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)])
                                        (mem_read_view (s.bst_fwdb l) t_r)))’ >>
  rename1 ‘_ = (v_opt, v_data)’ >>
  Cases_on ‘v_opt’ >- (rfs []) >>
  rename1 ‘_ = (SOME v, v_data)’ >>
  rfs [MEM_MAP, MEM_FILTER] >>
  fs [clstep_cases, bir_state_t_component_equality, combinTheory.UPDATE_def, MAXL_def, ifView_def] >>
  Q.EXISTS_TAC ‘v_data’ >>
  Q.EXISTS_TAC ‘m_r.val’ >>
  Q.EXISTS_TAC ‘v’ >>
  Q.EXISTS_TAC ‘v_wPost’ >>
  Q.EXISTS_TAC ‘t_r’ >>
  fs [mem_get_mem_read] >>
  (Cases_on ‘acq’ >> Cases_on ‘rel’ >> fs [MAX_ASSOC]) >>
  (
  Cases_on ‘t'’ >- (fs []) >>
  fs [mem_is_loc_correctness] >>
  rpt strip_tac >>
  rfs [mem_every_thm] >>
  qpat_x_assum ‘!m' t. oEL t M = SOME m' ==> _’ MP_TAC >>
  fs [] >>
  HINT_EXISTS_TAC >>
  HINT_EXISTS_TAC >>
  fs []
  )
QED

Theorem eval_clstep_expr_soundness:
  ∀p cid M s s' var e.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e ⇒
  MEM s' (eval_clstep_exp s var e) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_exp_def] >>
  rpt (FULL_CASE_TAC >> fs [bir_get_stmt_expr])
QED                                              

Theorem eval_clstep_fence_soundness:
  ∀p cid M s s' K1 K2.
  bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2 ⇒
  MEM s' (eval_clstep_fence s K1 K2) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_fence_def, bir_state_t_component_equality] >>
  rpt FULL_CASE_TAC >>
  (fs [] >> METIS_TAC [MAX_COMM])
QED

Theorem eval_clstep_branch_soundness:
  ∀p cid M s s' cond_e lbl1 lbl2.
  bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2 ⇒
  MEM s' (eval_clstep_branch p s cond_e lbl1 lbl2) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_branch_def, bir_state_t_component_equality] >>
  Cases_on ‘bir_exec_stmt p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s’ >>
  Cases_on ‘bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv’ >>
  fs [] >>
  FULL_CASE_TAC >>
  (fs [])
QED

Theorem eval_clstep_generic_soundness:
  ∀p cid M s s' stmt.
  bir_get_stmt p s.bst_pc = BirStmt_Generic stmt ⇒
  MEM s' (eval_clstep_bir_step p s stmt) ⇒ ?l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_bir_step_def, bir_state_t_component_equality] >>
  Cases_on ‘bir_exec_stmt p stmt s’ >>
  fs []
QED

Theorem eval_clstep_soundness:
  ∀p cid M l s s'.
  MEM s' (eval_clstep cid p s M) ⇒ ∃l. clstep p cid s M l s'
Proof
  rpt strip_tac
  >> fs [eval_clstep_def]
  >> Cases_on ‘bir_get_stmt p s.bst_pc’
  >| [
    fs [eval_clstep_read_soundness]
    ,
    fs [eval_clstep_fulfil_soundness, eval_clstep_xclfail_soundness]
    ,
    fs [eval_clstep_amofulfil_soundness]
    ,
    fs [eval_clstep_expr_soundness]
    ,
    fs [eval_clstep_fence_soundness]
    ,
    fs [eval_clstep_branch_soundness]
    ,
    fs [eval_clstep_generic_soundness]
    ,
    fs []
  ]
QED

Theorem eval_clstep_read_completeness:
  ∀p cid M s s' var a_e acq rel xcl cast l.
    clstep p cid s M l s' /\
    bir_get_stmt p s.bst_pc = BirStmt_Read var a_e cast xcl acq rel ==>
    MEM s' (eval_clstep_read s M var a_e xcl acq rel)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_read_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp a_e s.bst_environ’
  >- (gvs [CaseEq"option"])
  >>  gvs [CaseEq"option"]
  (* MEM s' (MAP_PARTIAL (λ(msg,t). state option) (mem_readable M x (MAX ...)) *)
  >> fs [MEM_MAP_PARTIAL, MEM_MAP, mem_read_def, CaseEq"option"]
  >> Q.EXISTS_TAC ‘(m,t)’
  >> fs [MEM_readable_thm, bir_state_t_component_equality]
  >> fs [MAXL_def, ifView_def, combinTheory.UPDATE_def]
  >> rw []
  >> (
  gvs []
  (* Fix the MAX parts if needed. *)
  >> METIS_TAC [MAX_ASSOC, MAX_COMM]
  )
QED                                   

Theorem eval_clstep_write_completeness:
  ∀p s s' a_e v_e xcl acq rel cid M l.
    clstep p cid s M l s' /\
    bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ==>
    (MEM s' (eval_clstep_fulfil p cid s M a_e v_e xcl acq rel) \/
    MEM s' (eval_clstep_xclfail p cid s xcl))
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_fulfil_def, eval_clstep_xclfail_def, bir_eval_exp_view_def]
  >| [
    (* xclfail *)
    DISJ2_TAC >>
    (Cases_on ‘xclfail_update_env p s’ >>
    Cases_on ‘xclfail_update_viewenv p s’) >>
    (fs [bir_state_t_component_equality, combinTheory.UPDATE_def])
    ,
    (* fulfill *)
    DISJ1_TAC >>
    (Cases_on ‘bir_eval_exp a_e s.bst_environ’ >>
     Cases_on ‘bir_eval_exp v_e s.bst_environ’ >> fs []) >>
    fs [MEM_MAP_PARTIAL, MEM_MAP, MEM_FILTER] >>
    Q.EXISTS_TAC ‘v_post’ >>
    (Cases_on ‘fulfil_update_env p s xcl’ >>
     Cases_on ‘fulfil_update_viewenv p s xcl v_post’ >> fs[]) >>
    gvs [bir_state_t_component_equality, combinTheory.UPDATE_def, ifView_def, MAXL_def] >>
    fs [mem_atomic_correctness, IS_SOME_NONE] >>
    (rpt FULL_CASE_TAC >> fs[] >>
    METIS_TAC [MAX_ASSOC, MAX_COMM])
  ] 
QED

Theorem eval_clstep_amo_completeness:
  ∀p s var a_e v_e acq rel s' cid M prom_fulfilled.
    clstep p cid s M prom_fulfilled s' /\
    bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel ==>
    MEM s' (eval_clstep_amofulfil cid s M var a_e v_e acq rel)
Proof
  rpt strip_tac
  >> fs [clstep_cases, eval_clstep_amofulfil_def, bir_eval_exp_view_def]
  >> Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- fs []
  >> fs [LIST_BIND_def, MEM_FLAT, MEM_MAP]
  >> CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV)
  >> CONV_TAC SWAP_EXISTS_CONV
  >> fs [mem_read_def]
  >> Cases_on ‘mem_get M l t_r’ >- fs []
  >> rename1 ‘mem_get M l t_r = SOME msg’
  >> fs []
  >> Q.EXISTS_TAC ‘(msg, t_r)’
  >> fs [MEM_readable_thm]
  >> Cases_on ‘env_update_cast64 (bir_var_name var) v_r (bir_var_type var) s.bst_environ’ >- fs []
  >> gvs []
  >> Cases_on ‘bir_eval_exp v_e new_environ’ >- fs []
  >> gvs [] 
  >> fs [MEM_MAP, MEM_FILTER]
  >> CONV_TAC RIGHT_AND_EXISTS_CONV
  >> Q.EXISTS_TAC ‘t_w’
  >> fs []
  >> fs [mem_every_thm, MAXL_def, ifView_def, bir_state_t_component_equality, combinTheory.UPDATE_def]
  >> Cases_on ‘acq’ >> Cases_on ‘rel’
  >> fs []
  >> rpt strip_tac
  >> assume_tac mem_is_loc_correctness
  >> res_tac
QED

Theorem eval_clstep_expr_completeness:
  ∀p cid M s s' var e l.
  clstep p cid s M l s' /\
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e ==>
  MEM s' (eval_clstep_exp s var e)
Proof
  rpt strip_tac
  >> gvs [clstep_cases, eval_clstep_exp_def, bir_eval_exp_view_def]
  >> Cases_on ‘bir_eval_exp e s.bst_environ’ >- fs []
  >> Cases_on ‘env_update_cast64 (bir_var_name var) x (bir_var_type var) s.bst_environ’ >- fs []
  >> fs []
QED                                              

Theorem eval_clstep_fence_completeness:
  ∀p cid M s s' K1 K2 l.
  bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2 ==>
  clstep p cid s M l s' ==>
  MEM s' (eval_clstep_fence s K1 K2)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_fence_def, bir_eval_exp_view_def] >>
  fs [combinTheory.UPDATE_def, bir_state_t_component_equality, MAX_COMM]
QED

Theorem eval_clstep_branch_completeness:
  ∀p cid M s s' cond_e lbl1 lbl2 l.
  bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2 ==>
  clstep p cid s M l s' ==>
  MEM s' (eval_clstep_branch p s cond_e lbl1 lbl2)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_branch_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp cond_e s.bst_environ’ >> (fs [])
QED

Theorem eval_clstep_bir_generic_completeness:
  ∀p cid M s s' stmt l.
  bir_get_stmt p s.bst_pc = BirStmt_Generic stmt ==>
  clstep p cid s M l s' ==>
  MEM s' (eval_clstep_bir_step p s stmt)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_bir_step_def]
QED

Theorem eval_clstep_completeness:
  ∀p cid s M l s'.
   clstep p cid s M l s' ⇒ MEM s' (eval_clstep cid p s M)
Proof
  rpt strip_tac >>
  fs [eval_clstep_def] >>
  Cases_on ‘bir_get_stmt p s.bst_pc’ >> (fs [])
  >| [
    (* read *)
    imp_res_tac eval_clstep_read_completeness
    ,
    (* fulfil & xclfail *)
    imp_res_tac eval_clstep_write_completeness >> fs[]
    ,
    (* amofulfil *)
    imp_res_tac eval_clstep_amo_completeness
    ,
    (* expr *)
    imp_res_tac eval_clstep_expr_completeness
    ,
    (* fence *)
    imp_res_tac eval_clstep_fence_completeness
    ,
    (* branch *)
    imp_res_tac eval_clstep_branch_completeness
    ,
    (* generic *)
    imp_res_tac eval_clstep_bir_generic_completeness
    ,
    (* none *)
    fs [clstep_cases]
  ]
QED

Theorem eval_clstep_correctness:
  ∀p cid s M s'.
  MEM s' (eval_clstep cid p s M) = ∃l. clstep p cid s M l s'
Proof
  rpt strip_tac >>
  eq_tac >|
  [
    simp [eval_clstep_soundness]
    ,
    simp [eval_clstep_completeness]
  ]
QED

val _ = export_theory();
