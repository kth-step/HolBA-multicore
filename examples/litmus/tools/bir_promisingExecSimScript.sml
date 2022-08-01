open HolKernel Parse boolLib bossLib BasicProvers;
open bir_promisingTheory bir_promisingExecTheory bir_programTheory;

open listTheory rich_listTheory;
open arithmeticTheory;
open relationTheory;

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

Triviality IS_SOME_EQ_NOT_NONE:
  !x. IS_SOME x <=> x <> NONE
Proof
  Cases_on ‘x’ >> fs[]
QED

Theorem mem_get_SNOC:
  !M l t msg.
  t < SUC (LENGTH M) ==>
  mem_get (SNOC msg M) l t = mem_get M l t
Proof
  Cases_on ‘t’ >- fs [mem_get_def] >>
  fs [mem_get_def, oEL_THM, EL_SNOC]
QED

Theorem mem_get_SNOC2:
  !M l msg.
    mem_get (SNOC msg M) l (SUC (LENGTH M)) =
    if (msg.loc = l) then SOME msg else NONE 
Proof
  fs [mem_get_def, oEL_THM, EL_SNOC2]
QED

Theorem mem_read_correctness:
  !M l t v.
    mem_read M l t = SOME v <=>
    ?m. mem_get M l t = SOME m /\ m.val = v
Proof
  Cases_on ‘t’ >> fs [mem_read_def, mem_get_def, CaseEq"option"]
QED

Theorem mem_is_loc_correctness:
  !M t l.
  mem_is_loc M t l <=> (t = 0 \/
  (t <> 0 /\ PRE t < LENGTH M /\ (EL (PRE t) M).loc = l))
Proof
  Cases_on ‘t’ >- fs [mem_is_loc_def] >>
  fs [mem_is_loc_def, oEL_THM] >>
  rpt gen_tac >>
  Cases_on ‘n < LENGTH M’ >> fs []
QED

Theorem mem_is_loc_mem_get:
  !M t l.
  mem_is_loc M t l <=> (mem_get M l t <> NONE)
Proof
  Cases_on ‘t’ >|
  [
    fs[mem_is_loc_def, mem_get_def]
    ,
    fs [mem_is_loc_def, mem_get_def] >>
    gen_tac >>
    Cases_on ‘oEL n M’ >> fs []
  ]
QED

Theorem mem_is_cid_correctness:
  !M t cid.
  mem_is_cid M t cid <=> (t <> 0 /\ PRE t < LENGTH M /\ (EL (PRE t) M).cid = cid)
Proof
  Cases_on ‘t’ >|
  [
    fs [mem_is_cid_def]
    ,
    fs [mem_is_cid_def, oEL_THM] >>
    rpt gen_tac >>
    Cases_on ‘n < LENGTH M’ >> fs []
  ]
QED

Theorem MEM_ZIP_memory_timestamp:
  ∀m t M.
  MEM (m, t) (ZIP (M, [1 .. LENGTH M])) = (t <> 0 /\ oEL (PRE t) M = SOME m)
Proof
  Cases_on ‘t’ >|
  [
    Induct_on ‘M’ using SNOC_INDUCT >>
    (fs [GENLIST, listRangeTheory.listRangeINC_def, rich_listTheory.ZIP_SNOC])
    ,
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
        fs [EL_SNOC2, EL_SNOC]
        ,
        rpt strip_tac >>
        fs [GSYM ADD1, EL_SNOC2, EL_SNOC] >>
        rename1 ‘t < SUC (LENGTH M)’ >>
        ‘t < LENGTH M \/ t = LENGTH M’ by (fs []) >>
        (fs [EL_SNOC, EL_SNOC2])
      ]
    ]
  ]
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
    (fs [MEM_ZIP_memory_timestamp])
  ]
QED

Theorem mem_filter_thm:
  ∀P M m t.
  MEM (m, t) (mem_filter P M) = (P (m, t) /\ t <> 0 ∧ oEL (PRE t) M = SOME m)
Proof
  fs [MEM_ZIP_memory_timestamp, mem_filter_def, MEM_FILTER]
QED                           

Theorem mem_every_amo:
  !t_r t_w l M.
  mem_every (\ (msg,t'). t_r < t' /\ t' < t_w ==> msg.loc <> l) M
  <=> !t'. t_r < t' /\ t' < t_w ==> ~mem_is_loc M t' l
Proof
  rpt gen_tac >> eq_tac >|
  [
    rpt strip_tac >>
    fs [mem_every_thm, oEL_THM, mem_is_loc_correctness] >>
    Cases_on ‘t'’ >- fs[] >>
    fs [] >>
    res_tac
    ,
    rpt strip_tac >>
    fs [mem_every_thm, oEL_THM] >>
    rpt strip_tac >>
    fs [mem_is_loc_correctness] >>
    res_tac >>
    fs []
  ]
QED

Triviality MEM_MAP2:
  !l f x y.
    MEM (x, y) (MAP f l) <=> ?x' y'. (x, y) = f (x', y') /\ MEM (x', y') l
Proof
  rpt gen_tac >> eq_tac >|
  [
    fs [MEM_MAP] >>
    rpt strip_tac >>
    Cases_on ‘y'’ >>
    Q.EXISTS_TAC ‘q’ >> Q.EXISTS_TAC ‘r’ >>
    fs []
    ,
    fs [MEM_MAP] >>
    rpt strip_tac >>
    Q.EXISTS_TAC ‘(x', y')’  >>
    fs []
  ] 
QED

Triviality EXISTS_MEM2:
  !P l.
    EXISTS P l <=> ?x y. MEM (x, y) l /\ P (x, y)
Proof
  fs [EXISTS_MEM] >>
  rpt gen_tac >> eq_tac >-
   (rpt strip_tac >>
    Cases_on ‘e’ >> METIS_TAC []) >>
  METIS_TAC []
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

Theorem mem_get_correctness:
  !M l t m.
  mem_get M l t = SOME m <=>
  ((t = 0 /\ m = mem_default l)
  \/
  (t <> 0 /\ oEL (PRE t) M = SOME m /\ m.loc = l))
Proof
  Cases_on ‘t’ >- fs [mem_get_def, EQ_SYM_EQ] >>
  fs [mem_get_def, CaseEq"option"]
QED
  
Triviality IS_SOME_mem_get_0_thm:
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
      fs [mem_is_loc_correctness, mem_is_cid_correctness, oEL_THM]
    ]
    ,
    rpt strip_tac >>
    rename1 ‘t_r < SUC t’ >>
    ‘mem_is_loc M (SUC t) l’ by (fs [mem_is_loc_correctness, oEL_THM]) >>
    ‘mem_is_cid M (SUC t) cid’ by (fs [mem_is_cid_correctness, oEL_THM]) >>
    LAST_X_ASSUM drule >>
    gs [mem_is_cid_correctness, oEL_THM]
  ]
QED


Theorem MEM_readable_thm:
  ∀m_t M v_max l.
  MEM m_t (mem_readable M l v_max)
  = (mem_get M l (SND m_t) = SOME (FST m_t) ∧
     ∀t'. (SND m_t) < t' ∧ t' ≤ v_max ⇒ ~mem_is_loc M t' l)
Proof
  tmCases_on “m_t” ["m t"] >>
  fs [] >>
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
        fs [mem_is_loc_correctness, oEL_THM] >>
        FIRST_X_ASSUM drule >>
        fs []
      ]
      ,
      Cases_on ‘t’ >|
      [
        fs [MEM, mem_filter_def, MEM_ZIP_memory_timestamp, MEM_FILTER]
        ,
        fs [mem_filter_thm, mem_get_def]
      ]
      ,
      Cases_on ‘t'’ >|
      [
        fs []
        ,
        fs [mem_is_loc_correctness, oEL_THM] >>
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
      fs [mem_is_loc_correctness, oEL_THM]
      ,
      Cases_on ‘t’ >|
      [
        fs [mem_get_def]
        ,
        fs [mem_get_correctness, mem_filter_thm]
      ]
    ]
  ]
QED

(*
 ***********************************************************
 * Soundness proof of executable core-local step
 ************************************************************)

Theorem eval_clstep_read_soundness:
  ∀p cid M s s' var e acq rel xcl cast l.
  MEM (l, s') (eval_clstep_read s M var e acq rel xcl) ==>
  bir_get_stmt p s.bst_pc = BirStmt_Read var e cast acq rel xcl ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_read_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp e s.bst_environ’ >- (fs [CaseEq"option"]) >>
  fs [CaseEq"option"] >>
  fs [MEM_MAP_PARTIAL, MEM_MAP] >>
  rename1 ‘MEM msg_t (mem_readable M loc _)’ >> tmCases_on “msg_t” ["msg t"] >>
  fs [MEM_readable_thm] >>
  fs [clstep_cases, bir_state_t_component_equality, bir_eval_exp_view_def] >>
  imp_res_tac mem_get_mem_read >>
  Q.EXISTS_TAC ‘msg.val’ >> Q.EXISTS_TAC ‘t’ >>
  fs [MAXL_def, ifView_def, combinTheory.UPDATE_def] >>
  Cases_on ‘xcl’ >> Cases_on ‘acq’ >> Cases_on ‘rel’ >>
  (rfs [] >> METIS_TAC [MAX_COMM, MAX_ASSOC])
QED                                   

Theorem eval_clstep_fulfil_soundness:
  ∀p s s' a_e v_e xcl acq rel cid M l.
  bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ==>
  MEM (l, s') (eval_clstep_fulfil p cid s M a_e v_e xcl acq rel) ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_fulfil_def, bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp a_e s.bst_environ” ["", "loc"] >> fs[] >>
  tmCases_on “bir_eval_exp v_e s.bst_environ” ["", "val"] >> fs[] >>
  fs [MEM_MAP_PARTIAL, MEM_MAP, MEM_FILTER] >>
  tmCases_on “fulfil_update_env p s xcl” ["", "new_env"] >> fs [] >>
  tmCases_on “fulfil_update_viewenv p s xcl v_post” ["", "new_viewenv"] >> fs [] >>
  fs [clstep_cases, bir_eval_exp_view_def, bir_state_t_component_equality, combinTheory.UPDATE_def, mem_atomic_correctness, MAXL_def, ifView_def, IS_SOME_EQ_NOT_NONE] >>
  Cases_on ‘xcl’ >> Cases_on ‘acq’ >> Cases_on ‘rel’ >> fs [] >> METIS_TAC [MAX_COMM]
QED

Theorem eval_clstep_xclfail_soundness:
  ∀p s s' a_e v_e xcl acq rel cid M l.
  bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ==>
  MEM (l, s') (eval_clstep_xclfail p cid s xcl) ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  Cases_on ‘xcl’ >|
  [
    fs [eval_clstep_xclfail_def, clstep_cases] >>
    Cases_on ‘xclfail_update_env p s’ >- (fs []) >>
    Cases_on ‘xclfail_update_viewenv p s’ >- (fs []) >>
    rpt strip_tac >>
    fs [bir_state_t_component_equality]
    ,
    fs [eval_clstep_xclfail_def]
  ]
QED

Theorem eval_clstep_amofulfil_soundness:
  ∀p s var a_e v_e acq rel s' cid M l.
  MEM (l, s') (eval_clstep_amofulfil cid s M var a_e v_e acq rel) ==>
  bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_amofulfil_def, bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp a_e s.bst_environ” ["", "loc"] >> fs [] >>
  fs [LIST_BIND_def, MEM_FLAT] >>
  rename1 ‘MEM (l, s') state_list’ >>
  fs [MEM_MAP] >>
  rename1 ‘MEM x (mem_readable M loc _)’ >> tmCases_on “x” ["m_r t_r"] >>
  fs [MEM_readable_thm] >>
  Cases_on ‘env_update_cast64 (bir_var_name var) m_r.val (bir_var_type var) s.bst_environ’ >- (gs []) >>
  rename1 ‘SOME new_environ’ >>
  fs [bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp v_e new_environ” ["", "v"] >- rfs [] >>
  rfs [] >>
  fs [MEM_MAP, MEM_FILTER] >>
  fs [clstep_cases, bir_state_t_component_equality, combinTheory.UPDATE_def, MAXL_def, ifView_def, bir_eval_exp_view_def, mem_every_amo] >>
  imp_res_tac mem_get_mem_read >>
  Q.EXISTS_TAC ‘m_r.val’ >> Q.EXISTS_TAC ‘t_r’ >>
  Cases_on ‘acq’ >> Cases_on ‘rel’ >> fs []
QED

Theorem eval_clstep_expr_soundness:
  ∀p cid M s s' var e l.
  MEM (l, s') (eval_clstep_exp s var e) ==>
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_exp_def] >>
  rpt (FULL_CASE_TAC >> fs [bir_get_stmt_expr])
QED                                              

Theorem eval_clstep_fence_soundness:
  ∀p cid M s s' K1 K2 l.
  bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2 ==>
  MEM (l, s') (eval_clstep_fence s K1 K2) ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_fence_def, bir_state_t_component_equality] >>
  rpt FULL_CASE_TAC >>
  (fs [] >> METIS_TAC [MAX_COMM])
QED

Theorem eval_clstep_branch_soundness:
  ∀p cid M s s' cond_e lbl1 lbl2 l.
  bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2 ==>
  MEM (l,s') (eval_clstep_branch p s cond_e lbl1 lbl2) ==>
  clstep p cid s M l s'
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
  ∀p cid M s s' stmt l.
  bir_get_stmt p s.bst_pc = BirStmt_Generic stmt ==>
  MEM (l,s') (eval_clstep_bir_step p s stmt) ==>
  clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_bir_step_def, bir_state_t_component_equality] >>
  Cases_on ‘bir_exec_stmt p stmt s’ >>
  fs []
QED

Theorem eval_clstep_soundness:
  ∀p cid M s s' l.
  MEM (l,s') (eval_clstep cid p s M) ==>
  clstep p cid s M l s'
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
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Read var a_e cast xcl acq rel ==>
  MEM (l,s') (eval_clstep_read s M var a_e xcl acq rel)
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
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel ==>
  MEM (l,s') (eval_clstep_fulfil p cid s M a_e v_e xcl acq rel ++ eval_clstep_xclfail p cid s xcl)
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
    fs [mem_atomic_correctness, IS_SOME_EQ_NOT_NONE] >>
    (rpt FULL_CASE_TAC >> fs[] >>
     METIS_TAC [MAX_ASSOC, MAX_COMM])
  ] 
QED

Theorem eval_clstep_amo_completeness:
  ∀p s var a_e v_e acq rel s' cid M l.
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel ==>
  MEM (l,s') (eval_clstep_amofulfil cid s M var a_e v_e acq rel)
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_amofulfil_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- fs [] >>
  fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
  CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) >>
  CONV_TAC SWAP_EXISTS_CONV >>
  fs [mem_read_correctness] >>
  Q.EXISTS_TAC ‘(m, t_r)’ >>
  fs [MEM_readable_thm] >>
  Cases_on ‘env_update_cast64 (bir_var_name var) v_r (bir_var_type var) s.bst_environ’ >- fs [] >>
  Cases_on ‘bir_eval_exp v_e new_environ’ >- fs [] >>
  gvs [MEM_FILTER, MEM_MAP] >>
  fs [bir_state_t_component_equality, mem_every_amo] >>
  fs [MAXL_def, ifView_def] >>
  Cases_on ‘acq’ >> Cases_on ‘rel’ >> fs[]
QED                                              

Theorem eval_clstep_expr_completeness:
  ∀p cid M s s' var e l.
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e ==>
  MEM (l, s') (eval_clstep_exp s var e)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_exp_def, bir_eval_exp_view_def] >>
  CASE_TAC >- fs [] >>
  CASE_TAC >- fs [] >>
  fs [combinTheory.UPDATE_def, bir_state_t_component_equality, MAX_COMM]
QED

Theorem eval_clstep_fence_completeness:
  ∀p cid M s s' K1 K2 l.
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2 ==>
  MEM (l, s') (eval_clstep_fence s K1 K2)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_fence_def, bir_eval_exp_view_def] >>
  fs [combinTheory.UPDATE_def, bir_state_t_component_equality, MAX_COMM]
QED

Theorem eval_clstep_branch_completeness:
  ∀p cid M s s' cond_e lbl1 lbl2 l.
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2 ==>
  MEM (l,s') (eval_clstep_branch p s cond_e lbl1 lbl2)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_branch_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp cond_e s.bst_environ’ >> (fs [])
QED

Theorem eval_clstep_bir_generic_completeness:
  ∀p cid M s s' stmt l.
  clstep p cid s M l s' ==>
  bir_get_stmt p s.bst_pc = BirStmt_Generic stmt ==>
  MEM (l,s') (eval_clstep_bir_step p s stmt)
Proof
  rpt strip_tac >>
  gvs [clstep_cases, eval_clstep_bir_step_def]
QED

Theorem eval_clstep_completeness:
  ∀p cid s M s' l.
   clstep p cid s M l s' ⇒ MEM (l,s') (eval_clstep cid p s M)
Proof
  rpt strip_tac >>
  fs [eval_clstep_def] >>
  Cases_on ‘bir_get_stmt p s.bst_pc’ >> (fs []) >|
  [
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
  ∀p cid s M s' l.
  MEM (l,s') (eval_clstep cid p s M) = clstep p cid s M l s'
Proof
  rpt strip_tac >>
  eq_tac >|
  [
    simp [eval_clstep_soundness]
    ,
    simp [eval_clstep_completeness]
  ]
QED

Definition cstep_seq_rtc_f_def:
  (cstep_seq_rtc_f 0 p cid (s,M) (s',M') <=> (s = s' /\ M = M'))
  /\
  (cstep_seq_rtc_f (SUC f) p cid (s,M) (s',M') <=>
  ((s = s' /\ M = M') \/
   ?s'' M''. cstep_seq p cid (s,M) (s'',M'') /\ cstep_seq_rtc_f f p cid (s'',M'') (s',M')))
End

(* Fueled version of is_certified *)
Definition is_certified_f_def:
  is_certified_f f p cid s M <=>
   ?s' M'. cstep_seq_rtc_f f p cid (s, M) (s', M') /\ s'.bst_prom = []
End

Triviality NULL_prom_is_certified_triv:
  !p cid s M.
  s.bst_prom = [] ==> is_certified p cid s M
Proof
  rw [is_certified_def] >>
  Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘M’ >>
  fs [cstep_seq_rtc_def]
QED  

Theorem cstep_seq_rtc_f_soundness_thm:
  !f cid p s M s' M'.
    cstep_seq_rtc_f f p cid (s,M) (s', M') ==>
    cstep_seq_rtc p cid (s,M) (s',M')
Proof
  Induct_on ‘f’ >|
  [
    fs [cstep_seq_rtc_def, cstep_seq_rtc_f_def]
    ,
    simp [cstep_seq_rtc_def, Once RTC_CASES1] >>
    simp [cstep_seq_rtc_f_def] >>
    rpt strip_tac >|
    [
      fs []
      ,
      DISJ2_TAC >>
      Q.EXISTS_TAC ‘(s'', M'')’ >>
      res_tac >>
      fs [cstep_seq_rtc_def]
    ]
  ]
QED

Theorem cstep_seq_rtc_f_completeness_thm:
  !cid p s M s' M'.
    cstep_seq_rtc p cid (s,M) (s',M') ==>
    ?f. cstep_seq_rtc_f f p cid (s,M) (s', M')
Proof
  rpt gen_tac >>
  qabbrev_tac ‘sM = (s, M)’ >> qabbrev_tac ‘sM' = (s', M')’ >>
  qid_spec_tac ‘sM'’ >> qid_spec_tac ‘sM’ >>
  fs [Abbr ‘sM’, Abbr ‘sM'’] >>
  fs [cstep_seq_rtc_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >|
  [
    Q.EXISTS_TAC ‘0’ >>
    Cases_on ‘sM’ >>
    fs [cstep_seq_rtc_f_def]
    ,
    Cases_on ‘sM’ >> Cases_on ‘sM'’ >> Cases_on ‘sM''’ >>
    Q.EXISTS_TAC ‘SUC f’ >>
    simp [cstep_seq_rtc_f_def] >>
    DISJ2_TAC >>
    rename1 ‘cstep_seq p cid (s,M) (s', M')’ >>
    Q.EXISTS_TAC ‘s'’ >> Q.EXISTS_TAC ‘M'’ >>
    fs []
  ]  
QED

Theorem cstep_seq_rtc_f_correctness_thm:
  !cid p s M s' M'.
    (?f. cstep_seq_rtc_f f p cid (s,M) (s', M')) <=>
    cstep_seq_rtc p cid (s,M) (s',M')
Proof
  rpt gen_tac >> eq_tac >>
  simp [cstep_seq_rtc_f_completeness_thm, cstep_seq_rtc_f_soundness_thm]
QED

Theorem is_certified_f_correctness_thm:
  !cid p s M.
  (?f. is_certified_f f p cid s M) <=> is_certified p cid s M
Proof
  METIS_TAC [cstep_seq_rtc_f_correctness_thm, is_certified_f_def, is_certified_def]
QED

Theorem eval_cstep_seq_write_soundness:
  !cid p s M s' M' a_e v_e xcl acq rel msgs.
  MEM (s', msgs) (eval_cstep_seq cid p s M) ==>
  bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel
  ==>
  cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  (* Decompose assumptions *)
  gvs [eval_cstep_seq_def, eval_cstep_seq_write_def, bir_eval_exp_view_def] >|
  [
    Cases_on ‘bir_eval_exp v_e s.bst_environ’ >- fs[] >>
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- fs[] >>
    fs [MEM_MAP, MEM_FILTER] >>
    rename1 ‘(s', msgs) = _ smsgs’ >> Cases_on ‘smsgs’ >>
    ‘bir_get_stmt p (s with bst_prom updated_by SNOC (SUC (LENGTH M))).bst_pc = BirStmt_Write a_e v_e xcl acq rel’ by
      fs [] >>
    imp_res_tac eval_clstep_fulfil_soundness >>
    fs [cstep_seq_cases] >>
    Q.EXISTS_TAC ‘s with bst_prom updated_by SNOC (SUC (LENGTH M))’ >>
    Q.EXISTS_TAC ‘SUC (LENGTH M)’ >>
    gvs [SNOC_APPEND, cstep_cases, bir_state_t_component_equality]
    ,
    fs [MEM_MAP2, cstep_seq_cases] >>
    imp_res_tac eval_clstep_fulfil_soundness >>
    HINT_EXISTS_TAC >>
    fs []
    ,
    fs [MEM_MAP2, cstep_seq_cases] >>
    imp_res_tac eval_clstep_xclfail_soundness >>
    rename1 ‘MEM (l, s') _’ >>
    Q.EXISTS_TAC ‘l’ >>
    fs []
  ]   
QED

Theorem eval_cstep_seq_amowrite_soundness:
  !cid p s M s' M' var a_e v_e acq rel msgs.
  MEM (s', msgs) (eval_cstep_seq cid p s M) ==>
  bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel ==>
  cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  (* Decompose assumptions *)
  gvs [eval_cstep_seq_def, MEM_MAP2, eval_cstep_seq_amowrite_def, bir_eval_exp_view_def] >|
  [
    tmCases_on “bir_eval_exp a_e s.bst_environ” ["","a"] >- fs[] >>
    fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
    rename1 ‘MEM m_t_r (mem_readable _ _ _)’ >>
    tmCases_on “m_t_r” ["m t_r"] >>
    fs [MEM_readable_thm] >>
    tmCases_on “env_update_cast64 (bir_var_name var) m.val (bir_var_type var) s.bst_environ” ["","new_environ"] >- rfs [] >>
    tmCases_on “bir_eval_exp v_e new_environ” ["","v"] >- gvs [] >>
    gvs [MEM_MAP2, MEM_FILTER] >>
    imp_res_tac eval_clstep_amofulfil_soundness >>
    fs [cstep_seq_cases] >>
    Q.EXISTS_TAC ‘s with bst_prom updated_by SNOC (SUC (LENGTH M))’ >>
    Q.EXISTS_TAC ‘SUC (LENGTH M)’ >>
    CONJ_TAC >|
    [
      fs [cstep_cases, bir_state_t_component_equality]
      ,
      gvs []
    ]
    ,
    fs [cstep_seq_cases] >>
    imp_res_tac eval_clstep_amofulfil_soundness >>
    HINT_EXISTS_TAC >>
    fs []
  ]
QED

Theorem eval_cstep_seq_soundness:
  !cid p s M s' msgs.
  MEM (s', msgs) (eval_cstep_seq cid p s M)
  ==>
  cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  Cases_on ‘bir_get_stmt p s.bst_pc’ >|
  [
    gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
    rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
    fs [eval_clstep_read_soundness]
    ,
    imp_res_tac eval_cstep_seq_write_soundness
    ,
    imp_res_tac eval_cstep_seq_amowrite_soundness
    ,
    gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
    rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
    fs [eval_clstep_expr_soundness]
    ,
    gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
    rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
    fs [eval_clstep_fence_soundness]
    ,
    gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
    rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
    fs [eval_clstep_branch_soundness]
    , 
    gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
    rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
    fs [eval_clstep_generic_soundness]
    ,
    fs [eval_cstep_seq_def]
  ]
QED

Theorem eval_cstep_seq_write_completeness:
  !cid p s M s' a_e v_e xcl acq rel msgs.
    (cstep_seq p cid (s,M) (s',M ++ msgs)) ==>
    (bir_get_stmt p s.bst_pc = BirStmt_Write a_e v_e xcl acq rel) ==>
    MEM (s', msgs) (eval_cstep_seq cid p s M)
Proof
  rpt strip_tac >>
  fs [cstep_seq_cases, MEM_MAP2] >|
  [
    imp_res_tac eval_clstep_write_completeness >>
    fs [eval_cstep_seq_def] >|
    [
      DISJ1_TAC >> DISJ2_TAC >>
      fs [MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      DISJ2_TAC >>
      fs [MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
    ] 
    ,
    fs [eval_cstep_seq_def] >>
    DISJ1_TAC >> DISJ1_TAC >>
    fs [cstep_cases] >>
    fs [eval_cstep_seq_write_def, bir_eval_exp_view_def] >>
    Cases_on ‘bir_eval_exp v_e s.bst_environ’ >- gvs [bir_eval_exp_view_def, clstep_cases] >>
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- gvs [bir_eval_exp_view_def, clstep_cases] >>
    rename1 ‘bir_eval_exp v_e s.bst_environ = SOME v’ >>
    rename1 ‘bir_eval_exp a_e s.bst_environ = SOME l’ >>
    fs [MEM_MAP2, MEM_FILTER] >>
    imp_res_tac eval_clstep_write_completeness >>
    gvs [bir_state_t_accfupds] >|
    [
      ‘<| loc := l; val := v; cid := msg.cid |> = msg’ by
       (gvs [clstep_cases, bir_eval_exp_view_def, GSYM ADD1, GSYM SNOC_APPEND, mem_get_SNOC2]) >>
      ‘(\pr. pr ++ [LENGTH M + 1]) = SNOC (SUC (LENGTH M))’ by
        METIS_TAC [ADD1, GSYM SNOC_APPEND] >>
      gvs [GSYM ADD1, GSYM SNOC_APPEND]
      ,
      Cases_on ‘xcl’ >|
      [
        fs [eval_clstep_xclfail_def] >>
        Cases_on ‘xclfail_update_env p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))’ >- fs[] >>
        Cases_on ‘xclfail_update_viewenv p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))’ >- fs[] >>
        fs []
        ,
        fs [eval_clstep_xclfail_def]
      ]
    ]
  ]
QED
  

Theorem eval_cstep_seq_amowrite_completeness:
  !cid p s M s' M a_e v_e xcl acq rel var msgs.
    (cstep_seq p cid (s,M) (s',M ++ msgs)) ==>
    (bir_get_stmt p s.bst_pc = BirStmt_Amo var a_e v_e acq rel) ==>
    MEM (s', msgs) (eval_cstep_seq cid p s M)
Proof
  rpt strip_tac >>
  fs [cstep_seq_cases, MEM_MAP2] >|
  [
    imp_res_tac eval_clstep_amo_completeness >>
    fs [eval_cstep_seq_def] >>
    DISJ2_TAC >>
    fs [MEM_MAP2] >>
    Q.EXISTS_TAC ‘prom’ >>
    fs []
    ,
    fs [cstep_cases] >>
    ‘bir_get_stmt p (s''').bst_pc = BirStmt_Amo var a_e v_e acq rel’ by fs [] >>
    imp_res_tac eval_clstep_amo_completeness >>
    fs [eval_cstep_seq_def] >>
    DISJ1_TAC >>
    fs [eval_cstep_seq_amowrite_def, bir_eval_exp_view_def] >>
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- gvs [clstep_cases, bir_eval_exp_view_def] >>
    fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
    CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) >>
    CONV_TAC SWAP_EXISTS_CONV >>
    fs [clstep_cases, bir_eval_exp_view_def] >>
    Q.EXISTS_TAC ‘(THE (mem_get (M ++ msgs) l t_r), t_r)’ >>
    fs [MEM_readable_thm] >>
    gvs [mem_read_correctness] >>
    fs [mem_get_SNOC, Once (GSYM SNOC_APPEND)] >>
    Cases_on ‘env_update_cast64 (bir_var_name var) m.val (bir_var_type var) s.bst_environ’ >- fs[] >>
    Cases_on ‘bir_eval_exp v_e new_environ’ >- gvs [] >>
    gvs [MEM_MAP2, MEM_FILTER] >>
    ‘(\pr. pr ++ [LENGTH M + 1]) = SNOC (SUC (LENGTH M))’ by
      METIS_TAC [ADD1, GSYM SNOC_APPEND] >>
    ‘<| loc := l; val := v_w; cid := msg.cid |> = msg’ by
       (gvs [GSYM ADD1, GSYM SNOC_APPEND, mem_get_SNOC2]) >>
    gvs [SNOC_APPEND, ADD1] >>
    fs [MAXL_def, ifView_def] >>
    strip_tac  >> strip_tac >>
    (‘t' < LENGTH M + 1’ by (Cases_on ‘acq’ >> Cases_on ‘rel’ >> fs []) >>
     fs [mem_is_loc_mem_get, GSYM SNOC_APPEND, mem_get_SNOC])
  ]
QED


Theorem eval_cstep_seq_completeness:
  !cid p s M s' msgs.
  cstep_seq p cid (s, M) (s', M ++ msgs) ==> MEM (s', msgs) (eval_cstep_seq cid p s M)
Proof
  rpt strip_tac >>
  Cases_on ‘bir_get_stmt p s.bst_pc’ >|
  [
    fs [cstep_seq_cases] >|
    [
      imp_res_tac eval_clstep_read_completeness >>
      fs [eval_cstep_seq_def, MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
    ,
    imp_res_tac eval_cstep_seq_write_completeness
    ,

    imp_res_tac eval_cstep_seq_amowrite_completeness
    ,
    fs [cstep_seq_cases] >|
    [
      imp_res_tac eval_clstep_expr_completeness >>
      fs [eval_cstep_seq_def, MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
    ,
    fs [cstep_seq_cases] >|
    [
      imp_res_tac eval_clstep_fence_completeness >>
      fs [eval_cstep_seq_def, MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
    ,
    fs [cstep_seq_cases] >|
    [
      imp_res_tac eval_clstep_branch_completeness >>
      fs [eval_cstep_seq_def, MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
    ,
    fs [cstep_seq_cases] >|
    [
      imp_res_tac eval_clstep_bir_generic_completeness >>
      fs [eval_cstep_seq_def, MEM_MAP2] >>
      Q.EXISTS_TAC ‘prom’ >>
      fs []
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
    ,
    fs [cstep_seq_cases] >|
    [
      fs [clstep_cases]
      ,
      gvs [cstep_cases, clstep_cases, bir_state_t_component_equality]
    ]
  ] 
QED

Theorem eval_cstep_seq_correctness:
  !cid p s M s' msgs.
    MEM (s', msgs) (eval_cstep_seq cid p s M) <=> cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt gen_tac >> eq_tac >> fs [eval_cstep_seq_soundness, eval_cstep_seq_completeness]
QED

Theorem cstep_seq_Msuffix:
  !p cid s M s' M'.
  cstep_seq p cid (s,M) (s', M') ==>
  ?suffix. M ++ suffix = M'
Proof
  fs [cstep_seq_cases, cstep_cases] >>
  rpt strip_tac >> (fs [cstep_cases])
QED
  

Theorem eval_is_certified_correctness:
  !f cid p s M.
     eval_is_certified f p cid s M <=> is_certified_f f p cid s M
Proof
  Induct_on ‘f’ >|
  [
    fs [eval_is_certified_def, is_certified_f_def, cstep_seq_rtc_f_def]
    ,
    fs [eval_is_certified_def, is_certified_f_def, EXISTS_MEM2, eval_cstep_seq_correctness] >>
    rpt gen_tac >> eq_tac >|
    [
      rpt strip_tac >|
      [
        Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘M’ >>
        fs [cstep_seq_rtc_f_def]
        ,
        Q.EXISTS_TAC ‘s'’ >> Q.EXISTS_TAC ‘M'’ >>
        fs [cstep_seq_rtc_f_def] >>
        DISJ2_TAC >>
        rename1 ‘cstep_seq p cid (s,M) (s'', M'')’ >>
        Q.EXISTS_TAC ‘s''’ >> Q.EXISTS_TAC ‘M''’ >>
        fs []
      ]
      ,
      rpt strip_tac >> 
      fs [cstep_seq_rtc_f_def] >>
      DISJ2_TAC >>
      imp_res_tac cstep_seq_Msuffix >>
      Q.EXISTS_TAC ‘s''’ >> Q.EXISTS_TAC ‘suffix’ >>
      fs [] >>
      rpt HINT_EXISTS_TAC >>
      fs []
    ]
  ]
QED

val _ = export_theory();
