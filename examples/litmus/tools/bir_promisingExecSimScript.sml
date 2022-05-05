open HolKernel Parse boolLib bossLib;
open bir_promisingTheory bir_promisingExecScript bir_programTheory;
open listTheory arithmeticTheory;
open bir_expTheory;
open numeralTheory arithmeticTheory;
open pred_setTheory;
open BasicProvers listRangeTheory;
open rich_listTheory;
open prim_recTheory

val _ = new_theory "bir_promisingExecSim";

Theorem MAXL_LE:
  ∀xs y.
  MAXL xs ≤ y ⇔ EVERY (\x. x ≤ y) xs
Proof
  cheat
QED

Triviality EL_SNOC2:
  ∀x l.
    EL (LENGTH l) (SNOC x l) = x
Proof
  Induct_on ‘l’ >>
  (asm_rewrite_tac [LENGTH, SNOC, EL, HD, TL])
QED

Triviality zip_memory_ts:
  ∀m t M.
  MEM (m, t) (ZIP (M, [1 .. LENGTH M])) = (t ≠ 0 ∧ oEL (PRE t)  M = SOME m)
Proof
  Induct_on ‘M’ using SNOC_INDUCT >|
  [
    fs [listRangeINC_def, oEL_def]
    ,
    fs [GENLIST, listRangeINC_def, ZIP_SNOC, oEL_THM] >>
    rpt gen_tac >>
    eq_tac >|
    [
      rpt strip_tac >>
      (fs [LESS_THM, EL_SNOC2, GSYM ADD1, EL_SNOC])
      ,
      rpt strip_tac >>
      gvs [oEL_THM, LESS_THM, EL_SNOC, EL_SNOC2]
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
  mem_every P M = ∀m t. t ≠ 0 ∧ oEL (PRE t) M = SOME m ⇒ P (m, t)
Proof
  rpt gen_tac >>
  eq_tac >|
  [
    Induct_on ‘M’ using SNOC_INDUCT >|
    [
      fs [mem_every_def, oEL_THM, listRangeINC_def]
      ,
      fs [mem_every_def, oEL_THM, listRangeINC_def, ZIP_SNOC, GENLIST, EVERY_SNOC] >>
      rpt strip_tac >>
      fs [LESS_THM] >|
      [
        Cases_on ‘t’ >>
        (fs [GSYM ADD1, EL_SNOC, EL_SNOC2])
        ,
        fs [EL_SNOC]
      ]
    ]
    ,
    rpt strip_tac >>
    fs [mem_every_def, EVERY_MEM] >>
    gen_tac >>
    Cases_on ‘e’ >> rename1 ‘P (x, t)’ >>
    Cases_on ‘t’ >> (fs[zip_memory_ts])
  ]
QED

Theorem MEM_LIST_BIND:
  ∀e f ll.
  MEM e (LIST_BIND ll f) ⇔ EXISTS (\l. MEM e (f l)) ll 
Proof
  Induct_on ‘ll’ >> (fs [])
QED

Theorem mem_filter_thm:
∀P M m t.
  MEM (m, t) (mem_filter P M) = (P (m, t) ∧ t ≠ 0 ∧ oEL (PRE t) M = SOME m)
Proof
  fs [mem_filter_def, MEM_FILTER, zip_memory_ts]
QED                           

                              open optionTheory;
Theorem mem_get_SOME_thm:
  ∀M l t m.
    mem_get M l t = SOME m ⇔ ((t = 0 ∧ m = mem_default l) ∨ (t ≠ 0 ∧ oEL (PRE t) M = SOME m ∧ m.loc = l))
Proof
  rpt gen_tac >>
  Cases_on ‘t’ >|
  [
    fs [mem_get_def, EQ_SYM_EQ]
    ,
    fs [mem_get_def, CaseEq"option"]
  ]
QED

Theorem mem_get_NONE_thm:
  ∀M l t.
    mem_get M l t = NONE ⇔ (t > LENGTH M ∨ (t ≠ 0 ∧ t ≤ LENGTH M ∧ (EL (PRE t) M).loc ≠ l))
Proof
  rpt gen_tac >>
  Cases_on ‘t’ >|
  [
    fs [mem_get_def]
    ,
    eq_tac >|
    [
      rpt strip_tac >>
      gvs [mem_get_def, oEL_THM, CaseEq"option"]
      ,
      rpt strip_tac >|
      [
        fs [mem_get_def, CaseEq"option", oEL_THM]
        ,
        fs [mem_get_def, CaseEq"option", oEL_THM]
      ]
    ]
  ]
QED

Theorem MEM_readable_thm:
  ∀m t M v_max l.
    MEM (m, t) (mem_readable M l v_max)
    = (mem_get M l t = SOME m ∧
       ∀t'. t < t' ∧ t' ≤ v_max ⇒ mem_get M l t' = NONE)
Proof
  rpt strip_tac >>
  eq_tac >|
  [ (* soundness *)
    rewrite_tac [mem_readable_def, MEM_FILTER] >>
    rpt strip_tac >|
    [
      Cases_on ‘t’ >>
      (fs [mem_get_SOME_thm, mem_filter_thm])
      ,
      fs [mem_get_NONE_thm, mem_every_thm, oEL_THM] >>
      (Cases_on ‘t' > LENGTH M’ >|
      [
        fs []
        ,
        fs [NOT_GREATER]
      ])
    ]
    , (* completeness *)
    rewrite_tac [mem_readable_def, MEM_FILTER, MEM] >>
    rpt strip_tac >|
    [
      fs [mem_every_thm] >>
      rpt strip_tac >>
      first_x_assum drule >>
      fs [oEL_THM, mem_get_NONE_thm]
      ,
      fs [mem_every_thm, mem_filter_thm] >>
      Cases_on ‘t’ >>
      (fs [mem_default_def, mem_get_def, CaseEq"option"])
    ]
  ]
QED

Theorem MEM_MAP_PARTIAL2:
∀x f l.
  MEM x (MAP_PARTIAL f l)
  ⇔
  ∃x'. SOME x = f x' ∧ MEM x' l
Proof
  fs [MEM_MAP_PARTIAL, MEM_MAP]
QED

Theorem mem_read_get:
  ∀M l t.
    mem_read M l t =
    case mem_get M l t of
    | SOME msg => SOME msg.val
    | NONE => NONE
Proof
  Cases_on ‘t’ >|
  [
    fs [mem_read_def, mem_get_def, mem_default_def, mem_default_value_def]
    ,
    fs [mem_read_def, mem_get_def]
    rpt gen_tac >> CASE_TAC >|
    [
      fs [mem_read_aux_def, mem_read_def, mem_get_def]
      ,
      fs [mem_read_def, mem_read_aux_def] >>
      CASE_TAC
    ]
  ]
QED
                   


Theorem eval_clstep_read_soundness:
  ∀p cid M s s' var e acq rel xcl cast.
  bir_get_stmt p s.bst_pc = BirStmt_Read var e cast acq rel xcl ⇒
  MEM s' (eval_clstep_read s M var e acq rel xcl) ⇒ clstep p cid s M [] s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_read_def, bir_state_t_component_equality, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp e s.bst_environ’ >|
  [
    (* SOME l = NONE *)
    fs [CaseEq"option"]
    ,
    (* SOME l = SOME x *)
    fs [CaseEq"option"] >>
    (* MEM s' (MAP_PARTIAL (λ(msg,t). state option) (mem_readable M x (MAX ...)) *)
    fs [MEM_MAP_PARTIAL2] >>
    rename1 ‘MEM x' (mem_readable _ _ _)’ >>
    Cases_on ‘x'’ >>
    fs [MEM_readable_thm] >>
    rename1 ‘mem_get M l t = SOME msg’ >>
    Q.EXISTS_TAC ‘msg.val’ >> Q.EXISTS_TAC ‘t’ >>
    fs [mem_read_def]


QED                                   


Theorem eval_clstep_expr_soundness:
  ∀p cid M s s' var e.
  bir_get_stmt p s.bst_pc = BirStmt_Expr var e ⇒
  MEM s' (eval_clstep_exp s var e) ⇒ clstep p cid s M [] s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_exp_def] >>
  rpt (FULL_CASE_TAC >> fs [bir_get_stmt_expr])
QED                                              

Theorem eval_clstep_fence_soundness:
  ∀p cid M s s' K1 K2.
  bir_get_stmt p s.bst_pc = BirStmt_Fence K1 K2 ⇒
  MEM s' (eval_clstep_fence s K1 K2) ⇒ clstep p cid s M [] s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_fence_def, bir_state_t_component_equality] >>
  rpt FULL_CASE_TAC >>
  (fs [] >> METIS_TAC [MAX_COMM])
QED

Theorem eval_clstep_branch_soundness:
  ∀p cid M s s' cond_e lbl1 lbl2.
  bir_get_stmt p s.bst_pc = BirStmt_Branch cond_e lbl1 lbl2 ⇒
  MEM s' (eval_clstep_branch p s cond_e lbl1 lbl2) ⇒ clstep p cid s M [] s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_branch_def, bir_state_t_component_equality] >>
  Cases_on ‘bir_exec_stmt p (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) s’ >>
  Cases_on ‘bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv’ >>
  fs [] >>
  FULL_CASE_TAC >>
  (fs [])
QED

Theorem eval_clstep_bir_step_soundness:
  ∀p cid M s s' stmt.
  bir_get_stmt p s.bst_pc = BirStmt_Generic stmt ⇒
  MEM s' (eval_clstep_bir_step p s stmt) ⇒ clstep p cid s M [] s'
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
  rpt strip_tac >>
  fs [eval_clstep_def] >>
  Cases_on ‘bir_get_stmt p s.bst_pc’ >> (fs []) >|
  [
    (* read *)
    Q.EXISTS_TAC ‘[]’ >>
    fs [eval_clstep_read_soundness]
    ,
    (* fulfil *)
    cheat
    ,
    (* xclfail *)
    cheat
    ,
    (* amofulfil *)
    cheat
    ,
    (* expr *)
    Q.EXISTS_TAC ‘[]’ >>
    fs [eval_clstep_expr_soundness]
    ,
    (* fence *)
    Q.EXISTS_TAC ‘[]’ >>
    fs [eval_clstep_fence_soundness]
    ,
    (* branch *)
    Q.EXISTS_TAC ‘[]’ >>
    fs [eval_clstep_branch_soundness]
    ,
    (* bir_step *)
    Q.EXISTS_TAC ‘[]’ >>
    fs [eval_clstep_bir_step_soundness]
  ]
QED

Theorem eval_clstep_completeness:
  ∀p cid s M l s'.
   clstep p cid s M l s' ⇒ MEM s' (eval_clstep cid p s M)
Proof
  rewrite [eval_clstep_def, clstep_cases, ABS_SIMP] >>
  rpt strip_tac >|
  [
    fs [mem_default_def]
    ,
    fs []
    ,
    fs [mem_filter_thm]
    ,
    gs [mem_every_thm, mem_filter_thm, oEL_THM]
  Cases_on ‘bir_get_stmt p s.bst_pc’ >> (simp [])
  >| [
    (* read *)
    rw [bir_state_t_component_equality, eval_clstep_read_def, mem_read_view_def, mem_readable_def, mem_filter_def] >|
QED


Theorem LIST_TO_SET_MEM:
  ∀x l.
  set l x = MEM x l
Proof
  Induct_on ‘l’ >> (simp [])
QED

Theorem eval_clstep_correctness:
  ∀p cid s M s'.
  set (eval_clstep cid p s M) s' = ∃l. clstep p cid s M l s'
Proof
  rpt strip_tac >> EQ_TAC >>
  (simp [LIST_TO_SET_MEM, eval_clstep_completeness, eval_clstep_soundness])
QED

val _ = export_theory();
