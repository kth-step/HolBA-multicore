(*
  Theorems about promising semantics relevant for refinement proofs with composition

  One central definition is `transition_within`, which defines jumps within a
  program.
  
  Contains theorems valid for composition ("APPEND") and permutation of
  programs (search for "PERM"), valid for BIR constants
  `bir_labels_of_program`, `bir_get_current_statement`
  Defines constant list_disj for disjunction of lists, list_subset for subset
  of lists
*)

open HolKernel boolLib bossLib Parse;
open listTheory rich_listTheory arithmeticTheory
     wordsTheory bitstringTheory llistTheory wordsLib
     finite_mapTheory string_numTheory relationTheory
     bir_programTheory bir_promisingTheory
     bir_promising_wfTheory bir_programLib
     pairTheory

val _ = new_theory "promising_thms";

(* for strong post condition generation *)

Definition bir_stmts_of_progs_def:
  bir_stmts_of_progs $ BirProgram p =
    MAP (λbl.
      let stmts =
        case bl of
        | BBlock_Stmts stmts =>
          SOME (LENGTH stmts.bb_statements,stmts.bb_statements,stmts.bb_last_statement)
        | BBlock_Ext R => NONE
      in
        (bir_label_of_block bl, stmts)
    ) p
End

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

Definition jmp_targets_def:
  jmp_targets prog =
    FLAT $ MAP (λx. case x of
      BLE_Label bla => [bla]
    | _ => []
    )
    $ FLAT $ MAP (λx. case x of
        BStmt_CJmp _ lbl1 lbl2 => [lbl1;lbl2]
      | BStmt_Jmp lbl => [lbl]
    )
    $ FLAT $ case prog of BirProgram pl =>
      MAP (λx.
        case x of BBlock_Stmts bl => [bl.bb_last_statement]
          | BBlock_Ext R => []
      ) pl
End

(* uncurried definition of parstep *)
Definition parstep_uc_def:
  parstep_uc cid = λ(cores,M) (cores',M'). parstep cid cores M cores' M'
End

(* TODO move closer to definition *)

Theorem type_of_bir_imm_EQ_ELIMS:
  !v0 v1.
  type_of_bir_imm v0 = v1
  <=> (?v. v0 = Imm1 v /\ v1 = Bit1)
    \/ (?v. v0 = Imm8 v /\ v1 = Bit8)
    \/ (?v. v0 = Imm16 v /\ v1 = Bit16)
    \/ (?v. v0 = Imm32 v /\ v1 = Bit32)
    \/ (?v. v0 = Imm64 v /\ v1 = Bit64)
    \/ (?v. v0 = Imm128 v /\ v1 = Bit128)
Proof
  ntac 2 Cases
  >> fs[bir_immTheory.type_of_bir_imm_def]
QED

Theorem PERM_MEM:
  !a b x. PERM a b ==> MEM x a = MEM x b
Proof
  rpt strip_tac
  >> drule sortingTheory.PERM_LIST_TO_SET
  >> fs[]
QED

(* clstep theorems *)

Theorem clstep_bgcs_imp:
  !p cid s M prom s'.
    clstep p cid s M prom s'
    ==> ?stmt. bir_get_current_statement p s.bst_pc = SOME stmt
Proof
  dsimp[clstep_cases]
QED

Theorem clstep_bgcs_cases:
  !p cid c M prom c'.
  clstep p cid c M prom c'
  ==> ?stmt. bir_get_current_statement p c.bst_pc = SOME stmt /\ (
    (?var a_e opt_cast xcl acq rel. stmt = BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel)
    \/ (?var_succ a_e v_e xcl acq rel. stmt = BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel /\ xcl /\ prom = [])
    \/ (?var_succ a_e v_e xcl acq rel. stmt = BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel /\ ~(NULL prom))
    \/ (?var a_e v_e acq rel. stmt = BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel)
    \/ (?K1 K2. stmt = BSGen $ BStmtB $ BMCStmt_Fence K1 K2)
    \/ (?cond_e lbl1 lbl2. stmt = BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2)
    \/ (?var e. stmt = BSGen $ BStmtB $ BMCStmt_Assign var e)
    \/ (?e. stmt = BSGen $ BStmtB $ BMCStmt_Assert e)
    \/ (?e. stmt = BSGen $ BStmtB $ BMCStmt_Assume e)
    \/ (?e. stmt = BSGen $ BStmtE $ BStmt_Halt e)
    \/ (?e. stmt = BSGen $ BStmtE $ BStmt_Jmp e)
    \/ (?R. stmt = BSExt R))
Proof
  rpt strip_tac
  >> gvs[clstep_cases,bmc_exec_general_stmt_exists]
QED

Theorem cstep_bgcs_imp:
  !P prog cid s M prom s' M'.
    cstep prog cid s M prom s' M'
    /\ M = M'
    ==> ?stmt. bir_get_current_statement prog s.bst_pc = SOME stmt
Proof
  dsimp[clstep_cases,cstep_cases]
QED


Theorem bir_exec_stmt_cjmp_disj:
  !p cond lbl1 lbl2 s.
     (bir_exec_stmt_cjmp p cond (BLE_Label lbl1) (BLE_Label lbl2) s).bst_pc.bpc_label = s.bst_pc.bpc_label
  \/ (bir_exec_stmt_cjmp p cond (BLE_Label lbl1) (BLE_Label lbl2) s).bst_pc.bpc_label = lbl1
  \/ (bir_exec_stmt_cjmp p cond (BLE_Label lbl1) (BLE_Label lbl2) s).bst_pc.bpc_label = lbl2
Proof
  rw[bir_exec_stmt_cjmp_def,AllCaseEqs(),bir_state_set_typeerror_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_eval_label_exp_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem bir_exec_stmt_jmp_disj:
  !p lbl s.
  (bir_exec_stmt_jmp p (BLE_Label lbl) s).bst_pc.bpc_label = s.bst_pc.bpc_label
  \/ ((bir_exec_stmt_jmp p (BLE_Label lbl) s).bst_pc.bpc_label = lbl
    /\ (bir_exec_stmt_jmp p (BLE_Label lbl) s).bst_pc.bpc_index = 0)
Proof
  rw[bir_exec_stmt_jmp_def,bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def]
QED


Theorem INDEX_FIND_append:
  !ls n P ls'. INDEX_FIND n P (ls ++ ls') =
  if EXISTS P ls then INDEX_FIND n P ls else INDEX_FIND (n + LENGTH ls) P ls'
Proof
  Induct >> rw[listTheory.INDEX_FIND_def] >> fs[arithmeticTheory.ADD1]
QED

Definition list_disj_def:
  list_disj l1 l2 = !x. MEM x l1 ==> ~MEM x l2
End

Theorem list_disj_eq:
  list_disj l1 l2 = DISJOINT (set l1) (set l2)
Proof
  fs[pred_setTheory.DISJOINT_ALT,list_disj_def]
QED

Theorem list_disj_ALL_DISTINCT:
  !l1 l2. ALL_DISTINCT (l1 ++ l2) ==> list_disj l1 l2
Proof
  rw[listTheory.ALL_DISTINCT_APPEND,list_disj_def]
QED

Theorem list_disj_nub:
  list_disj (nub l1) l2 = list_disj l1 l2
  /\ list_disj l2 (nub l1) = list_disj l2 l1
Proof
  fs[list_disj_def]
QED

Theorem list_disj_eq:
  !l1 l2. list_disj l1 l2 = ALL_DISTINCT (nub l1 ++ nub l2)
Proof
  rw[listTheory.ALL_DISTINCT_APPEND,list_disj_def]
QED

Theorem list_disj_spec:
  !l1 l2. list_disj l1 l2 =
  !x. (MEM x l1 ==> ~MEM x l2) /\ (MEM x l2 ==> ~MEM x l1)
Proof
  rw[list_disj_def,EQ_IMP_THM]
  >> PRED_ASSUM is_forall $ imp_res_tac o REWRITE_RULE[Once MONO_NOT_EQ]
QED

Theorem list_disj_spec_ho =
  Ho_Rewrite.REWRITE_RULE[FORALL_AND_THM] list_disj_spec

Theorem list_disj_sym:
  !l1 l2. list_disj l1 l2 = list_disj l2 l1
Proof
  fs[list_disj_spec,AC CONJ_ASSOC CONJ_COMM]
QED

Theorem list_disj_sym_imp = iffLR list_disj_sym

Theorem list_disj_append2:
  !l1 l2 l3. list_disj l1 (l2 ++ l3) <=> list_disj l1 l2 /\ list_disj l1 l3
Proof
  dsimp[list_disj_def]
QED

Theorem list_disj_append1 =
  ONCE_REWRITE_RULE[GSYM list_disj_sym] list_disj_append2;

Theorem list_disj_sub:
  list_disj l1 l2 /\ MEM a l1 ==> list_disj [a] l2
Proof
  fs[list_disj_def]
QED

Theorem list_disj_singleton:
  list_disj [a] l1 = ~MEM a l1
  /\ list_disj l1 [a] = ~MEM a l1
Proof
  fs[list_disj_def]
QED

Definition list_subset_def:
  list_subset l1 l2 = !x. MEM x l1 ==> MEM x l2
End

Theorem list_subset_eq:
  list_subset l1 l2 <=> (set l1) SUBSET (set l2)
Proof
  fs[pred_setTheory.SUBSET_DEF,list_subset_def]
QED

Theorem list_subset_id:
  !l1. list_subset l1 l1
Proof
  fs[list_subset_def]
QED

Theorem list_subset_trans:
  !l1 l2 l3. list_subset l1 l2 /\ list_subset l2 l3
  ==> list_subset l1 l3
Proof
  rw[list_subset_def]
QED

Theorem list_subset_EVERY:
  !l1 l2. list_subset l1 l2 = EVERY (λx. MEM x l2) l1
Proof
  fs[listTheory.EVERY_MEM,list_subset_def]
QED

Theorem list_subset_append2_imp:
  (!l1 l2 l3. list_subset l1 l3 ==> list_subset l1 (l2 ++ l3))
  /\ !l1 l2 l3. list_subset l1 l2 ==> list_subset l1 (l2 ++ l3)
Proof
  simp[list_subset_def]
QED

Theorem bir_labels_of_program_APPEND:
  !A B.
    bir_labels_of_program (BirProgram $ A ++ B) =
      bir_labels_of_program (BirProgram A)
      ++ (bir_labels_of_program (BirProgram B))
Proof
  fs[bir_labels_of_program_def]
QED

Theorem bir_get_program_block_info_by_label_eq:
  !p. set $ bir_labels_of_program p
  = { l | ?i bl. bir_get_program_block_info_by_label p l = SOME (i,bl) }
Proof
  Cases >> rw[pred_setTheory.EXTENSION,bir_get_program_block_info_by_label_MEM]
QED

Theorem bir_get_program_block_info_by_label_APPEND_list_disj:
  !A B label v.
  bir_get_program_block_info_by_label (BirProgram A) label = SOME v
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==>
  bir_get_program_block_info_by_label (BirProgram (A ++ B)) label = SOME v
Proof
  fs[pairTheory.FORALL_PROD]
  >> rw[bir_get_program_block_info_by_label_THM]
  >> fs[rich_listTheory.EL_APPEND1]
QED

Theorem bir_get_program_block_info_by_label_APPEND2:
  !A B label v.
  bir_get_program_block_info_by_label (BirProgram A) label = NONE
  ==>
  bir_get_program_block_info_by_label (BirProgram (A ++ B)) label =
    OPTION_MAP (λ(l,b). (l + LENGTH A,b)) $
      bir_get_program_block_info_by_label (BirProgram B) label
Proof
  rw[bir_get_program_block_info_by_label_THM]
  >> qmatch_goalsub_abbrev_tac `_ = x` >> Cases_on `x`
  >> fs[bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,pairTheory.EXISTS_PROD]
  >> dsimp[]
  >> fs[bir_get_program_block_info_by_label_THM,listTheory.EL_APPEND_EQN]
  >> rw[rich_listTheory.EL_MEM]
QED

Theorem bir_get_current_statement_SOME_MEM:
  !prog pc x.
  bir_get_current_statement prog pc = SOME x
  ==> MEM pc.bpc_label $ bir_labels_of_program prog
Proof
  rw[bir_get_current_statement_def,AllCaseEqs(),bir_get_program_block_info_by_label_MEM]
  >> fs[GSYM pairTheory.EXISTS_PROD]
QED

Theorem clstep_MEM_bir_labels_of_program:
  !prog s s' M prom cid x.
  clstep prog cid s M prom s'
  ==> MEM s'.bst_pc.bpc_label $ bir_labels_of_program prog
Proof
  rw[clstep_cases,bir_state_read_view_updates_def,bir_get_current_statement_def,AllCaseEqs(),bir_get_program_block_info_by_label_MEM,bir_state_fulful_view_updates_def,fence_updates_def,bmc_exec_general_stmt_exists]
  >> fs[bir_exec_stmt_jmp_to_label_mc_invar]
  >> fs[bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac
  >> fs[bir_state_set_typeerror_def,bir_block_pc_def,bir_get_program_block_info_by_label_MEM]
  >> gvs[bir_pc_next_def,GSYM pairTheory.EXISTS_PROD,pairTheory.ELIM_UNCURRY]
QED

Theorem bir_get_current_statement_MEM1:
  !A B pc stmt.
  bir_get_current_statement (BirProgram $ A ++ B) pc = SOME stmt
  /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A
  ==> bir_get_current_statement (BirProgram A) pc = SOME stmt
Proof
  fs[bir_get_current_statement_def,optionTheory.IS_SOME_EXISTS,bir_get_program_block_info_by_label_MEM]
  >> rw[AllCaseEqs()]
  >> qmatch_asmsub_rename_tac `bir_get_program_block_info_by_label (BirProgram $ A ++ B) _ = SOME x`
  >> qmatch_asmsub_rename_tac `bir_get_program_block_info_by_label (BirProgram A) _ = SOME x'`
  >> qsuff_tac `x = x'` >- (rw[] >> fs[])
  >> PairCases_on `x` >> PairCases_on `x'`
  >> Cases_on `x0 <> x'0`
  >> gs[bir_get_program_block_info_by_label_THM,rich_listTheory.EL_APPEND1,arithmeticTheory.NOT_NUM_EQ,GSYM arithmeticTheory.LESS_EQ]
  >> first_x_assum drule
  >> gs[rich_listTheory.EL_APPEND1]
QED

Theorem bir_get_current_statement_MEM1':
  !A B pc stmt.
  bir_get_current_statement (BirProgram A) pc = SOME stmt
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==> bir_get_current_statement (BirProgram $ A ++ B) pc = SOME stmt
Proof
  rpt strip_tac
  >> imp_res_tac bir_get_current_statement_SOME_MEM
  >> fs[bir_get_current_statement_def,optionTheory.IS_SOME_EXISTS,bir_get_program_block_info_by_label_MEM]
  >> drule_all_then assume_tac bir_get_program_block_info_by_label_APPEND_list_disj
  >> fs[AllCaseEqs(),pairTheory.ELIM_UNCURRY,PULL_EXISTS]
QED

Theorem bir_get_current_statement_BirProgram_APPEND:
  !A B pc.
  list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==>
    bir_get_current_statement (BirProgram $ A ++ B) pc =
      if IS_SOME $ bir_get_program_block_info_by_label (BirProgram A) pc.bpc_label
      then bir_get_current_statement (BirProgram A) pc
      else bir_get_current_statement (BirProgram B) pc
Proof
  rw[bir_get_current_statement_def,optionTheory.IS_SOME_EXISTS]
  >- (
    drule_all_then assume_tac bir_get_program_block_info_by_label_APPEND_list_disj
    >> fs[]
  )
  >> qmatch_asmsub_abbrev_tac `~?x. blah = SOME x` >> Cases_on `blah`
  >> fs[bir_get_program_block_info_by_label_APPEND2]
  >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ bgpbibl` >> Cases_on `bgpbibl`
  >> fs[]
  >> qmatch_asmsub_rename_tac `SOME x` >> PairCases_on `x`
  >> fs[]
QED

Theorem bir_get_current_statement_MEM2:
  !A B pc stmt.
  bir_get_current_statement (BirProgram $ A ++ B) pc = SOME stmt
  /\ list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B
  ==> bir_get_current_statement (BirProgram B) pc = SOME stmt
Proof
  rpt strip_tac
  >> drule_then assume_tac bir_get_current_statement_BirProgram_APPEND
  >> fs[optionTheory.IS_SOME_EXISTS,Once list_disj_sym,list_disj_def]
  >> first_x_assum $ drule_then assume_tac
  >> fs[bir_get_program_block_info_by_label_MEM,GSYM pairTheory.FORALL_PROD]
QED

Theorem bir_get_current_statement_APPEND1:
  !A B pc.
  list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A
  ==>
    bir_get_current_statement (BirProgram $ A ++ B) pc =
      bir_get_current_statement (BirProgram A) pc
Proof
  rpt strip_tac
  >> fs[bir_get_current_statement_BirProgram_APPEND,list_disj_def]
  >> first_x_assum $ drule_then assume_tac
  >> fs[AllCaseEqs(),bir_get_program_block_info_by_label_eq]
QED

Theorem bir_get_current_statement_APPEND2:
  !A B pc.
  list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B
  ==>
    bir_get_current_statement (BirProgram $ A ++ B) pc =
      bir_get_current_statement (BirProgram B) pc
Proof
  rpt strip_tac
  >> fs[bir_get_current_statement_BirProgram_APPEND,Once list_disj_sym,list_disj_def]
  >> first_x_assum $ drule_then assume_tac
  >> fs[AllCaseEqs(),bir_get_program_block_info_by_label_eq,GSYM pairTheory.FORALL_PROD]
  >> Cases_on `bir_get_program_block_info_by_label (BirProgram A) pc.bpc_label`
  >> fs[]
QED

Theorem bir_get_program_block_info_by_label_IS_NONE_NOT_MEM:
  !A lbl. IS_NONE $ bir_get_program_block_info_by_label (BirProgram A) lbl
  ==> ~(MEM lbl $ bir_labels_of_program $ BirProgram A)
Proof
  fs[bir_get_program_block_info_by_label_MEM,GSYM pairTheory.EXISTS_PROD,optionTheory.IS_SOME_EXISTS]
QED

Theorem bir_get_program_block_info_by_label_IS_SOME_MEM:
  !A lbl. IS_SOME $ bir_get_program_block_info_by_label (BirProgram A) lbl
  ==> MEM lbl $ bir_labels_of_program $ BirProgram A
Proof
  fs[bir_get_program_block_info_by_label_MEM,GSYM pairTheory.EXISTS_PROD,optionTheory.IS_SOME_EXISTS]
QED

Theorem bir_get_current_statement_APPEND_cases:
  !A B pc.
  list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  ==>
    (~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ bir_get_current_statement (BirProgram $ A ++ B) pc =
      bir_get_current_statement (BirProgram B) pc)
    \/ (MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ bir_get_current_statement (BirProgram $ A ++ B) pc =
      bir_get_current_statement (BirProgram A) pc)
Proof
  rw[bir_get_current_statement_BirProgram_APPEND,iffLR list_disj_sym]
  >> fs[bir_get_program_block_info_by_label_IS_NONE_NOT_MEM,bir_get_program_block_info_by_label_IS_SOME_MEM,list_disj_sym_imp,list_disj_def]
QED

Theorem bir_get_current_statement_APPEND3_cases:
  !A B C pc.
  list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram C)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
      (bir_labels_of_program $ BirProgram C)
  ==>
    (MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A
      /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
      /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram C)
      /\ bir_get_current_statement (BirProgram $ A ++ B ++ C) pc =
        bir_get_current_statement (BirProgram A) pc)
    \/ (~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
      /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B
      /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram C)
      /\ bir_get_current_statement (BirProgram $ A ++ B ++ C) pc =
        bir_get_current_statement (BirProgram B) pc)
    \/ (~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
      /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
      /\ bir_get_current_statement (BirProgram $ A ++ B ++ C) pc =
        bir_get_current_statement (BirProgram C) pc)
Proof
  rpt strip_tac
  >> qspecl_then [`A`,`B ++ C`,`pc`] assume_tac bir_get_current_statement_APPEND_cases
  >> qspecl_then [`B`,`C`,`pc`] assume_tac bir_get_current_statement_APPEND_cases
  >> gs[list_disj_sym_imp,bir_labels_of_program_APPEND,list_disj_append1,list_disj_append2]
QED

Theorem bir_get_current_statement_three:
  !pc A B C.
  MEM pc.bpc_label $ bir_labels_of_program $ BirProgram $ A ++ B ++ C
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
    (bir_labels_of_program $ BirProgram C)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram C)
  /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
  ==>
  (MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A
  /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram C)
  /\ bir_get_current_statement (BirProgram $ A ++ B ++ C) pc = bir_get_current_statement (BirProgram $ A) pc)
  \/
  (~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
  /\ MEM pc.bpc_label $ bir_labels_of_program $ BirProgram C
  /\ bir_get_current_statement (BirProgram $ A ++ B ++ C) pc = bir_get_current_statement (BirProgram $ C) pc)
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `(P /\ ~Q /\ _) \/ (~P /\ Q /\ _)`
  >> Cases_on `P`
  >> gs[list_disj_sym_imp,bir_get_current_statement_APPEND1,list_disj_append1,list_disj_append2,bir_get_current_statement_APPEND2,bir_labels_of_program_APPEND]
  >> gs[list_disj_spec_ho]
QED

(* jump within a program *)

(* restrict an external program to a fixed shape that either encodes progress to
 * a certain label if a condition P holds, or stagnates *)
Definition ext_loop_def:
  ext_loop p lbl P R' (s,prom,M) s' =
    if P (s,prom,M) then s = s' else
      (s' = bir_exec_stmt_jmp_to_label p lbl s' /\ R' (s,prom,M) s')
End

(* all external programs have a certain fixed shape *)
Definition ext_loops_def:
  ext_loops (BirProgram p) =
    EVERY (λstmt.
      !x. stmt = BBlock_Ext x
      ==> ?lbl P R'. x.beb_relation = ext_loop (BirProgram p) lbl P R'
    ) p
End

Definition is_jump_def:
  is_jump p c <=>
    ?stmt. bir_get_current_statement (BirProgram p) c.bst_pc = SOME stmt
    /\ (
      (?cond_e lbl1 lbl2. stmt = BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2)
      \/ (?e. stmt = BSGen (BStmtE (BStmt_Jmp e)))
      \/ ?lbl P R'. stmt = BSExt $ ext_loop (BirProgram p) lbl P R'
    )
End

(* a jump to a given label *)
Definition is_jump_to_label_def:
  is_jump_to_label p' c lbl <=>
  is_jump p' c
  /\ (
    !cond_e lbl1 lbl2 v v'.
    bir_get_current_statement (BirProgram p') c.bst_pc =
      SOME $ BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2
    /\ bir_eval_exp cond_e c.bst_environ = SOME v'
    /\ bir_dest_bool_val v' = SOME v
    ==> (v ==> bir_eval_label_exp lbl1 c.bst_environ = SOME lbl)
      /\ (~v ==> bir_eval_label_exp lbl2 c.bst_environ = SOME lbl)
  )
  /\ (
    !lbl'.
    bir_get_current_statement (BirProgram p') c.bst_pc =
      SOME $ BSGen $ BStmtE $ BStmt_Jmp lbl'
    ==> bir_eval_label_exp lbl' c.bst_environ = SOME lbl
  )
  /\ (
    ?lbl' P R.
    bir_get_current_statement (BirProgram p') c.bst_pc
    = SOME $ BSExt $ ext_loop (BirProgram p') lbl' P R
    ==> lbl' = lbl
  )
End

(* the central definition of a jump within a program *)
Definition transition_within_def:
  transition_within p c <=>
    !lbl. is_jump_to_label p c lbl ==> MEM lbl $ bir_labels_of_program $ BirProgram p
End

Theorem well_formed_mem_read_view_zero:
  !cid M s l.
  well_formed cid M s ==> mem_read_view (s.bst_fwdb l) 0 = 0
Proof
  rw[mem_read_view_def,well_formed_fwdb_def,well_formed_def]
  >> qmatch_asmsub_rename_tac `s.bst_fwdb l`
  >> first_x_assum $ qspec_then `l` assume_tac
  >> fs[]
QED

(* properties of permutation of program instructions *)

Theorem bir_labels_of_program_PERM:
  !p p'. PERM p p'
  ==> PERM (bir_labels_of_program (BirProgram p))
    (bir_labels_of_program (BirProgram p'))
Proof
  ho_match_mp_tac sortingTheory.PERM_lifts_monotonicities
  >> fs[bir_labels_of_program_APPEND]
  >> rpt strip_tac
  >> irule_at Any EQ_REFL
  >> fs[]
QED

Theorem bir_labels_of_program_ALL_DISTINCT:
  !p p'. PERM p p'
  ==> ALL_DISTINCT (bir_labels_of_program (BirProgram p))
    = ALL_DISTINCT (bir_labels_of_program (BirProgram p'))
Proof
  fs[bir_labels_of_program_PERM,sortingTheory.ALL_DISTINCT_PERM]
QED

Theorem PERMUTES_count_less:
  k < n /\ f PERMUTES count n ==> f k < n
Proof
  fs[pred_setTheory.BIJ_ALT,pred_setTheory.FUNSET]
QED

Theorem INDEX_FIND_ALL_DISTINCT:
  !f p p' z0 z1 a. PERM p p'
  /\ ALL_DISTINCT (MAP f p)
  /\ ALL_DISTINCT (MAP f p')
  /\ INDEX_FIND 0 (λx. f x = a) p = SOME (z0,z1)
  ==> ?z'. INDEX_FIND 0 (λx. f x = a) p' = SOME z' /\ SND z' = z1
Proof
  rpt strip_tac
  >> fs[bir_auxiliaryTheory.INDEX_FIND_EQ_SOME_0,pairTheory.EXISTS_PROD,sortingTheory.PERM_BIJ_IFF,LENGTH_GENLIST]
  >> qmatch_asmsub_rename_tac `n < LENGTH p`
  >> cheat (* properties about BIJ functions (PERMUTES) *)
QED

Theorem bir_get_program_block_info_by_label_PERM:
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==> OPTION_MAP SND $ bir_get_program_block_info_by_label (BirProgram p) label =
      OPTION_MAP SND $ bir_get_program_block_info_by_label (BirProgram p') label
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac`OPTION_MAP SND a = OPTION_MAP SND b`
  >> drule_all_then assume_tac $ iffLR bir_labels_of_program_ALL_DISTINCT
  >> fs[bir_get_program_block_info_by_label_def]
  >> Cases_on `a`
  >> fs[markerTheory.Abbrev_def,bir_auxiliaryTheory.INDEX_FIND_EQ_NONE]
  >- (
    drule_then irule $ iffLR sortingTheory.PERM_EVERY
    >> fs[]
  )
  >> qmatch_asmsub_rename_tac `SOME x` >> PairCases_on `x`
  >> fs[pairTheory.EXISTS_PROD,bir_labels_of_program_def]
  >> qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
  >> qmatch_asmsub_abbrev_tac `MAP f`
  >> rpt $ pop_assum mp_tac
  >> CONV_TAC $ DEPTH_CONV ETA_CONV
  >> rpt $ disch_then strip_assume_tac
  >> qspec_then `f` mp_tac INDEX_FIND_ALL_DISTINCT
  >> rpt $ disch_then drule
  >> unabbrev_all_tac
  >> fs[]
  >> disch_then $ drule_then assume_tac
  >> fs[pairTheory.EXISTS_PROD]
QED

Theorem bir_get_current_statement_PERM:
  !p p' pc.
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==> bir_get_current_statement (BirProgram p) pc =
      bir_get_current_statement (BirProgram p') pc
Proof
  rpt strip_tac
  >> drule_all bir_get_program_block_info_by_label_PERM
  >> dsimp[bir_get_current_statement_def,optionTheory.option_case_compute,AllCaseEqs()]
  >> rw[DISJ_EQ_IMP]
  >> ntac 2 (pairarg_tac >> gvs[])
  >- (
    qmatch_asmsub_abbrev_tac `IS_SOME a ==> _`
    >> Cases_on `a` >> gvs[markerTheory.Abbrev_def]
    >> qmatch_asmsub_rename_tac `bir_get_program_block_info_by_label _ pc.bpc_label`
    >> qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
    >> first_x_assum $ qspec_then `pc.bpc_label` assume_tac
    >> gvs[]
  )
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> qmatch_asmsub_rename_tac `bir_get_program_block_info_by_label _ pc.bpc_label`
  >> first_x_assum $ qspec_then `pc.bpc_label` assume_tac
  >> gvs[]
QED

Theorem bir_exec_stmt_jmp_to_label_PERM:
  !p p' lbl c.
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==> bir_exec_stmt_jmp_to_label (BirProgram p) lbl c
    = bir_exec_stmt_jmp_to_label (BirProgram p') lbl c
Proof
  dsimp[bir_exec_stmt_jmp_to_label_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR]
  >> rpt strip_tac
  >> drule_then assume_tac bir_labels_of_program_PERM
  >> dxrule_then assume_tac PERM_MEM
  >> csimp[]
QED

Theorem bir_exec_stmt_jmp_PERM:
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==> bir_exec_stmt_jmp (BirProgram p) lbl c
    = bir_exec_stmt_jmp (BirProgram p') lbl c
Proof
  dsimp[bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND]
  >> rpt strip_tac
  >> fs[bir_exec_stmt_jmp_to_label_PERM]
QED

Theorem bir_exec_stmt_cjmp_PERM:
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==> bir_exec_stmt_cjmp (BirProgram p) cond_e lbl1 lbl2 c
    = bir_exec_stmt_cjmp (BirProgram p') cond_e lbl1 lbl2 c
Proof
  rpt strip_tac
  >> dsimp[bir_exec_stmt_cjmp_def,optionTheory.option_case_compute,COND_RAND,COND_EXPAND_OR]
  >> csimp[bir_exec_stmt_jmp_PERM]
  >> qmatch_goalsub_abbrev_tac `IS_SOME a /\ IS_SOME b`
  >> Cases_on `a` >> Cases_on `b` >> fs[]
QED

Theorem clstep_permute_prog:
  !p p' cid c M prom c'.
  PERM p p' /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram p
  ==>
  clstep (BirProgram p) cid c M prom c' = clstep (BirProgram p') cid c M prom c'
Proof
  dsimp[EQ_IMP_THM]
  >> conj_asm2_tac
  >- (
    rpt strip_tac
    >> first_x_assum irule
    >> fs[PULL_EXISTS]
    >> drule_then (irule_at Any) $ iffLR sortingTheory.PERM_SYM
    >> dxrule bir_labels_of_program_ALL_DISTINCT
    >> fs[]
  )
  >> rpt strip_tac
  >> drule_then strip_assume_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_labels_of_program_ALL_DISTINCT
  >> qmatch_asmsub_abbrev_tac `bir_get_current_statement _ c.bst_pc`
  >> drule_all_then (qspec_then `c.bst_pc` assume_tac) bir_get_current_statement_PERM
  >> gvs[clstep_cases,bmc_exec_general_stmt_exists]
  >> dsimp[]
  >> gvs[bir_exec_stmt_jmp_PERM]
  >~ [`BMCStmt_Load`]
  >- (
    qpat_assum `mem_read _ _ _ = _` $ irule_at Any
    >> rpt $ goal_assum drule
    >> fs[]
  )
  >~ [`BMCStmt_Store`]
  >- rpt (rpt $ goal_assum drule >> fs[])
  >~ [`BMCStmt_Amo`]
  >- rpt (rpt $ goal_assum drule >> fs[])
  >~ [`BStmt_CJmp`]
  >- (
    goal_assum drule
    >> drule_all bir_exec_stmt_cjmp_PERM
    >> fs[]
  )
  >~ [`BMCStmt_Assign`]
  >- (
    rpt $ goal_assum drule
    >> fs[]
  )
  >~ [`BMCStmt_Store`]
  >- rpt (rpt $ goal_assum drule >> fs[])
  >~ [`BSExt`]
  >- (
    drule_then assume_tac bir_labels_of_program_PERM
    >> dxrule_then assume_tac PERM_MEM
    >> drule_all_then (gs o single) bir_exec_stmt_jmp_to_label_PERM
    >> goal_assum drule
    >> fs[]
  )
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND1:
  !p p' lbl c.
    MEM lbl $ bir_labels_of_program $ BirProgram p
    ==> bir_exec_stmt_jmp_to_label (BirProgram $ p ++ p') lbl c
    = bir_exec_stmt_jmp_to_label (BirProgram p) lbl c
Proof
  rpt strip_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND2:
  !p p' lbl c.
    MEM lbl $ bir_labels_of_program $ BirProgram p'
    ==> bir_exec_stmt_jmp_to_label (BirProgram $ p ++ p') lbl c
    = bir_exec_stmt_jmp_to_label (BirProgram p') lbl c
Proof
  rpt strip_tac
  >> fs[bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND]
QED

Theorem bir_get_current_statement_BSExt:
  bir_get_current_statement (BirProgram p) c.bst_pc = SOME $ BSExt R
  ==> ?x. MEM (BBlock_Ext x) p /\ R = x.beb_relation
Proof
  gs[bir_get_current_statement_def,optionTheory.option_case_eq,ELIM_UNCURRY,PULL_EXISTS,bir_get_program_block_info_by_label_THM]
  >> Induct >> rw[] >> fs[]
  >> BasicProvers.every_case_tac
  >> gvs[bir_get_program_block_info_by_label_THM]
  >> irule_at Any EQ_REFL
  >> qpat_assum `EL _ _ = BBlock_Ext _` $ rewrite_tac o single o GSYM
  >> fs[EL_MEM]
QED

Theorem clstep_imp_clstep_APPEND:
  clstep (BirProgram $ p ++ p') cid c M prom c'
  /\ MEM c.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p'
  /\ list_disj (bir_labels_of_program $ BirProgram p)
           (bir_labels_of_program $ BirProgram p')
  /\ ext_loops $ BirProgram p'
  /\ transition_within p' c
  ==> clstep (BirProgram p') cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_get_current_statement_MEM2
  >> gs[clstep_cases,is_jump_to_label_def,bir_eval_exp_view_def,bmc_exec_general_stmt_exists,transition_within_def]
  >> rpt $ qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
  >> fs[]
  >~ [`BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel`]
  >- (
    qhdtm_x_assum `mem_read` $ irule_at Any
    >> fs[]
  )
  >~ [`BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel`]
  >- (
    qhdtm_x_assum `mem_read` $ irule_at Any
    >> fs[]
  )
  >~ [`bir_exec_stmt_cjmp`]
  >- (
    MK_COMB_TAC >> fs[]
    >> fs[bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND,bir_block_pc_def]
    >> BasicProvers.every_case_tac
    >> gs[is_jump_def]
  )
  >~ [`bir_exec_stmt_jmp`]
  >- (
    fs[bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND,bir_block_pc_def]
    >> BasicProvers.every_case_tac
    >> gvs[is_jump_def]
  )
  >~ [`BSExt`]
  >- (
    gs[bir_exec_stmt_jmp_to_label_APPEND2,EVERY_MEM,ext_loops_def]
    >> drule_then strip_assume_tac bir_get_current_statement_BSExt
    >> gvs[PULL_FORALL,is_jump_def,PULL_EXISTS,ext_loop_def]
    >> first_x_assum $ drule_then strip_assume_tac
    >> qmatch_asmsub_abbrev_tac `_ = ext_loop _ lbl' P R'`
    >> qmatch_goalsub_abbrev_tac `bir_exec_stmt_jmp_to_label _ lbl _`
    >> gvs[ext_loop_def]
    >> first_x_assum $ qspecl_then [`lbl'`,`lbl'`,`P`,`R`] assume_tac
    >> gvs[COND_EXPAND_OR,bir_exec_stmt_jmp_to_label_def]
    >> cheat
    (* use transition_within_def and definition of jump *)
  )
QED

Theorem clstep_imp_clstep_APPEND1':
  clstep (BirProgram p) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram p)
      (bir_labels_of_program $ BirProgram p')
  /\ ext_loops $ BirProgram p
  /\ transition_within p c
  ==> clstep (BirProgram $ p ++ p') cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> imp_res_tac bir_get_current_statement_SOME_MEM
  >> drule_all_then assume_tac bir_get_current_statement_APPEND1
  >> gs[clstep_cases,bir_eval_exp_view_def,bmc_exec_general_stmt_exists,transition_within_def]
  >> rpt $ qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
  >> fs[]
  >~ [`BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel`]
  >- (
    qhdtm_x_assum `mem_read` $ irule_at Any
    >> fs[]
  )
  >~ [`BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel`]
  >- (
    qhdtm_x_assum `mem_read` $ irule_at Any
    >> fs[]
  )
  >~ [`bir_exec_stmt_cjmp`]
  >- (
    MK_COMB_TAC >> fs[]
    >> fs[bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND,bir_block_pc_def]
    >> BasicProvers.every_case_tac
    >> gs[is_jump_to_label_def]
    >> cheat
  )
  >~ [`bir_exec_stmt_jmp`]
  >- (
    fs[bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND,bir_block_pc_def]
    >> BasicProvers.every_case_tac
    >> gvs[is_jump_to_label_def]
  >> cheat
  )
  >~ [`BSExt`]
  >- (
    gs[is_jump_to_label_def,bir_exec_stmt_jmp_to_label_APPEND1]
    >> fs[bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_APPEND]
    >> cheat
  )
QED

Theorem clstep_imp_clstep_APPEND2':
  clstep (BirProgram p) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram p)
      (bir_labels_of_program $ BirProgram p')
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p ++ p'
  /\ ext_loops $ BirProgram p
  /\ transition_within p c
  ==> clstep (BirProgram $ p' ++ p) cid c M prom c'
Proof
  rpt strip_tac
  >> drule clstep_imp_clstep_APPEND1'
  >> disch_then drule
  >> disch_then $ drule_then assume_tac
  >> `PERM (p ++ p') (p' ++ p)` by fs[sortingTheory.PERM_APPEND]
  >> gs[]
  >> drule_all $ iffLR clstep_permute_prog
  >> fs[]
QED

Theorem clstep_RC_imp_clstep_APPEND1:
  RC (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M') s s'
  /\ list_disj (bir_labels_of_program $ BirProgram p)
      (bir_labels_of_program $ BirProgram p')
  /\ ext_loops $ BirProgram p
  /\ transition_within p (FST s)
  ==> RC (λ(s,M) (s',M'). ?prom. clstep (BirProgram $ p ++ p') cid s M prom s' /\ M = M') s s'
Proof
  rpt strip_tac
  >> fs[RC_DEF,ELIM_UNCURRY]
  >> dxrule_all_then assume_tac clstep_imp_clstep_APPEND1'
  >> disj2_tac >> gs[]
  >> goal_assum drule
QED

Theorem clstep_RC_imp_clstep_APPEND2:
  RC (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M') s s'
  /\ list_disj (bir_labels_of_program $ BirProgram p)
      (bir_labels_of_program $ BirProgram p')
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p ++ p'
  /\ ext_loops $ BirProgram p
  /\ transition_within p (FST s)
  ==> RC (λ(s,M) (s',M'). ?prom. clstep (BirProgram $ p' ++ p) cid s M prom s' /\ M = M') s s'
Proof
  rpt strip_tac
  >> fs[RC_DEF,ELIM_UNCURRY]
  >> dxrule_all_then assume_tac clstep_imp_clstep_APPEND2'
  >> disj2_tac >> gs[]
  >> goal_assum drule
QED

(* read a variable from a state *)

Definition bir_read_reg_def:
  bir_read_reg var env v <=>
    bir_eval_exp (BExp_Den $ BVar var $ BType_Imm Bit64) env
    = SOME $ BVal_Imm $ Imm64 v
End

Theorem bir_read_reg_prime =
  bir_read_reg_def
  |> CONV_RULE $ ONCE_DEPTH_CONV $ (RHS_CONV o ONCE_REWRITE_CONV o single) EQ_SYM_EQ
  |> GSYM

Theorem bir_read_reg_update:
  !f var v. bir_read_reg var (BEnv f(|var |-> SOME $ BVal_Imm $ Imm64 v|)) v
Proof
  rw[bir_read_reg_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
QED

Theorem bir_env_lookup_update:
  !var v f.
  bir_env_lookup var (BEnv f(|var |-> SOME $ BVal_Imm $ Imm64 v|))
  = SOME $ BVal_Imm $ Imm64 v
Proof
  rw[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
QED

Theorem bir_read_reg_env_update_cast64:
  !env var new_env v.
  env_update_cast64 var (BVal_Imm $ Imm64 v) (BType_Imm Bit64) env = SOME new_env
  ==> bir_read_reg var new_env v
Proof
  Cases >> EVAL_TAC
  >> rw[env_update_cast64_def,bir_envTheory.bir_env_update_def,bir_read_reg_def]
  >> fs[bir_env_lookup_update,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS]
QED

Definition bir_read_reg_zero_def:
  bir_read_reg_zero var env = bir_read_reg var env 0w
End

Theorem bir_read_reg_imp:
  !f var v.
  f var = SOME (BVal_Imm (Imm64 v)) ==> bir_read_reg var (BEnv f) v
Proof
  rw[bir_read_reg_zero_def,bir_read_reg_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,type_of_bir_imm_EQ_ELIMS,bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
QED

Definition bir_read_reg_nonzero_def:
  bir_read_reg_nonzero var env = ?v. bir_read_reg var env v /\ v <> 0w
End

Theorem mem_get_EVERY:
  !t M l v f. mem_get M l t = SOME v /\ 0 < t /\ EVERY f M ==> f v
Proof
  Cases >> rw[CaseEq"option"]
  >> gvs[mem_get_def,CaseEq"option",listTheory.oEL_THM,listTheory.EVERY_EL]
QED

Definition wf_mem_val_def:
  wf_mem_val (m : mem_msg_t) = ?v'. m.val = BVal_Imm $ Imm64 v'
End

Definition wf_mem_vals_def:
  wf_mem_vals M = EVERY wf_mem_val M
End

Theorem wf_mem_vals_mem_read:
  !t M l v. mem_read M l t = SOME v /\ wf_mem_vals M
  ==> ?v'. v = BVal_Imm $ Imm64 v'
Proof
  Cases >> rpt strip_tac
  >> fs[mem_read_zero,mem_read_def,CaseEq"option",wf_mem_vals_def]
  >> drule_then (dxrule_at Any) mem_get_EVERY
  >> fs[wf_mem_val_def]
QED

Definition wf_mem_loc_def:
  wf_mem_loc (m :mem_msg_t) = ?v'. m.loc = BVal_Imm $ Imm64 v'
End

Definition wf_mem_locs_def:
  wf_mem_locs M = EVERY wf_mem_loc M
End

Theorem wf_mem_locs_mem_get:
  !t M l v f. mem_get M l t = SOME v /\ 0 < t /\ wf_mem_locs M
  ==> wf_mem_loc v
Proof
  rw[wf_mem_locs_def]
  >> drule_all_then irule mem_get_EVERY
QED

Theorem xclfail_update_env_SOME:
  !env name new_env.
  xclfail_update_env (BVar name (BType_Imm Bit64)) env = SOME new_env
  <=> ?f. env = BEnv f /\ f name <> NONE
    /\ new_env = BEnv f(|name |-> SOME $ BVal_Imm v_fail |)
Proof
  Cases >> rpt gen_tac
  >> CONV_TAC $ LAND_CONV EVAL
  >> fs[EQ_IMP_THM,v_fail_def]
QED

Theorem bir_env_update_SOME_eq =
  EVAL o Term $ `bir_env_update var (BVal_Imm v) (BType_Imm ty) (BEnv f) = SOME new_env`
 |> SIMP_RULE std_ss [COND_RATOR,COND_RAND,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS]
 |> GEN_ALL

Theorem bir_env_update_SOME_eq' =
  CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV $ ONCE_REWRITE_CONV[EQ_SYM_EQ]) bir_env_update_SOME_eq

Theorem bir_eval_exp_BExp_Den_update_eq:
  !name v f. bir_eval_exp (BExp_Den (BVar name (BType_Imm Bit64)))
    (BEnv f(|name |-> SOME (BVal_Imm (Imm64 v ))|)) =
      SOME (BVal_Imm (Imm64 v))
Proof
  fs[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,PULL_EXISTS,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS,combinTheory.APPLY_UPDATE_THM]
QED

Theorem bir_eval_exp_BExp_Den_update_eq':
  !name name' v f.
    name <> name' ==>
    bir_eval_exp (BExp_Den (BVar name (BType_Imm Bit64)))
      (BEnv f(|name' |-> SOME v|)) =
    bir_eval_exp (BExp_Den (BVar name (BType_Imm Bit64))) (BEnv f)
Proof
  fs[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS,combinTheory.APPLY_UPDATE_THM]
QED

Theorem fulfil_update_env_BVar_eq:
  !env new_env name xcl.
  fulfil_update_env (BVar name (BType_Imm Bit64)) xcl env = SOME new_env
  <=> ?f. env = BEnv f /\ if xcl then (f name <> NONE
    /\ new_env = BEnv f(|name |-> SOME $ BVal_Imm v_succ |))
                          else new_env = BEnv f
Proof
  Cases >> rpt gen_tac
  >> CONV_TAC $ LAND_CONV EVAL
  >> fs[EQ_IMP_THM,v_succ_def]
  >> dsimp[COND_RAND,COND_RATOR]
QED

Theorem fulfil_update_env_BVar_eq' =
  CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV $ ONCE_REWRITE_CONV[EQ_SYM_EQ])
  fulfil_update_env_BVar_eq

Theorem bir_dest_bool_val_false =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 0w``

Theorem bir_dest_bool_val_true =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 $ -1w``

Theorem bir_dest_bool_val_true' =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 1w``

Theorem bir_read_reg_bir_env_read:
  bir_env_read (BVar var (BType_Imm Bit64)) env = SOME (BVal_Imm (Imm64 v))
  <=> bir_read_reg var env v
Proof
  fs[bir_read_reg_def,bir_envTheory.bir_env_read_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def]
QED

(* TODO generalise *)
Theorem bir_eval_exp_BExp_UnaryExp:
  bir_read_reg var env x
  ==> bir_eval_exp (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar var (BType_Imm Bit64)))
                (BExp_Const (Imm64 v)))) env
                = SOME $ BVal_Imm $ Imm1 (if x = v then 0w else 1w)
Proof
  fs[bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_unary_exp_def,bir_expTheory.bir_eval_unary_exp_def,bir_expTheory.bir_eval_bin_pred_REWRS,type_of_bir_imm_EQ_ELIMS,bir_exp_immTheory.bir_bin_pred_def,bir_exp_immTheory.bir_bin_pred_GET_OPER_def,GSYM bir_read_reg_bir_env_read]
  >> fs[bir_immTheory.bool2b_def,bir_exp_immTheory.bir_unary_exp_def,bir_exp_immTheory.bir_unary_exp_GET_OPER_def]
  >> strip_tac
  >> EVAL_TAC
  >> fs[COND_RAND,bir_auxiliaryTheory.word1_neg]
QED

Theorem bir_eval_exp_BExp_UnaryExp':
  bir_read_reg var env x
  ==> (bir_eval_exp (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar var (BType_Imm Bit64)))
                (BExp_Const (Imm64 v)))) env
                = SOME w
        <=> w = BVal_Imm $ Imm1 (if x = v then 0w else 1w))
Proof
  fs[bir_expTheory.bir_eval_exp_def,bir_expTheory.bir_eval_unary_exp_def,bir_expTheory.bir_eval_unary_exp_def,bir_expTheory.bir_eval_bin_pred_REWRS,type_of_bir_imm_EQ_ELIMS,bir_exp_immTheory.bir_bin_pred_def,bir_exp_immTheory.bir_bin_pred_GET_OPER_def,GSYM bir_read_reg_bir_env_read]
  >> fs[bir_immTheory.bool2b_def,bir_exp_immTheory.bir_unary_exp_def,bir_exp_immTheory.bir_unary_exp_GET_OPER_def]
  >> strip_tac
  >> EVAL_TAC
  >> fs[COND_RAND,bir_auxiliaryTheory.word1_neg]
QED

Theorem bir_eval_exp_SOME:
  !exp env v. bir_eval_exp exp env = SOME v
  <=> ?f. bir_eval_exp exp (BEnv f) = SOME v /\ env = BEnv f
Proof
  Cases_on `env` >> fs[]
QED

Theorem bir_eval_exp_SOME' =
  CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV $ ONCE_REWRITE_CONV[EQ_SYM_EQ])
  bir_eval_exp_SOME

Theorem bir_exec_stmt_jmp_eq:
  MEM (BL_Address x) $ bir_labels_of_program prog
  ==> (bir_exec_stmt_jmp prog (BLE_Label $ BL_Address x) s).bst_pc =
    bir_block_pc $ BL_Address x
Proof
  fs[bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_exec_stmt_jmp_to_label_def]
QED

Theorem bir_eval_exp_BExp_Const =
  EVAL ``bir_eval_exp (BExp_Const v) env``
  |> GEN_ALL

Theorem bir_eval_exp_view_BExp_Const =
  EVAL ``bir_eval_exp_view (BExp_Const v) env viewenv = (SOME l,v_addr)``
  |> GEN_ALL

Theorem bir_eval_exp_view_BExp_Const' =
  CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV $ ONCE_REWRITE_CONV[EQ_SYM_EQ]) bir_eval_exp_view_BExp_Const

Theorem parstep_FLOOKUP:
  !p' p cid' cid cores M cores' M' s s' P.
    FLOOKUP cores cid = SOME $ Core cid p s
    /\ parstep cid cores M cores' M'
    /\ FLOOKUP cores' cid = SOME $ Core cid' p' s'
    ==> cid' = cid /\ p = p'
Proof
  rpt gen_tac >> strip_tac
  >> gvs[FLOOKUP_UPDATE,cstep_cases,parstep_cases]
QED

Theorem remove_prom_ID:
  remove_prom [] = I
  /\ remove_prom p (a ++ b) = remove_prom p a ++ remove_prom p b
  /\ remove_prom [t] [t] = []
Proof
  fs[remove_prom_def,FUN_EQ_THM,FILTER_APPEND]
QED

Theorem remove_prom_contra:
  ~(remove_prom [x] a = a ++ [x])
Proof
  spose_not_then assume_tac
  >> fs[remove_prom_def]
  >> qmatch_asmsub_abbrev_tac `FILTER P a = a ++ [b]`
  >> `MEM b $ FILTER P a` by fs[]
  >> qhdtm_x_assum `FILTER` kall_tac
  >> unabbrev_all_tac
  >> fs[MEM_FILTER]
QED

Theorem clstep_imp_bst_prom:
  clstep p cid s M prom s'
  ==> s'.bst_prom = remove_prom prom s.bst_prom
    /\ EVERY (λt. MEM t s.bst_prom) prom
Proof
  rw[clstep_cases,bir_state_fulful_view_updates_def,bir_state_read_view_updates_def,fence_updates_def,bmc_exec_general_stmt_exists]
  >> fs[bir_state_t_fupdfupds,bir_state_t_fupdcanon,remove_prom_ID,bir_exec_stmt_cjmp_mc_invar,bir_exec_stmt_jmp_bst_prom]
  >> fs[bir_exec_stmt_assert_def,bir_exec_stmt_assume_def,bir_state_set_typeerror_def,bir_exec_stmt_halt_def]
  >> BasicProvers.every_case_tac
  >> fs[]
  >> fs[EVERY_MEM,pred_setTheory.SUBSET_DEF]
QED

Theorem clstep_imp_cstep:
  clstep p cid s M prom s' ==> cstep p cid s M prom s' M
Proof
  fs[cstep_cases]
QED

Theorem clstep_imp_cstep_RC:
  !sM sM'.
    RC (λ(s,M) (s',M'). ?prom. clstep p cid s M prom s' /\ M = M') sM sM'
    ==> RC (λ(s,M) (s',M'). ?prom. cstep p cid s M prom s' M /\ M = M') sM sM'
Proof
  rw[RC_DEF,ELIM_UNCURRY]
  >> disj2_tac
  >> drule clstep_imp_cstep
  >> disch_then $ irule_at Any
  >> fs[]
QED

Theorem clstep_imp_cstep_RTC:
  !sM sM'.
    RTC (λ(s,M) (s',M'). ?prom. clstep p cid s M prom s' /\ M = M') sM sM'
    ==> RTC (λ(s,M) (s',M'). ?prom. cstep p cid s M prom s' M /\ M = M') sM sM'
Proof
  ho_match_mp_tac RTC_INDUCT
  >> rw[RTC_REFL,ELIM_UNCURRY]
  >> irule $ cj 2 RTC_RULES
  >> goal_assum $ dxrule_at Any
  >> fs[ELIM_UNCURRY]
  >> irule_at Any clstep_imp_cstep
  >> goal_assum drule
QED

Theorem clstep_imp_cstep_seq:
  clstep p cid s M prom s'
  ==> cstep_seq p cid (s,M) (s',M)
Proof
  rw[cstep_seq_cases]
  >> goal_assum drule
QED

Theorem clstep_imp_cstep_seq_RC:
  !sM sM'.
    RC (λ(s,M) (s',M'). ?prom. clstep p cid s M prom s' /\ M = M') sM sM'
    ==> RC (cstep_seq p cid) sM sM'
Proof
  rw[RC_DEF]
  >> disj2_tac
  >> fs[ELIM_UNCURRY,cstep_seq_cases]
  >> disj1_tac
  >> irule_at Any $ GSYM PAIR
  >> qhdtm_x_assum `clstep` $ irule_at Any
  >> fs[]
QED

Theorem clstep_imp_cstep_seq_RTC:
  !sM sM'.
    RTC (λ(s,M) (s',M'). ?prom. clstep p cid s M prom s' /\ M = M') sM sM'
    ==> RTC (cstep_seq p cid) sM sM'
Proof
  ho_match_mp_tac RTC_INDUCT
  >> rw[RTC_REFL]
  >> irule $ cj 2 RTC_RULES
  >> goal_assum $ dxrule_at Any
  >> rewrite_tac[cstep_seq_cases]
  >> disj1_tac
  >> fs[ELIM_UNCURRY,PULL_EXISTS,FORALL_PROD]
  >> goal_assum $ dxrule_at Any
  >> fs[]
QED

val _ = export_theory ();
