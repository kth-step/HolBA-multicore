(*
 * Spinlock proofs
 *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory llistTheory wordsLib
     finite_mapTheory string_numTheory relationTheory
     bir_programTheory bir_promisingTheory
     bir_promising_wfTheory bir_programLib
     listTheory rich_listTheory arithmeticTheory
     example_spinlockTheory promising_thmsTheory
open strongPostCondLib

val _ = new_theory "example_spinlockProof";

Theorem bir_exec_stmt_cjmp_cases:
  !xx p e a b s. (bir_exec_stmt_cjmp (BirProgram p) e (BLE_Label $ a) (BLE_Label $ b) s).bst_pc.bpc_label = xx
  /\ MEM a $ bir_labels_of_program $ BirProgram p
  /\ MEM b $ bir_labels_of_program $ BirProgram p
  ==> (xx = a \/ xx = b \/ xx = s.bst_pc.bpc_label)
Proof
  rpt gen_tac
  >> csimp[bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def,bir_state_set_typeerror_def,bir_eval_label_exp_def,bir_exec_stmt_jmp_to_label_def,optionTheory.option_case_compute,bir_block_pc_def]
  >> fs[COND_RATOR,COND_RAND]
  >> BasicProvers.every_case_tac
  >> gvs[]
QED

Theorem LRC_APPEND:
  !ls1 ls2 R x y. ~NULL ls2
  ==>
    LRC R (ls1 ++ ls2) x y = (LRC R ls1 x (HD ls2) /\ LRC R ls2 (HD ls2) y)
Proof
  Induct >> fs[listTheory.LRC_def]
  >- (Cases >> csimp[listTheory.LRC_def])
  >> csimp[PULL_EXISTS,AC CONJ_ASSOC CONJ_COMM]
QED

Theorem LRC_TAKE_DROP:
  !R n ls x y. n < LENGTH ls
  ==> LRC R ls x y = (LRC R (TAKE n ls) x (EL n ls) /\ LRC R (DROP n ls) (EL n ls) y)
Proof
  rw[]
  >> CONV_TAC $ LAND_CONV $ ONCE_REWRITE_CONV[GSYM listTheory.TAKE_DROP]
  >> fs[LRC_APPEND,listTheory.HD_DROP,listTheory.LENGTH_DROP,GSYM rich_listTheory.LENGTH_NOT_NULL]
QED

Theorem LRC_TAKE_SUC:
  !R n ls x y.
  SUC n <= LENGTH ls ==> LRC R (TAKE (SUC n) ls) x y
    = (LRC R (TAKE n ls) x (EL n ls) /\ R (EL n ls) y)
Proof
  rpt strip_tac
  >> reverse $ dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >> fs[]
  >- (
    `n < LENGTH ls` by fs[]
    >> dxrule_then mp_tac LRC_TAKE_DROP
    >> fs[TAKE_LENGTH_ID,DROP_CONS_EL,DROP_LENGTH_NIL,LRC_def]
  )
  >> qspecl_then [`n`,`ls`] mp_tac TAKE_DROP
  >> disch_then $ CONV_TAC o LAND_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> fs[TAKE_APPEND,TAKE_TAKE_MIN,MIN_DEF]
  >> qmatch_goalsub_abbrev_tac `LRC R (l1 ++ l2) x y`
  >> qspecl_then [`l1`,`l2`] mp_tac LRC_APPEND
  >> unabbrev_all_tac
  >> fs[GSYM LENGTH_NOT_NULL]
  >> disch_then kall_tac
  >> REWRITE_TAC[GSYM EL]
  >> fs[REWRITE_RULE[GSYM NULL_EQ,GSYM LENGTH_NOT_NULL] TAKE1,LRC_def,EL_DROP,Excl"EL_restricted.1"]
  >> fs[]
QED

Theorem LRC_HD:
  !ls R x y. ~NULL ls /\ LRC R ls x y ==> x = HD ls
Proof
  Cases >> fs[listTheory.LRC_def]
QED

Theorem LRC_LAST:
  !ls R x y. ~NULL ls /\ LRC R ls x y ==> R (LAST ls) y
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `LRC R ls x y`
  >> `LRC R (FRONT ls ++ [LAST ls]) x y` by fs[NULL_EQ,APPEND_FRONT_LAST]
  >> dxrule_at (Pat `LRC`) $ iffLR LRC_APPEND
  >> fs[LRC_def]
QED

Theorem LRC_TAKE_DROP_SUC:
  !R n ls x y. SUC n < LENGTH ls
  ==> LRC R ls x y = (LRC R (TAKE n ls) x (EL n ls)
  /\ R (EL n ls) (EL (SUC n) ls)
  /\ LRC R (DROP (SUC n) ls) (EL (SUC n) ls) y)
Proof
  rw[]
  >> `n < LENGTH ls` by fs[]
  >> dxrule_then (fs o single) LRC_TAKE_DROP
  >> `1 < LENGTH $ DROP n ls` by fs[]
  >> dxrule_then (fs o single) LRC_TAKE_DROP
  >> fs[rich_listTheory.DROP_DROP_T,listTheory.EL_DROP,GSYM arithmeticTheory.ADD1,listTheory.TAKE1_DROP,listTheory.LRC_def]
QED


(* relation that states equality of an fmap and a map 'a -> ('b option) *)
Definition env_to_fmap_def:
  env_to_fmap env fmap =
    !id x. env id = SOME x <=> FLOOKUP fmap id = SOME x
End

Theorem env_to_fmap_FLOOKUP:
  env_to_fmap (FLOOKUP f) f
Proof
  fs[env_to_fmap_def]
QED

Theorem MOD_UNIQUE_EQ =
  Q.SPEC `λn. r = n` arithmeticTheory.MOD_P
  |> SIMP_RULE std_ss []
  |> GEN_ALL

Definition DRESTR_SUBMAP_def:
  DRESTR_SUBMAP names fm fm' <=> (DRESTRICT fm names) SUBMAP (DRESTRICT fm' names)
End

Theorem DRESTR_SUBMAP_eq_FLOOKUP:
  DRESTR_SUBMAP ids fm fm' = !id v. FLOOKUP fm id = SOME v /\ id IN ids ==> FLOOKUP fm' id = SOME v
Proof
  fs[DRESTR_SUBMAP_def,FLOOKUP_DRESTRICT,SUBMAP_FLOOKUP_EQN,AC CONJ_ASSOC CONJ_COMM]
QED

(* positive restriction: only equality on ids *)
Definition restr_submap_def:
  restr_submap ids f f' <=> !id v. f id = SOME v /\ id IN ids ==> f' id = SOME v
End

Theorem env_to_fmap_restr_submap_eq_DRESTR_SUBMAP:
  env_to_fmap env fmap /\ env_to_fmap env' fmap'
  ==> restr_submap ids env env' = DRESTR_SUBMAP ids fmap fmap'
Proof
  rw[EQ_IMP_THM,DRESTR_SUBMAP_eq_FLOOKUP]
  >> gs[restr_submap_def,env_to_fmap_def]
QED

(* negative restriction: equality everywhere but on ids *)
Definition restr_submap_neg_def:
  restr_submap_neg ids f f' <=>
    (!id. id NOTIN ids ==> IS_SOME $ f id = IS_SOME $ f' id)
    /\ !id v. f id = SOME v /\ id NOTIN ids ==> f' id = SOME v
End

Theorem restr_submap_neg_EMPTY:
  restr_submap_neg {} f f' <=> f = f'
Proof
  EQ_TAC >> fs[restr_submap_neg_def]
  >> rw[FUN_EQ_THM]
  >> qmatch_goalsub_rename_tac `f x = f' x`
  >> Cases_on `f x`
  >> fs[]
  >> ntac 2 $ first_x_assum $ qspec_then `x` assume_tac
  >> gs[]
QED

Definition DRESTR_SUBMAP_neg_def:
  DRESTR_SUBMAP_neg ids fm fm' <=>
    (!id. id NOTIN ids ==> FLOOKUP fm id = FLOOKUP fm' id)
    /\ !id v. FLOOKUP fm id = SOME v /\ id NOTIN ids ==> FLOOKUP fm' id = SOME v
End

Theorem DRESTR_SUBMAP_neg_EMPTY:
  !fm fm'. DRESTR_SUBMAP_neg {} fm fm' <=> fm = fm'
Proof
  rw[EQ_IMP_THM,DRESTR_SUBMAP_neg_def,FUN_EQ_THM,FLOOKUP_EXT]
QED

Theorem IS_SOME_eq_imp:
  (!x. a = SOME x <=> b = SOME x) ==> IS_SOME a = IS_SOME b
Proof
  fs[optionTheory.IS_SOME_EXISTS]
QED

Theorem env_to_fmap_restr_submap_neg_eq_DRESTR_SUBMAP_neg:
  env_to_fmap env fmap /\ env_to_fmap env' fmap'
  ==> restr_submap_neg ids env env' = DRESTR_SUBMAP_neg ids fmap fmap'
Proof
  rw[EQ_IMP_THM]
  >> gs[restr_submap_neg_def,env_to_fmap_def,DRESTR_SUBMAP_neg_def]
  >- (
    rw[]
    >> qmatch_goalsub_rename_tac `FLOOKUP fmap id = FLOOKUP fmap' id`
    >> rpt $ first_x_assum $ qspec_then `id` assume_tac
    >> imp_res_tac IS_SOME_eq_imp
    >> Cases_on `FLOOKUP fmap id`
    >> gvs[]
  )
  >> rw[]
  >> qmatch_goalsub_rename_tac `IS_SOME $ env id = IS_SOME $ env' id`
  >> rpt $ first_x_assum $ qspec_then `id` assume_tac
  >> imp_res_tac IS_SOME_eq_imp
  >> gvs[]
QED

Theorem DRESTR_SUBMAP_neg_EMPTY':
  !fm fm'. DRESTR_SUBMAP_neg {} fm fm' <=> fm = fm'
Proof
  rpt gen_tac
  >> irule EQ_TRANS
  >> irule_at Any $ GSYM env_to_fmap_restr_submap_neg_eq_DRESTR_SUBMAP_neg
  >> irule_at Any EQ_TRANS
  >> irule_at Any restr_submap_neg_EMPTY
  >> ntac 2 $ irule_at Any env_to_fmap_FLOOKUP
  >> fs[FLOOKUP_EXT]
QED

(* below: general TODO move *)

Theorem mem_is_loc_eq:
  !t M l l'. mem_is_loc M t l /\ mem_is_loc M t l' /\ 0 < t ==> l = l'
Proof
  Cases >> rw[mem_is_loc_def,listTheory.oEL_THM,AllCaseEqs()]
QED

Theorem cstep_same_label:
  !P p cid s M prom s' M' stmt.
  cstep P p cid s M prom s' M'
  /\ bir_get_current_statement p s.bst_pc = SOME stmt
  /\ ((!cond_e lbl1 lbl2. stmt <> BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2)
    /\ (!lbl. stmt <> BSGen $ BStmtE $ BStmt_Jmp lbl)
    /\ (!R. stmt <> BSExt R))
  ==> s'.bst_pc.bpc_label = s.bst_pc.bpc_label
Proof
  rpt strip_tac
  >> fs[cstep_cases,clstep_cases,bir_pc_next_def,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,fence_updates_def]
  >> gvs[bmc_exec_general_stmt_exists,AllCaseEqs(),bir_exec_stmt_halt_def,bir_exec_stmt_assume_def,bir_exec_stmt_assert_def,bir_state_set_typeerror_def]
QED

Definition parstep_tr_def:
  parstep_tr P cid tpM tpM' = parstep P cid (FST tpM) (SND tpM) (FST tpM') (SND tpM')
End

Theorem FEVERY_FLOOKUP_eq:
  !P fmap. FEVERY P fmap = !id v. FLOOKUP fmap id = SOME v ==> P (id,v)
Proof
  fs[FEVERY_DEF,flookup_thm]
QED

Theorem FLOOKUP_FEVERY = FEVERY_FLOOKUP_eq

Theorem FEVERY_FUPDATE':
  !P f x y.
    FEVERY P (f |+ (x,y)) <=>
    P (x,y) /\ !z v. FLOOKUP f z = SOME v /\ z <> x ==> P (z,v)
Proof
  csimp[FLOOKUP_DRESTRICT,pred_setTheory.IN_COMPL,pred_setTheory.IN_SING,FEVERY_FUPDATE,FLOOKUP_FEVERY,AC CONJ_ASSOC CONJ_COMM]
QED

Theorem bir_eval_exp_indep_stmtE:
  !var name imm s p addr.
  bir_eval_exp (BExp_Den var) s.bst_environ
  = bir_eval_exp (BExp_Den var) ((bir_exec_stmtE p
             (BStmt_Jmp (BLE_Label (BL_Address (Imm64 addr)))) s).bst_environ)
Proof
  Cases
  >> rw[bir_expTheory.bir_eval_exp_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_state_set_typeerror_def,bir_exec_stmt_jmp_to_label_def]
  >> BasicProvers.every_case_tac
  >> fs[]
QED

Theorem bir_pc_next_bpc_label_eq:
  (!s x. s.bst_pc.bpc_label = x ==> (bir_pc_next s.bst_pc).bpc_label = x)
  /\ (!s x. s.bst_pc.bpc_index = x ==> (bir_pc_next s.bst_pc).bpc_index = SUC x)
Proof
  fs[bir_pc_next_def]
QED

Theorem bir_programcounter_t_intro:
  !x n lbl.
    x.bpc_index = n
    /\ x.bpc_label = lbl
    <=> x = <| bpc_index := n; bpc_label := lbl |>
Proof
  fs[bir_programcounter_t_component_equality,AC CONJ_ASSOC CONJ_COMM]
QED

Definition is_store_def:
  is_store p pc a_e =
  ?var_succ v_e xcl acq rel.
    bir_get_current_statement p pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel
End

Definition is_load_def:
  is_load p pc a_e =
  ?var opt_cast xcl acq rel.
    bir_get_current_statement p pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel
End

(* the statement in program p at pc can jump to the address  jump_target  *)
Definition is_jump_def:
  is_jump p pc jump_target =
  ?x.
    bir_get_current_statement p pc = SOME $ BSGen $ BStmtE x
    /\ (x = BStmt_Jmp (BLE_Label jump_target)
      \/ ?e pc'.
        x = BStmt_CJmp e (BLE_Label jump_target) (BLE_Label pc')
        /\ x = BStmt_CJmp e (BLE_Label pc') (BLE_Label jump_target))
End

(* TODO external blocks should be required to only jump to index 0 *)
Definition is_ext_jump_def:
  is_ext_jump p pc jump_target =
  ?R s M s'.
  bir_get_current_statement p pc = SOME $ BSExt R
  /\ R (s,M) s'
  /\ s.bst_pc = pc
  /\ s'.bst_pc = <| bpc_index := 0; bpc_label := BL_Address $ Imm64 jump_target |>
End

Definition FEVERY_prog_def:
  FEVERY_prog p P cores =
    FEVERY (λ(cid,v). !s. v = Core cid p s ==> P cid s) cores
End

Theorem FEVERY_prog_eq1:
  !p P cores cid s.
  P cid s /\ (!s. FLOOKUP cores cid = SOME $ Core cid p s ==> P cid s)
  ==>
  FEVERY_prog p P (cores |+ (cid, Core cid p s))
  = FEVERY_prog p P cores
Proof
  dsimp[FEVERY_FUPDATE',FEVERY_prog_def]
  >> rw[FLOOKUP_FEVERY,EQ_IMP_THM]
  >> qmatch_goalsub_rename_tac `P id s'`
  >> qmatch_assum_rename_tac `P cid s`
  >> Cases_on `cid = id` >> fs[]
QED

Theorem FEVERY_prog_eq2:
  !p P cores cid s s'.
  ~P cid s /\ FLOOKUP cores cid = SOME $ Core cid p s' /\ ~P cid s'
  ==>
  FEVERY_prog p P (cores |+ (cid, Core cid p s))
  = FEVERY_prog p P cores
Proof
  dsimp[FEVERY_FUPDATE',FEVERY_prog_def]
  >> rw[FLOOKUP_FEVERY]
  >> dsimp[]
  >> goal_assum drule_all
QED

(* cores running program parameterised by core id *)
Definition run_prog_def:
  run_prog cores prog =
  !cid p s. FLOOKUP cores cid = SOME $ Core cid p s
    ==> p = prog cid
End

Definition run_progc_def:
  run_progc cores p = run_prog cores (λx:num. p)
End

Theorem parstep_FLOOKUP:
  !p' p cid' cid cores M cores' M' s s' P.
    FLOOKUP cores cid = SOME $ Core cid p s
    /\ parstep P cid cores M cores' M'
    /\ FLOOKUP cores' cid = SOME $ Core cid' p' s'
    ==> cid' = cid /\ p = p'
Proof
  rpt gen_tac >> strip_tac
  >> gvs[FLOOKUP_UPDATE,cstep_cases,parstep_cases]
QED

Theorem run_prog_parstep_preserves:
  !cid cores M cores' M' prog P.
  parstep P cid cores M cores' M'
  /\ run_prog cores prog
  ==> run_prog cores' prog
Proof
  rpt strip_tac
  >> drule_at Any parstep_FLOOKUP
  >> gvs[parstep_cases,cstep_cases,run_prog_def]
  >> rpt strip_tac
  >- (
    Cases_on `cid = cid'`
    >> fs[FLOOKUP_UPDATE]
  )
  >> qmatch_assum_rename_tac `FLOOKUP (cores |+ (msg.cid,_)) cid = SOME $ Core cid p' s'`
  >> Cases_on `cid = msg.cid`
  >> fs[FLOOKUP_UPDATE]
QED

(* read a variable from an environment  *)

Definition bir_read_var_def:
  bir_read_var var env =
    bir_eval_exp (BExp_Den $ BVar var $ BType_Imm Bit64) env
End

Definition core_def:
  core cid S = THE $ FLOOKUP S cid
End

Definition core_state_def:
  core_state cid S = get_core_state $ core cid S
End

Definition core_prog_def:
  core_prog cid S = get_core_prog $ core cid S
End

Definition core_pc_def:
  core_pc cid S = bst_pc_tuple (core_state cid S).bst_pc
End

Theorem core_zoo =
  LIST_CONJ $
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
  [core_def,core_pc_def,core_state_def,get_core_state_def,core_prog_def,get_core_prog_def]

(* read a variable from a core state *)

Definition bir_read_core_reg_def:
  bir_read_core_reg var cid S v <=>
    bir_read_var var (core_state cid S).bst_environ
    = SOME $ BVal_Imm $ Imm64 v
End

(* read a zero variable from a core state *)
Definition bir_read_core_reg_zero_def:
  bir_read_core_reg_zero var cid S <=>
    bir_read_core_reg var cid S 0w
End

Definition bir_read_core_reg_nonzero_def:
  bir_read_core_reg_nonzero var cid S <=>
    ?v. bir_read_core_reg var cid S v /\ v <> 0w
End

(* spinlock abstract *)


(* sketch *)
(*
Theorem is_ext_jump_spinlock_abstract_BSExt =
  EVAL ``is_ext_jump spinlock_abstract pc jump_target``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM,COND_EXPAND,PULL_EXISTS]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [AC CONJ_ASSOC CONJ_COMM,bir_programcounter_t_component_equality,bir_state_t_accfupds]
*)

(* given location is not accessed neither by load nor store *)
Definition protected_loc_def:
  protected_loc p pc env loc <=>
    !a_e. (is_load p pc a_e \/ is_store p pc a_e)
     ==> bir_eval_exp a_e env <> SOME loc
End

(* several protected locations *)
Definition protected_locs_def:
  protected_locs p pc env locs <=>
    !loc. loc IN locs ==> protected_loc p pc env loc
End

Theorem bir_exec_stmtB_noop_unchanged =
  EVAL ``bir_exec_stmtB (BStmt_Assert $ BExp_Const $ Imm1 1w) s``
  |> GEN_ALL


(* registers and constraints on registers *)

(* registers written to within a statement *)
Definition registers_of_stmt_def:
  registers_of_stmt stmt :bir_var_t list =
    case stmt of
    | BMCStmt_Load var _ _ _ _ _ => [var]
    | BMCStmt_Store var _ _ _ _ _ => [var]
    | BMCStmt_Amo var exp1 exp2 _ _ => [var]
    | BMCStmt_Assign var exp => [var]
    | BMCStmt_Fence _ _ => []
    | BMCStmt_Assert exp => []
    | BMCStmt_Assume exp => []
End

Definition registers_of_block_def:
  registers_of_block bl =
    case bl of
    | BBlock_Stmts stmts_bl =>
      FLAT $ MAP registers_of_stmt stmts_bl.bb_statements
    | BBlock_Ext _ => []
End

Definition registers_of_prog_def:
  registers_of_prog (BirProgram progl) = FLAT $ MAP registers_of_block progl
End

Theorem registers_of_prog_lock =
  EVAL ``nub $ registers_of_prog (BirProgram $ lock lock_addr 0w jump_after)``

Theorem registers_of_prog_unlock =
  EVAL ``nub $ registers_of_prog (BirProgram $ unlock lock_addr unlock_entry)``

(* separation of registers *)
Definition registers_wf_def:
  registers_wf blocks jump_after unlock_entry <=>
    list_disj (registers_of_prog $ BirProgram blocks) $ registers_of_prog ((BirProgram $ unlock lock_addr unlock_entry) : progc_t)
    /\ list_disj (registers_of_prog $ BirProgram blocks) $ registers_of_prog ((BirProgram $ lock lock_addr 0w jump_after) : progc_t)
End

(* inclusion of state modulo register names *)
(* s restricted to names is a subset of s': s|_names ⊆ s' *)

Definition state_mod_subset_def:
  state_mod_subset names s s' <=>
    ?a a'. BEnv a = s.bst_environ /\ BEnv a' = s'.bst_environ
    /\ restr_submap_neg names a a'
    (* this is the fixed type of variable types for these kind of programs *)
    /\ DRESTR_SUBMAP_neg (IMAGE (λs. BVar s $ BType_Imm Bit64) names) s.bst_viewenv s'.bst_viewenv
    (* equality of rest of the state *)
    /\ !x y. s with <| bst_environ := x; bst_viewenv := y |> = s' with <| bst_environ := x; bst_viewenv := y |>
End



(* TODO define the state separation property depending on

registers_of_prog (BirProgram $ lock lock_addr 0w jump_after)
/\ registers_of_prog (BirProgram $ unlock lock_addr unlock_entry)

for the refinement property and add it to the refinement relation

fmap restricted inclusion

*)


(* well-formed labels *)
Definition labels_wf_def:
  labels_wf blocks jump_after unlock_entry <=>
    list_disj (bir_labels_of_program $ BirProgram blocks) $ bir_labels_of_program ((BirProgram $ unlock lock_addr unlock_entry) : progc_t)
    /\ list_disj (bir_labels_of_program $ BirProgram blocks) $ bir_labels_of_program ((BirProgram $ lock lock_addr 0w jump_after) :  progc_t)
    /\ list_disj
      (bir_labels_of_program ((BirProgram $ lock lock_addr 0w jump_after) : progc_t))
      $ bir_labels_of_program ((BirProgram $ unlock lock_addr unlock_entry) : progc_t)
    /\ ALL_DISTINCT $
        bir_labels_of_program ((BirProgram $ lock lock_addr 0w jump_after ++ unlock lock_addr unlock_entry ++ blocks) : progc_t)
    /\ MEM jump_after $ bir_labels_of_program $ BirProgram blocks
    /\ ~(MEM (BL_Address $ Imm64 $ unlock_entry + 12w) $ bir_labels_of_program $ (BirProgram $ lock lock_addr 0w jump_after ++ blocks ++ unlock lock_addr unlock_entry) : progc_t)
End

Theorem labels_wf_eq =
  REFL ``labels_wf blocks jump_after unlock_entry``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss)
    [labels_wf_def,bir_labels_of_program_unlock,bir_labels_of_program_lock,list_disj_def,bir_labels_of_program_APPEND]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem labels_wf_imp =
  iffLR labels_wf_eq
  |> CONV_RULE $ RAND_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [AC CONJ_ASSOC CONJ_COMM]

Theorem labels_wf_jump_after_lock_unlock:
  !blocks jump_after unlock_entry.
  labels_wf blocks jump_after unlock_entry
  ==> ~(MEM jump_after $ bir_labels_of_program ((BirProgram $ unlock lock_addr unlock_entry) : progc_t))
    /\ ~(MEM jump_after $ bir_labels_of_program ((BirProgram $ lock lock_addr 0w jump_after) :  progc_t))
Proof
  fs[labels_wf_def,list_disj_def]
QED

Theorem labels_wf_jump_after =
  labels_wf_jump_after_lock_unlock
  |> SIMP_RULE (srw_ss()) [bir_labels_of_program_lock,bir_labels_of_program_unlock,AC CONJ_ASSOC CONJ_COMM]

(*
Theorem is_load_spinlock_concrete2 =
  REFL ``is_load (spinlock_concrete2 blocks unlock_entry) pc a_e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [is_load_def,is_store_def,bir_get_spinlock_cprog_zoo]
  |> GEN_ALL

Theorem is_store_spinlock_concrete2 =
  REFL ``is_store (spinlock_concrete2 blocks unlock_entry) pc a_e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [is_load_def,is_store_def,bir_get_spinlock_cprog_zoo]
  |> GEN_ALL
*)

Theorem spinlock_concrete_wf_ext:
  !cid s M blocks jump_after unlock_entry.
    labels_wf blocks jump_after unlock_entry
    /\ wf_ext (BirProgram blocks) cid s M
    ==> wf_ext (spinlock_concrete2 blocks jump_after unlock_entry) cid s M
Proof
  rw[wf_ext_def,spinlock_concrete2_def,lock_wrap_def,labels_wf_def]
  >> gs[list_disj_sym_imp,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND,bir_get_current_statement_BirProgram_APPEND]
  >> BasicProvers.every_case_tac
  >> fs[bgcs_lock_zoo,bgcs_unlock_zoo]
  >> first_x_assum $ drule_then irule
QED

(* bir_eval_exp equalities *)

Theorem bir_eval_exp_env_update_cast64:
  !var' env v new_env var var_name.
    env_update_cast64 (bir_var_name var) (BVal_Imm v) (bir_var_type var) env
    = SOME new_env
    /\ var = (BVar var_name (BType_Imm Bit64))
    /\ bir_var_name var' <> bir_var_name var
  ==>
    bir_eval_exp (BExp_Den var') env
    = bir_eval_exp (BExp_Den var') new_env
Proof
  gen_tac >> ntac 3 Cases
  >> rw[env_update_cast64_def,bir_envTheory.bir_env_update_def]
  >> EVAL_TAC
  >> fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def]
QED

Theorem bir_exec_stmt_cjmp_second:
  !s.
  bir_eval_exp (BExp_Den (BVar "success" (BType_Imm Bit64))) s.bst_environ =
        SOME (BVal_Imm (Imm64 0w))
  ==> bir_exec_stmt_cjmp spinlock_concrete
  (BExp_UnaryExp BIExp_Not
      (BExp_BinPred BIExp_Equal
        (BExp_Den (BVar "success" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0w)))) (BLE_Label (BL_Address (Imm64 4w)))
  (BLE_Label (BL_Address (Imm64 24w))) s
  = s with bst_pc := <| bpc_label := (BL_Address $ Imm64 24w); bpc_index := 0 |>
Proof
  rpt gen_tac
  >> EVAL_TAC
  >> BasicProvers.every_case_tac
  >> rpt $ pop_assum mp_tac
  >> EVAL_TAC
QED

Theorem bir_exec_stmt_cjmp_first:
  !s v.
  bir_eval_exp (BExp_Den (BVar "success" (BType_Imm Bit64))) s.bst_environ =
        SOME (BVal_Imm (Imm64 v))
        /\ v <> 0w
  ==> bir_exec_stmt_cjmp spinlock_concrete
  (BExp_UnaryExp BIExp_Not
      (BExp_BinPred BIExp_Equal
        (BExp_Den (BVar "success" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0w)))) (BLE_Label (BL_Address (Imm64 4w)))
  (BLE_Label (BL_Address (Imm64 24w))) s
  = s with bst_pc := <| bpc_label := (BL_Address $ Imm64 4w); bpc_index := 0 |>
Proof
  rpt gen_tac
  >> EVAL_TAC
  >> BasicProvers.every_case_tac
  >> rpt $ pop_assum mp_tac
  >> EVAL_TAC
  >> rw[]
QED

Definition slc_mem_inv_def:
  slc_mem_inv prom M =
  !t v. mem_read M lock_addr_val t = SOME v /\ ~MEM t prom
  ==> ?x. v = BVal_Imm $ Imm64 x
End


(* spinlock: concrete invariant, parameterised *)

Definition slc_inv_def:
  slc_inv lock_entry jump_after unlock_entry cid s M <=>
  slc_mem_inv s.bst_prom M /\
  !lbl index.
    bst_pc_tuple s.bst_pc = (BL_Address $ Imm64 lbl, index)
  ==>
    (lbl = lock_entry + 12w /\ 0 < index ==> ?v. bir_read_reg "success" s.bst_environ v)
    /\ (lbl = lock_entry + 16w ==> ?v. bir_read_reg "success" s.bst_environ v)
    /\ ((lbl = lock_entry + 0w /\ index = 1) \/ lbl = lock_entry + 4w
    ==>
      IS_SOME s.bst_xclb
      /\ ((THE s.bst_xclb).xclb_time <= s.bst_coh lock_addr_val
      /\ latest_t lock_addr_val M (THE s.bst_xclb).xclb_time (s.bst_coh lock_addr_val))
      /\ IS_SOME $ mem_read M lock_addr_val (THE s.bst_xclb).xclb_time
      /\
      (~MEM (THE s.bst_xclb).xclb_time s.bst_prom
      ==> ?v. bir_read_reg "x5" s.bst_environ v
        /\ mem_read M lock_addr_val (THE s.bst_xclb).xclb_time = SOME $ BVal_Imm $ Imm64 v)
    )
    (* up until to the store we have v_rOld = coh lock
       spinlock_concrete2_v_rOld_eq_coh_inv *)
    /\ (
      (lbl = lock_entry + 0w
      \/ lbl = lock_entry + 4w
      \/ lbl = lock_entry + 8w
      \/ (lbl = lock_entry + 12w /\ index = 0))
      ==>
      s.bst_v_rOld = s.bst_coh lock_addr_val
      /\ s.bst_v_rNew = 0 (* initial value *)
    )
    (* equalities due to starting out from initial state *)
    /\ (
      ((lbl = lock_entry + 0w /\ 0 < index)
      \/ lbl = lock_entry + 4w
      \/ lbl = lock_entry + 8w
      \/ (lbl = lock_entry + 12w /\ index = 0))
      ==>
        IS_SOME s.bst_xclb
        /\ s.bst_v_rOld = (THE s.bst_xclb).xclb_view
        /\ (THE s.bst_xclb).xclb_view = (THE s.bst_xclb).xclb_time
    )
    /\ (lbl = lock_entry + 8w /\ index = 0 ==>
      IS_SOME s.bst_xclb
      /\ bir_read_reg "x5" s.bst_environ 0w
      /\ IS_SOME $ mem_read M lock_addr_val (THE s.bst_xclb).xclb_time
      /\ (~MEM (THE s.bst_xclb).xclb_time s.bst_prom
        ==> mem_read M lock_addr_val (THE s.bst_xclb).xclb_time = SOME $ BVal_Imm $ Imm64 0w)
      /\ ((THE s.bst_xclb).xclb_time <= s.bst_coh lock_addr_val
      /\ latest_t lock_addr_val M (THE s.bst_xclb).xclb_time (s.bst_coh lock_addr_val))
    )
    /\ ((lbl = lock_entry + 8w /\ index = 1)
      \/ (lbl = lock_entry + 12w /\ index = 0)
      ==>
      IS_SOME s.bst_xclb
      /\ bir_read_reg "x5" s.bst_environ 1w
      /\ IS_SOME $ mem_read M lock_addr_val (THE s.bst_xclb).xclb_time
      /\ (~MEM (THE s.bst_xclb).xclb_time s.bst_prom
        ==> mem_read M lock_addr_val (THE s.bst_xclb).xclb_time = SOME $ BVal_Imm $ Imm64 0w)
      /\ ((THE s.bst_xclb).xclb_time <= s.bst_coh lock_addr_val
      /\ latest_t lock_addr_val M (THE s.bst_xclb).xclb_time (s.bst_coh lock_addr_val))
    )
    /\ ((((lbl = lock_entry + 12w /\ index = 1) \/ lbl = lock_entry + 16w)
      /\ bir_read_reg_zero "success" s.bst_environ)
      ==>
      ?t.
      t <= LENGTH M
      /\ IS_SOME $ mem_read M lock_addr_val t
      /\ (~MEM t s.bst_prom
        ==> mem_read M lock_addr_val t = SOME $ BVal_Imm $ Imm64 0w)
      /\ mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w
      /\ ~MEM (s.bst_coh lock_addr_val) s.bst_prom
      /\ fulfil_atomic_ok M lock_addr_val cid t (s.bst_coh lock_addr_val)
    )
    /\ ((lbl = lock_entry + 16w /\ index = 1)
      /\ bir_read_reg_zero "success" s.bst_environ
      ==> mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ (s.bst_pc.bpc_label = jump_after /\ index = 0
      ==> mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ ((lbl = unlock_entry \/ lbl = unlock_entry + 4w)
      ==> mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ (lbl = unlock_entry + 8w /\ index = 0
      ==>
      mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ (lbl = unlock_entry /\ index = 1
      ==> bir_read_reg "x5" s.bst_environ 0w)
End

Theorem slc_inv_slc_mem_inv_imp:
  !lock_entry jump_after unlock_entry cid s M.
  slc_inv lock_entry jump_after unlock_entry cid s M ==> slc_mem_inv s.bst_prom M
Proof
  fs[slc_inv_def]
QED

Theorem slc_inv_APPEND:
  !v jump_after unlock_entry msg s M.
  slc_inv v jump_after unlock_entry msg.cid s M
  /\ s.bst_coh lock_addr_val <= LENGTH M
  ==> slc_inv v jump_after unlock_entry msg.cid
        (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))
        (M ++ [msg])
Proof
  rpt strip_tac
  >> simp[slc_inv_def]
  >> conj_tac
  >- (
    imp_res_tac slc_inv_slc_mem_inv_imp
    >> rw[slc_mem_inv_def,mem_read_append]
    >> qmatch_asmsub_rename_tac `mem_read _ _ t = SOME _`
    >> `t <= LENGTH M` by (
      imp_res_tac mem_read_some >> fs[]
    )
    >> fs[mem_read_append,arithmeticTheory.NOT_NUM_EQ,GSYM arithmeticTheory.LESS_EQ,slc_mem_inv_def]
    >> first_x_assum drule_all
    >> fs[]
  )
  >> fs[slc_inv_def,bst_pc_tuple_def]
  >> rw[] >> fs[mem_read_append,latest_t_append]
  >> gs[mem_read_append]
  >> qmatch_asmsub_rename_tac `IS_SOME $ mem_read _ _ t`
  >> qexists_tac `t`
  >> fs[mem_read_append,fulfil_atomic_ok_append]
QED

Theorem slc_mem_inv_subset:
  !prom prom' M.
  slc_mem_inv prom M
  /\ EVERY (λt. IS_SOME $ mem_read M lock_addr_val t ==> MEM t prom') prom
  ==> slc_mem_inv prom' M
Proof
  rw[slc_mem_inv_def]
  >> Cases_on `MEM t prom`
  >> fs[listTheory.EVERY_MEM]
  >> first_x_assum drule
  >> fs[]
QED

Theorem slc_inv_init:
  !cid jump_after blocks unlock_entry.
    labels_wf blocks jump_after unlock_entry
    ==> slc_inv 0w jump_after unlock_entry cid (bmc_state_init $ spinlock_concrete2 blocks jump_after unlock_entry) []
Proof
  rw[bir_init_progTheory.bmc_state_init_def,bir_pc_first_def,lock_wrap_def,lock_def,spinlock_concrete2_def,bir_programTheory.bir_label_of_block_def,bir_programTheory.bir_block_pc_def,bst_pc_tuple_def]
  >> rw[slc_inv_def,bst_pc_tuple_def,slc_mem_inv_def]
  >> imp_res_tac mem_read_some
  >> fs[mem_read_def,mem_get_def,mem_default_value_def,mem_default_def]
  >> gs[labels_wf_eq]
QED

Theorem sl_bir_eval_exp_Unary =
  EVAL ``bir_eval_exp (BExp_UnaryExp BIExp_Not
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar name (BType_Imm Bit64)))
            (BExp_Const (Imm64 0w)))) (BEnv f) = SOME v``
 |> SIMP_RULE (std_ss ++ boolSimps.DNF_ss) [AllCaseEqs(),COND_RATOR,Ntimes
 COND_RAND 2,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS]
 |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
 |> CONV_RULE $ RAND_CONV EVAL
 |> SIMP_RULE std_ss [COND_RATOR,COND_RAND]
 |> GEN_ALL

(* the lock remains taken by this core while in the critical section *)
Definition in_cs_inv_def:
  in_cs_inv prog label M coh addr value <=>
    MEM label (bir_labels_of_program prog)
    ==> mem_read M addr (coh addr) = SOME $ BVal_Imm value
End

Theorem bir_get_program_block_info_by_label_SOME_NONE:
  !A B lbl. list_disj (bir_labels_of_program $ BirProgram A) (bir_labels_of_program $ BirProgram B)
  /\ IS_SOME $ bir_get_program_block_info_by_label (BirProgram A) lbl
  ==> IS_NONE $ bir_get_program_block_info_by_label (BirProgram B) lbl
Proof
  rw[bir_get_program_block_info_by_label_THM,optionTheory.IS_SOME_EXISTS]
  >> qmatch_asmsub_abbrev_tac `SOME x` >> PairCases_on `x`
  >> fs[bir_get_program_block_info_by_label_THM,list_disj_def,bir_labels_of_program_def,listTheory.MEM_MAP,PULL_EXISTS]
  >> imp_res_tac rich_listTheory.EL_MEM
  >> first_x_assum drule
  >> fs[]
  >> disch_then $ drule_at Concl
  >> fs[]
QED

(* when transitioning from pc to pc' within section, either pc' was at the entry
 * of the section or pc was already within this section *)
Definition jump_constraints_def:
  jump_constraints pc pc' sections =
  EVERY (λsection.
    ~NULL section
    /\ MEM pc'.bpc_label $ bir_labels_of_program (BirProgram section :progc_t)
    /\ pc' <> bir_pc_first $ BirProgram section :progc_t
    ==> MEM pc.bpc_label $ bir_labels_of_program $ BirProgram section : progc_t
  ) sections
End

Theorem jump_constraints_eq:
  !pc pc' lock_entry jump_after unlock_entry.
  jump_constraints pc pc' [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
  <=>
  (MEM pc'.bpc_label $ bir_labels_of_program $ BirProgram (unlock lock_addr unlock_entry) : progc_t
    /\ pc' <> bir_block_pc (BL_Address $ Imm64 unlock_entry)
    ==> MEM pc.bpc_label $ bir_labels_of_program $ BirProgram (unlock lock_addr unlock_entry) : progc_t)
  /\ (MEM pc'.bpc_label $ bir_labels_of_program $ BirProgram (lock lock_addr 0w jump_after) : progc_t
    /\ pc' <> bir_block_pc (BL_Address $ Imm64 0w)
    ==> MEM pc.bpc_label $ bir_labels_of_program $ BirProgram (lock lock_addr 0w jump_after) : progc_t )
Proof
  dsimp[listTheory.EVERY_MEM,jump_constraints_def,bir_block_pc_def]
  >> fs[lock_NOT_NULL,unlock_NOT_NULL,lock_bir_pc_first,unlock_bir_pc_first]
QED

Theorem jump_constraints_thm:
  !pc pc' sections.
  jump_constraints pc pc' sections =
  EVERY (λsection.
    ~NULL section
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram section : progc_t)
    /\ MEM pc'.bpc_label $ bir_labels_of_program $ BirProgram section : progc_t
    ==> pc' = bir_pc_first $ BirProgram section :progc_t
  ) sections
Proof
  rpt strip_tac
  >> fs[jump_constraints_def,EQ_IMP_THM]
  >> conj_tac
  >> ho_match_mp_tac
    $ REWRITE_RULE[GSYM AND_IMP_INTRO] listTheory.EVERY_MEM_MONO
  >> rw[] >> gs[]
QED

(* only when in regions the addr may change *)
Definition addr_unchanged_def:
  addr_unchanged addr pc coh coh' prom prom' M regions <=>
  EVERY (λprogl. ~(MEM pc.bpc_label $ bir_labels_of_program (BirProgram progl : progc_t))) regions
      ==> coh addr = coh' addr
(* promset unchanged is a consequence of the above *)
(*
        /\ EVERY (λt. IS_SOME $ mem_read M addr t ==> MEM t prom') prom
*)
End

Theorem addr_unchanged_imp_promises_unchanged_clstep:
  !addr s s' M regions prom progl cid.
  addr_unchanged addr s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M regions
  (* No relation between regions and program required *)
  (* /\ EVERY (λregion. ?ls ls'. progl = ls ++ region ++ ls') regions (* subset *) *)
  /\ clstep progl cid s M prom s'
  /\ EVERY (λprogl. ~(MEM s.bst_pc.bpc_label $ bir_labels_of_program (BirProgram progl : progc_t))) regions
  ==> EVERY (λt. IS_SOME $ mem_read M addr t ==> MEM t s'.bst_prom) s.bst_prom
Proof
  rw[clstep_cases,addr_unchanged_def]
  >> fs[bir_state_read_view_updates_def,listTheory.EVERY_MEM,remove_prom_def,bir_state_fulful_view_updates_def,fence_updates_def,bir_exec_stmt_cjmp_mc_invar]
  >~ [`fulfil_update_viewenv`]
  >- (
    fs[optionTheory.IS_SOME_EXISTS]
    >> rpt strip_tac
    >> dxrule_then strip_assume_tac mem_get_mem_read
    >> fs[listTheory.MEM_FILTER] >> disch_then assume_tac
    >> gvs[]
    >> dxrule_then (drule_then assume_tac) mem_get_eq
    >> gs[]
    >> qpat_x_assum `s.bst_coh _ = _` mp_tac
    >> qpat_x_assum `_ < v_post` mp_tac
    >> simp[combinTheory.APPLY_UPDATE_THM]
  )
  >~ [`BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel`]
  >- (
    fs[optionTheory.IS_SOME_EXISTS]
    >> rpt strip_tac
    >> dxrule_then strip_assume_tac mem_get_mem_read
    >> fs[listTheory.MEM_FILTER] >> disch_then assume_tac
    >> gvs[]
    >> dxrule_then (drule_then assume_tac) mem_get_eq
    >> gs[]
    >> qpat_x_assum `s.bst_coh _ = _` mp_tac
    >> qpat_x_assum `s.bst_coh(|l |-> t_w|) l < t_w` mp_tac
    >> simp[combinTheory.APPLY_UPDATE_THM]
  )
  >~ [`BSExt R`]
  >- (
    fs[remove_prom_def,optionTheory.IS_SOME_EXISTS,listTheory.EVERY_MEM]
    >> rw[listTheory.MEM_FILTER]
    >> strip_tac
    >> imp_res_tac mem_read_mem_is_loc_imp
    >> first_x_assum $ drule_then strip_assume_tac
    >> dxrule_then (drule_then assume_tac) mem_is_loc_eq
    >> gs[]
  )
  >~ [`BSGen stm`]
  >- (
    drule_then assume_tac bmc_exec_general_stmt_mc_invar
    >> fs[]
  )
QED

Theorem addr_unchanged_imp_promises_unchanged_cstep:
  !addr s s' M regions prom M' progl cid P.
  addr_unchanged addr s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M regions
  /\ cstep P progl cid s M prom s' M'
  /\ EVERY (λprogl. ~(MEM s.bst_pc.bpc_label $ bir_labels_of_program (BirProgram progl : progc_t))) regions
  ==> EVERY (λt. IS_SOME $ mem_read M addr t ==> MEM t s'.bst_prom) s.bst_prom
Proof
  rw[cstep_cases]
  >- (
    drule_all addr_unchanged_imp_promises_unchanged_clstep
    >> fs[]
  )
  >> gs[addr_unchanged_def]
  >> rw[listTheory.EVERY_MEM]
QED

Theorem addr_unchanged_EVERY_APPEND:
  !addr pc coh coh' prom prom' M regions msg.
  addr_unchanged addr pc coh coh' prom prom' M regions
  /\ coh addr <= LENGTH M
  /\ EVERY (λt. t <= LENGTH M) prom
  /\ EVERY (λprogl.
      ~MEM pc.bpc_label (bir_labels_of_program (BirProgram progl))) regions
  /\ EVERY (λt. IS_SOME $ mem_read M addr t ==> MEM t prom') prom
  ==> EVERY (\t. IS_SOME (mem_read (M ++ [msg]) addr t) ==> MEM t prom') prom
Proof
  rw[addr_unchanged_def] >> fs[]
  >> rev_drule_at Any listTheory.EVERY_MEM_MONO
  >> disch_then irule
  >> rw[] >> gs[listTheory.EVERY_MEM,mem_read_append]
QED

Theorem addr_unchanged_APPEND:
  !addr pc coh coh' prom prom' M regions msg.
  addr_unchanged addr pc coh coh' prom prom' M regions
  /\ coh addr <= LENGTH M
  /\ EVERY (λt. t <= LENGTH M) prom
  /\ (
   EVERY (λprogl.
      ~MEM pc.bpc_label (bir_labels_of_program (BirProgram progl))) regions
    ==> EVERY (λt. IS_SOME $ mem_read M addr t ==> MEM t prom') prom
  )
  ==> addr_unchanged addr pc coh coh'
      (prom ++ [LENGTH M + 1]) prom' (M ++ [msg]) regions
Proof
  rpt strip_tac
  >> drule addr_unchanged_EVERY_APPEND
  >> fs[addr_unchanged_def]
QED

(* preservance of in_cs_inv *)
Theorem addr_unchanged_in_cs_inv:
  !bl1 blocks bl2 s M s' addr_val value.
  addr_unchanged addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [bl1; bl2]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh addr_val value
  /\ list_disj (bir_labels_of_program $ BirProgram blocks)
      (bir_labels_of_program $ BirProgram $ bl1 ++ bl2)
  /\ MEM s.bst_pc.bpc_label (bir_labels_of_program $ BirProgram blocks : progc_t)
  ==> in_cs_inv (BirProgram blocks) s'.bst_pc.bpc_label M s'.bst_coh addr_val value
Proof
  rw[in_cs_inv_def,addr_unchanged_def,list_disj_append2,bir_labels_of_program_APPEND,list_disj_def]
  >> gs[]
QED

(* clstep preserves in_cs_inv as memory is unchanged *)
Theorem clstep_in_cs_inv:
  !blocks jump_after unlock_entry cid s M s' prom.
  labels_wf blocks jump_after unlock_entry
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ clstep (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s'
  ==> in_cs_inv (BirProgram blocks) s'.bst_pc.bpc_label M s'.bst_coh lock_addr_val (Imm64 1w)
Proof
  rw[spinlock_concrete2_def,lock_wrap_def]
  >> qmatch_asmsub_abbrev_tac `clstep p`
  >> reverse $ Cases_on `IS_SOME $ bir_get_current_statement p s.bst_pc`
  >- gs[clstep_cases]
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> imp_res_tac bir_get_current_statement_SOME_MEM
  >> unabbrev_all_tac
  >> fs[bir_labels_of_program_APPEND]
  >~ [`bir_labels_of_program $ BirProgram $ lock lock_addr 0w jump_after`]
  >- (
    rw[in_cs_inv_def]
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> FULL_SIMP_TAC std_ss [GSYM listTheory.APPEND_ASSOC]
    >> drule_all_then assume_tac bir_get_current_statement_MEM1
    >> fs[labels_wf_def,list_disj_def]
    >> ntac 2 $ first_x_assum $ drule_then assume_tac
    >> fs[]
    >> gs[bir_labels_of_program_lock,clstep_cases,bgcs_lock_zoo,bir_pc_next_def,bir_state_read_view_updates_def,bmc_exec_general_stmt_exists,bir_state_fulful_view_updates_def]
    >> gvs[bir_exec_stmt_jmp_def,bir_exec_stmt_cjmp_def,bir_state_set_typeerror_def,AllCaseEqs(),bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_APPEND]
    >> BasicProvers.every_case_tac
    >> gvs[]
    >> fs[slc_inv_def,bst_pc_tuple_def,bir_read_reg_def,bir_read_reg_zero_def]
    >> fs[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,PULL_EXISTS,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS,combinTheory.APPLY_UPDATE_THM]
    >> gs[COND_RAND,COND_RATOR]
    >> qpat_x_assum `option_CASE _ _ _ = SOME F` $ assume_tac o CONV_RULE EVAL
    >> gs[COND_RAND,COND_RATOR]
  )
  >~ [`MEM s.bst_pc.bpc_label (bir_labels_of_program (BirProgram blocks : progc_t))`]
  >- (
    drule_then irule addr_unchanged_in_cs_inv
    >> simp[list_disj_append2,bir_labels_of_program_APPEND]
    >> fs[labels_wf_def]
  )
  >~ [`bir_labels_of_program $ BirProgram $ unlock lock_addr unlock_entry`]
  >> rw[in_cs_inv_def]
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> drule bir_get_current_statement_MEM2
  >> impl_tac
  >- fs[labels_wf_def,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND,list_disj_sym_imp]
  >> strip_tac
  >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,labels_wf_def,list_disj_def]
  >> gvs[clstep_cases,bgcs_unlock_zoo,bir_pc_next_def,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def]
  >> fs[AND_IMP_INTRO,FORALL_AND_THM,IMP_CONJ_THM]
  >> gvs[bir_labels_of_program_APPEND,bmc_exec_general_stmt_exists,bgcs_unlock_zoo]
  >> fs[bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,fence_updates_def,bir_pc_next_def]
  >~ [`BSGen $ BStmtE $ BStmt_Jmp _`]
  >- (
    BasicProvers.every_case_tac
    >> gs[bir_block_pc_def,bir_state_set_typeerror_def,bir_eval_label_exp_def]
  )
  >~ [`BSGen $ BStmtB $ BMCStmt_Fence _ _`]
  >- gs[]
  (* all remaining *)
  >~ [`BSGen $ BStmtE $ BStmt_Jmp _`]
  >> fs[COND_RATOR,COND_RAND,bir_block_pc_def]
  >> BasicProvers.every_case_tac
  >> gs[]
QED
Theorem cstep_in_cs_inv:
  !blocks jump_after unlock_entry cid s M s' M' prom P.
  labels_wf blocks jump_after unlock_entry
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ well_formed cid M s
  /\ cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s' M'
  ==> in_cs_inv (BirProgram blocks) s'.bst_pc.bpc_label M' s'.bst_coh lock_addr_val (Imm64 1w)
Proof
  rpt strip_tac >> gvs[cstep_cases]
  >- drule_all_then irule clstep_in_cs_inv
  >> fs[in_cs_inv_def] >> rw[]
  >> `s.bst_coh lock_addr_val <= LENGTH M` by fs[well_formed_def]
  >> fs[mem_read_append]
QED


(*
Theorem cstep_seq_in_cs_inv:
  !blocks jump_after unlock_entry cid s M s' M' P.
  labels_wf blocks jump_after unlock_entry
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ well_formed cid M s
  /\ cstep_seq (spinlock_concrete2 blocks jump_after unlock_entry) cid (s, M) (s', M')
  ==> in_cs_inv (BirProgram blocks) s'.bst_pc.bpc_label M' s'.bst_coh lock_addr_val (Imm64 1w)
Proof
  rpt strip_tac >> gvs[cstep_seq_cases,cstep_cases]
  >- drule_all_then irule clstep_in_cs_inv
  >> fs[in_cs_inv_def]
  >> irule clstep_in_cs_inv
  >> goal_assum $ drule_at Any
  >> `s.bst_coh lock_addr_val <= LENGTH M` by fs[well_formed_def]
  >> fs[in_cs_inv_def,mem_read_append,slc_inv_APPEND]
  >> qmatch_asmsub_rename_tac `[msg]`
  >> reverse $ Cases_on `msg.loc = lock_addr_val`
  >- fs[well_formed_def,addr_unchanged_APPEND]
  >> simp[addr_unchanged_def]
  >> strip_tac
  >> drule_then (irule_at Any) addr_unchanged_EVERY_APPEND
  >> fs[iffLR well_formed_def,addr_unchanged_def]
  >>



  >> conj_tac

  >- fs[mem_read_append,slc_inv_def]
  >> rw[]
  >> fs[mem_read_append]
QED
*)

Theorem clstep_slc_inv:
  !cid s M prom s' blocks jump_after unlock_entry.
  labels_wf blocks jump_after unlock_entry
  /\ wf_ext (BirProgram blocks : progc_t) cid s M
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ well_formed cid M s
  /\ clstep (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s'
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ jump_constraints s.bst_pc s'.bst_pc
    [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
  ==> slc_inv 0w jump_after unlock_entry cid s' M
Proof
  rpt strip_tac
  >> drule_at (Pat `clstep`) clstep_preserves_wf
  >> fs[spinlock_concrete_wf_ext,jump_constraints_eq] >> strip_tac
  >> Cases_on `MEM s.bst_pc.bpc_label (bir_labels_of_program $ BirProgram blocks : progc_t)`
  >- (
    drule_then (drule_then assume_tac) addr_unchanged_imp_promises_unchanged_clstep
    >> drule_at (Pat `addr_unchanged`) addr_unchanged_in_cs_inv
    >> disch_then $ drule_at_then (Pat `in_cs_inv`) assume_tac
    >> fs[labels_wf_def,list_disj_def,addr_unchanged_def]
    >> rpt $ first_x_assum (fn thm =>
      (drule_then assume_tac thm) >> (rev_drule_then assume_tac thm)
    )
    >> Cases_on `MEM s'.bst_pc.bpc_label (bir_labels_of_program (BirProgram (lock lock_addr 0w jump_after) : progc_t))`
    >- (
      gs[bir_block_pc_def]
      >> first_x_assum $ drule_then assume_tac
      >> simp[slc_inv_def,bst_pc_tuple_def]
      >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_labels_of_program_APPEND]
      >> imp_res_tac slc_inv_slc_mem_inv_imp
      >> drule_then (irule_at Any) slc_mem_inv_subset
      >> fs[]
      >> gvs[labels_wf_def]
      >> cheat (* TODO add another constraint that prevents jump from blocks to the start of the lock *)
          (* clstep s M s' /\ jump_constraints ... => s'.bst_pc <> (0,0) *)
    )
    >> Cases_on `MEM s'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram (unlock lock_addr unlock_entry) : progc_t`
    >- (
      last_x_assum $ drule_at_then Concl assume_tac
      >> gs[bir_block_pc_def]
      >> simp[slc_inv_def,bst_pc_tuple_def]
      >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_labels_of_program_APPEND]
      >> imp_res_tac slc_inv_slc_mem_inv_imp
      >> drule_all_then (irule_at Any) slc_mem_inv_subset
      (* by invariant that when entering unlock = the lock is held *)
      >> `mem_read M lock_addr_val (s'.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w` by (
        dxrule_then assume_tac $ iffLR in_cs_inv_def
        >> gs[]
        >> asm_rewrite_tac[]
      )
      >> fs[]
    )
    (* by CS invariant *)
    >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock]
    >> simp[slc_inv_def,bst_pc_tuple_def]
    >> imp_res_tac slc_inv_slc_mem_inv_imp
    >> drule_all_then (irule_at Any) slc_mem_inv_subset
    >> gen_tac >> strip_tac
    >> fs[]
    >> fs[in_cs_inv_def] (* TODO can in_cs_inv be omitted *)
  )
  >> imp_res_tac clstep_MEM_bir_labels_of_program
  >> Cases_on `MEM s'.bst_pc.bpc_label (bir_labels_of_program (BirProgram blocks : progc_t))`
  >- (
    
  )
  >> Cases_on `MEM s'.bst_pc.bpc_label (bir_labels_of_program (BirProgram A : progc_t))`
  >- (
    
  )
  >> Cases_on `MEM s'.bst_pc.bpc_label (bir_labels_of_program (BirProgram C : progc_t))`
  >- (
    
  )

  >> fs[spinlock_concrete2_def,lock_wrap_def]
  >> qmatch_asmsub_abbrev_tac `clstep (BirProgram $ A ++ blocks ++ C)`
  >> qspecl_then [`A`,`blocks ++ C`,`s.bst_pc`] mp_tac bir_get_current_statement_BirProgram_APPEND
  >> impl_tac >- fs[bir_labels_of_program_APPEND,list_disj_append2,list_disj_sym_imp,labels_wf_def]
  >> qspecl_then [`blocks`,`C`,`s.bst_pc`] mp_tac bir_get_current_statement_BirProgram_APPEND
  >> impl_tac >- fs[labels_wf_def]
  >> qmatch_asmsub_rename_tac `lock lock_addr 0w jump_after`
  >> qmatch_asmsub_rename_tac `unlock lock_addr unlock_entry`
  >> rw[]
  >> fs[bir_get_program_block_info_by_label_IS_SOME_MEM,labels_wf_imp]

(*
  >~ [`IS_SOME $ bir_get_program_block_info_by_label (BirProgram A) s.bst_pc.bpc_label`]
  >- (
  )
  >~ [`bir_get_program_block_info_by_label (BirProgram blocks) s.bst_pc.bpc_label = NONE`,
      `bir_get_program_block_info_by_label (BirProgram A) s.bst_pc.bpc_label = NONE`]
  >- (
    `IS_SOME $ bir_get_program_block_info_by_label (BirProgram C) s.bst_pc.bpc_label` by (
      imp_res_tac clstep_MEM_bir_labels_of_program
      >> imp_res_tac $ REWRITE_RULE[optionTheory.option_CLAUSES] bir_get_program_block_info_by_label_IS_NONE_NOT_MEM
      >> cheat (* *)
      clstep_bgcs_imp
      >> gvs[]
    )
  )
*)

  >> qpat_x_assum `bir_get_current_statement (BirProgram (blocks ++ C)) _ = _` kall_tac
  >> unabbrev_all_tac
  >> gvs[clstep_cases,bgcs_lock_zoo,bgcs_unlock_zoo,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,bir_eval_exp_view_BExp_Const,GSYM lock_addr_val_def,combinTheory.APPLY_UPDATE_THM,fence_updates_def]

  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    gs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,combinTheory.APPLY_UPDATE_THM]
    >> drule_then (fs o single) labels_wf_imp
    >> conj_tac
    >- (
      drule_then (irule_at Any) latest_t_dec
      >> qmatch_asmsub_abbrev_tac `well_formed cid M s'`
      >> `well_formed_fwdb lock_addr_val M (s.bst_coh lock_addr_val) $ s.bst_fwdb lock_addr_val` by fs[well_formed_def]
      >> imp_res_tac well_formed_fwdb_coh
      >> simp[mem_read_view_def,Once COND_RATOR,COND_RAND]
      >> fs[well_formed_fwdb_def]
    )
    >> fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,slc_mem_inv_def]
    >> strip_tac
    >> first_x_assum $ drule_all_then strip_assume_tac
    >> gvs[]
    >> drule_then irule $ GSYM bir_read_reg_env_update_cast64
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`,`xclfail_update_viewenv`]
  >- (
    gvs[AllCaseEqs(),PULL_EXISTS,slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_read_reg_zero_def,bir_read_reg_def,CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV SYM_CONV) xclfail_update_env_SOME,bir_eval_exp_BExp_Den_update_eq,v_fail_def]
    >> drule_then (fs o single) labels_wf_imp
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]
  >- (
    gvs[CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV SYM_CONV) fulfil_update_env_BVar_eq,bir_eval_exp_view_def,bir_eval_exp_BExp_Den_update_eq]
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_read_reg_zero_def,v_succ_def,bir_read_reg_def,bir_eval_exp_BExp_Den_update_eq,combinTheory.APPLY_UPDATE_THM,remove_prom_def]
    >> drule_then (fs o single) labels_wf_imp
    >> qhdtm_assum `fulfil_atomic_ok` $ irule_at Any
    >> imp_res_tac mem_get_mem_read_imp
    >> fs[listTheory.MEM_FILTER,slc_mem_inv_def]
    >> dsimp[listTheory.MEM_FILTER]
    >> fs[well_formed_def,well_formed_xclb_def]
    >> asm_rewrite_tac[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address $ Imm64 4w`,`s.bst_pc.bpc_index = 0`]
  >- (
    fs[bir_eval_exp_view_def,bir_exec_stmt_cjmp_def,bir_eval_exp_view_def]
    >> qmatch_goalsub_abbrev_tac `bir_eval_exp exp`
    >> Cases_on `bir_eval_exp exp s.bst_environ`
    >- gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
    >> unabbrev_all_tac
    >> Cases_on `s.bst_environ` >> fs[sl_bir_eval_exp_Unary]
    >> qmatch_assum_abbrev_tac `COND c _ _` >> Cases_on `c`
    >> fs[bir_dest_bool_val_true,bir_dest_bool_val_false]
    >> imp_res_tac bir_read_reg_imp
    >> fs[bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,COND_RAND]
    >> qmatch_goalsub_abbrev_tac `COND c _ _`
    >> `c` by (
      unabbrev_all_tac
      >> fs[bir_labels_of_program_APPEND,bir_labels_of_program_lock]
    )
    >> fs[bst_pc_tuple_def,bir_pc_next_def,slc_inv_def,bir_block_pc_def,bir_read_reg_def]
    >> drule_then (fs o single) labels_wf_imp
    >> drule_then (fs o single) labels_wf_jump_after
  )
  >~ [`s.bst_pc.bpc_label = BL_Address $ Imm64 16w`,`s.bst_pc.bpc_index = 0`]
  >- (
    (* TODO generalise - similar to previous case *)
    fs[bir_eval_exp_view_def,bir_exec_stmt_cjmp_def,bir_eval_exp_view_def]
    >> qmatch_goalsub_abbrev_tac `bir_eval_exp exp`
    >> Cases_on `bir_eval_exp exp s.bst_environ`
    >- gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
    >> unabbrev_all_tac
    >> Cases_on `s.bst_environ` >> fs[sl_bir_eval_exp_Unary]
    >> qmatch_assum_abbrev_tac `COND c _ _` >> Cases_on `c`
    >> fs[bir_dest_bool_val_true,bir_dest_bool_val_false]
    >> imp_res_tac bir_read_reg_imp
    >> fs[bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,COND_RAND]
    >> qmatch_goalsub_abbrev_tac `COND c _ _`
    >- (
      `c` by (
        unabbrev_all_tac
        >> fs[bir_labels_of_program_APPEND,labels_wf_def]
      )
      >> imp_res_tac labels_wf_jump_after
      >> fs[bst_pc_tuple_def,bir_pc_next_def,slc_inv_def,bir_block_pc_def,bir_read_reg_def]
      >> strip_tac
      >> gs[bir_read_reg_zero_def,bir_read_reg_def]
      >> strip_tac
      >> gs[bir_read_reg_zero_def,bir_read_reg_def]
    )
    >> `c` by (
      unabbrev_all_tac
      >> fs[bir_labels_of_program_APPEND,labels_wf_def,bir_labels_of_program_lock]
    )
    >> imp_res_tac labels_wf_jump_after
    >> fs[bst_pc_tuple_def,bir_pc_next_def,slc_inv_def,bir_block_pc_def,bir_read_reg_def]
    >> drule_then (fs o single) labels_wf_imp
  )
  >~ [`s.bst_pc.bpc_label = BL_Address $ Imm64 8w`,`s.bst_pc.bpc_index = 0`]
  >- (
    Cases_on `s.bst_environ`
    >> fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def]
    >> drule $ GSYM bir_read_reg_env_update_cast64
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
    >> drule_then (fs o single) labels_wf_imp
  )
  >~ [`BL_Address $ Imm64 $ unlock_entry + 8w = s.bst_pc.bpc_label`,`s.bst_pc.bpc_index = 0`]
  >- (
    qpat_x_assum `BL_Address _ = s.bst_pc.bpc_label` $ assume_tac o GSYM
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,fulfil_update_env_def,slc_mem_inv_def,bir_eval_exp_view_def,bir_eval_exp_BExp_Const,lock_addr_def,GSYM lock_addr_val_def]
    >> drule_then (fs o single) labels_wf_imp
    >> dsimp[listTheory.MEM_FILTER,remove_prom_def]
    >> imp_res_tac mem_get_mem_read_imp
    >> asm_rewrite_tac[]
    >> rw[] >> fs[]
  )
  >~ [`BL_Address (Imm64 (unlock_entry + 4w)) = s.bst_pc.bpc_label`,`s.bst_pc.bpc_index = 0`]
  >- (
    gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
    >> gen_tac >> strip_tac
    >> gvs[]
    >> drule_then (fs o single) labels_wf_imp
  )
  >~ [`BL_Address (Imm64 unlock_entry) = s.bst_pc.bpc_label`,`s.bst_pc.bpc_index = 0`]
  >- (
    fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,slc_mem_inv_def,bir_eval_exp_view_BExp_Const]
    >> drule_then assume_tac $ GSYM bir_read_reg_env_update_cast64
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_eval_exp_view_BExp_Const]
    >> gen_tac >> strip_tac
    >> gvs[]
    >> drule_then (fs o single) labels_wf_imp
  )
  >~ [`bir_get_current_statement (BirProgram $ lock _ _ _) s.bst_pc = SOME $ BSGen stm`]
  >- (
    gvs[bmc_exec_general_stmt_exists,bgcs_lock_zoo,bir_exec_stmt_assert_def,bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_lock,bir_eval_exp_BExp_Const,bir_dest_bool_val_true',bst_pc_tuple_def,bir_pc_next_def,bir_labels_of_program_APPEND,bir_labels_of_program_lock]
    >> fs[slc_inv_def,bst_pc_tuple_def]
    >> drule_then (fs o single) labels_wf_imp
    >> drule_then (fs o single) labels_wf_jump_after
    >> goal_assum drule
  )
  >~ [`bir_get_current_statement (BirProgram $ unlock _ _) s.bst_pc = SOME $ BSGen stm`]
  >- (
    gvs[bmc_exec_general_stmt_exists,bgcs_unlock_zoo,bir_exec_stmt_assert_def,bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_lock,bir_eval_exp_BExp_Const,bir_dest_bool_val_true',bst_pc_tuple_def,bir_pc_next_def,bir_labels_of_program_APPEND,bir_labels_of_program_lock,bir_labels_of_program_unlock]
    >> qpat_x_assum `BL_Address _ = s.bst_pc.bpc_label` $ assume_tac o GSYM
    >> fs[slc_inv_def,bst_pc_tuple_def]
    >> drule_then (fs o single) labels_wf_imp
  )
QED

(* show assumptions for a trivial blocks *)
Theorem clstep_slc_inv_assumptions_for_trivial_block:
  !jump_after blocks unlock_entry cid M prom.
  jump_after = BL_Address $ Imm64 20w (* width of lock + 4w *)
  /\ unlock_entry = 24w (* jump_after + 4w *)
  /\ blocks = [BBlock_Stmts <|bb_label := jump_after;
        bb_statements := [
          BMCStmt_Assert (BExp_Const $ Imm1 1w) (* no-op *)
        ];
        bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 unlock_entry |>]
  ==> !s s'. labels_wf blocks jump_after unlock_entry
  /\ wf_ext (BirProgram blocks : progc_t) cid s M
  /\ (clstep (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s'
  /\ slc_inv 0w jump_after unlock_entry cid s M
  ==>
  addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ jump_constraints s.bst_pc s'.bst_pc
    [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
  )
Proof
  rpt gen_tac >> strip_tac
  >> fs[labels_wf_def,bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_labels_of_program_APPEND]
  >> fs[bir_labels_of_program_def,bir_label_of_block_def]
  >> dsimp[list_disj_def]
  >> fs[wf_ext_def,bir_get_current_statement_def,bir_get_program_block_info_by_label_def]
  >> dsimp[AllCaseEqs(),listTheory.INDEX_FIND_def]
  >> rpt conj_tac
  >~ [`addr_unchanged`]
  >- (
    rpt gen_tac >> strip_tac
    >> qmatch_asmsub_abbrev_tac `clstep p`
    >> reverse $ Cases_on `IS_SOME $ bir_get_current_statement p s.bst_pc`
    >- gs[clstep_cases]
    >> unabbrev_all_tac
    >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,optionTheory.IS_SOME_EXISTS,spinlock_concrete2_def,lock_wrap_def,addr_unchanged_def]
    >> reverse $ Cases_on `MEM s.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram blocks`
    >- (
      gs[bir_labels_of_program_def,bir_label_of_block_def]
      >> fs[bir_get_current_statement_def,bir_get_program_block_info_by_label_def,INDEX_FIND_append,lock_def,unlock_def]
      >> gs[AllCaseEqs(),listTheory.INDEX_FIND_def,bir_label_of_block_def]
    )
    >> FULL_SIMP_TAC std_ss [GSYM listTheory.APPEND_ASSOC]
    >> drule bir_get_current_statement_MEM2
    >> impl_tac
    >- (
      REWRITE_TAC[bir_labels_of_program_APPEND,list_disj_append2]
      >> fs[list_disj_def,bir_labels_of_program_lock,bir_labels_of_program_unlock]
      >> gs[bir_labels_of_program_def,bir_label_of_block_def]
      >> dsimp[]
    )
    >> strip_tac
    >> dxrule bir_get_current_statement_MEM1
    >> impl_tac
    >- gs[bir_labels_of_program_def,bir_label_of_block_def]
    >> disch_then $ assume_tac o CONV_RULE EVAL
    >> simp[listTheory.EVERY_MEM,PULL_EXISTS]
    >> gvs[bir_labels_of_program_def,bir_label_of_block_def,AllCaseEqs()]
    >> gs[clstep_cases,bir_auxiliaryTheory.NUM_LSONE_EQZ,bmc_exec_general_stmt_exists]
    >> gvs[bir_exec_stmt_assert_def,AllCaseEqs(),bir_eval_exp_BExp_Const,bir_state_set_typeerror_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_labels_of_program_APPEND,bir_labels_of_program_lock,bir_labels_of_program_unlock]
  )
  >~ [`in_cs_inv`]
  >- (
    fs[in_cs_inv_def,bir_labels_of_program_def,bir_label_of_block_def]
    >> rpt gen_tac >> ntac 2 strip_tac
    >> gs[slc_inv_def,bst_pc_tuple_def]
    >> cheat (* needs slc_inv invariant to discharge state after jump from lock *)
  )
  >~ [`jump_constraints`]
  >> dsimp[jump_constraints_def,bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_pc_first_def,bir_block_pc_def,bir_label_of_block_def,lock_def,unlock_def,bir_programcounter_t_component_equality]
  >> cheat (* invariant that some addresses are only jumped to from within the un/lock *)
QED

Theorem slc_inv_prom:
  !cid s M msg lock_entry jump_after unlock_entry.
  slc_inv lock_entry jump_after unlock_entry cid s M
  /\ well_formed cid M s
  ==> slc_inv lock_entry jump_after unlock_entry cid
    (s with bst_prom updated_by (λpr. pr ++ [LENGTH M + 1])) (M ++ [msg])
Proof
  rpt strip_tac >> fs[slc_inv_def,bst_pc_tuple_def]
  >> conj_tac
  >~ [`slc_mem_inv`]
  >- (
    PRED_ASSUM is_forall kall_tac
    >> fs[slc_mem_inv_def]
    >> rw[]
    >> `t <= LENGTH M` by (
      imp_res_tac mem_read_LENGTH
      >> gs[arithmeticTheory.LESS_OR_EQ]
    )
    >> gs[mem_read_append]
    >> first_x_assum $ drule_all_then irule
  )
  >> rpt gen_tac >> strip_tac
  >> first_x_assum $ drule_then strip_assume_tac
  >> dsimp[] >> fs[]
  >> rpt strip_tac
  >> gvs[well_formed_def,fulfil_atomic_ok_append,mem_is_loc_append,mem_read_append,well_formed_xclb_def,DISJ_IMP_THM,optionTheory.IS_SOME_EXISTS,latest_t_append]
  >> qmatch_asmsub_rename_tac `mem_read M lock_addr_val t = _`
  >> imp_res_tac mem_read_LENGTH
  >> qexists_tac `t`
  >> gvs[mem_read_append,fulfil_atomic_ok_append]
  >> first_x_assum $ qspec_then `lock_addr_val` mp_tac
  >> fs[]
QED

Theorem cstep_slc_inv:
  !cid s M s' M' P prom jump_after unlock_entry blocks.
  labels_wf blocks jump_after unlock_entry
  /\ wf_ext (BirProgram blocks : progc_t) cid s M
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ jump_constraints s.bst_pc s'.bst_pc
    [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
  /\ well_formed cid M s
  /\ cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s' M'
  ==> slc_inv 0w jump_after unlock_entry cid s' M'
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases,cstep_cases]
  >- drule_all_then irule clstep_slc_inv
  >> fs[slc_inv_prom]
QED

Theorem cstep_seq_slc_inv:
  !cid s M s' M' jump_after unlock_entry blocks.
  labels_wf blocks jump_after unlock_entry
  /\ wf_ext_p (BirProgram blocks : progc_t) cid
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
    [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
  /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh lock_addr_val (Imm64 1w)
  /\ jump_constraints s.bst_pc s'.bst_pc
    [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
  /\ well_formed cid M s
  /\ cstep_seq (spinlock_concrete2 blocks jump_after unlock_entry) cid (s, M) (s', M')
  ==> slc_inv 0w jump_after unlock_entry cid s' M'
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases,cstep_cases]
  >~ [`clstep _ _ _ _ [_] _`]
  >- (
    drule_then irule clstep_slc_inv
    >> goal_assum $ drule_at $ Pat `clstep`
    >> fs[slc_inv_prom,well_formed_promise_self,iffLR wf_ext_p_def]
    >> `s.bst_coh lock_addr_val <= LENGTH M` by fs[well_formed_def]
    >> `EVERY (λt. t <= LENGTH M) s.bst_prom` by fs[well_formed_def]
    >> fs[mem_read_append,in_cs_inv_def,addr_unchanged_def]
  )
  >~ [`clstep`]
  >- (
    fs[wf_ext_p_def]
    >> qmatch_asmsub_rename_tac `clstep _ cid s M prom s'`
    >> first_x_assum $ qspecl_then [`M`,`s`] assume_tac
    >> drule_all_then irule clstep_slc_inv
  )
QED

(* dynamically determined property *)
Definition cstepR_def:
  cstepR R P p cid s M prom s' M' <=>
    R (s,M) (s',M') /\ cstep P p cid s M prom s' M'
End

Definition cstep_seqR_def:
  cstep_seqR R p cid sM sM' <=>
    R sM sM' /\ cstep_seq p cid sM sM'
End

Theorem cstepR_T:
  cstepR (λx y. T) = cstep
Proof
  fs[cstepR_def,FUN_EQ_THM]
QED

Theorem cstep_seqR_T:
  cstep_seqR (λx y. T) = cstep_seq
Proof
  fs[cstep_seqR_def,FUN_EQ_THM]
QED

Theorem cstepR_cstep = cj 2 $ iffLR cstepR_def
Theorem cstep_seqR_cstep_seq = cj 2 $ iffLR cstep_seqR_def

Theorem NRC_MONOTONE:
  !n x y R Q. (!x y. R x y ==> Q x y)
  /\ NRC R n x y
  ==> NRC Q n x y
Proof
  Induct
  >> rw[arithmeticTheory.NRC_SUC_RECURSE_LEFT]
  >> first_assum $ irule_at Any
  >> last_x_assum $ irule_at Any
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem cstep_seqR_NRC_cstep_seq_NCR:
  !R p cid n sM sM'.
    NRC (cstep_seqR R p cid) n sM sM'
    ==> NRC (cstep_seq p cid) n sM sM'
Proof
  rpt strip_tac
  >> irule NRC_MONOTONE
  >> goal_assum $ dxrule_at Any
  >> rpt strip_tac
  >> drule_then irule cstep_seqR_cstep_seq
QED

Theorem cstep_seqR_NRC_prom_subset:
  !R p cid n sM sM'.
  NRC (cstep_seqR R p cid) n sM sM'
  ==> set (FST sM').bst_prom SUBSET set (FST sM).bst_prom
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `cstep_seqR R p cid`
  >> irule cstep_seq_NRC_prom_subset
  >> dxrule_at_then Any (irule_at Any) NRC_MONOTONE
  >> qexistsl_tac [`p`,`cid`]
  >> qspecl_then [`R`,`p`,`cid`] mp_tac cstep_seqR_cstep_seq
  >> fs[]
QED

Theorem cstepR_seq_NRC_wf:
  !n cid M s p s' M' R.
  well_formed cid M s /\ wf_ext_p p cid
  /\ NRC (cstep_seqR R p cid) n (s,M) (s',M')
  ==> well_formed cid M' s'
Proof
  rpt strip_tac
  >> dxrule_then assume_tac cstep_seqR_NRC_cstep_seq_NCR
  >> drule_all_then irule cstep_seq_NRC_wf
QED

Definition is_certifiedR_def:
  is_certifiedR R sM <=> ?sM'. RTC R sM sM' /\ (FST sM').bst_prom = []
End

Theorem is_certifiedR_eq:
  !p cid sM. is_certifiedR (cstep_seqR (λx y. T) p cid) sM = is_certified p cid (FST sM) (SND sM)
Proof
  rw[is_certifiedR_def,is_certified_def,pairTheory.EXISTS_PROD,cstep_seq_rtc_def,cstep_seqR_T]
QED

Theorem is_certified_imp_is_certifiedR =
  iffRL is_certifiedR_eq
  |> SIMP_RULE(srw_ss())[pairTheory.FORALL_PROD]

Theorem is_certifiedR_cstep_seqR_is_certified:
  !p cid sM R. is_certifiedR (cstep_seqR R p cid) sM
  ==> is_certified p cid (FST sM) (SND sM)
Proof
  rw[is_certifiedR_def,PULL_EXISTS,is_certified_def,cstep_seq_rtc_def]
  >> irule_at Any RTC_MONOTONE
  >> qmatch_asmsub_rename_tac `RTC _ sM sM'` >> PairCases_on `sM'`
  >> qhdtm_assum `RTC` $ irule_at Any
  >> fs[] >> rpt strip_tac
  >> drule_then irule cstep_seqR_cstep_seq
QED

Inductive parstepR:
  !p cid s s' M M' cores prom P R.
    FLOOKUP cores cid = SOME (Core cid p s)
    /\ cstepR R P p cid s M prom s' M'
    /\ is_certifiedR (cstep_seqR R p cid) (s',M')
    ==>
      parstepR R P cid cores M (FUPDATE cores (cid, Core cid p s')) M'
End

Theorem parstepR_parstep:
  !p cid s s' M M' cores prom P R cores'.
    parstepR R P cid cores M cores' M'
    ==> parstep P cid cores M cores' M'
Proof
  rw[parstep_cases,parstepR_cases]
  >> drule_then (irule_at Any) cstepR_cstep
  >> imp_res_tac is_certifiedR_cstep_seqR_is_certified
  >> fs[]
QED

Definition parstepR_tr_def:
  parstepR_tr R P cid cM cM' =
    parstepR R P cid (FST cM) (SND cM) (FST cM') (SND cM')
End

(*
Definition trace_restr_def:
  trace_restr P R sM sM' = !sM''. RTC R sM sM'' /\ RTC R sM'' sM' ==> P sM'' sM'
End

Theorem trace_restr_SUBSET:
  !R x x' x'' P. RTC R x x' /\ trace_restr P R x x'' ==> trace_restr P R x' x''
Proof
  rw[trace_restr_def]
  >> first_x_assum irule
  >> fs[]
  >> irule $ REWRITE_RULE[transitive_def] relationTheory.RTC_TRANSITIVE
  >> goal_assum drule_all
QED

Definition trace_restr1_def:
  trace_restr1 P R sM = !sM' sM''. RTC R sM sM' /\ R sM' sM'' ==> P sM' sM''
End

Theorem trace_restr1_SUBSET:
  !R x x' P. RTC R x x' /\ trace_restr1 P R x ==> trace_restr1 P R x'
Proof
  rw[trace_restr1_def]
  >> first_x_assum irule
  >> drule_all $ REWRITE_RULE[transitive_def] relationTheory.RTC_TRANSITIVE
  >> fs[]
QED

Theorem trace_restr1_SUBSET1:
  !R x x' P. R x x' /\ trace_restr1 P R x ==> trace_restr1 P R x'
Proof
  rw[trace_restr1_def]
  >> first_x_assum irule
  >> fs[]
  >> drule_all_then irule $ cj 2 RTC_RULES
QED

Theorem trace_restr1_ONE:
  !R P x x'. trace_restr1 P R x /\ R x x' ==> P x x'
Proof
  fs[trace_restr1_def]
QED
*)

Definition step_restr_def:
  step_restr jump_after blocks unlock_entry =
  (λsM sM'.
    !M M' s s'. s = FST sM /\ M = SND sM /\ M' = SND sM' /\ s' = FST sM' ==>
    addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom s'.bst_prom M
      [lock lock_addr 0w jump_after; unlock lock_addr unlock_entry]
    /\ jump_constraints s.bst_pc s'.bst_pc
      [unlock lock_addr unlock_entry; lock lock_addr 0w jump_after]
    (* TODO: assert on s or s'? *)
    /\ in_cs_inv (BirProgram blocks) s'.bst_pc.bpc_label M' s'.bst_coh
      lock_addr_val (Imm64 1w)
    /\ in_cs_inv (BirProgram blocks) s.bst_pc.bpc_label M s.bst_coh
      lock_addr_val (Imm64 1w)
  )
End

Theorem cstep_seqR_NRC_slc_inv:
  !cid jump_after unlock_entry blocks n seM seM'.
  labels_wf blocks jump_after unlock_entry
  /\ wf_ext_p (BirProgram blocks : progc_t) cid
  /\ NRC (cstep_seqR (step_restr jump_after blocks unlock_entry)
    (spinlock_concrete2 blocks jump_after unlock_entry) cid) n seM seM'
  /\ well_formed cid (SND seM) (FST seM)
  /\ slc_inv 0w jump_after unlock_entry cid (FST seM) (SND seM)
  ==> slc_inv 0w jump_after unlock_entry cid (FST seM') (SND seM')
Proof
  ntac 4 gen_tac
  >> Induct >> fs[arithmeticTheory.NRC,PULL_EXISTS]
  >> rpt PairCases >> rpt strip_tac
  >> first_x_assum $ drule_at_then (Pat `NRC`) irule
  >> fs[cstep_seqR_def]
  >> drule_at_then (Pat `cstep_seq`) assume_tac cstep_seq_preserves_wf
  >> gs[spinlock_concrete_wf_ext,wf_ext_p_def]
  >> drule_at_then (Pat `cstep_seq`) irule cstep_seq_slc_inv
  >> simp[wf_ext_p_def]
  >> fs[step_restr_def]
QED

(*
Theorem cstep_seq_NRC_slc_inv:
  !cid n seM seM'.
  NRC (cstep_seq spinlock_concrete cid) n seM seM'
  /\ well_formed cid (SND seM) (FST seM)
  /\ slc_inv 4w 24w cid (FST seM) (SND seM)
  ==> slc_inv 4w 24w cid (FST seM') (SND seM')
Proof
  ntac 2 gen_tac
  >> Induct >> fs[arithmeticTheory.NRC,PULL_EXISTS]
  >> rpt PairCases >> rpt strip_tac
  >> fs[]
  >> drule_at (Pat `cstep_seq`) cstep_seq_preserves_wf
  >> fs[spinlock_concrete_wf_ext,wf_ext_p_def]
  >> strip_tac
  >> drule_all_then assume_tac cstep_seq_slc_inv
  >> first_x_assum drule
  >> fs[]
QED
*)

(* TODO replace theorem version from bir_promising_wfTheory by this one *)
Theorem is_certifiedR_promise_disch:
  !cid M s p t R.
  is_certifiedR (cstep_seqR R p cid) (s,M)
  /\ MEM t s.bst_prom
  ==>
    ?n m sM2 sM3 sM4. NRC (cstep_seqR R p cid) m (s,M) sM2
    /\ cstep_seqR R p cid sM2 sM3
    /\ NRC (cstep_seqR R p cid) n sM3 sM4
    /\ MEM t (FST sM2).bst_prom
    /\ ~MEM t (FST sM3).bst_prom
    /\ NULL (FST sM4).bst_prom
Proof
  rpt strip_tac
  >> fs[is_certifiedR_def,pairTheory.EXISTS_PROD]
  >> dxrule_then strip_assume_tac arithmeticTheory.RTC_NRC
  >> qmatch_asmsub_rename_tac `NRC (cstep_seqR R p cid) n (s,M) (s',M')`
  >> Cases_on `0 < n` >> gvs[]
  >> Cases_on `!m. m <= n ==> !s'' M''.
    NRC (cstep_seqR R p cid) m (s,M) (s'',M'')
    /\ NRC (cstep_seqR R p cid) (n - m) (s'',M'') (s',M')
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
  >> qmatch_asmsub_rename_tac `cstep_seqR R p cid z (s'',M'')`
  >> PairCases_on `z`
  >> rpt $ goal_assum drule
  >> fs[]
  >> first_x_assum irule
  >> goal_assum $ dxrule_at Any
  >> dxrule_at (Pat `NRC`) $
    Ho_Rewrite.REWRITE_RULE[PULL_EXISTS] $ iffRL $ cj 2 arithmeticTheory.NRC
  >> disch_then dxrule
  >> qmatch_goalsub_rename_tac `NRC _ (SUC $ n - SUC n')`
  >> `SUC $ n - SUC n' = n - n'` by decide_tac
  >> fs[]
QED

Theorem is_certifiedR_locking:
  !cid s M msg t jump_after blocks unlock_entry.
  is_certifiedR
    (cstep_seqR
      (step_restr jump_after blocks unlock_entry)
      (spinlock_concrete2 blocks jump_after unlock_entry) cid)
    (s,(M ++ [msg]))
  /\ slc_inv 0w jump_after unlock_entry cid s (M ++ [msg])
  /\ labels_wf blocks jump_after unlock_entry
  /\ wf_ext_p (BirProgram blocks) cid
  /\ well_formed cid (M ++ [msg]) s
  /\ MEM (LENGTH M + 1) s.bst_prom
  /\ msg.loc = lock_addr_val
  /\ msg.cid = cid
  /\ msg.val = BVal_Imm $ Imm64 1w (* 1w = locked *)
  /\ t = latest lock_addr_val (LENGTH M) M
  ==> ?m. mem_get M lock_addr_val t = SOME m
    /\ m.val = BVal_Imm $ Imm64 0w (* 0w = free *)
Proof
  rpt strip_tac
  >> imp_res_tac is_certifiedR_cstep_seqR_is_certified
  >> fs[]
  >> drule_all_then strip_assume_tac is_certifiedR_promise_disch
  >> qmatch_asmsub_rename_tac `cstep_seqR _ _ cid sM2 sM3`
  >> PairCases_on `sM3` >> PairCases_on `sM2`
  >> fs[]
  >> qmatch_asmsub_rename_tac
    `NRC (cstep_seqR _ _ cid) m (s,M ++ [msg]) (s1,M1)`
  >> qmatch_asmsub_rename_tac
    `cstep_seqR _ _ cid (s1,M1) (s2,M2)`
  >> `slc_inv 0w jump_after unlock_entry cid s1 M1
    /\ well_formed cid M1 s1` by (
    rev_drule_at_then (Pat `NRC`) assume_tac cstep_seqR_NRC_slc_inv
    >> rev_drule_at_then (Pat `NRC`) assume_tac cstepR_seq_NRC_wf
    >> gs[spinlock_concrete_wf_ext,wf_ext_p_def]
  )
  >> imp_res_tac cstep_seqR_NRC_prom_subset
  >> fs[listTheory.NULL_EQ]
  >> qmatch_asmsub_abbrev_tac `cstep_seqR R p cid (s1,M1) (s2,M2)`
  >> `is_certifiedR (cstep_seqR R p cid) (s2,M2)
    /\ is_certifiedR (cstep_seqR R p cid) (s1,M1)` by (
    conj_asm1_tac
    >> simp[is_certifiedR_def,arithmeticTheory.RTC_eq_NRC,PULL_EXISTS]
    >- (
      irule_at Any arithmeticTheory.NRC_ADD_I
      >> goal_assum drule
      >> irule_at Any $ iffRL arithmeticTheory.NRC_0
      >> qmatch_asmsub_rename_tac `NRC (cstep_seqR _ _ cid) _ (s2,M2) sM4`
      >> PairCases_on `sM4`
      >> fs[]
    )
    >> fs[is_certifiedR_def,arithmeticTheory.RTC_eq_NRC]
    >> irule_at Any arithmeticTheory.NRC_ADD_I
    >> irule_at Any $ iffRL arithmeticTheory.NRC_1
    >> qhdtm_x_assum `cstep_seqR` $ irule_at Any
    >> rpt $ goal_assum drule
  )
  >> dxrule_then mp_tac is_certifiedR_cstep_seqR_is_certified
  >> dxrule_then assume_tac is_certifiedR_cstep_seqR_is_certified
  >> strip_tac
  >> dxrule_at Any is_certified_promises
  >> qunabbrev_tac `p`
  >> fs[wf_ext_p_def,spinlock_concrete_wf_ext]
  >> disch_then drule
  >> dxrule_at Any is_certified_promises
  >> drule_then assume_tac cstep_seqR_cstep_seq
  >> drule_at (Pat `cstep_seq`) cstep_seq_preserves_wf
  >> fs[wf_ext_p_def,spinlock_concrete_wf_ext]
  >> disch_then kall_tac (* well_formed cid M2 s2*)
  >> rev_drule_then assume_tac cstep_seqR_NRC_cstep_seq_NCR
  >> dxrule_then strip_assume_tac cstep_seq_NRC_mem_mono
  >> dxrule_then (drule_then drule) cstep_seq_is_clstep
  >> fs[spinlock_concrete_wf_ext,wf_ext_p_def]
  >> rw[]
  >> fs[spinlock_concrete2_def,lock_wrap_def]
  >> qmatch_asmsub_abbrev_tac `BirProgram $ A ++ blocks ++ C`
  >> Cases_on `MEM s1.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram blocks`
  >- (
    (* cannot fulfil to lock_addr_val *)
    dxrule_then strip_assume_tac $ iffLR cstep_seqR_def
    >> qunabbrev_tac `R`
    >> qhdtm_x_assum `step_restr` $ assume_tac o REWRITE_RULE[step_restr_def]
    >> gs[]
    >> drule_at_then (Pat `clstep`) drule addr_unchanged_imp_promises_unchanged_clstep
    >> impl_keep_tac
    >- gs[labels_wf_def,list_disj_spec_ho]
    >> strip_tac
    >> gvs[rich_listTheory.IS_PREFIX_APPEND,listTheory.EVERY_MEM]
    >> first_x_assum drule
    >> fs[mem_read_append]
    >> rw[mem_read_def,mem_get_def,GSYM arithmeticTheory.ADD1,listTheory.oEL_THM,rich_listTheory.EL_APPEND2]
  )
  >> qspecl_then [`s1.bst_pc`,`A`,`blocks`,`C`] mp_tac bir_get_current_statement_three
  >> unabbrev_all_tac
  >> drule $ iffLR labels_wf_def
  >> fs[list_disj_sym_imp]
  >> disch_then kall_tac
(*
  >> disch_then assume_tac
*)
  >> dxrule_then assume_tac $ iffLR slc_inv_def
  (* TODO continue *)
  >> gvs[clstep_cases,bst_pc_tuple_def,listTheory.MEM_FILTER,bir_labels_of_program_APPEND]
  >> imp_res_tac bir_get_current_statement_SOME_MEM
  >> fs[bir_labels_of_program_APPEND]
  >> gs[bgcs_unlock_zoo,bgcs_lock_zoo]
  >> strip_tac
  >> gvs[bir_labels_of_program_APPEND,bst_pc_tuple_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_eval_exp_view_BExp_Const,remove_prom_def,bir_state_read_view_updates_def]
  (* prevents rewrite loop detection of  msg = <| cid = msg.cid |> *)
  >> qmatch_asmsub_abbrev_tac `is_certified _ cid`
  >~ [`BL_Address (Imm64 (unlock_entry + 8w)) = s1.bst_pc.bpc_label`,`s1.bst_pc.bpc_index = 0`]
  >- (
    qpat_x_assum `BL_Address _ = s1.bst_pc.bpc_label` $ assume_tac o GSYM
    >> gvs[bst_pc_tuple_def,rich_listTheory.IS_PREFIX_APPEND,mem_get_append,mem_read_append,GSYM lock_addr_val_def,mem_get_def,listTheory.oEL_THM,rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1,bir_programcounter_t_component_equality,GSYM arithmeticTheory.ADD1,listTheory.MEM_FILTER]
  )
  >~ [`s1.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s1.bst_pc.bpc_index = 0`]
  >> gvs[GSYM lock_addr_val_def,rich_listTheory.IS_PREFIX_APPEND,mem_read_append,fulfil_atomic_ok_append,mem_get_append,listTheory.MEM_FILTER]
  >> first_x_assum $ drule_then assume_tac
  >> fs[slc_mem_inv_def]
  >> `~MEM (THE s1.bst_xclb).xclb_time s1.bst_prom` by (
    spose_not_then assume_tac
    >> `mem_is_cid M (THE s1.bst_xclb).xclb_time cid` by (
      fs[well_formed_def,listTheory.EVERY_MEM]
      >> first_x_assum drule
      >> fs[mem_is_cid_append]
    )
    >> first_x_assum $ drule_at Any
    >> fs[]
    >> qexists_tac `lock_addr_val`
    >> gs[mem_get_append,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM]
    >> imp_res_tac mem_get_mem_read
    >> drule_all_then strip_assume_tac mem_get_mem_is_cid
    >> fs[]
  )
  >> gs[]
  >> `latest_t lock_addr_val M (s1.bst_coh lock_addr_val) (LENGTH M)` by (
    spose_not_then assume_tac
    >> gs[fulfil_atomic_ok_def,mem_is_loc_append,mem_read_mem_is_loc_imp,latest_t_def]
    >> qmatch_asmsub_rename_tac `mem_is_loc M t' lock_addr_val`
    >> ntac 3 $ first_x_assum $ qspec_then `t'` assume_tac
    >> first_x_assum $ qspecl_then [`lock_addr_val`,`t'`] assume_tac
    >> imp_res_tac $ iffRL mem_get_is_loc
    >> gs[mem_is_loc_append,mem_is_cid_append,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM,mem_get_append]
    >> drule_all_then assume_tac mem_get_mem_is_cid
    >> fs[]
    >> dxrule_at_then (Pat `well_formed _ _ s1`) strip_assume_tac $ iffLR well_formed_def
    >> first_x_assum $ drule_at_then (Pat `~MEM _ s1.bst_prom`) assume_tac
    >> gs[mem_get_append,GSYM mem_get_is_loc,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM,mem_is_cid_append]
    >> pop_assum $ drule_then assume_tac
    >> gs[]
  )
  >> gs[latest_t_append_eq]
  >> dxrule_all_then assume_tac latest_t_trans
  >> dxrule_then (fs o single) latest_t_latest_is_lowest
  >> imp_res_tac mem_get_mem_read
  >> fs[latest_exact]
QED

(*
Theorem is_certified_locking:
  !cid s M msg t.
  is_certified spinlock_concrete cid s (M ++ [msg])
  /\ slc_inv 4w 24w cid s (M ++ [msg])
  /\ well_formed cid (M ++ [msg]) s
  /\ MEM (LENGTH M + 1) s.bst_prom
  /\ msg.loc = lock_addr_val
  /\ msg.cid = cid
  /\ msg.val = BVal_Imm $ Imm64 1w (* 1w = locked *)
  /\ t = latest lock_addr_val (LENGTH M) M
  ==> ?m. mem_get M lock_addr_val t = SOME m
    /\ m.val = BVal_Imm $ Imm64 0w (* 0w = free *)
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac is_certified_promise_disch
  >> qmatch_asmsub_rename_tac `cstep_seq spinlock_concrete cid sM2 sM3`
  >> PairCases_on `sM3` >> PairCases_on `sM2`
  >> fs[]
  >> qmatch_asmsub_rename_tac
    `NRC (cstep_seq spinlock_concrete cid) m (s,M ++ [msg]) (s1,M1)`
  >> qmatch_asmsub_rename_tac
    `cstep_seq spinlock_concrete cid (s1,M1) (s2,M2)`
  >> `slc_inv 4w 24w cid s1 M1 /\ well_formed cid M1 s1` by (
    rev_drule_at (Pat `NRC`) cstep_seq_NRC_slc_inv
    >> rev_drule_at (Pat `NRC`) cstep_seq_NRC_wf
    >> fs[spinlock_concrete_wf_ext,wf_ext_p_def]
  )
  >> imp_res_tac cstep_seq_NRC_prom_subset
  >> fs[listTheory.NULL_EQ]
  >> qmatch_asmsub_rename_tac `cstep_seq _ cid (s1,M1) (s2,M2)`
  >> `is_certified spinlock_concrete cid s2 M2
    /\ is_certified spinlock_concrete cid s1 M1` by (
    conj_asm1_tac
    >> simp[is_certified_def,cstep_seq_rtc_def,arithmeticTheory.RTC_eq_NRC,PULL_EXISTS]
    >- (
      irule_at Any arithmeticTheory.NRC_ADD_I
      >> goal_assum drule
      >> irule_at Any $ iffRL arithmeticTheory.NRC_0
      >> qmatch_asmsub_rename_tac `NRC (cstep_seq _ cid) _ (s2,M2) sM4`
      >> PairCases_on `sM4`
      >> fs[]
    )
    >> fs[is_certified_def,cstep_seq_rtc_def,arithmeticTheory.RTC_eq_NRC]
    >> irule_at Any arithmeticTheory.NRC_ADD_I
    >> irule_at Any $ iffRL arithmeticTheory.NRC_1
    >> qhdtm_x_assum `cstep_seq` $ irule_at Any
    >> rpt $ goal_assum drule
  )
  >> dxrule_at Any is_certified_promises
  >> fs[wf_ext_p_def,spinlock_concrete_wf_ext]
  >> disch_then drule
  >> dxrule_at Any is_certified_promises
  >> drule_at (Pat `cstep_seq`) cstep_seq_preserves_wf
  >> fs[wf_ext_p_def,spinlock_concrete_wf_ext]
  >> disch_then kall_tac (* well_formed cid M2 s2*)
  >> rev_drule_then strip_assume_tac cstep_seq_NRC_mem_mono
  >> dxrule_then (drule_then drule) cstep_seq_is_clstep
  >> fs[spinlock_concrete_wf_ext,wf_ext_p_def]
  >> rw[]
  >> dxrule_then assume_tac $ iffLR slc_inv_def
  >> gvs[clstep_cases,bst_pc_tuple_def,bir_get_spinlock_cprog_zoo,listTheory.MEM_FILTER]
  >> gvs[bst_pc_tuple_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_eval_exp_view_BExp_Const,remove_prom_def,bir_state_read_view_updates_def]
  >> gvs[GSYM lock_addr_val_def,rich_listTheory.IS_PREFIX_APPEND,mem_read_append,fulfil_atomic_ok_append,mem_get_append,listTheory.MEM_FILTER]
  (* prevents rewrite loop detection of  msg = <| cid = msg.cid |> *)
  >> qmatch_asmsub_abbrev_tac `is_certified _ cid`
  >~ [`s1.bst_pc.bpc_index = 0`,`s1.bst_pc.bpc_label = BL_Address (Imm64 32w)`]
  >- gs[mem_get_def,GSYM arithmeticTheory.ADD1,listTheory.oEL_THM,rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1,bir_programcounter_t_component_equality]
  >~ [`s1.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s1.bst_pc.bpc_index = 0`]
  >> first_x_assum $ drule_then assume_tac
  >> fs[slc_mem_inv_def]
  >> `~MEM (THE s1.bst_xclb).xclb_time s1.bst_prom` by (
    spose_not_then assume_tac
    >> `mem_is_cid M (THE s1.bst_xclb).xclb_time cid` by (
      fs[well_formed_def,listTheory.EVERY_MEM]
      >> first_x_assum drule
      >> fs[mem_is_cid_append]
    )
    >> first_x_assum $ drule_at Any
    >> fs[]
    >> qexists_tac `lock_addr_val`
    >> gs[mem_get_append,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM]
    >> imp_res_tac mem_get_mem_read
    >> drule_all_then strip_assume_tac mem_get_mem_is_cid
    >> fs[]
  )
  >> gs[]
  >> `latest_t lock_addr_val M (s1.bst_coh lock_addr_val) (LENGTH M)` by (
    spose_not_then assume_tac
    >> gs[fulfil_atomic_ok_def,mem_is_loc_append,mem_read_mem_is_loc_imp,latest_t_def]
    >> qmatch_asmsub_rename_tac `mem_is_loc M t' lock_addr_val`
    >> ntac 3 $ first_x_assum $ qspec_then `t'` assume_tac
    >> first_x_assum $ qspecl_then [`lock_addr_val`,`t'`] assume_tac
    >> imp_res_tac $ iffRL mem_get_is_loc
    >> gs[mem_is_loc_append,mem_is_cid_append,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM,mem_get_append]
    >> drule_all_then assume_tac mem_get_mem_is_cid
    >> fs[]
    >> dxrule_at_then (Pat `well_formed _ _ s1`) strip_assume_tac $ iffLR well_formed_def
    >> first_x_assum $ drule_at_then (Pat `~MEM _ s1.bst_prom`) assume_tac
    >> gs[mem_get_append,GSYM mem_get_is_loc,optionTheory.IS_SOME_EXISTS,combinTheory.APPLY_UPDATE_THM,mem_is_cid_append]
    >> pop_assum $ drule_then assume_tac
    >> gs[]
  )
  >> gs[latest_t_append_eq]
  >> dxrule_all_then assume_tac latest_t_trans
  >> dxrule_then (fs o single) latest_t_latest_is_lowest
  >> imp_res_tac mem_get_mem_read
  >> fs[latest_exact]
QED
*)

Definition slc_prop_def:
  slc_prop cid M msg <=>
    msg.cid = cid /\ msg.val = BVal_Imm $ Imm64 1w (* 1w = locked *)
    /\ msg.loc = lock_addr_val
    ==>
    ?m. mem_get M lock_addr_val (latest lock_addr_val (LENGTH M) M) = SOME m
    /\ m.val = BVal_Imm $ Imm64 0w (* 0w = free *)
End

Theorem is_certifiedR_locking_slc_prop:
  !cid s M msg jump_after blocks unlock_entry.
  is_certifiedR
    (cstep_seqR
      (step_restr jump_after blocks unlock_entry)
      (spinlock_concrete2 blocks jump_after unlock_entry) cid)
    (s,(M ++ [msg]))
  /\ slc_inv 0w jump_after unlock_entry cid s (M ++ [msg])
  /\ labels_wf blocks jump_after unlock_entry
  /\ wf_ext_p (BirProgram blocks) cid
  /\ well_formed cid (M ++ [msg]) s
  /\ msg.cid = cid
  /\ MEM (LENGTH M + 1) s.bst_prom
  ==> slc_prop cid M msg
Proof
  rw[slc_prop_def]
  >> drule_then irule is_certifiedR_locking
  >> fs[]
QED

(* spinlock memory correctness invariant *)
Definition sl_mem_correct_inv_def:
  sl_mem_correct_inv M =
    !cid pre. IS_PREFIX M pre /\ LENGTH pre < LENGTH M
    ==> slc_prop cid pre (EL (LENGTH pre) M)
End

Theorem sl_mem_correct_inv_init:
  sl_mem_correct_inv []
Proof
  fs[sl_mem_correct_inv_def]
QED

Theorem sl_mem_correct_inv_prefix:
  !M M'. sl_mem_correct_inv (M ++ M') ==> sl_mem_correct_inv M
Proof
  rw[sl_mem_correct_inv_def]
  >> qmatch_goalsub_rename_tac `slc_prop cid pre`
  >> first_x_assum $ qspecl_then [`cid`,`pre`] assume_tac
  >> gs[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1]
QED

Theorem sl_mem_correct_inv_APPEND_eq:
  !M msg. sl_mem_correct_inv (M ++ [msg])
  <=> sl_mem_correct_inv M /\ !cid. slc_prop cid M msg
Proof
  rw[EQ_IMP_THM,sl_mem_correct_inv_prefix]
  >- drule_then irule sl_mem_correct_inv_prefix
  >> fs[sl_mem_correct_inv_def,rich_listTheory.IS_PREFIX_APPEND,PULL_EXISTS]
  >- (
    qmatch_goalsub_rename_tac `slc_prop cid M msg`
    >> first_x_assum $ qspecl_then [`cid`,`M`,`[msg]`] assume_tac
    >> fs[rich_listTheory.EL_APPEND2]
  )
  >> rw[]
  >> dxrule_then strip_assume_tac $ iffLR listTheory.APPEND_EQ_APPEND
  >> gvs[quantHeuristicsTheory.LIST_LENGTH_COMPARE_1]
  >> simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1]
  >> qmatch_goalsub_rename_tac `pre ++ l' ++ [msg]`
  >> Cases_on `l'` using listTheory.SNOC_CASES
  >> fs[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1]
QED

Theorem parstep_preserves_slc_mem_correct_inv:
  !cid cores M cores' M' s jump_after blocks unlock_entry.
  parstepR_tr (step_restr jump_after blocks unlock_entry)
    (λmem msg. T) cid (cores,M) (cores',M')
  /\ slc_inv 0w jump_after unlock_entry cid s M
  /\ labels_wf blocks jump_after unlock_entry
  /\ wf_ext_p (BirProgram blocks) cid
  /\ sl_mem_correct_inv M
  /\ FLOOKUP cores cid = SOME $ Core cid (spinlock_concrete2 blocks jump_after unlock_entry) s
  /\ well_formed cid M s
  ==> sl_mem_correct_inv M'
Proof
  rpt strip_tac
  >> gvs[cstepR_def,cstep_cases,parstepR_tr_def,parstepR_cases]
  >> drule is_certifiedR_locking_slc_prop
  >> gs[slc_inv_prom,well_formed_promise_self,sl_mem_correct_inv_APPEND_eq,slc_inv_slc_mem_inv_imp]
  >> fs[slc_prop_def]
QED

(* instantiation of the program block *)
Definition prog_block_def:
  prog_block jump_after unlock_entry =
    BBlock_Stmts <|bb_label := BL_Address (Imm64 jump_after);
        bb_statements :=
          [
          (* no-op *)
          BMCStmt_Assert (BExp_Const $ Imm1 1w)
          ];
        bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 unlock_entry |>
End

(* the init state when running the program *)
Definition prog_block_init_def:
  prog_block_init s M = T
End

Theorem prog_block_bir_labels_of_program:
  !jump_after unlock_entry.
    bir_labels_of_program $ BirProgram [prog_block jump_after unlock_entry]
    = [BL_Address (Imm64 jump_after)]
Proof
  EVAL_TAC >> fs[]
QED

Theorem prog_block_addr_unchanged:
  !jump_after' jump_after unlock_entry P blocks cid s M prom s' M'.
   jump_after' = 20w /\ jump_after = BL_Address (Imm64 jump_after') /\
     unlock_entry = jump_after' + 4w /\
    blocks = [prog_block jump_after' unlock_entry] /\
   cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s' M'
  ==>
   addr_unchanged lock_addr_val s.bst_pc s.bst_coh s'.bst_coh s.bst_prom
     s'.bst_prom M
     [lock lock_addr 0w (BL_Address (Imm64 20w)); unlock lock_addr 24w]
Proof
  rpt strip_tac
  >> fs[bir_labels_of_program_unlock,bir_labels_of_program_lock,addr_unchanged_def,listTheory.EVERY_MEM]
  >> strip_tac
  >> imp_res_tac cstep_bgcs_imp
  >> qmatch_assum_rename_tac `cstep P _ cid s M prom s' M'`
  >> reverse $ Cases_on `M = M'`
  >> gvs[cstep_cases]
  >> gvs[spinlock_concrete2_def,lock_wrap_def]
  >> drule_at Any bir_get_current_statement_MEM1
  >> impl_keep_tac
  >- (
    drule bir_get_current_statement_SOME_MEM
    >> fs[bir_labels_of_program_APPEND,bir_labels_of_program_lock,bir_labels_of_program_unlock]
  )
  >> strip_tac
  >> drule bir_get_current_statement_MEM2
  >> impl_keep_tac
  >- (
    drule_then assume_tac bir_get_current_statement_SOME_MEM
    >> gs[bir_labels_of_program_APPEND,bir_labels_of_program_lock,prog_block_bir_labels_of_program,list_disj_def]
  )
  >> CONV_TAC $ LAND_CONV EVAL
  >> csimp[AllCaseEqs(),arithmeticTheory.NOT_LESS,bir_auxiliaryTheory.NUM_LSONE_EQZ]
  >> strip_tac (* 2 subgoals *)
  >> gvs[cstep_cases,clstep_cases,bir_state_read_view_updates_def,combinTheory.APPLY_UPDATE_THM,listTheory.EL]
  >~ [`bmc_exec_general_stmt _ $ BStmtB _`]
  >- (
    fs[bmc_exec_general_stmt_exists]
    >> qhdtm_x_assum `bir_exec_stmt_assert` $ assume_tac o CONV_RULE EVAL
    >> fs[]
  )
  >~ [`bmc_exec_general_stmt _ $ BStmtE _`]
  >> gvs[bmc_exec_general_stmt_exists,bir_exec_stmt_jmp_bst_eq]
QED

Theorem prog_block_jump_constraints:
  !jump_after jump_after' unlock_entry blocks P cid s M prom s' M'.
   jump_after' = 20w /\ jump_after = BL_Address (Imm64 jump_after') /\
     unlock_entry = jump_after' + 4w /\
    blocks = [prog_block jump_after' unlock_entry] /\
   cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom
     s' M' ==>
   jump_constraints s.bst_pc s'.bst_pc
     [unlock lock_addr 24w; lock lock_addr 0w (BL_Address (Imm64 20w))]
Proof
  rpt strip_tac
  >> drule_then assume_tac cstep_same_label
  >> csimp[jump_constraints_eq,bir_labels_of_program_unlock,bir_labels_of_program_lock,bir_block_pc_def,bir_programcounter_t_component_equality]
  >> fs[spinlock_concrete2_def,lock_wrap_def]
  >> qmatch_asmsub_abbrev_tac `BirProgram (A ++ B ++ C)`
  >> Q.ISPECL_THEN [`A`,`B`,`C`,`s.bst_pc`] mp_tac bir_get_current_statement_APPEND3_cases
  >> impl_tac
  >- (
    unabbrev_all_tac
    >> fs[bir_labels_of_program_unlock,bir_labels_of_program_lock]
    >> dsimp[bir_labels_of_program_def,bir_label_of_block_def,prog_block_def,list_disj_def]
  )
  >> unabbrev_all_tac
  >> gvs[cstep_cases,clstep_cases,bir_pc_next_def,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,fence_updates_def,bmc_exec_general_stmt_exists]
  >> imp_res_tac bir_get_current_statement_SOME_MEM
  >> qpat_x_assum `bir_get_current_statement _ _ = SOME _` mp_tac
  >~ [`bir_exec_stmt_cjmp _ cond_e _ _ s`]
  >- (
    ntac 2 $ disch_then strip_assume_tac
    >> gs[bir_labels_of_program_APPEND]
    >> qhdtm_x_assum `SOME` $ mp_tac o GSYM
    >> CONV_TAC $ LAND_CONV EVAL
    >> disch_then assume_tac
    >> gvs[AllCaseEqs()]
    >> qmatch_goalsub_abbrev_tac `bir_exec_stmt_cjmp p cond_e (BLE_Label lbl1) (BLE_Label lbl2) s`
    >> Q.ISPECL_THEN [`p`,`cond_e`,`lbl1`,`lbl2`,`s`] strip_assume_tac bir_exec_stmt_cjmp_disj
    >> unabbrev_all_tac
    >> fs[]
  )
  >~ [`bir_exec_stmt_jmp`]
  >- (
    ntac 2 $ disch_then strip_assume_tac
    >> gs[bir_labels_of_program_APPEND]
    >> qhdtm_x_assum `SOME` $ mp_tac o GSYM
    >> CONV_TAC $ LAND_CONV EVAL
    >> fs[AllCaseEqs(),pairTheory.LAMBDA_PROD,pairTheory.EXISTS_PROD]
    >> strip_tac
    >> gvs[]
    >> qmatch_goalsub_abbrev_tac `bir_exec_stmt_jmp p (BLE_Label lbl) s`
    >> Q.ISPECL_THEN [`p`,`lbl`,`s`] strip_assume_tac bir_exec_stmt_jmp_disj
    >> unabbrev_all_tac
    >> fs[]
  )
  >~ [`bir_get_current_statement _ _ = SOME $ BSExt _`]
  >- (
    (* no statements of this kind *)
    ntac 2 $ disch_then strip_assume_tac
    >> gs[bir_labels_of_program_APPEND,prog_block_bir_labels_of_program]
    >> qhdtm_x_assum `SOME` $ mp_tac o GSYM
    >> CONV_TAC $ LAND_CONV EVAL
    >> fs[AllCaseEqs(),pairTheory.LAMBDA_PROD,pairTheory.EXISTS_PROD]
    >> disch_then assume_tac
    >> gvs[AllCaseEqs()]
  )
QED

(*
Theorem trace_prop:
  !jump_after jump_after' unlock_entry blocks P prom cid s M s' M'.
  jump_after' = 20w
  /\ jump_after = BL_Address $ Imm64 jump_after'
  /\ unlock_entry = jump_after' + 4w
  /\ blocks = [prog_block jump_after' unlock_entry]
  /\ cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s' M'
  /\ well_formed cid M s
  /\ well_formed cid M' s'
  /\ jump_constraints s.bst_pc s'.bst_pc
      [unlock lock_addr 24w; lock lock_addr 0w (BL_Address (Imm64 20w))]
  /\ in_cs_inv (BirProgram [prog_block 20w 24w]) s.bst_pc.bpc_label M
      s.bst_coh lock_addr_val (Imm64 1w)
  ==> in_cs_inv (BirProgram [prog_block 20w 24w]) s'.bst_pc.bpc_label M'
        s'.bst_coh lock_addr_val (Imm64 1w)
Proof
  rw[in_cs_inv_def,prog_block_bir_labels_of_program,cstep_cases]
  >> gs[jump_constraints_eq]
  >~ [`mem_read (M ++ [msg]) lock_addr_val $ s.bst_coh lock_addr_val`]
  >- (
    Cases_on `s.bst_coh lock_addr_val <= LENGTH M`
    >> fs[arithmeticTheory.NOT_LESS_EQUAL,mem_read_append,well_formed_def]
  )
  >> fs[bir_labels_of_program_unlock,bir_labels_of_program_lock]
  >> cheat
  (*
    show that from s through
  *)
QED
*)

(*
TODO fix
Theorem prog_:
  !jump_after jump_after' unlock_entry blocks P prom cid s M s' M'.
  jump_after' = 20w
  /\ jump_after = BL_Address $ Imm64 jump_after'
  /\ unlock_entry = jump_after' + 4w
  /\ blocks = [prog_block jump_after' unlock_entry]
  /\ cstep P (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s' M'
  /\ well_formed cid M s
  /\ well_formed cid M' s'
  ==> step_restr jump_after blocks unlock_entry (s,M) (s',M')
Proof
  rpt strip_tac >> fs[step_restr_def]
  >> conj_asm1_tac
  >~ [`addr_unchanged`]
  >- (
    irule prog_block_addr_unchanged
    >> gvs[]
    >> goal_assum drule
  )
  >> conj_tac
  >~ [`jump_constraints`]
  >- (
    irule prog_block_jump_constraints
    >> gvs[]
    >> goal_assum drule
  )
  >> conj_asm2_tac
  >~ [`cstep P _ cid s M prom s' M'`,`in_cs_inv _ _ M' _ _ _`]
  >- (
    drule_then drule addr_unchanged_in_cs_inv
    >> fs[prog_block_bir_labels_of_program,bir_labels_of_program_APPEND,bir_labels_of_program_unlock,bir_labels_of_program_lock,list_disj_def]
clstep_in_cs_inv
cstep_in_cs_inv
  )
  (* in_cs_inv *)
  >> fs[in_cs_inv_def,bir_labels_of_program_def,bir_label_of_block_def,prog_block_def]
  >> cheat
QED
*)

Theorem bir_labels_of_program_spinlock_concrete =
  blop_prog_labels_thm ``spinlock_concrete``

Theorem bir_labels_of_program_spinlock_abstract_locking =
  blop_prog_labels_thm ``BirProgram $ spinlock_abstract_locking lock_addr' label jump_after``

Theorem bir_labels_of_program_spinlock_abstract_unlocking =
  blop_prog_labels_thm ``BirProgram $ spinlock_abstract_unlocking lock_addr' label jump_after``

Theorem bir_get_stmt_spinlock_cprog_BSGen =
  `bir_get_current_statement spinlock_concrete as.bst_pc = SOME $ BSGen stmt`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

(* equality of the state except for a pc offset *)
Definition state_eq_pc_def:
  state_eq_pc s s' pc_pair <=>
    bst_pc_tuple s'.bst_pc = pc_pair
    /\ !x. s with <| bst_pc := x |> = s' with <| bst_pc := x |>
End

(* invariant for beginning of the lock program regarding v_rOld *)

Theorem lock_v_rOld_eq_coh_inv:
  !blocks jump_after unlock_entry cid s M s' prom jump_after_lock y.
  clstep (BirProgram $ lock lock_addr 0w $ BL_Address $ Imm64 jump_after_lock) cid s M prom s'
  /\ labels_wf blocks (BL_Address (Imm64 jump_after_lock)) unlock_entry
  /\ jump_after = BL_Address (Imm64 jump_after_lock)
  /\ s.bst_pc.bpc_label = BL_Address $ Imm64 y
  /\ MEM y [0w; 4w; 8w]
  /\ s.bst_v_rOld = s.bst_coh lock_addr_val
  ==> s'.bst_v_rOld = s'.bst_coh lock_addr_val
Proof
  rpt strip_tac
  >> imp_res_tac clstep_MEM_bir_labels_of_program
  >> `MEM s.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram $ lock lock_addr 0w jump_after` by
    fs[bir_labels_of_program_lock]
  >> imp_res_tac clstep_bgcs_imp
  >> gvs[clstep_cases,bgcs_lock_zoo,bir_state_read_view_updates_def,bir_eval_exp_view_BExp_Const,GSYM lock_addr_val_def,combinTheory.APPLY_UPDATE_THM,bir_exec_stmt_cjmp_mc_invar]
  >> imp_res_tac bmc_exec_general_stmt_mc_invar
  >> gvs[]
QED

Theorem spinlock_concrete2_v_rOld_eq_coh_inv:
  !blocks jump_after unlock_entry cid s M s' prom jump_after_lock y.
  clstep (spinlock_concrete2 blocks jump_after unlock_entry) cid s M prom s'
  /\ labels_wf blocks (BL_Address (Imm64 jump_after_lock)) unlock_entry
  /\ jump_after = BL_Address (Imm64 jump_after_lock)
  /\ s.bst_pc.bpc_label = BL_Address $ Imm64 y
  /\ MEM y [0w; 4w; 8w]
  /\ s.bst_v_rOld = s.bst_coh lock_addr_val
  ==> s'.bst_v_rOld = s'.bst_coh lock_addr_val
Proof
  rpt strip_tac
  >> gns[spinlock_concrete2_def,lock_wrap_def]
  >> imp_res_tac clstep_bgcs_imp
  >> qmatch_asmsub_abbrev_tac `BirProgram $ lck ++ blocks ++ ulck`
  >> qspecl_then [`lck`,`blocks++ulck`,`s.bst_pc`] mp_tac bir_get_current_statement_APPEND1
  >> unabbrev_all_tac
  >> impl_tac
  >- (
    fs[bir_labels_of_program_APPEND,labels_wf_def,list_disj_append1,list_disj_append2,list_disj_sym_imp,bir_labels_of_program_lock]
  )
  >> gns[]
  >> disch_then $ assume_tac o GSYM
  >> imp_res_tac clstep_MEM_bir_labels_of_program
  >> `MEM s.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram $ lock lock_addr 0w jump_after` by
    fs[spinlock_concrete2_def,bir_labels_of_program_lock]
  >> gvs[clstep_cases,bgcs_lock_zoo,bir_state_read_view_updates_def,bir_eval_exp_view_BExp_Const,GSYM lock_addr_val_def,combinTheory.APPLY_UPDATE_THM,bir_exec_stmt_cjmp_mc_invar]
  >> imp_res_tac bmc_exec_general_stmt_mc_invar
  >> gvs[]
QED


(* refinement *)

Definition spinlock_ref1_core_def:
  spinlock_ref1_core lock_entry unlock_entry
    jump_after_lock jump_after_unlock
    (c, M) (a, aM) <=>
  M = aM /\ a.bst_prom = c.bst_prom
  (* status matches, thus also type errors *)
  /\ (c.bst_status = BST_Running ==> a.bst_status = c.bst_status)
  (* abstract coherence cannot be larger than concrete coherence *)
  /\ (a.bst_coh lock_addr_val <= c.bst_coh lock_addr_val)
  /\ !lbl index.
    bst_pc_tuple c.bst_pc = (BL_Address $ Imm64 lbl, index)
      ==>
(* locking section pc synchronisation *)
    (lbl = lock_entry + 12w /\ 0 < index ==> ?v. bir_read_reg "success" c.bst_environ v)
    /\ (lbl = lock_entry + 16w ==> ?v. bir_read_reg "success" c.bst_environ v)
    (* not (yet) taking the lock *)
    /\ (MEM lbl $ MAP (λx. x + lock_entry) $
          MAP (n2w : num -> word64) $ GENLIST (λx. x * 4) 4
      /\ (lbl = lock_entry + 12w ==> index = 0)
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 lock_entry,0))
    /\ (
      (lbl = lock_entry + 8w /\ index = 1) \/
      (lbl = lock_entry + 12w /\ index = 0)
      ==> bir_read_reg "x5" c.bst_environ 1w (* 1w = locked *)
    )
(*
slc_inv
   /\ (
      (lbl = lock_entry + 12w /\ index = 0w)
      (* following assumption is to be discharged by spinlock_concrete2_v_rOld_eq_coh_inv *)
      ==> s.bst_v_rOld = s.bst_coh lock_addr_val
)
*)
    (* unsuccessful store *)
    /\ (lbl = lock_entry + 12w /\ 0 < index /\ bir_read_reg_nonzero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 lock_entry,0))
    /\ (lbl = lock_entry + 16w /\ index = 0 /\ bir_read_reg_nonzero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 lock_entry,0))
    (* successful store *)
    /\ (
      ((lbl = lock_entry + 16w /\ index = 0) \/ lbl = lock_entry + 12w)
      /\ 0 < index /\ bir_read_reg_zero "success" c.bst_environ
      ==>
        (* state_eq_pc c a (BL_Address $ Imm64 jump_after_lock,0) *)
        (* equality modulo success register *)
        (* state_mod_subset {"success"} c a *)
        a = c
    )
(* after lock, before unlock *)
    /\ (
      (* addresses in lock_def: bir_labels_of_program_lock *)
      ~(MEM lbl $ MAP (λx. x + lock_entry) $
          MAP (n2w : num -> word64) $ GENLIST (λx. x * 4) 4)
      (* addresses in unlock_def: bir_labels_of_program_unlock *)
      /\ ~(MEM lbl $ MAP (λx. x + unlock_entry) $
            MAP (n2w : num -> word64) $ GENLIST (λx. x * 4) 3)
      (* all state components are equal *)
      ==>
        (* the offset is the difference of both
         * max of   bir_labels_of_program_lock    less 4w *)
        (* state_eq_pc c a (BL_Address $ Imm64 $ lbl + 8w,index) *)
        (* state_mod_subset {"success"} c a *)
        a = c
    )
(* unlocking section pc synchronisation *)
    /\ (
      MEM lbl $ MAP (λx. x + unlock_entry) $
        MAP (n2w : num -> word64) $ GENLIST (λx. x * 4) 3
      /\ (lbl = unlock_entry + 8w ==> index = 0)
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 unlock_entry,0)
    )
    (* after unlock *)
    /\ (
      lbl = unlock_entry + 8w ==> index = 1
      ==> (* bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 jump_after_unlock,0) *)
        (* state_mod_subset {"success"} c a *)
        a = c
    )
End

(*
Definition spinlock_ref1_core_def:
  spinlock_ref1_core (c, M) (a, aM) <=>
  M = aM /\ a.bst_prom = c.bst_prom
  /\ (c.bst_status = BST_Running ==> a.bst_status = c.bst_status)
  /\ (a.bst_coh lock_addr_val <= c.bst_coh lock_addr_val)
  /\ !lbl index.
    bst_pc_tuple c.bst_pc = (BL_Address $ Imm64 lbl, index)
      ==>
    (lbl = 16w /\ 0 < index ==> ?v. bir_read_reg "success" c.bst_environ v)
    /\ (lbl = 20w ==> ?v. bir_read_reg "success" c.bst_environ v)
    (* not (yet) taking the lock *)
    /\ (lbl <= 16w /\ (lbl = 16w ==> index = 0)
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 0w,0))
    /\ (
      (lbl = 12w /\ index = 1) \/
      (lbl = 16w /\ index = 0)
      ==> bir_read_reg "x5" c.bst_environ 1w (* 1w = locked *)
    )
    (* unsuccessful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_reg_nonzero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 0w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_reg_nonzero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 0w,0))
    (* successful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_reg_zero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 4w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_reg_zero "success" c.bst_environ
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 4w,0))
    (* after lock, before unlock *)
    /\ (
      20w < lbl /\ lbl <= 32w /\ (lbl = 32w ==> index = 0)
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
      32w <= lbl /\ (lbl = 32w ==> index = 1)
      ==> bst_pc_tuple a.bst_pc = (BL_Address $ Imm64 8w,0)
    )
End
*)

(*
MEM c'.bst_pc.bpc_label (bir_labels_of_program (BirProgram blocks))
==> spinlock_ref1_core 0w unlock_entry jump_after_lock (unlock_entry + 12w) (c',M) (c',M)
*)


Theorem spinlock_ref1_core_promises_self:
  !c M a aM msg f.
  spinlock_ref1_core lock_entry unlock_entry
    jump_after_lock jump_after_unlock (c,M) (a,aM)
  ==> spinlock_ref1_core lock_entry unlock_entry
    jump_after_lock jump_after_unlock (c with bst_prom updated_by f,M++[msg]) (a with bst_prom updated_by f,aM++[msg])
Proof
  rpt strip_tac
  >> fs[spinlock_ref1_core_def]
  >> dsimp[]
  >> rpt strip_tac
  >> gvs[state_mod_subset_def,bir_state_t_component_equality]
  >> rpt $ goal_assum drule
QED

Theorem spinlock_ref1_core_promises_other:
  !c M a aM msg.
  spinlock_ref1_core lock_entry unlock_entry
    jump_after_lock jump_after_unlock (c,M) (a,aM)
  ==> spinlock_ref1_core lock_entry unlock_entry
    jump_after_lock jump_after_unlock (c,M++[msg]) (a,aM++[msg])
Proof
  rpt strip_tac
  >> fs[spinlock_ref1_core_def]
  >> dsimp[]
QED

val simple_refl_step =
    disj1_tac
    >> gvs[spinlock_ref1_core_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def,fence_updates_def,
      combinTheory.APPLY_UPDATE_THM]

(* wf of labels in blocks *)
Definition prog_addr64_def:
  prog_addr64 blocks =
    EVERY (λx. ?y. x = BL_Address $ Imm64 y)
      $ bir_labels_of_program $ BirProgram blocks
End

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM1:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ MEM l (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ A ++ B) l c
    = bir_exec_stmt_jmp_to_label (BirProgram A) l c
Proof
  fs[bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM2:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ MEM l (bir_labels_of_program $ BirProgram B)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ A ++ B) l c
    = bir_exec_stmt_jmp_to_label (BirProgram B) l c
Proof
  fs[bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM1:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ MEM lbl1 (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1
  ==> bir_exec_stmt_jmp (BirProgram $ A ++ B) lbl_exp1 c
    = bir_exec_stmt_jmp (BirProgram $ A) lbl_exp1 c
Proof
  fs[bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_APPEND_MEM1]
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM2:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ MEM lbl1 (bir_labels_of_program $ BirProgram B)
  /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1
  ==> bir_exec_stmt_jmp (BirProgram $ A ++ B) lbl_exp1 c
    = bir_exec_stmt_jmp (BirProgram $ B) lbl_exp1 c
Proof
  fs[bir_exec_stmt_jmp_def,bir_exec_stmt_jmp_to_label_APPEND_MEM2]
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM1:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ OPTION_BIND (bir_eval_exp cond_e c.bst_environ) bir_dest_bool_val = v
  /\ (IS_SOME v /\ THE v ==> MEM lbl1 (bir_labels_of_program $ BirProgram A)
    /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1)
  /\ (IS_SOME v /\ ~(THE v) ==> MEM lbl2 (bir_labels_of_program $ BirProgram A)
    /\ bir_eval_label_exp lbl_exp2 c.bst_environ = SOME lbl2)
  ==> bir_exec_stmt_cjmp (BirProgram $ A ++ B) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def,optionTheory.OPTION_BIND_EQUALS_OPTION]
  >> BasicProvers.TOP_CASE_TAC
  >> rw[COND_RAND,COND_EXPAND_OR]
  >> gs[CaseEq"option"]
  >> fs[bir_exec_stmt_jmp_APPEND_MEM1]
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM2:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ OPTION_BIND (bir_eval_exp cond_e c.bst_environ) bir_dest_bool_val = v
  /\ (IS_SOME v /\ THE v ==> MEM lbl1 (bir_labels_of_program $ BirProgram A)
    /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1)
  /\ (IS_SOME v /\ ~(THE v) ==> MEM lbl2 (bir_labels_of_program $ BirProgram A)
    /\ bir_eval_label_exp lbl_exp2 c.bst_environ = SOME lbl2)
  ==> bir_exec_stmt_cjmp (BirProgram $ B ++ A) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def,optionTheory.OPTION_BIND_EQUALS_OPTION]
  >> BasicProvers.TOP_CASE_TAC
  >> rw[COND_RAND,COND_EXPAND_OR]
  >> gs[CaseEq"option"]
  >> fs[bir_exec_stmt_jmp_APPEND_MEM2]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM2':
  MEM (bir_exec_stmt_jmp_to_label (BirProgram $ B ++ A) x c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ B ++ A) x c
    = bir_exec_stmt_jmp_to_label (BirProgram $ A) x c
Proof
  rw[bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_APPEND]
  >> fs[]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM2'':
  MEM (bir_exec_stmt_jmp_to_label (BirProgram $ A) x c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ MEM x (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ B ++ A) x c
    = bir_exec_stmt_jmp_to_label (BirProgram $ A) x c
Proof
  rw[bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM1':
  MEM (bir_exec_stmt_jmp_to_label (BirProgram $ A ++ B) x c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ A ++ B) x c
    = bir_exec_stmt_jmp_to_label (BirProgram $ A) x c
Proof
  rw[bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_APPEND]
  >> fs[]
QED

Theorem bir_exec_stmt_jmp_to_label_APPEND_MEM1'':
  MEM (bir_exec_stmt_jmp_to_label (BirProgram $ A) x c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ MEM x (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ A ++ B) x c
    = bir_exec_stmt_jmp_to_label (BirProgram $ A) x c
Proof
  rw[bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM2':
  MEM (bir_exec_stmt_jmp (BirProgram $ B ++ A) lbl_exp c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp (BirProgram $ B ++ A) lbl_exp c
    = bir_exec_stmt_jmp (BirProgram A) lbl_exp c
Proof
  rw[bir_exec_stmt_jmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> fs[bir_exec_stmt_jmp_to_label_APPEND_MEM2']
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM2'':
  MEM (bir_exec_stmt_jmp (BirProgram A) lbl_exp c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp c.bst_environ = SOME lbl
  /\ MEM lbl (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp (BirProgram $ B ++ A) lbl_exp c
    = bir_exec_stmt_jmp (BirProgram A) lbl_exp c
Proof
  rw[bir_exec_stmt_jmp_def]
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> fs[bir_exec_stmt_jmp_to_label_APPEND_MEM2'']
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM1':
  MEM (bir_exec_stmt_jmp (BirProgram $ A ++ B) lbl_exp c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp (BirProgram $ A ++ B) lbl_exp c
    = bir_exec_stmt_jmp (BirProgram A) lbl_exp c
Proof
  rw[bir_exec_stmt_jmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> fs[bir_exec_stmt_jmp_to_label_APPEND_MEM1']
QED

Theorem bir_exec_stmt_jmp_APPEND_MEM1'':
  MEM (bir_exec_stmt_jmp (BirProgram $ A) lbl_exp c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp c.bst_environ = SOME lbl
  /\ MEM lbl (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_jmp (BirProgram $ A ++ B) lbl_exp c
    = bir_exec_stmt_jmp (BirProgram A) lbl_exp c
Proof
  rw[bir_exec_stmt_jmp_def]
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> fs[bir_exec_stmt_jmp_to_label_APPEND_MEM1'']
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM1'':
  MEM (bir_exec_stmt_cjmp (BirProgram $ A) cond_e lbl_exp1 lbl_exp2 c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1
  /\ MEM lbl1 (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp2 c.bst_environ = SOME lbl2
  /\ MEM lbl2 (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_cjmp (BirProgram $ A ++ B) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> gs[bir_exec_stmt_jmp_APPEND_MEM1'']
  >> csimp[]
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM2'':
  MEM (bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c).bst_pc.bpc_label
    (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp1 c.bst_environ = SOME lbl1
  /\ MEM lbl1 (bir_labels_of_program $ BirProgram A)
  /\ bir_eval_label_exp lbl_exp2 c.bst_environ = SOME lbl2
  /\ MEM lbl2 (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_cjmp (BirProgram $ B ++ A) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> gs[bir_exec_stmt_jmp_APPEND_MEM2'']
  >> csimp[]
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM2':
  MEM (bir_exec_stmt_cjmp (BirProgram $ B ++ A) cond_e lbl_exp1 lbl_exp2 c).bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_cjmp (BirProgram $ B ++ A) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> csimp[bir_exec_stmt_jmp_APPEND_MEM2']
QED

Theorem bir_exec_stmt_cjmp_APPEND_MEM1':
  MEM (bir_exec_stmt_cjmp (BirProgram $ A ++ B) cond_e lbl_exp1 lbl_exp2 c).bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  ==> bir_exec_stmt_cjmp (BirProgram $ A ++ B) cond_e lbl_exp1 lbl_exp2 c
    = bir_exec_stmt_cjmp (BirProgram A) cond_e lbl_exp1 lbl_exp2 c
Proof
  rw[bir_exec_stmt_cjmp_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gs[AllCaseEqs(),COND_RAND,COND_RATOR,COND_EXPAND]
  >> csimp[bir_exec_stmt_jmp_APPEND_MEM1']
QED

Theorem clstep_APPEND_MEM1_imp:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ MEM c'.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ clstep (BirProgram $ A ++ B) cid c M prom c'
  ==> clstep (BirProgram A) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_all_then assume_tac bir_get_current_statement_MEM1
  >> fs[clstep_cases]
  >> gs[bmc_exec_general_stmt_exists]
  >> rpt $ goal_assum $ rev_drule_at Any
  >> gvs[bir_exec_stmt_jmp_APPEND_MEM1',bir_exec_stmt_cjmp_APPEND_MEM1']
  >> fs[COND_RAND,COND_RATOR,bir_labels_of_program_APPEND]
QED

Definition jmp_targets_in_region_def:
  jmp_targets_in_region p pc env =
    !labels. labels = bir_labels_of_program $ BirProgram p
    ==>
      case bir_get_current_statement (BirProgram p) pc of
      | SOME $ BSGen $ BStmtE $ BStmt_Jmp l_exp =>
          (case bir_eval_label_exp l_exp env of
          | NONE => T
          | SOME l => MEM l labels)
      | SOME $ BSGen $ BStmtE $ BStmt_CJmp exp l1_exp l2_exp =>
          ((case bir_eval_label_exp l1_exp env of
          | NONE => T
          | SOME l => MEM l labels)
            /\ (case bir_eval_label_exp l2_exp env of
            | NONE => T
            | SOME l => MEM l labels))
      | _ => T
End

Theorem jmp_targets_in_region_APPEND1:
  jmp_targets_in_region B pc env
  /\ MEM pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==> jmp_targets_in_region (A ++ B) pc env
Proof
  fs[jmp_targets_in_region_def,optionTheory.option_case_compute]
  >> rpt strip_tac
  >> drule bir_get_current_statement_APPEND2
  >> disch_then $ drule_then $ fs o single
  >> dxrule_then strip_assume_tac $ iffLR optionTheory.IS_SOME_EXISTS
  >> rpt BasicProvers.TOP_CASE_TAC
  >> gvs[]
  >> rw[] >> fs[bir_labels_of_program_APPEND]
  >> first_x_assum drule >> fs[]
QED

Theorem jmp_targets_in_region_APPEND2:
  jmp_targets_in_region B pc env
  /\ MEM pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
    (bir_labels_of_program $ BirProgram A)
  ==> jmp_targets_in_region (B ++ A) pc env
Proof
  fs[jmp_targets_in_region_def,optionTheory.option_case_compute]
  >> rpt strip_tac
  >> drule bir_get_current_statement_APPEND1
  >> disch_then $ drule_then $ fs o single
  >> dxrule_then strip_assume_tac $ iffLR optionTheory.IS_SOME_EXISTS
  >> rpt BasicProvers.TOP_CASE_TAC
  >> gvs[]
  >> rw[] >> fs[bir_labels_of_program_APPEND]
  >> first_x_assum drule >> fs[]
QED

Theorem clstep_APPEND_MEM1_imp2:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram A)
  /\ jmp_targets_in_region A c.bst_pc c.bst_environ
  /\ clstep (BirProgram A) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==> clstep (BirProgram $ A ++ B) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_all_then assume_tac bir_get_current_statement_APPEND1
  >> imp_res_tac clstep_MEM_bir_labels_of_program
  >> fs[clstep_cases]
  >~ [`BSExt`]
  >- dsimp[bir_labels_of_program_APPEND]
  >> gs[bmc_exec_general_stmt_exists]
  >> rpt $ goal_assum $ rev_drule_at Any
  >> fs[]
  >> gvs[AllCaseEqs(),optionTheory.option_case_compute]
  >> rw[optionTheory.option_case_compute,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def]
  >> gvs[COND_RAND,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_to_label_APPEND_MEM1,bir_labels_of_program_APPEND,optionTheory.option_case_compute,bir_exec_stmt_jmp_def,jmp_targets_in_region_def]
QED

Theorem clstep_APPEND_MEM2_imp:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ jmp_targets_in_region B c.bst_pc c.bst_environ
  /\ MEM c'.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ clstep (BirProgram $ A ++ B) cid c M prom c'
  ==> clstep (BirProgram B) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_all_then assume_tac bir_get_current_statement_MEM2
  >> fs[clstep_cases]
  >> gs[bmc_exec_general_stmt_exists]
  >> rpt $ goal_assum $ rev_drule_at Any
  >> fs[]
  >> gvs[AllCaseEqs(),optionTheory.option_case_compute]
  >> rw[optionTheory.option_case_compute,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def]
  >> gvs[COND_RAND,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_to_label_APPEND_MEM2,bir_labels_of_program_APPEND,optionTheory.option_case_compute,bir_exec_stmt_jmp_def,jmp_targets_in_region_def]
QED

Theorem clstep_APPEND_MEM2_imp2:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ jmp_targets_in_region B c.bst_pc c.bst_environ
  /\ clstep (BirProgram B) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  ==> clstep (BirProgram $ A ++ B) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_all_then assume_tac bir_get_current_statement_APPEND2
  >> fs[clstep_cases,jmp_targets_in_region_def]
  >> gs[bmc_exec_general_stmt_exists]
  >> rpt $ goal_assum $ rev_drule_at Any
  >> fs[]
  >> gvs[AllCaseEqs(),optionTheory.option_case_compute]
  >> rw[optionTheory.option_case_compute,bir_exec_stmt_cjmp_def,bir_exec_stmt_jmp_def]
  >> gvs[COND_RAND,bir_exec_stmt_jmp_to_label_APPEND_MEM2,bir_labels_of_program_APPEND]
QED

(* reduce reasoning about compound program to reasoning about one region, apart
 * from the jumps between regions *)
Theorem clstep_APPEND3_mid_imp:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ jmp_targets_in_region B c.bst_pc c.bst_environ
  /\ clstep (BirProgram B) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
    (bir_labels_of_program $ BirProgram C)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram C)
  ==> clstep (BirProgram $ A ++ B ++ C) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> irule clstep_APPEND_MEM1_imp2
  >> irule_at Any clstep_APPEND_MEM2_imp2
  >> fs[bir_labels_of_program_APPEND,list_disj_sym_imp,list_disj_append2,list_disj_append1,jmp_targets_in_region_APPEND1]
QED

Theorem clstep_APPEND3_fst_imp:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ jmp_targets_in_region B c.bst_pc c.bst_environ
  /\ clstep (BirProgram B) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
    (bir_labels_of_program $ BirProgram C)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram C)
  ==> clstep (BirProgram $ B ++ A ++ C) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> irule clstep_APPEND_MEM1_imp2
  >> irule_at Any clstep_APPEND_MEM1_imp2
  >> gs[bir_labels_of_program_APPEND,list_disj_sym_imp,list_disj_append2,list_disj_append1,jmp_targets_in_region_APPEND2]
QED

Theorem clstep_APPEND3_thrd_imp:
  MEM c.bst_pc.bpc_label (bir_labels_of_program $ BirProgram B)
  /\ jmp_targets_in_region B c.bst_pc c.bst_environ
  /\ clstep (BirProgram B) cid c M prom c'
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ list_disj (bir_labels_of_program $ BirProgram B)
    (bir_labels_of_program $ BirProgram C)
  /\ list_disj (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram C)
  ==> clstep (BirProgram $ A ++ C ++ B) cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> irule clstep_APPEND_MEM2_imp2
  >> gs[bir_labels_of_program_APPEND,list_disj_sym_imp,list_disj_append2,list_disj_append1,jmp_targets_in_region_APPEND2]
QED

(* same transition with a common part *)

Theorem bir_exec_stmt_jmp_to_label_MEM:
  MEM lbl1 $ bir_labels_of_program $ BirProgram p''
  ==> bir_exec_stmt_jmp_to_label (BirProgram $ p ++ p'') lbl1 c
    = bir_exec_stmt_jmp_to_label (BirProgram $ p' ++ p'') lbl1 c
Proof
  dsimp[bir_exec_stmt_jmp_to_label_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR,bir_labels_of_program_APPEND]
QED

Theorem bir_exec_stmt_jmp_MEM:
  (IS_SOME $ bir_eval_label_exp lbl1 c.bst_environ
    ==> MEM (THE $ bir_eval_label_exp lbl1 c.bst_environ) $ bir_labels_of_program $ BirProgram p'')
  ==> bir_exec_stmt_jmp (BirProgram $ p ++ p'') lbl1 c
    = bir_exec_stmt_jmp (BirProgram $ p' ++ p'') lbl1 c
Proof
  dsimp[bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND]
  >> rpt strip_tac
  >> gs[bir_exec_stmt_jmp_to_label_MEM]
QED

Theorem bir_exec_stmt_cjmp_MEM:
  OPTION_BIND (bir_eval_exp cond_e c.bst_environ) bir_dest_bool_val = v
  /\ (IS_SOME v /\ THE v ==> MEM lbl1 (bir_labels_of_program $ BirProgram p'')
    /\ bir_eval_label_exp lbl1_exp c.bst_environ = SOME lbl1)
  /\ (IS_SOME v /\ ~(THE v) ==> MEM lbl2 (bir_labels_of_program $ BirProgram p'')
    /\ bir_eval_label_exp lbl2_exp c.bst_environ = SOME lbl2)
  ==> bir_exec_stmt_cjmp (BirProgram $ p ++ p'') cond_e lbl1_exp lbl2_exp c
    = bir_exec_stmt_cjmp (BirProgram $ p' ++ p'') cond_e lbl1_exp lbl2_exp c
Proof
  dsimp[bir_exec_stmt_cjmp_def,optionTheory.OPTION_BIND_EQUALS_OPTION,COND_RAND,optionTheory.option_case_compute,COND_EXPAND_OR]
  >> csimp[]
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `OPTION_BIND a` >> Cases_on `a` >> fs[]
  >> qmatch_asmsub_abbrev_tac `IS_SOME a` >> Cases_on `a` >> fs[]
  >> qmatch_asmsub_abbrev_tac `SOME a` >> Cases_on `a`
  >> gs[bir_exec_stmt_jmp_MEM]
QED

Theorem clstep_common_prog:
  !p p' p'' cid c M prom c' stmt.
  clstep (BirProgram $ p ++ p'') cid c M prom c'
  /\ MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p''
  /\ (!x. c'.bst_status = BST_JumpOutside x ==> ~(MEM x $ bir_labels_of_program $ BirProgram p)
      /\ ~(MEM x $ bir_labels_of_program $ BirProgram p'))
  /\ MEM c.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p''
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p ++ p''
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p' ++ p''
  ==> clstep (BirProgram $ p' ++ p'') cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_get_current_statement_MEM2
  >> qmatch_goalsub_rename_tac `BirProgram $ p' ++ p''`
  >> drule_at_then Any (qspec_then `p'` assume_tac) bir_get_current_statement_APPEND2
  >> gs[bir_labels_of_program_APPEND,list_disj_ALL_DISTINCT,list_disj_sym_imp]
  >> gvs[clstep_cases,bmc_exec_general_stmt_exists]
  >> dsimp[]
  >> gvs[]
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
    goal_assum drule >> MK_COMB_TAC >> fs[]
    >> fs[bir_exec_stmt_cjmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR]
    >> gs[bir_exec_stmt_jmp_def,optionTheory.IS_SOME_EXISTS,optionTheory.OPTION_BIND_EQUALS_OPTION]
    >> gs[bir_block_pc_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR,bir_labels_of_program_def,bir_state_set_typeerror_def]
    >> gs[bir_state_set_typeerror_def]
  )
  >~ [`BMCStmt_Assign`]
  >- (
    rpt $ goal_assum drule
    >> fs[]
  )
  >~ [`BMCStmt_Store`]
  >- rpt (rpt $ goal_assum drule >> fs[])
  >~ [`BStmt_Jmp`]
  >- (
    fs[bir_exec_stmt_cjmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR]
    >> gs[bir_exec_stmt_jmp_def,optionTheory.IS_SOME_EXISTS,optionTheory.OPTION_BIND_EQUALS_OPTION]
    >> gs[bir_block_pc_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR,bir_labels_of_program_def,bir_state_set_typeerror_def]
  )
  >~ [`BSExt`]
  >- fs[bir_labels_of_program_APPEND]
QED

(* clstep_common_prog for when the jump target is within p and p' *)

Theorem clstep_common_prog':
  !p p' p'' cid c M prom c' stmt.
  clstep (BirProgram $ p ++ p'') cid c M prom c'
  /\ MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p
  /\ MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p'
  /\ (!x. c'.bst_status = BST_JumpOutside x ==> ~(MEM x $ bir_labels_of_program $ BirProgram p)
      /\ ~(MEM x $ bir_labels_of_program $ BirProgram p'))
  /\ MEM c.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram p''
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p ++ p''
  /\ ALL_DISTINCT $ bir_labels_of_program $ BirProgram $ p' ++ p''
  ==> clstep (BirProgram $ p' ++ p'') cid c M prom c'
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_get_current_statement_MEM2
  >> qmatch_goalsub_rename_tac `BirProgram $ p' ++ p''`
  >> drule_at_then Any (qspec_then `p'` assume_tac) bir_get_current_statement_APPEND2
  >> gs[bir_labels_of_program_APPEND,list_disj_ALL_DISTINCT,list_disj_sym_imp]
  >> gvs[clstep_cases,bmc_exec_general_stmt_exists]
  >> dsimp[]
  >> gvs[]
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
    goal_assum drule >> MK_COMB_TAC >> fs[]
    >> fs[bir_exec_stmt_cjmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR]
    >> gs[bir_exec_stmt_jmp_def,optionTheory.IS_SOME_EXISTS,optionTheory.OPTION_BIND_EQUALS_OPTION]
    >> gs[bir_block_pc_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR,bir_labels_of_program_def,bir_state_set_typeerror_def]
  )
  >~ [`BMCStmt_Assign`]
  >- (
    rpt $ goal_assum drule
    >> fs[]
  )
  >~ [`BMCStmt_Store`]
  >- rpt (rpt $ goal_assum drule >> fs[])
  >~ [`BStmt_Jmp`]
  >- (
    fs[bir_exec_stmt_cjmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR]
    >> gs[bir_exec_stmt_jmp_def,optionTheory.IS_SOME_EXISTS,optionTheory.OPTION_BIND_EQUALS_OPTION]
    >> gs[bir_block_pc_def,bir_exec_stmt_jmp_to_label_def,bir_exec_stmt_jmp_def,optionTheory.option_case_compute,COND_RAND,COND_RATOR,COND_EXPAND_OR,bir_labels_of_program_def,bir_state_set_typeerror_def]
  )
  >~ [`BSExt`]
  >- fs[bir_labels_of_program_APPEND]
QED


(* evaluation of all intermediate steps in the concrete lock section *)

(*

Theorem
  clstep p cid s M prom s'
  /\ slc_inv lock_entry jump_after unlock_entry cid s M
  /\ mem_value_Imm64 M
  /\ lock_entry = 0w
  /\ jump_after = BL_Address $ Imm64 32w
(*
  /\ s.bst_pc.bpc_label = BL_Address $ Imm64 $ lock_entry + 12w
*)
  /\ s.bst_pc.bpc_label = BL_Address $ Imm64 $ lock_entry + 12w
  /\ s.bst_pc.bpc_index = 0
  /\ p = BirProgram $ lock lock_addr lock_entry jump_after
  /\ s.bst_environ = BEnv f
  ==> XX s'
Proof

rpt strip_tac
>> gvs[clstep_cases,bgcs_lock_zoo,bmc_exec_general_stmt_exists,bir_eval_exp_view_BExp_Const',bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def]
>> gvs[bir_state_fulful_view_updates_def,bir_state_read_view_updates_def,GSYM lock_addr_def,GSYM lock_addr_val_def,bir_eval_exp_view_def,bir_eval_view_of_exp_def,fulfil_update_viewenv_def]
>> fs[mem_value_Imm64_def] >> PRED_ASSUM is_forall imp_res_tac
>> gvs[env_update_cast64_def,bir_immTheory.n2bs_b2n,type_of_bir_imm_EQ_ELIMS]
>> gvs[bir_env_update_SOME_eq',bir_exec_stmt_cjmp_def]
>> gvs[fulfil_update_env_BVar_eq,slc_inv_def,bst_pc_tuple_def]
>> gvs[bir_read_reg_def]

>> fs o single $ EVAL o Term $ `bir_eval_exp
                   (BExp_UnaryExp BIExp_Not
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "x5" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 0w)))) (BEnv f)`
>> qmatch_goalsub_abbrev_tac `option_CASE X NONE bir_dest_bool_val`
>> qmatch_goalsub_abbrev_tac `option_CASE X`
>> Cases_on`IS_SOME X` >> unabbrev_all_tac
>> gvs[optionTheory.IS_SOME_EXISTS]
>> Cases_on`bir_dest_bool_val x = SOME F`
>> fs[]

QED
*)

(*
well_formed_def
well_formed_fwdb_def
well_formed_fwdb_coh
clstep_cases

(* first step: constant view, lock address is constant *)
(* know that t = latest "unlock" store to lock address before the "lock" store *)
   s.bst_pc.bpc_label = BL_Address $ Imm64 lock_entry
/\ s.bst_pc.bpc_index = 0
/\ v_post = MAX s.bst_v_rNew (mem_read_view (s.bst_fwdb lock_addr_val) t)
(* mem_read M lock_addr_val t = SOME $ BVal_Imm $ Imm64 v' *)
==> (* BVal_Imm $ Imm64 42w; v_addr = 0 *)
  s' = s with <| bst_pc updated_by bir_pc_next;
          bst_environ := BEnv f(|"x5" |-> SOME (BVal_Imm (Imm64 v'))|);
          bst_viewenv updated_by (\env. env |+ (BVar "x5" (BType_Imm Bit64), v_post)); (* obsolete (by later) *)
          bst_coh updated_by (lock_addr_val =+ MAX (s.bst_coh lock_addr_val) v_post);  (* obsolete (by later) *)
(* keep *) bst_v_rOld := MAX s.bst_v_rOld v_post;
          bst_xclb := SOME <|xclb_time := t; xclb_view := v_post|> |>  (* obsolete (by later) *)

(* conditional jump at
   s.bst_pc.bpc_label = BL_Address $ Imm64 $ lock_entry + 4w
/\ s.bst_pc.bpc_index = 0
only ensures that the condition holds
 IS_SOME $ FLOOKUP s.bst_viewenv $ BVar "x5" $ BType_Imm Bit64
 s.bst_environ = BEnv f /\ IS_SOME $ f "x5"
   /\ f "x5" <> SOME $ BVal_Imm $ Imm64 0w
   /\ type_of_bir_val $ THE $ f "x5" = BType_Imm Bit64
 *)

(* assignment ? *)
   s.bst_pc.bpc_label = BL_Address $ Imm64 $ lock_entry + 8w
/\ s.bst_pc.bpc_index = 0
==>
  s' = s with <|bst_pc updated_by bir_pc_next;
             bst_environ := BEnv f(|"x5" |-> SOME (BVal_Imm (Imm64 1w))|);
             bst_viewenv updated_by
               (\e. e |+ (BVar "x5" (BType_Imm Bit64),0))|>

(* successful store
 * from first step: upd < v_post *)
     s.bst_pc.bpc_label = BL_Address $ Imm64 $ lock_entry + 12w
  /\ s.bst_pc.bpc_index = 0
(* "success" register exists *)
(* IS_SOME $ FLOOKUP s.bst_viewenv $ BVar "success" $ BType_Imm Bit64
  s.bst_environ = BEnv f /\ IS_SOME $ f "success"
*)
==> s' = s with <|bst_pc updated_by bir_pc_next;
          bst_environ := BEnv f(|"success" |-> SOME (BVal_Imm v_succ)|);
          bst_viewenv := s.bst_viewenv |+ (BVar "success" $ BType_Imm Bit64,v_post);
          bst_coh updated_by (lock_addr_val =+ v_post);
          bst_v_wOld := MAX s.bst_v_wOld v_post;
          bst_v_rNew := s.bst_v_rNew;
          bst_v_wNew := s.bst_v_wNew;
          bst_v_CAP := s.bst_v_CAP;
          bst_v_Rel := s.bst_v_Rel;
          bst_prom updated_by remove_prom [v_post];
          bst_fwdb updated_by (lock_addr_val =+ <|fwdb_time := v_post; fwdb_view := 0; fwdb_xcl := T|>);
          bst_xclb := NONE|>
*)

(*
 * refinement of lock and abstract lock
 *)
Theorem clstep_concrete_abstract_refinement_lock:
   clstep
     (BirProgram
        (lock lock_addr 0w (BL_Address (Imm64 jump_after_lock)) ++ blocks ++
         unlock lock_addr unlock_entry)) cid c M prom c' /\
   jump_after_unlock = unlock_entry + 12w /\ lock_entry = 0w /\
   labels_wf blocks (BL_Address (Imm64 jump_after_lock)) unlock_entry /\
   prog_addr64 blocks /\
   jump_constraints c.bst_pc c'.bst_pc
     [unlock lock_addr unlock_entry;
      lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))] /\
   spinlock_ref1_core lock_entry unlock_entry jump_after_lock
     jump_after_unlock (c,M) (a,aM) /\
   MEM c.bst_pc.bpc_label
     (bir_labels_of_program
        (BirProgram (lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))))) /\
   bir_get_current_statement
     (BirProgram (lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))))
     c.bst_pc =
   SOME stmt ==>
   spinlock_ref1_core 0w unlock_entry jump_after_lock (unlock_entry + 12w)
     (c',M) (a,aM) /\ NULL prom \/
   ?a'.
     clstep
       (spinlock_abstract2 blocks (BL_Address (Imm64 0w))
          (BL_Address (Imm64 jump_after_lock))
          (BL_Address (Imm64 unlock_entry))
          (BL_Address (Imm64 (unlock_entry + 12w)))) cid a aM prom a' /\
     spinlock_ref1_core 0w unlock_entry jump_after_lock (unlock_entry + 12w)
       (c',M) (a',aM)
Proof

QED


Theorem clstep_preserves_spinlock_ref1_core:
  !cid c M prom c' a aM.
    clstep (spinlock_concrete2 blocks (BL_Address $ Imm64 jump_after_lock) unlock_entry) cid c M prom c'
    /\ jump_after_unlock = unlock_entry + 12w
    /\ lock_entry = 0w
    /\ labels_wf blocks (BL_Address $ Imm64 jump_after_lock) unlock_entry
    /\ prog_addr64 blocks
    /\ jump_constraints c.bst_pc c'.bst_pc
      [unlock lock_addr unlock_entry; lock lock_addr 0w (BL_Address $ Imm64 jump_after_lock)]
    /\ spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock  (c,M) (a,aM)
    ==>
    (* reflexive case cannot happen when promises are discharged *)
    (spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock (c',M) (a,aM)
      /\ NULL prom)
    \/ ?a'.
      clstep (spinlock_abstract2 blocks (BL_Address $ Imm64 0w) (BL_Address $ Imm64 jump_after_lock) (BL_Address $ Imm64 unlock_entry) (BL_Address $ Imm64 jump_after_unlock)) cid a aM prom a'
      /\ spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock (c',M) (a',aM)
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule bir_get_current_statement_SOME_MEM
  >> disch_then $ strip_assume_tac o REWRITE_RULE[spinlock_concrete2_def,lock_wrap_def,bir_labels_of_program_APPEND,listTheory.MEM_APPEND]
  >~ [`MEM c.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram blocks`,`spinlock_concrete2 blocks`]
  >- (
    `MEM c'.bst_pc.bpc_label $ bir_labels_of_program
      (BirProgram (lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))
        ++ unlock lock_addr unlock_entry) : progc_t)
      ==> bst_pc_tuple c'.bst_pc = (BL_Address $ Imm64 lock_entry, 0)
        \/ bst_pc_tuple c'.bst_pc = (BL_Address $ Imm64 unlock_entry, 0)` by (
      gs[bir_labels_of_program_APPEND,jump_constraints_thm,bir_block_pc_def,labels_wf_def,bir_programcounter_t_component_equality,lock_NOT_NULL,unlock_NOT_NULL,list_disj_spec_ho,lock_bir_pc_first,unlock_bir_pc_first,bst_pc_tuple_def]
      >> dsimp[]
    )
    >> `~(MEM c.bst_pc.bpc_label $ bir_labels_of_program
        (BirProgram (lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))
          ++ unlock lock_addr unlock_entry) : progc_t))` by (
      fs[list_disj_spec_ho,bir_labels_of_program_APPEND,labels_wf_def]
    )
    >> `?y. c.bst_pc.bpc_label = BL_Address $ Imm64 y` by fs[prog_addr64_def,listTheory.EVERY_MEM]
    >> dxrule_then assume_tac $ iffLR spinlock_ref1_core_def
    >> gvs[bst_pc_tuple_def,bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_labels_of_program_APPEND]
    (* transition: blocks -> _ *)
    >> disj2_tac
    (* TODO show: perform same step Why possible? *)
    >> fs[spinlock_concrete2_def,lock_wrap_def]
    >> qmatch_asmsub_abbrev_tac `BirProgram $ lck ++ blocks ++ unl`
    >> Cases_on `MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram blocks`

    >- (
      unabbrev_all_tac
      >> simp[spinlock_abstract2_def]
      >> irule_at Any clstep_APPEND3_thrd_imp
      >> `jmp_targets_in_region blocks a.bst_pc a.bst_environ` by (
        cheat (* restrict relation to these transitions *)
      )
      >> dxrule_then assume_tac bir_get_current_statement_MEM1
      >> gs[bir_labels_of_program_APPEND]
      >> dxrule bir_get_current_statement_MEM2
      >> impl_tac
      >- gs[bir_labels_of_program_APPEND,labels_wf_def,list_disj_sym_imp]
      >> strip_tac
      >> dxrule_at_then (Pat `clstep`) assume_tac clstep_APPEND_MEM1_imp
      >> gs[bir_labels_of_program_APPEND]
      >> dxrule_at_then (Pat `clstep`) assume_tac clstep_APPEND_MEM2_imp
      >> gs[bir_labels_of_program_APPEND,labels_wf_def,list_disj_sym_imp]
      >> goal_assum $ drule_at $ Pat `clstep`
      >> fs[bir_labels_of_program_spinlock_abstract_unlocking,bir_labels_of_program_spinlock_abstract_locking]
      >> rpt conj_tac
      (* TODO speed-up this evaluation *)
      >~ [`spinlock_ref1_core 0w unlock_entry jump_after_lock (unlock_entry + 12w) (c',M) (c',M)`]
      >- (
        fs[spinlock_ref1_core_def,bst_pc_tuple_def]
        >> dsimp[]
        >> rw[]
        >> gs[bir_labels_of_program_lock,bir_labels_of_program_unlock,list_disj_spec_ho]
      )
      >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,list_disj_spec_ho]
    )

    >> Cases_on `MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram lck`
    (* blocks -> lock *)
    >- (

      (* put blocks last in assumption *)
      >> `PERM (lck ++ blocks ++ unl) $ lck ++ unl ++ blocks` by (
        REWRITE_TAC[GSYM APPEND_ASSOC]
        >> fs[sortingTheory.PERM_APPEND_IFF]
        >> ONCE_REWRITE_TAC[sortingTheory.PERM_FUN_APPEND]
        >> REWRITE_TAC[sortingTheory.PERM_REFL]
      )
      >> drule $ iffLR clstep_permute_prog
      >> disch_then $ dxrule_at Any
      >> impl_tac
      >- (
        unabbrev_all_tac
        >> gs[bir_labels_of_program_lock,bir_labels_of_program_unlock,labels_wf_def]
        >> cheat (* sortingTheory.ALL_DISTINCT_PERM *)
      )
      >> strip_tac
      >> dxrule bir_get_current_statement_PERM
      >> disch_then $ qspec_then `a.bst_pc` mp_tac
      >> impl_tac >- cheat
      >> strip_tac
      >> drule clstep_common_prog
      >> fs[spinlock_abstract2_def]
      >> disch_then $ irule_at Any
      >> gs[]
      >> qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
      >> simp[bir_labels_of_program_APPEND]
      >> unabbrev_all_tac
      >> fs[bir_labels_of_program_lock,bir_labels_of_program_unlock,bir_labels_of_program_spinlock_abstract_locking,bir_labels_of_program_spinlock_abstract_unlocking]
      >> REWRITE_TAC[APPEND_ASSOC]
      >> `spinlock_ref1_core 0w unlock_entry jump_after_lock
          (unlock_entry + 12w) (c',M) (c',M)` by (
        fs[spinlock_ref1_core_def,bst_pc_tuple_def]
        >> dsimp[]
        >> cheat
      )
      >> cheat (* addresses distinct by labels_wf_def *)
      (* TODO how to deal with the jump outside? *)
    )
    (* blocks -> unlock *)
    >> `MEM c'.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram unl` by (
      imp_res_tac clstep_MEM_bir_labels_of_program
      >> gs[bir_labels_of_program_APPEND]
    )
    >> cheat (* same reasoning as block -> locks  *)
    >> unabbrev_all_tac
    >> gs[jump_constraints_def,bir_labels_of_program_unlock,unlock_NOT_NULL,unlock_bir_pc_first]
    >- gs[labels_wf_def,bir_labels_of_program_unlock,bir_labels_of_program_lock]
    >> fs[spinlock_abstract2_def]
    >> irule_at Any clstep_common_prog
    >> dxrule_at (Pat `clstep`) $ iffLR clstep_permute_prog
    >> disch_then $ irule_at Any
    >> qmatch_asmsub_abbrev_tac `bir_get_current_statement (BirProgram  $ lck ++ _ ++ ulck) a.bst_pc = SOME stmt`
    >> `bir_get_current_statement (BirProgram $ lck ++ ulck ++ blocks) a.bst_pc = SOME stmt
      /\ bir_get_current_statement (BirProgram blocks) a.bst_pc = SOME stmt` by (
      qspecl_then [`lck++ulck`,`blocks`,`a.bst_pc`] mp_tac bir_get_current_statement_APPEND2
      >> qspecl_then [`lck`,`blocks`,`a.bst_pc`] mp_tac bir_get_current_statement_APPEND2
      >> qspecl_then [`lck++blocks`,`ulck`,`a.bst_pc`] mp_tac bir_get_current_statement_APPEND1
      >> fs[bir_labels_of_program_APPEND,list_disj_append1,list_disj_sym_imp,labels_wf_def]
  )
  >> goal_assum $ drule_at Any
  >> REWRITE_TAC[sortingTheory.PERM_APPEND_IFF,GSYM APPEND_ASSOC,sortingTheory.PERM_APPEND]
  >> unabbrev_all_tac
  >> fs[bir_labels_of_program_APPEND,bir_labels_of_program_unlock,bir_labels_of_program_lock]
  >> `spinlock_ref1_core 0w unlock_entry jump_after_lock (unlock_entry + 12w) (c',M) (c',M)` by (
    fs[bir_labels_of_program_lock,bir_labels_of_program_unlock]
    dsimp[spinlock_ref1_core_def,bst_pc_tuple_def]
  )

  )

  >~ [`MEM c.bst_pc.bpc_label $ bir_labels_of_program $ BirProgram $ lock _ _ _`]

  >- (

    fs[spinlock_concrete2_def,lock_wrap_def]
    >> drule bir_get_current_statement_MEM1
    >> impl_tac >- fs[bir_labels_of_program_APPEND]
    >> strip_tac
    >> dxrule bir_get_current_statement_MEM1
    >> impl_tac >- fs[bir_labels_of_program_APPEND]
    >> strip_tac
    >> dxrule_then strip_assume_tac $ iffLR clstep_cases
    >> gvs[bir_labels_of_program_lock,bst_pc_tuple_def,bgcs_lock_zoo]
    >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 0`]
    >- (
      simple_refl_step
      >> fs[COND_RAND]
      >> dsimp[]
      >> spose_not_then assume_tac
      >> fs[labels_wf_def,bir_labels_of_program_APPEND,bir_labels_of_program_lock,DISJ_IMP_THM]
    )
    >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`,`xclfail_update_viewenv`]
    >- (
      disj1_tac
      >> fs[xclfail_update_env_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def]
      >> Cases_on `s.bst_environ`
      >> fs o single $ CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV) bir_env_update_SOME_eq
      >> gvs[spinlock_ref1_core_def,bir_pc_next_def,bst_pc_tuple_def,bir_read_reg_update,v_fail_def,bir_read_reg_zero_def,bir_read_reg_def,bir_eval_exp_BExp_Den_update_eq]
      >> dsimp[]
      >> spose_not_then assume_tac
      >> fs[labels_wf_def,bir_labels_of_program_APPEND,bir_labels_of_program_lock,DISJ_IMP_THM]
    )
    >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]
    >- (
      Cases_on `s.bst_environ`
      >> fs[fulfil_update_env_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_eval_exp_view_def,bir_eval_exp_BExp_Const]
      >> gvs[bst_pc_tuple_def,bir_pc_next_def,spinlock_ref1_core_def,remove_prom_def,bir_state_fulful_view_updates_def]
      >> fs o single $ CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV) bir_env_update_SOME_eq
      >> imp_res_tac mem_get_mem_read_imp
      >> gvs[bir_read_reg_def,bir_read_reg_nonzero_def,bir_eval_exp_BExp_Den_update_eq,v_succ_def]
      >> imp_res_tac mem_read_LENGTH
      >> imp_res_tac mem_read_mem_is_loc_imp
      >> fs[combinTheory.APPLY_UPDATE_THM,GSYM lock_addr_val_def,COND_RAND,bir_read_reg_zero_def,bir_read_reg_update]
      (* TODO show: perform same step *)
      >> Q.REFINE_EXISTS_TAC `(x:bir_state_t) with <| bst_pc := <|bpc_label := BL_Address $ Imm64 jump_after_lock; bpc_index := 0 |>; bst_prom := FILTER (λt'. t' <> t) s.bst_prom  |>`
      >> fs[spinlock_abstract2_def]
      >> qmatch_goalsub_abbrev_tac `clstep (BirProgram $ p1 ++ p2 ++ p3)`
      (* TODO continue to show that same step can be performed *)
      bir_get_current_statement_MEM1
      >> dsimp[clstep_cases]

bir_get_current_statement_spinlock_abstract_locking_BSGen
bir_get_current_statement_spinlock_abstract_locking_BSExt

    )

  )
  >~ [`bir_labels_of_program $ BirProgram $ unlock _ _`]

  >>
  >> gvs[clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt]


    >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 0`]
    >- (
      simple_refl_step
    )

  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    (* transition one abstrace step *)
    dxrule_then assume_tac $ iffLR spinlock_ref1_core_def
    >> imp_res_tac mem_get_mem_read_imp
    >> imp_res_tac mem_read_LENGTH
    >> imp_res_tac mem_read_mem_is_loc_imp
    >> gs[core_zoo,bst_pc_tuple_def,bir_eval_exp_view_def,bir_eval_exp_BExp_Const,combinTheory.APPLY_UPDATE_THM,GSYM lock_addr_val_def,COND_RAND,remove_prom_def,spinlock_ref1_core_def,bst_pc_tuple_def,bir_pc_next_def,bir_state_fulful_view_updates_def]
    >> qhdtm_assum `mem_is_loc` $ irule_at Any
    >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 8w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> dxrule_then assume_tac $ iffLR spinlock_ref1_core_def
    >> Cases_on `s.bst_environ`
    >> qpat_x_assum `(SOME _,_) = bir_eval_exp_view _ _ _` $ assume_tac o GSYM
    >> gvs[bir_eval_exp_view_def,bst_pc_tuple_def,bir_exec_stmt_cjmp_def]
    >> gs[sl_bir_eval_exp_Unary,bir_dest_bool_val_false,bir_dest_bool_val_true,COND_EXPAND]
    >> fs[bir_programTheory.bir_exec_stmt_jmp_def,
      bir_programTheory.bir_exec_stmt_jmp_to_label_def,
      bir_eval_label_exp_def,bir_block_pc_def,
      bir_labels_of_program_spinlock_concrete,spinlock_ref1_core_def,bst_pc_tuple_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 20w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> dxrule_then strip_assume_tac $ iffLR spinlock_ref1_core_def
    >> Cases_on `s.bst_environ`
    >> qpat_x_assum `(SOME _,_) = bir_eval_exp_view _ _ _` $ assume_tac o GSYM
    >> gvs[bir_eval_exp_view_def,bst_pc_tuple_def,bir_exec_stmt_cjmp_def]
    >> gs[sl_bir_eval_exp_Unary,bir_dest_bool_val_false,bir_dest_bool_val_true,COND_EXPAND]
    >> imp_res_tac bir_read_reg_imp
    >> gs[bir_read_reg_nonzero_def,bir_read_reg_zero_def,bir_read_reg_def]
    >> fs[bir_programTheory.bir_exec_stmt_jmp_def,
      bir_programTheory.bir_exec_stmt_jmp_to_label_def,
      bir_eval_label_exp_def,bir_block_pc_def,
      bir_labels_of_program_spinlock_concrete,spinlock_ref1_core_def,bst_pc_tuple_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
    >> qpat_x_assum `SOME _ = _` $ assume_tac o GSYM
    >> Cases_on `s.bst_environ`
    >> gvs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_eval_exp_view_def,bir_eval_exp_BExp_Const,bir_env_update_SOME_eq,env_update_cast64_def]
    >> qmatch_goalsub_abbrev_tac
      `bir_read_reg var (BEnv f(|var |-> SOME (BVal_Imm v)|)) v''`
    >> qsuff_tac `v = Imm64 v''` >> fs[bir_read_reg_update]
    >> unabbrev_all_tac
    >> EVAL_TAC
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
  )
  (* jump statements *)
  >~ [`bmc_exec_general_stmt`]
  >> gvs[bir_get_stmt_spinlock_cprog_BSGen,bmc_exec_general_stmt_def,
    bir_exec_stmtE_def,bir_programTheory.bir_exec_stmt_jmp_def,
    bir_programTheory.bir_exec_stmt_jmp_to_label_def,
    bir_eval_label_exp_def,bir_block_pc_def,
    bir_labels_of_program_spinlock_concrete,bst_pc_tuple_def]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    gvs[bir_exec_stmtB_noop_unchanged]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 1`]
  >- (
      dxrule_then strip_assume_tac $ iffLR spinlock_ref1_core_def
      >> gvs[bst_pc_tuple_def]
      >> qmatch_assum_rename_tac `bir_read_reg _ _ v`
      >> Cases_on `v = 0w`
      >> gvs[bir_read_reg_zero_def,bst_pc_tuple_def]
      >> fs[spinlock_ref1_core_def,bst_pc_tuple_def,bir_read_reg_def,bir_read_reg_zero_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step
  )
QED

Theorem cstep_preserves_spinlock_ref1_core:
  !cid c M c' M' a aM prom.
    cstep (λmem msg. T) spinlock_concrete cid c M prom c' M'
    /\ spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock (c,M) (a,aM)
    ==>
    (* reflexive case cannot happen when promises are discharged *)
    (spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock (c,M) (a,aM) /\ NULL prom)
    \/ ?a' aM'.
    cstep (λmem msg. T) spinlock_abstract cid a aM prom a' aM'
      /\ spinlock_ref1_core lock_entry unlock_entry jump_after_lock jump_after_unlock (c',M') (a',aM')
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases,cstep_cases]
  >- (
    drule_all_then strip_assume_tac clstep_preserves_spinlock_ref1_core
    >> fs[IMP_CONJ_THM,FORALL_AND_THM]
    >> disj2_tac
    >> dsimp[]
    >> disj1_tac
    >> qmatch_goalsub_rename_tac `clstep _ cid`
    >> rpt $ goal_assum drule
  )
  >> dsimp[]
  >> disj2_tac
  >> irule_at Any EQ_REFL
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[spinlock_ref1_core_promises_self]
QED

Theorem cstep_seq_preserves_spinlock_ref1_core:
  !cid c M c' M' a aM.
    cstep_seq spinlock_concrete cid (c, M) (c', M')
    /\ spinlock_ref1_core (c,M) (a,aM)
    ==>
    spinlock_ref1_core (c',M') (a,aM)
    \/ ?a' aM'.
      cstep_seq spinlock_abstract cid (a, aM) (a', aM')
      /\ spinlock_ref1_core (c',M') (a',aM')
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases]
  >> dsimp[PULL_EXISTS]
  >- (
    drule clstep_preserves_spinlock_ref1_core
    >> fs[]
    >> disch_then $ drule_then strip_assume_tac
    >> fs[IMP_CONJ_THM,FORALL_AND_THM]
    >> disj2_tac >> disj1_tac
    >> rpt $ goal_assum drule
  )
  >> dsimp[]
  >> ntac 2 disj2_tac
  >> drule_all_then strip_assume_tac cstep_preserves_spinlock_ref1_core
  >> fs[listTheory.NULL_EQ,IMP_CONJ_THM,FORALL_AND_THM]
  >> drule_all_then strip_assume_tac clstep_preserves_spinlock_ref1_core
  >> fs[listTheory.NULL_EQ,IMP_CONJ_THM,FORALL_AND_THM]
  >> qmatch_asmsub_rename_tac `clstep spinlock_abstract cid a' aM' [t] a''`
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> goal_assum drule
  >> fs[]
  >> rpt $ goal_assum drule
QED

Theorem cstep_seq_rtc_preserves_spinlock_ref1_core:
  !cid cM cM' aM.
    cstep_seq_rtc spinlock_concrete cid cM cM'
    /\ spinlock_ref1_core cM aM
    ==>
    ?aM'.
      cstep_seq_rtc spinlock_abstract cid aM aM'
      /\ spinlock_ref1_core cM' aM'
Proof
  gen_tac
  >> fs[GSYM AND_IMP_INTRO,cstep_seq_rtc_def,GSYM PULL_FORALL]
  >> ho_match_mp_tac RTC_INDUCT
  >> rw[]
  >- (irule_at Any RTC_REFL >> fs[])
  >> qmatch_asmsub_rename_tac `cstep_seq spinlock_concrete cid cM cM'`
  >> PairCases_on `cM` >> PairCases_on `cM'`
  >> qmatch_asmsub_rename_tac `spinlock_ref1_core (cM0,cM1) aM`
  >> PairCases_on `aM`
  >> drule_all_then strip_assume_tac cstep_seq_preserves_spinlock_ref1_core
  >> first_x_assum $ drule_then strip_assume_tac
  >> qhdtm_x_assum `spinlock_ref1_core` $ irule_at Any
  >> fs[]
  >> irule $ cj 2 RTC_RULES
  >> goal_assum drule_all
QED

Theorem is_certified_slc_sla:
  !cid c M a aM.
  is_certified spinlock_concrete cid c M
  /\ spinlock_ref1_core (c,M) (a,aM)
  ==> is_certified spinlock_abstract cid a aM
Proof
  rw[is_certified_def]
  >> drule_all_then strip_assume_tac cstep_seq_rtc_preserves_spinlock_ref1_core
  >> qmatch_asmsub_rename_tac `cstep_seq_rtc spinlock_abstract cid (a,aM) aM'`
  >> PairCases_on `aM'`
  >> goal_assum drule
  >> fs[spinlock_ref1_core_def]
QED

(*
Theorem cstep_is_certified_preserves_spinlock_ref1_core:
  !cid c M c' M' a aM prom.
    cstep (λmem msg. T) spinlock_concrete cid c M prom c' M'
    /\ is_certified spinlock_concrete cid c' M'
    /\ spinlock_ref1_core (c,M) (a,aM)
    ==>
    (* reflexive case cannot happen when promises are discharged *)
    (spinlock_ref1_core (c',M') (a,aM) /\ NULL prom)
    \/ ?a' aM'.
    cstep (λmem msg. T) spinlock_abstract cid a aM prom a' aM'
      /\ spinlock_ref1_core (c',M') (a',aM')
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases,cstep_cases,spinlock_ref1_core_promises_self]
  >- (
    drule_all_then strip_assume_tac clstep_preserves_spinlock_ref1_core
    >> fs[IMP_CONJ_THM,FORALL_AND_THM]
    >> disj2_tac
    >> dsimp[]
    >> disj1_tac
    >> qmatch_goalsub_rename_tac `clstep _ cid`
    >> rpt $ goal_assum drule
  )
  >> dsimp[]
  >> disj2_tac
  >> irule_at Any EQ_REFL
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[spinlock_ref1_core_promises_self]
QED
*)

Theorem parstep_preserves_spinlock_ref1:
  !cid cores M cores' M' acores aM as jump_after.
    parstep_tr (λmem msg. T) cid (cores,M) (cores',M')
    /\ jump_after = BL_Address $ Imm64 24w (* width of lock + 4w *)
    /\ run_progc cores spinlock_concrete
    /\ FEVERY_prog spinlock_concrete (λcid s.
      spinlock_ref1_core (core_state cid cores,M) (core_state cid acores,aM)
      /\ well_formed cid M s /\ slc_inv 4w jump_after 24w cid s M
    ) cores
    /\ run_progc acores spinlock_abstract
    /\ FLOOKUP acores cid = SOME $ Core cid spinlock_abstract as
    ==>
    ?acores' aM'.
     FEVERY_prog spinlock_concrete (λcid s.
      spinlock_ref1_core (core_state cid cores',M') (core_state cid acores',aM')
    ) cores'
    /\ (acores' = acores /\ aM = aM' /\ M = M' \/ parstep_tr (slc_prop cid) cid (acores,aM) (acores',aM'))
Proof
  rpt strip_tac
  >> dxrule_then assume_tac $ iffLR parstep_tr_def
  >> rev_dxrule_then assume_tac $ iffLR run_progc_def
  >> gvs[parstep_cases]
  >> dxrule_then (drule_then assume_tac) $ iffLR run_prog_def
  >> `spinlock_ref1_core (s,M) (as,aM)
    /\ well_formed cid M s /\ slc_inv 4w (BL_Address $ Imm64 24w) 24w cid s M` by (
    fs[FEVERY_prog_def,FLOOKUP_FEVERY]
    >> first_x_assum $ drule_then assume_tac
    >> gs[core_zoo]
  )
  >> gvs[cstep_cases]
  >~ [`clstep`]
  >- (
    drule_all_then strip_assume_tac clstep_preserves_spinlock_ref1_core
    >~ [`NULL prom`]
    >- (
      dsimp[] >> disj1_tac
      >> fs[FEVERY_prog_def,FLOOKUP_UPDATE,FLOOKUP_FEVERY]
      >> rw[] >> fs[core_zoo,FLOOKUP_UPDATE]
    )
    >> dsimp[parstep_cases,parstep_tr_def]
    >> disj2_tac
    >> dsimp[cstep_cases] >> disj1_tac
    >> drule_all_then assume_tac is_certified_slc_sla
    >> ntac 2 $ goal_assum $ drule_at Any
    >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
    >> fs[FEVERY_prog_def,FLOOKUP_UPDATE,FLOOKUP_FEVERY]
    >> rw[] >> fs[core_zoo,FLOOKUP_UPDATE]
  )
  >~ [`LENGTH M + 1`,`M ++ [msg]`]
  >> dsimp[parstep_cases,parstep_tr_def]
  >> dsimp[cstep_cases] >> disj2_tac
  (* TODO *)

  >> drule_then assume_tac is_certified_imp_is_certifiedR
  >> dxrule_then assume_tac is_certifiedR_locking_slc_prop
  (*
  >> drule_then assume_tac is_certified_locking_slc_prop
  *)

  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> gs[spinlock_ref1_core_promises_self,slc_inv_prom,well_formed_promise_self]
  >> drule_then (irule_at Any) is_certified_slc_sla
  >> qhdtm_x_assum `slc_prop` $ irule_at Any
  >> fs[spinlock_ref1_core_promises_self,FEVERY_prog_def,FLOOKUP_UPDATE,FLOOKUP_FEVERY]
  >> rw[] >> fs[core_zoo,FLOOKUP_UPDATE,spinlock_ref1_core_promises_other,spinlock_ref1_core_promises_self]
QED

Theorem parstep_preserves_sla_mem_correct_inv:
  !cid acores aM acores' aM'.
  parstep_tr (slc_prop cid) cid (acores,aM) (acores',aM')
  /\ sl_mem_correct_inv aM
  ==> sl_mem_correct_inv aM'
Proof
  rpt strip_tac
  >> gvs[cstep_cases,parstep_tr_def,parstep_cases,sl_mem_correct_inv_APPEND_eq]
  >> fs[slc_prop_def]
QED

(* correctness of memory due to trace inclusion and parstep_preserves_sla_mem_correct_inv *)

Theorem parstep_spinlock_concrete_mem_correct:
  !cid cores M cores' M' acores aM as.
    parstep_tr (λmem msg. T) cid (cores,M) (cores',M')
    /\ run_progc cores spinlock_concrete
    /\ FEVERY_prog spinlock_concrete (λcid s.
      spinlock_ref1_core (core_state cid cores,M) (core_state cid acores,aM)
      /\ well_formed cid M s /\ slc_inv 4w 24w cid s M
    ) cores
    /\ run_progc acores spinlock_abstract
    /\ FLOOKUP acores cid = SOME $ Core cid spinlock_abstract as
    /\ sl_mem_correct_inv M
  ==> sl_mem_correct_inv M'
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac parstep_preserves_spinlock_ref1
  >> `?s. FLOOKUP cores cid = SOME $ Core cid spinlock_concrete s
    /\ spinlock_ref1_core (s,M) (as,aM)` by (
    gvs[FEVERY_prog_def,parstep_tr_def,parstep_cases,run_progc_def,run_prog_def,FLOOKUP_FEVERY]
    >> rpt $ first_x_assum $ drule_then assume_tac
    >> gs[core_zoo]
  )
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[]
  >> drule_all parstep_preserves_sla_mem_correct_inv
  >> `?s as. FLOOKUP cores' cid = SOME $ Core cid spinlock_concrete s
    /\ FLOOKUP acores' cid = SOME $ Core cid spinlock_abstract as
    /\ spinlock_ref1_core (s,M') (as,aM')` by (
    gvs[FEVERY_prog_def,parstep_tr_def,parstep_cases,run_progc_def,run_prog_def,FLOOKUP_FEVERY]
    >> gs[core_zoo,FLOOKUP_UPDATE,COND_EXPAND,COND_RAND,COND_RATOR]
  )
  >> fs[FEVERY_prog_def,FLOOKUP_FEVERY]
  >> rpt $ first_x_assum $ drule_then assume_tac
  >> fs[]
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[]
QED

Definition mem_value_Imm64_def:
  mem_value_Imm64 M <=>
    !l t v. mem_read M l t = SOME v
    ==> ?v'. v = BVal_Imm $ Imm64 v'
End

Definition address_Imm64_def:
  address_Imm64 p pc <=>
    IS_SOME $ bir_get_current_statement p pc
    ==> ?label. pc.bpc_label = BL_Address (Imm64 label)
End

Definition maxlabel_def:
  maxlabel = dimword(:64)
End

(* operation on address at certain labels *)
Definition op_on_addr_def:
  op_on_addr loc p labels =
  !pc. (is_load p pc loc \/ is_store p pc loc)
    ==> MEM pc.bpc_label labels
End

(*
   for a core with a well-nested lock-unlock-primitives we assume on the
   surrounding code that no jumps go from the critical section to start of lock
   correctness:
   1. if jumping from CS to start of lock the value at current coherence is
   'locked' thus such jump is prohibited
   2. if jumping into CS without taking the lock (assuming CS well-formed) at
   unlock we would detect that the jump did not pass by the lock
 *)
Definition control_flow_def:
  control_flow M cid p coh pc lock_entry unlock_entry labels =
  !lbl index jump_target.
    bst_pc_tuple pc = (lbl, index)
    /\ is_jump p pc jump_target
    /\ ~MEM pc.bpc_label labels
    /\ MEM jump_target labels
    ==>
      index = 0
      /\ ((lbl = lock_entry
        /\ !m. mem_get M lock_addr_val (latest lock_addr_val coh M) = SOME m
        /\ m.cid = cid ==> m.val = BVal_Imm $ Imm64 0w) (* 0w = free *)
      \/ (lbl = unlock_entry
        /\ !m. mem_get M lock_addr_val (latest lock_addr_val coh M) = SOME m
        /\ m.cid = cid ==> m.val = BVal_Imm $ Imm64 1w)) (* 1w = locked *)
End

(* relativise theorems *)
Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Load =
  EVAL ``bir_get_current_statement (BirProgram $ lock addr lock_entry) pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_current_statement_list_disj1:
  !pc A B blocks address labels1 labels2.
  list_disj
    (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ op_on_addr address (BirProgram (A ++ B)) (labels1 ++ labels2)
  /\ list_subset labels1 (bir_labels_of_program $ BirProgram A)
  /\ list_subset labels2 (bir_labels_of_program $ BirProgram B)
  /\ (is_store (BirProgram (A ++ B)) pc address \/ is_load (BirProgram (A ++ B)) pc address)
  /\ MEM pc.bpc_label labels1
  ==>
    ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ bir_get_current_statement (BirProgram (A ++ B)) pc = bir_get_current_statement (BirProgram A) pc
Proof
  rpt strip_tac
  >> fs[op_on_addr_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,bst_pc_tuple_def,optionTheory.IS_SOME_EXISTS]
  >> first_x_assum drule
  >> PRED_ASSUM is_forall kall_tac
  >> `?stmt. bir_get_current_statement (BirProgram $ A ++ B) pc = SOME stmt` by
    gs[is_store_def,is_load_def]
  >> fs[list_subset_def]
  >> first_x_assum drule
  >> drule_then assume_tac bir_get_current_statement_MEM1
  >> drule_then assume_tac bir_get_current_statement_MEM2
  >> gvs[list_disj_def]
  >> res_tac
  >> first_x_assum $ drule_at Concl
  >> fs[]
QED

Theorem bir_get_current_statement_list_disj2:
  !pc A B blocks address labels1 labels2.
  list_disj
    (bir_labels_of_program $ BirProgram A)
    (bir_labels_of_program $ BirProgram B)
  /\ op_on_addr address (BirProgram (A ++ B)) (labels1 ++ labels2)
  /\ list_subset labels1 (bir_labels_of_program $ BirProgram A)
  /\ list_subset labels2 (bir_labels_of_program $ BirProgram B)
  /\ (is_store (BirProgram (A ++ B)) pc address \/ is_load (BirProgram (A ++ B)) pc address)
  /\ MEM pc.bpc_label labels2
  ==>
    ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ bir_get_current_statement (BirProgram (A ++ B)) pc = bir_get_current_statement (BirProgram B) pc
Proof
  rpt strip_tac
  >> fs[op_on_addr_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,bst_pc_tuple_def,optionTheory.IS_SOME_EXISTS]
  >> first_x_assum drule
  >> PRED_ASSUM is_forall kall_tac
  >> `?stmt. bir_get_current_statement (BirProgram $ A ++ B) pc = SOME stmt` by
    gs[is_store_def,is_load_def]
  >> fs[list_subset_def]
  >> first_x_assum drule
  >> drule_then assume_tac bir_get_current_statement_MEM1
  >> drule_then assume_tac bir_get_current_statement_MEM2
  >> gvs[list_disj_def]
QED

Theorem bir_get_current_store_list_disj1 =
  cj 1 $ REWRITE_RULE[DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR]
  bir_get_current_statement_list_disj1

Theorem bir_get_current_load_list_disj1 =
  cj 2 $ REWRITE_RULE[DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR]
  bir_get_current_statement_list_disj1

Theorem bir_get_current_store_list_disj2 =
  cj 1 $ REWRITE_RULE[DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR]
  bir_get_current_statement_list_disj2

Theorem bir_get_current_load_list_disj2 =
  cj 2 $ REWRITE_RULE[DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR]
  bir_get_current_statement_list_disj2

Theorem bir_get_current_statement_list_disj3:
  !pc p A B blocks address.
  p = BirProgram (A ++ blocks ++ B)
  /\ list_disj
      (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ list_disj
      (bir_labels_of_program $ BirProgram B)
      (bir_labels_of_program $ BirProgram blocks)
  /\ list_disj
      (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram blocks)
  /\ op_on_addr address p (
    (bir_labels_of_program $ BirProgram A)
    ++ (bir_labels_of_program $ BirProgram B)
  )
  /\ (is_store p pc address \/ is_load p pc address)
  ==>
    ((MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ bir_get_current_statement p pc = bir_get_current_statement (BirProgram A) pc)
  \/
    ((MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ bir_get_current_statement p pc = bir_get_current_statement (BirProgram B) pc)
Proof
  rpt strip_tac
  >> fs[op_on_addr_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,bst_pc_tuple_def,optionTheory.IS_SOME_EXISTS]
  >> first_x_assum $ drule_then assume_tac
  >> PRED_ASSUM is_forall kall_tac
  >> fs[]
  >> rev_drule $ iffLR list_disj_def
  >> disch_then (fn thm => drule thm ORELSE drule_at Concl thm)
  >> strip_tac
  >> simp[]
  >> REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
  >- (
    irule bir_get_current_statement_APPEND1
    >> fs[list_disj_append2,list_disj_append1,bir_labels_of_program_APPEND]
  )
  >- (
    fs[]
    >> irule bir_get_current_statement_APPEND2
    >> fs[list_disj_append2,list_disj_append1,bir_labels_of_program_APPEND,list_disj_sym_imp]
  )
  >- (
    irule bir_get_current_statement_APPEND1
    >> fs[list_disj_append2,list_disj_append1,bir_labels_of_program_APPEND]
  )
  >- (
    fs[]
    >> irule bir_get_current_statement_APPEND2
    >> fs[list_disj_append2,list_disj_append1,bir_labels_of_program_APPEND,list_disj_sym_imp]
  )
QED

Theorem bir_get_current_statement_list_disj5:
  !pc p A B blocks1 blocks2 blocks3 address.
  p = BirProgram (blocks1 ++ A ++ blocks2 ++ B ++ blocks3)
  /\ list_disj
      (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram B)
  /\ list_disj
      (bir_labels_of_program $ BirProgram B)
      (bir_labels_of_program $ BirProgram $ blocks1 ++ blocks2 ++ blocks3)
  /\ list_disj
      (bir_labels_of_program $ BirProgram A)
      (bir_labels_of_program $ BirProgram $ blocks1 ++ blocks2 ++ blocks3)
  /\ list_disj
      (bir_labels_of_program $ BirProgram blocks1)
      (bir_labels_of_program $ BirProgram $ blocks2 ++ blocks3)
  /\ list_disj
      (bir_labels_of_program $ BirProgram blocks2)
      (bir_labels_of_program $ BirProgram blocks3)
  /\ op_on_addr address p (
    (bir_labels_of_program $ BirProgram A)
    ++ (bir_labels_of_program $ BirProgram B)
  )
  /\ (is_store p pc address \/ is_load p pc address)
  ==>
    ((MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ bir_get_current_statement p pc = bir_get_current_statement (BirProgram A) pc)
  \/
    ((MEM pc.bpc_label $ bir_labels_of_program $ BirProgram B)
    /\ ~(MEM pc.bpc_label $ bir_labels_of_program $ BirProgram A)
    /\ bir_get_current_statement p pc = bir_get_current_statement (BirProgram B) pc)
Proof
  rpt strip_tac
  >> fs[op_on_addr_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,bst_pc_tuple_def,optionTheory.IS_SOME_EXISTS]
  >> first_x_assum $ drule_then assume_tac
  >> PRED_ASSUM is_forall kall_tac
  >> fs[]
  >> rev_drule $ iffLR list_disj_def
  >> disch_then (fn thm => drule thm ORELSE drule_at Concl thm)
  >> strip_tac
  >> simp[]
  >~ [`bir_get_current_statement (BirProgram $ blocks1 ++ A ++ blocks2 ++ B ++ blocks3) pc =
        bir_get_current_statement (BirProgram A) pc`]
  >- (
    qspecl_then [`blocks1 ++ A`,`blocks2 ++ B ++ blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND1
    >> qspecl_then [`blocks1`,`A`,`pc`] mp_tac bir_get_current_statement_APPEND2
    >> fs[list_disj_sym_imp,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND]
  )
  >~ [`bir_get_current_statement (BirProgram $ blocks1 ++ A ++ blocks2 ++ B ++ blocks3) pc =
        bir_get_current_statement (BirProgram B) pc`]
  >- (
    qspecl_then [`blocks1 ++ A ++ blocks2`,`B ++ blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND2
    >> qspecl_then [`B`,`blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND1
    >> fs[list_disj_sym_imp,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND]
  )
  >~ [`bir_get_current_statement (BirProgram $ blocks1 ++ A ++ blocks2 ++ B ++ blocks3) pc =
        bir_get_current_statement (BirProgram A) pc`]
  >- (
    qspecl_then [`blocks1 ++ A`,`blocks2 ++ B ++ blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND1
    >> qspecl_then [`blocks1`,`A`,`pc`] mp_tac bir_get_current_statement_APPEND2
    >> fs[list_disj_sym_imp,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND]
  )
  >~ [`bir_get_current_statement (BirProgram $ blocks1 ++ A ++ blocks2 ++ B ++ blocks3) pc =
        bir_get_current_statement (BirProgram B) pc`]
  >- (
    qspecl_then [`blocks1 ++ A ++ blocks2`,`B ++ blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND2
    >> qspecl_then [`B`,`blocks3`,`pc`] mp_tac bir_get_current_statement_APPEND1
    >> fs[list_disj_sym_imp,list_disj_append1,list_disj_append2,bir_labels_of_program_APPEND]
  )
QED

(*
  /\ cstep P p cid s M prom s' M'

well_formed_def
well_formed_fwdb_def

Theorem clstep_mutex_addr_unchanged:
  !p b blocks1 A blocks2 B blocks3.
  p = BirProgram $ blocks1 ++ A ++ blocks2 ++ B ++ blocks3
  /\ well_formed cid M s
  /\ clstep spinlock_concrete cid s M prom s'
  /\ op_on_addr address p
    ((bir_labels_of_program $ BirProgram A) ++ (bir_labels_of_program $ BirProgram B))
  /\ control_flow M cid p (s.bst_coh address) pc (bir_pc_first $ BirProgram A) (bir_pc_first $ BirProgram B)
    ((bir_labels_of_program $ BirProgram A) ++ (bir_labels_of_program $ BirProgram B))
  /\ bst_pc_tuple s.bst_pc = (label,index)
  /\
  ==>
Proof

QED
*)


(*
calculate size of lock and unlock code:
EVAL ``MAP (λx. case x of BL_Address $ Imm64 x => x) $ bir_labels_of_program $ BirProgram $ lock lock_addr 0w``
EVAL ``MAP (λx. case x of BL_Address $ Imm64 x => x) $ bir_labels_of_program $ BirProgram $ unlock lock_addr 0w``
EVAL `` 0w <=+ 127w:word8``
EVAL `` 0w <=+ 128w:word64``
*)

Theorem list_disj_slc:
  !lock_addr jump_after lock_entry unlock_entry lock_entry_n unlock_entry_n.
  lock_entry = n2w lock_entry_n /\ unlock_entry = n2w unlock_entry_n
  /\ unlock_entry_n + 8 < maxlabel       (*  8w = max difference of unlock labels *)
  /\ lock_entry_n + 16 < unlock_entry_n  (* 16w = max difference of lock labels *)
  ==> list_disj (bir_labels_of_program $ BirProgram $ unlock lock_addr unlock_entry : (bmc_stmt_basic_t, 'a) bir_generic_block_t list)
        (bir_labels_of_program $ BirProgram $ lock lock_addr lock_entry : (bmc_stmt_basic_t, 'a) bir_generic_block_t list)
Proof
  rw[lock_def,bir_labels_of_program_unlock,bir_labels_of_program_lock]
  >> fs[list_disj_def,DISJ_IMP_THM,FORALL_AND_THM,maxlabel_def]
  >> rpt conj_tac
  >> fs[word_add_n2w]
QED

(* here be dragons *)

(* the coherence does not change through certain labels *)
Definition mem_loc_coh_value_inv_def:
  mem_loc_coh_value_inv cid M loc pc labels coh v <=>
    MEM pc.bpc_label labels ==>
      ?m. mem_get M loc (latestP (λmsg. msg.loc = loc /\ msg.cid = cid) coh M) = SOME m
      /\ m.cid = cid /\ m.val = v
End

(* assumes incremental labels *)
Definition bir_next_block_pc_def:
  bir_next_block_pc empty_label block =
    bir_block_pc $
      if NULL block then BL_Address $ Imm64 empty_label
      else bir_label_of_block $ LAST block
End

(* operation on address at certain labels *)
Definition op_on_addr2_def:
  op_on_addr2 env loc_val p labels =
  !pc loc. (is_load p pc loc \/ is_store p pc loc)
    /\ bir_eval_exp loc env = SOME loc_val
    ==> MEM pc.bpc_label labels
End

(* operation on address at certain labels *)
Definition op_on_addr_ext_def:
  op_on_addr_ext loc_val p pc labels =
    !R s x s'. bir_get_current_statement p pc = SOME $ BSExt R
    /\ R (s,x) s'
    /\ MEM pc.bpc_label labels
    ==> s.bst_coh loc_val = s'.bst_coh loc_val
End

Theorem cstep_coherence_unchanged:
  !P p cid s M prom s' M' block0 block1 block2 b1l b0l A B.
  A = lock lock_addr b0l
  /\ B = unlock lock_addr b1l
  /\ p = BirProgram $ block0 ++ (lock_wrap lock_addr b0l b1l block1) ++ block2
  /\ (bir_next_block_pc 0w block0).bpc_label = BL_Address $ Imm64 b0l
  /\ (bir_next_block_pc (b0l + 16w + 4w) block1).bpc_label = BL_Address $ Imm64 b1l
  /\ cstep P p cid s M prom s' M'
  /\ list_disj
      (bir_labels_of_program $ BirProgram $ block0 ++ block1 ++ block2)
      (bir_labels_of_program $ BirProgram $ A ++ B)
  /\ op_on_addr_ext lock_addr_val p
      s.bst_pc
      (bir_labels_of_program $ BirProgram $ block0 ++ block1 ++ block2)
  /\ op_on_addr2 s.bst_environ lock_addr_val p $ (bir_labels_of_program $ BirProgram A)
    ++ (bir_labels_of_program $ BirProgram B)
  /\ control_flow M cid p (s.bst_coh lock_addr_val) s.bst_pc
    (bir_label_of_block $ HD A)
    (bir_label_of_block $ HD B)
      $ (bir_labels_of_program $ BirProgram A)
          ++ (bir_labels_of_program $ BirProgram B)
  /\ well_formed cid M s
  /\ MEM s.bst_pc.bpc_label (bir_labels_of_program $ BirProgram $
    block0 ++ block1 ++ block2)
  ==> s.bst_coh lock_addr_val = s'.bst_coh lock_addr_val
Proof
  rpt strip_tac
  >> fs[bir_labels_of_program_unlock,bir_labels_of_program_lock]
  >> fs[lock_def,unlock_def,bir_label_of_block_def]
  >> fs[bir_pc_first_def,bir_block_pc_def,cstep_cases,clstep_cases]
  >> fs[bir_state_fulful_view_updates_def,bir_state_read_view_updates_def,combinTheory.APPLY_UPDATE_THM,fence_updates_def,bir_exec_stmt_cjmp_mc_invar,bmc_exec_general_stmt_mc_invar]
  >~ [`BMCStmt_Load var a_e opt_cast xcl acq rel`]
  >- (
    qmatch_goalsub_abbrev_tac `COND c a`
    >> rw[]
    >> gs[op_on_addr2_def,op_on_addr_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,bst_pc_tuple_def,optionTheory.IS_SOME_EXISTS,is_load_def,PULL_EXISTS,bir_eval_exp_view_def]
    >> first_x_assum $ qspec_then `s.bst_pc` mp_tac
    >> PRED_ASSUM is_forall kall_tac
    >> gvs[]
    >> csimp[bir_labels_of_program_def,bir_label_of_block_def]
    >> fs[list_disj_def]
    >> first_x_assum $ drule_then assume_tac
    >> fs[bir_labels_of_program_def,bir_label_of_block_def]
  )
  >~ [`bmc_exec_general_stmt`]
  >- drule_then (fs o single) bmc_exec_general_stmt_mc_invar
  >~ [`BSExt R`]
  >- (
    gs[op_on_addr_ext_def]
  )

QED

(* from $CAKEMLDIR/misc/miscScript.sml *)
Definition steps_rel_def:
  steps_rel R x [] = T
  /\ (steps_rel R x ((j,y)::tr) <=> R x j y /\ steps_rel R y tr)
End

(* definition of a trace *)

Definition trace_from_l_def:
  trace_from_l cores_from P tr =
    steps_rel (λ(cores,M) cid (cores',M'). parstep P cid cores M cores' M') cores_from tr
End

Theorem trace_from_wf:
  !tr P cores M.
  trace_from_l (cores,M) P tr /\ well_formed_cores cores M /\ well_formed_ext_cores cores
  ==> EVERY (λ(lbl,(cores,M)). well_formed_cores cores M /\ well_formed_ext_cores cores) tr
Proof
  Induct >> fs[trace_from_l_def,pairTheory.FORALL_PROD]
  >> rpt gen_tac >> strip_tac
  >> fs[steps_rel_def]
  >> drule_all_then assume_tac parstep_preserves_wf
  >> drule_all_then assume_tac parstep_preserves_wf_ext_cores
  >> first_x_assum $ drule_then $ irule_at Any
  >> asm_rewrite_tac[]
QED

Definition trace_from_def:
  trace_from x P tr <=>
    ?tr'. trace_from_l x P tr' /\ tr = MAP SND tr'
End

(* spinlock trace *)

Definition spl_trace_def:
  spl_trace params P tr =
    ?cores blocks jump_after unlock_entry. init cores
    /\ params = (blocks,jump_after,unlock_entry)
    /\ (!cid s p. FLOOKUP cores cid = SOME $ Core cid p s ==> p = spinlock_concrete2 blocks jump_after unlock_entry)
    /\ trace_from_l (cores,[]) P tr
End

(* There is The point in a trace (not certifying), when a promise is made *)
(* subsumed by more specific version  parstep_promise_step_LRC *)
Theorem parstep_promise_step_RTC:
  !t cores M cores' M' P.
  RTC (λ(cores,M) (cores',M'). ?cid. parstep P cid cores M cores' M') (cores,M) (cores',M')
  /\ LENGTH M < t /\ t <= LENGTH M' /\ 0 < t
  ==> ?cores'' M'' cores''' M''' cid.
    RTC (λ(cores,M) (cores',M'). ?cid. parstep P cid cores M cores' M') (cores,M) (cores'',M'')
    /\ RTC (λ(cores,M) (cores',M'). ?cid. parstep P cid cores M cores' M') (cores''',M''') (cores',M')
    /\ parstep P cid cores'' M'' cores''' M'''
    /\ (EL (PRE t) M''').cid = cid /\ SUC $ LENGTH M'' = t /\ LENGTH M''' = t
Proof
  rpt strip_tac
  >> dxrule_then strip_assume_tac arithmeticTheory.RTC_NRC
  >> qmatch_asmsub_rename_tac `NRC _ n (cores,M) (cores',M')`
  >> qmatch_asmsub_abbrev_tac `NRC R n (cores,M) (cores',M')`
  >> Cases_on `0 < n` >> gvs[]
  >> Cases_on `!m. m <= n ==> !cores'' M''.
    NRC R m (cores,M) (cores'',M'') /\ NRC R (n - m) (cores'',M'') (cores',M')
    ==> LENGTH M'' < t`
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
  >> Cases_on `m` >> gs[DISJ_EQ_IMP,arithmeticTheory.NRC_SUC_RECURSE_LEFT,pairTheory.LAMBDA_PROD]
  >> fs[pairTheory.ELIM_UNCURRY,arithmeticTheory.NOT_LESS]
  >> qmatch_asmsub_rename_tac `parstep P cid (FST x)`
  >> PairCases_on `x` >> fs[]
  >> `LENGTH x1 < t` by (
    first_x_assum irule
    >> goal_assum $ drule_at Any
    >> `n - n' = SUC $ n - SUC n'` by decide_tac
    >> pop_assum $ ONCE_REWRITE_TAC o single
    >> once_rewrite_tac[arithmeticTheory.NRC]
    >> fs[PULL_EXISTS]
    >> goal_assum $ drule_at Any
    >> fs[]
    >> goal_assum drule
  )
  >> drule_then strip_assume_tac $ iffLR parstep_cases
  >> imp_res_tac cstep_mem_mono
  >> gvs[cstep_cases,GSYM arithmeticTheory.ADD1]
  >> qmatch_asmsub_rename_tac `t <= SUC $ LENGTH x1`
  >> `t = SUC $ LENGTH x1` by fs[arithmeticTheory.LESS_OR_EQ]
  >> drule_then (irule_at Any) arithmeticTheory.NRC_RTC
  >> drule_then (irule_at Any) arithmeticTheory.NRC_RTC
  >> fs[rich_listTheory.EL_APPEND2]
QED

(* existence of index in trace where a promise is discharged *)

(* TODO generalise reasoning to arbitrary traces and use in this theorem and in is_certified_promise_disch *)
(* TODO move next to is_certified_promise_disch *)
(* There is The point in a trace (not certifying), when a promise is made *)
Theorem parstep_promise_step_LRC:
  !cores M t R ls cores' M' P.
  Abbrev (R = (λcM cM'. ?cid. parstep_tr P cid cM cM'))
  /\ LRC R ls (cores,M) (cores',M')
  /\ LENGTH M < t /\ t <= LENGTH M'
  ==> ?k last. (* t <= k : consequence of #memory updates <= #transitions  *)
    SUC k <= LENGTH ls
    /\ last = (if SUC k = LENGTH ls then (cores',M') else EL (SUC k) ls)
    /\ LRC R (TAKE k ls) (cores,M) (EL k ls)
    /\ LRC R (DROP (SUC k) ls) last (cores',M')
    /\ SUC $ LENGTH $ SND $ EL k ls = t
    /\ LENGTH $ SND $ last = t
    /\ ?cid. parstep_tr P cid (EL k ls) last
    /\ (EL (PRE t) $ SND $ last).cid = cid
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `LRC _ ls (cores,M) (cores',M')`
  >> qabbrev_tac `n = LENGTH ls`
  >> qmatch_asmsub_abbrev_tac `LRC R ls (cores,M) (cores',M')`
  >> Cases_on `0 < n` >> gvs[listTheory.LRC_def]
  >> Cases_on `!m. m <= n ==> !cM''. (cM'' = if m = n then (cores',M') else EL m ls)
    /\ LRC R (TAKE m ls) (cores,M) cM'' /\ LRC R (DROP m ls) cM'' (cores',M')
    ==> LENGTH $ SND cM'' < t`
  >- (
    `n <= n` by fs[]
    >> first_x_assum drule
    >> unabbrev_all_tac
    >> fs[TAKE_LENGTH_ID,DROP_LENGTH_NIL,LRC_def]
  )
  >> PRED_ASSUM is_neg $ mp_tac o SIMP_RULE std_ss [NOT_FORALL_THM]
  >> qho_match_abbrev_tac `(?m. P' m) ==> _`
  >> disch_then assume_tac
  >> dxrule_then strip_assume_tac arithmeticTheory.WOP
  >> qmatch_asmsub_rename_tac `P' m`
  >> `0 < m /\ m <= n` by (
    unabbrev_all_tac
    >> gvs[GSYM NULL_EQ,LENGTH_NOT_NULL]
    >> imp_res_tac LRC_HD
    >> fs[] >> Cases_on `m`
    >> gs[pairTheory.ELIM_UNCURRY,GSYM NULL_EQ]
    >> pop_assum $ fs o single o GSYM
  )
  >> `PRE m < m` by decide_tac
  >> unabbrev_all_tac
  >> Cases_on `m` >> gs[DISJ_EQ_IMP,arithmeticTheory.NRC_SUC_RECURSE_LEFT,pairTheory.LAMBDA_PROD]
  >> fs[pairTheory.ELIM_UNCURRY,arithmeticTheory.NOT_LESS]
  >> qmatch_asmsub_rename_tac `SUC n <= LENGTH ls`
  >> `LENGTH $ SND $ EL n ls < t` by (
    first_x_assum irule
    >> rev_drule_at (Pat `LRC`) $ iffLR LRC_TAKE_DROP
    >> fs[]
  )
  >> PRED_ASSUM is_forall kall_tac
  >> gs[LRC_TAKE_SUC]
  >> rpt $ goal_assum $ drule_at $ Pat `LRC`
  >> unabbrev_all_tac
  >> fs[parstep_tr_def]
  >> REWRITE_TAC[CONJ_ASSOC]
  >> qmatch_goalsub_abbrev_tac `A /\ parstep _ cid' _ _ _ _`
  >> qsuff_tac `cid' = cid /\ A` >- fs[]
  >> unabbrev_all_tac
  >> qmatch_asmsub_abbrev_tac `parstep _ _ _ _ _ $ SND last`
  >> drule_then strip_assume_tac $ iffLR parstep_cases
  >> imp_res_tac cstep_mem_mono
  >> gvs[cstep_cases,GSYM ADD1]
  >> qmatch_asmsub_rename_tac `t <= SUC $ LENGTH $ SND $ EL n ls`
  >> `t = SUC $ LENGTH $ SND $ EL n ls` by fs[arithmeticTheory.LESS_OR_EQ]
  >> fs[rich_listTheory.EL_APPEND2]
QED

Definition trace_prom_index_def:
  trace_prom_index P cores M t ls cores' M' k =
  ?R last. (R = (λcM cM'. ?cid. parstep_tr P cid cM cM'))
    /\ SUC k <= LENGTH ls
    /\ last = (if SUC k = LENGTH ls then (cores',M') else EL (SUC k) ls)
    /\ LRC R (TAKE k ls) (cores,M) (EL k ls)
    /\ LRC R (DROP (SUC k) ls) last (cores',M')
    /\ SUC $ LENGTH $ SND $ EL k ls = t
    /\ LENGTH $ SND $ last = t
    /\ ?cid. parstep_tr P cid (EL k ls) last
    /\ (EL (PRE t) $ SND $ last).cid = cid
End

Theorem trace_prom_index_exists:
  !cores M t R ls cores' M' P.
  Abbrev (R = (λcM cM'. ?cid. parstep_tr P cid cM cM'))
  /\ LRC R ls (cores,M) (cores',M')
  /\ LENGTH M < t /\ t <= LENGTH M'
  ==> ?k. trace_prom_index P cores M t ls cores' M' k
Proof
  rw[trace_prom_index_def]
  >> drule_all_then strip_assume_tac parstep_promise_step_LRC
  >> rpt $ goal_assum $ drule_at Any
  >> gs[]
QED

Theorem trace_prom_index_unique:
  !k k' cores M t R ls cores' M' P.
  Abbrev (R = (λcM cM'. ?cid. parstep_tr P cid cM cM'))
  /\ LRC R ls (cores,M) (cores',M')
  /\ LENGTH M < t /\ t <= LENGTH M'
  /\ trace_prom_index P cores M t ls cores' M' k
  /\ trace_prom_index P cores M t ls cores' M' k'
  ==> k = k'
Proof
  ntac 2 gen_tac
  >> spose_not_then mp_tac
  >> wlog_tac `k < k'` []
  >- (
    strip_tac
    >> dxrule_then assume_tac LESS_CASES_IMP
    >> gs[AND_IMP_INTRO,PULL_FORALL,DISJ_EQ_IMP]
    >> first_x_assum drule
    >> ntac 2 $ disch_then $ drule_at Any
    >> strip_tac
    >> gs[]
  )
  >> strip_tac
  >> fs[trace_prom_index_def]
  >> cheat (* the promise t can only be fulfiled once *)
QED

(* uniqueness of index in trace where a promise is discharged *)

(* for a promise in a trace  trace_from cores_from P tr
 * returns the index at which the promise is discharged
 *)
Definition prom_disch_index_def:
  prom_disch_index t (cores,M) P tr =
    if ~NULL tr /\ 0 < t /\ t <= LENGTH $ SND $ LAST tr
    then SOME @k. trace_prom_index P cores M t tr (FST $ LAST tr) (SND $ LAST tr) k
    else NONE
End

Theorem prom_disch_index_distinct_time:
  Abbrev (R = (λcM cM'. ?cid. parstep_tr P cid cM cM'))
  /\ LRC R tr (cores,M) (cores',M')
  /\ prom_disch_index t (cores,M) P tr = SOME k
  /\ prom_disch_index t' (cores,M) P tr = SOME k'
  ==> (t <> t' <=> k <> k')
Proof
  cheat (* trace_prom_index_unique *)
QED

(* mutual exclusion
 * for a trace with two stores t and t' to protected locations by different
 * cores with t < t' it holds that at state of the promise of t it is impossible
 * for a store to M(t').loc of any value to be (promised and) certified.
 *)

Definition mut_ex_def:
  mut_ex x P procloc <=>
    !tr t t' k k' loc loc' cid cid'.
    trace_from x P tr /\ 0 < t /\ t < t' /\ t' < LENGTH tr
    /\ prom_disch_index t x P tr = SOME k
    /\ prom_disch_index t' x P tr = SOME k'
    /\ loc = (EL t $ SND $ LAST tr).loc /\ loc' = (EL t' $ SND $ LAST tr).loc
    /\ cid = (EL t $ SND $ LAST tr).cid /\ cid' = (EL t' $ SND $ LAST tr).cid
    /\ MEM loc procloc /\ MEM loc' procloc
    /\ cid <> cid'
    ==> k < k'
End

Theorem mut_ex_spinlock_concrete2:
  init cores
  /\ labels_wf blocks (BL_Address (Imm64 jump_after_lock)) unlock_entry
  /\ prog_addr64 blocks
  /\ jump_constraints c.bst_pc c'.bst_pc
    [unlock lock_addr unlock_entry; lock lock_addr 0w (BL_Address (Imm64 jump_after_lock))]
  /\ (!cid p s. FLOOKUP cores cid = SOME $ Core cid p s
    ==> p = spinlock_concrete2 blocks jump_after unlock_entry)
  ==> mut_ex (cores,[]) (λx y. T) procloc
Proof
  rw[mut_ex_def]
  >> cheat
QED

(*

(* also requires coherence loc is unchanged *)
Theorem cstep_mem_loc_coh_value_inv:
  !P p cid s M prom s' M'.
  p = BirProgram $ block0 ++ A ++ block1 ++ B ++ block2
  /\ cstep P p cid s M prom s' M'
  /\ mem_loc_coh_value_inv M loc s.bst_pc
    (bir_labels_of_program block1 ++ bir_labels_of_program block2) (s.bst_coh loc) v
  /\ well_formed cid M s
  ==> mem_loc_coh_value_inv M' loc s'.bst_pc
    (bir_labels_of_program block1) (s'.bst_coh loc) v
Proof

QED

(* correctness of memory with the additional constraints on
 * control flow and on operations on protected address *)
(*
  - make refinement relation spinlock_ref1_core relative to
    concrete and abstract - lock_entry and unlock_entry addresses
  - add possibility to have additional blocks (before, between and after CS)
    - to abstract program
    - to concrete program
  - add to refinement the synchronisation of other unrelated blocks
  - proof for arbitary program block concatenation
    if  op_on_addr  holds for the labels in a block then the location remains
    unchanged in all other blocks
    o define bir_pc_last -- only necessary (?) due to jump statements in BSGen generic statements
    * define invariant: program mem_loc_coh_value
    - prove above invariant
    - prove property on steps, namely coherence of protected location does not
      change in certain sections, assuming op_on_addr and control_flow
      p = block1 ++ A ++ block2 ++ B ++ block3
        p = BirProgram A ++ block ++ B
        /\ op_on_addr addr p
          ((bir_labels_of_program $ BirProgram A) ++ (bir_labels_of_program $ BirProgram B))
        /\

->     - rephrase op_on_addr to contain evaluated address!!!


*)

Theorem parstep_spinlock_abstract_prog_mem_correct:
  !cid cores M cores' M' acores aM as.
    parstep_tr (λmem msg. T) cid (cores,M) (cores',M')
    /\ run_progc cores ( spinlock_concrete
    /\ FEVERY_prog spinlock_concrete (λcid s.
      spinlock_ref1_core (core_state cid cores,M) (core_state cid acores,aM)
      /\ well_formed cid M s /\ slc_inv 4w 24w cid s M
    ) cores
    /\ run_progc acores spinlock_abstract
    /\ FLOOKUP acores cid = SOME $ Core cid spinlock_abstract as
    /\ sl_mem_correct_inv M
  ==> sl_mem_correct_inv M'
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac parstep_preserves_spinlock_ref1
  >> `?s. FLOOKUP cores cid = SOME $ Core cid spinlock_concrete s
    /\ spinlock_ref1_core (s,M) (as,aM)` by (
    gvs[FEVERY_prog_def,parstep_tr_def,parstep_cases,run_progc_def,run_prog_def,FLOOKUP_FEVERY]
    >> rpt $ first_x_assum $ drule_then assume_tac
    >> gs[core_zoo]
  )
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[]
  >> drule_all parstep_preserves_sla_mem_correct_inv
  >> `?s as. FLOOKUP cores' cid = SOME $ Core cid spinlock_concrete s
    /\ FLOOKUP acores' cid = SOME $ Core cid spinlock_abstract as
    /\ spinlock_ref1_core (s,M') (as,aM')` by (
    gvs[FEVERY_prog_def,parstep_tr_def,parstep_cases,run_progc_def,run_prog_def,FLOOKUP_FEVERY]
    >> gs[core_zoo,FLOOKUP_UPDATE,COND_EXPAND,COND_RAND,COND_RATOR]
  )
  >> fs[FEVERY_prog_def,FLOOKUP_FEVERY]
  >> rpt $ first_x_assum $ drule_then assume_tac
  >> fs[]
  >> imp_res_tac $ cj 1 $ iffLR spinlock_ref1_core_def
  >> fs[]
QED



Definition in_lock_concrete_def:
  in_lock_concrete pc =
  !lbl index.
    bst_pc_tuple pc = (BL_Address $ Imm64 lbl, index)
    ==> 0w <= lbl /\ lbl <= 20w
      /\ (lbl = 0w ==> index = 1)
End

Definition in_unlock_concrete_def:
  in_unlock_concrete pc =
  !lbl index.
    bst_pc_tuple pc = (BL_Address $ Imm64 lbl, index)
    ==> 24w <= lbl /\ lbl <= 36w
      /\ (lbl = 24w ==> index = 1)
End
*)

val _ = export_theory();
