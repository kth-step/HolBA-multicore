(*
  Spinlock abstract and concrete implementation in multicore BIR syntax
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory llistTheory wordsLib;
open finite_mapTheory string_numTheory relationTheory;
open bir_programTheory bir_promisingTheory;
open bir_promising_wfTheory;

val _ = new_theory "example_spinlock";

(* general TODO move *)

Theorem FLOOKUP_FEVERY:
  !P fmap. FEVERY P fmap = !id v. FLOOKUP fmap id = SOME v ==> P (id,v)
Proof
  fs[FEVERY_DEF,flookup_thm]
QED

Theorem FEVERY_FUPDATE':
  !P f x y.
    FEVERY P (f |+ (x,y)) <=>
    P (x,y) /\ !z v. FLOOKUP f z = SOME v /\ z <> x ==> P (z,v)
Proof
  csimp[FLOOKUP_DRESTRICT,pred_setTheory.IN_COMPL,pred_setTheory.IN_SING,FEVERY_FUPDATE,FLOOKUP_FEVERY,AC CONJ_ASSOC CONJ_COMM]
QED

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
    /\ (x = BStmt_Jmp (BLE_Label $ BL_Address $ Imm64 jump_target)
      \/ ?e pc'.
        x = BStmt_CJmp e (BLE_Label $ BL_Address $ Imm64 jump_target) (BLE_Label pc')
        /\ x = BStmt_CJmp e (BLE_Label pc') (BLE_Label $ BL_Address $ Imm64 jump_target))
End

(* TODO external blocks should be required to only jump to index 0 *)
Definition is_ext_jump_def:
  is_ext_jump p pc jump_target =
  ?R s tp M s'.
  bir_get_current_statement p pc = SOME $ BSExt R
  /\ R (s,(tp,M)) s'
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

(* program specific instantiations *)

Definition lock_var_def:
  lock_var = BVar "x7" $ BType_Imm Bit64
End

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
  !p' p cid' cid cores M cores' M' s s'.
    FLOOKUP cores cid = SOME $ Core cid p s
    /\ parstep cid cores M cores' M'
    /\ FLOOKUP cores' cid = SOME $ Core cid' p' s'
    ==> cid' = cid /\ p = p'
Proof
  rpt gen_tac >> strip_tac
  >> gvs[FLOOKUP_UPDATE,cstep_cases,parstep_cases]
QED

Theorem run_prog_parstep_preserves:
  !cid cores M cores' M' prog.
  parstep cid cores M cores' M'
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

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

Definition core_pc_def:
  core_pc cid S = bst_pc_tuple (core_state cid S).bst_pc
End

Theorem core_zoo =
  LIST_CONJ $
  map (CONV_RULE (ONCE_DEPTH_CONV $ LHS_CONV SYM_CONV))
  [core_def,core_pc_def,core_state_def,get_core_state_def,core_prog_def,get_core_prog_def]

Theorem bir_env_lookup_update:
  !var v f.
  bir_env_lookup var (BEnv f(|var |-> SOME $ BVal_Imm $ Imm64 v|))
  = SOME $ BVal_Imm $ Imm64 v
Proof
  rw[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
QED

(* read a variable from a state *)

Definition bir_read_reg_def:
  bir_read_reg var env v <=>
    bir_eval_exp (BExp_Den $ BVar var $ BType_Imm Bit64) env
    = SOME $ BVal_Imm $ Imm64 v
End

Theorem bir_read_reg_update:
  !f var v. bir_read_reg var (BEnv f(|var |-> SOME $ BVal_Imm $ Imm64 v|)) v
Proof
  rw[bir_read_reg_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
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

Definition bir_pc_label_def:
  bir_pc_label lbl s <=>
    s.bst_pc = <| bpc_label := lbl; bpc_index := 0 |>
End

Definition bir_pc_label_upd_def:
  bir_pc_label_upd lbl s <=>
    s with bst_pc := <| bpc_label := lbl; bpc_index := 0 |>
End

(* TODO move to promising semantics *)
Definition remove_prom_def:
  remove_prom t s = s with bst_prom updated_by (FILTER ($<> t))
End

Definition lock_addr_def:
  lock_addr = BExp_Const $ Imm64 42w
End

Definition lock_addr_val_def:
  lock_addr_val = BVal_Imm $ Imm64 42w
End

Theorem bir_eval_lock_addr_val_unchanged =
  EVAL ``bir_eval_exp (BExp_Const (Imm64 42w)) (BEnv f) = SOME lock_addr_val``
  |> GEN_ALL

Definition spinlock_abstract_def:
  spinlock_abstract cid
  : ((bir_state_t -> bool) # mem_msg_t list) bmc_program_t
  = BirProgram $ MAP BBlock_Ext [
    (* lock *)
    <|
        beb_label    := BL_Address $ Imm64 0w
      ; beb_relation := (λ(s,(tp,M)) s'.
        ?t t'. (* TODO time  t  given by the transition *)
          t' = latest lock_addr_val t M /\
          if (?m. mem_get M lock_addr_val t' = SOME m
            /\ m.val = BVal_Imm $ Imm64 0w) (* 0w = free *)
          then
            s' = remove_prom t'
                  $ bir_pc_label_upd (BL_Address $ Imm64 4w)
                  $ bir_state_fulful_view_updates s t' lock_addr_val s.bst_v_CAP 0 T F F s
          else s = s'
      )
    |>;
    (* unlock *)
    <|
        beb_label    := BL_Address $ Imm64 4w
      ; beb_relation := (λ(s,(tp,M)) s'.
        (* TODO time  t  given by the transition *)
        ?t. mem_is_loc M t lock_addr_val /\ t <= s.bst_v_CAP
        (* bir_state_read_view_updates s t loc v_addr v_post acq rel xcl *)
        /\ s' = fence_updates BM_ReadWrite BM_Write
                $ bir_pc_label_upd (BL_Address $ Imm64 8w)
                $ bir_state_fulful_view_updates s t lock_addr_val s.bst_v_CAP 0 F F F s
      )
    |>
  ]
End

(* sketch *)
Theorem is_ext_jump_spinlock_abstract_BSExt =
  EVAL ``is_ext_jump (spinlock_abstract cid) pc jump_target``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM,COND_EXPAND,PULL_EXISTS]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [AC CONJ_ASSOC CONJ_COMM,bir_programcounter_t_component_equality,bir_state_t_accfupds]


Theorem bir_get_current_statement_spinlock_abstract_BSExt =
  `bir_get_current_statement (spinlock_abstract cid) s.bst_pc = SOME $ BSExt R`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_current_statement_spinlock_abstract_BSGen =
  `bir_get_current_statement (spinlock_abstract cid) as.bst_pc = SOME (BSGen stmt)`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

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

(* control flow of abstract lock/unlock *)
(*
  ensures
  - jump target not within lock/unlock sections
    as on abstract level the lock/unlock sections are atomic
  - code cannot lock/unlock again
*)

Definition control_flow_def:
  control_flow ext pc cid =
  !jump_target.
  (is_jump (spinlock_abstract cid) pc jump_target
  \/ is_ext_jump (spinlock_abstract cid) pc jump_target)
  /\ (
    (* cannot jump to beginning of abstract lock *)
    FLOOKUP ext cid = SOME T ==> jump_target <> 0w
  )
  /\ (
    (* cannot jump to beginning of abstract unlock *)
    FLOOKUP ext cid <> SOME T ==> jump_target <> 4w
  )
End

Theorem bir_exec_stmtB_noop_unchanged =
  EVAL ``bir_exec_stmtB (BStmt_Assert $ BExp_Const $ Imm1 1w) s``
  |> GEN_ALL

(* lock blocks with entry and jump to *)
Definition lock_def:
  lock lock_addr lock_entry jump_after = MAP BBlock_Stmts [
(* lr.w.aq	t0,(t2) *)
    <|bb_label := BL_Address $ Imm64 lock_entry;
      bb_mc_tags := NONE;
      bb_statements := [
      (*
        BMCStmt_Assert
            $ BExp_Aligned Bit64 2 $ BExp_Den $ BVar "x7" $ BType_Imm Bit64;
*)
        BMCStmt_Load (BVar "x5" $ BType_Imm Bit64)
          lock_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) T F F
          (*
              (BExp_Cast BIExp_SignedCast
                (BExp_Load (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
                    (BExp_Den (BVar "x7" (BType_Imm Bit64)))
                    BEnd_LittleEndian Bit32) Bit64);
          *)
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ lock_entry + 4w|>;
(* bnez	t0,4 <.L1^B1> *)
    <|bb_label := BL_Address $ Imm64 $ lock_entry + 4w;
      bb_mc_tags := NONE; bb_statements := [];
      bb_last_statement :=
        BStmt_CJmp
          (BExp_UnaryExp BIExp_Not
              (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "x5" (BType_Imm Bit64)))
                (BExp_Const (Imm64 0w))))
          (BLE_Label $ BL_Address $ Imm64 lock_entry)
          (BLE_Label $ BL_Address $ Imm64 $ lock_entry + 8w)|>;
(* li	t0,1 *)
    <|bb_label := BL_Address $ Imm64 $ lock_entry + 8w;
      bb_mc_tags := NONE;
      bb_statements := [
        BMCStmt_Assign (BVar "x5" $ BType_Imm Bit64) (BExp_Const $ Imm64 1w)
      ];
      bb_last_statement :=
        BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ lock_entry + 12w|>;
(* sc.w	t1,t0,(t2) *)
    <|bb_label := BL_Address $ Imm64 $ lock_entry + 12w;
      bb_mc_tags := NONE;
      bb_statements := [
      (*
        BMCStmt_Assert $ BExp_Aligned Bit64 2 $ BExp_Den $ BVar "x7" $ BType_Imm Bit64;
      *)
        BMCStmt_Store
          (BVar "success" $ BType_Imm Bit64)
          lock_addr
          (BExp_Den $ BVar "x5" $ BType_Imm Bit64)
          T T F;
      ];
      bb_last_statement :=
        BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ lock_entry + 16w |>;
(* bnez	t1,4 <.L1^B1> *)
    <|bb_label := BL_Address $ Imm64 $ lock_entry + 16w;
      bb_mc_tags := NONE; bb_statements := [];
      bb_last_statement :=
        BStmt_CJmp
          (BExp_UnaryExp BIExp_Not
              (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "success" (BType_Imm Bit64)))
                (BExp_Const v_succ)))
          (BLE_Label (BL_Address $ Imm64 lock_entry))
          (BLE_Label (BL_Address $ Imm64 jump_after))|>
  ]
End

Definition unlock_def:
  unlock lock_addr unlock_entry jump_after = MAP BBlock_Stmts [
(* li	t0,0 *)
    <|bb_label := BL_Address $ Imm64 unlock_entry;
      bb_mc_tags := NONE;
      bb_statements :=
        [BMCStmt_Assign (BVar "x5" $ BType_Imm Bit64) (BExp_Const $ Imm64 0w)];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ unlock_entry + 4w |>;
(* fence	rw,w *)
    <|bb_label := BL_Address $ Imm64 $ unlock_entry + 4w ;
      bb_mc_tags := NONE;
      bb_statements := [BMCStmt_Fence BM_ReadWrite BM_Write];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ unlock_entry + 8w |>;
(* sw	zero,0(t2) *)
    <|bb_label := BL_Address $ Imm64 $ unlock_entry + 8w;
      bb_mc_tags := NONE;
      bb_statements := [
      (*
        BMCStmt_Assert
            (BExp_Aligned Bit64 2
              (BExp_BinExp BIExp_Plus
                  (BExp_Den lock_var)
                  (BExp_Const $ Imm64 0w)));
          BMCStmt_Assert
            (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
              (BExp_BinExp BIExp_Plus
                  (BExp_Den lock_var)
                (BExp_Const $ Imm64 0w)) 4);
*)
          (* success reg, address, value, xcl, acq, rel *)
          BMCStmt_Store
            (BVar "success" $ BType_Imm Bit64)
            lock_addr
            (BExp_Const (Imm64 0w))
            F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 jump_after|>
  ]
End

Definition spinlock_concrete_def:
  spinlock_concrete : ((bir_state_t -> bool) # mem_msg_t list) bmc_program_t
  = BirProgram $
  [
    BBlock_Stmts <|bb_label := BL_Address (Imm64 0w);
        bb_mc_tags := NONE;
        bb_statements :=
          [
          (* no-op *)
          BMCStmt_Assert (BExp_Const $ Imm1 1w)
          (* BMCStmt_Assign lock_var (BExp_Const $ Imm64 42w) *)
          ];
        bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 4w|>;
  ]
  ++ lock lock_addr 4w 24w
  ++ unlock lock_addr 24w 36w
End

Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Load =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Store =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Amo =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Fence =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Fence K1 K2``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BMCStmt_Assign =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtB $ BMCStmt_Assign var e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BSExt =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSExt x``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []


Theorem bir_get_stmt_spinlock_cprog_BStmtE =
  EVAL ``bir_get_current_statement spinlock_concrete pc
    = SOME $ BSGen $ BStmtE x``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_stmt_spinlock_cprog_BSGen =
  EVAL ``bir_get_current_statement spinlock_concrete pc = SOME $ BSGen x``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_spinlock_cprog_BMC_Stmt_Assume =
  EVAL ``bir_get_current_statement spinlock_concrete pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assume e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_stmt_spinlock_cprog_BMC_Stmt_Assert =
  EVAL ``bir_get_current_statement spinlock_concrete pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assert e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [bir_programTheory.bir_get_program_block_info_by_label_THM,pairTheory.LAMBDA_PROD,wordsTheory.NUMERAL_LESS_THM,bir_programTheory.bir_get_current_statement_def,CaseEq"option",AllCaseEqs()]
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV  (srw_ss() ++ boolSimps.CONJ_ss) [GSYM pairTheory.PEXISTS_THM]
  |> SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [listTheory.EL,wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL


Theorem bir_get_spinlock_cprog_zoo =
  LIST_CONJ $ map GEN_ALL
    [bir_get_stmt_spinlock_cprog_BStmtE,
    bir_get_stmt_spinlock_cprog_BSExt,
    bir_get_stmt_spinlock_cprog_BMCStmt_Load,
    bir_get_stmt_spinlock_cprog_BMCStmt_Store,
    bir_get_stmt_spinlock_cprog_BMCStmt_Amo,
    bir_get_stmt_spinlock_cprog_BMCStmt_Fence,
    bir_get_stmt_spinlock_cprog_BMC_Stmt_Assume,
    bir_get_stmt_spinlock_cprog_BMC_Stmt_Assert,
    bir_get_stmt_spinlock_cprog_BMCStmt_Assign]

Theorem bir_labels_of_program_spinlock_concrete =
  EVAL ``bir_labels_of_program spinlock_concrete``

Theorem is_load_spinlock_concrete =
  REFL ``is_load spinlock_concrete pc a_e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [is_load_def,is_store_def,bir_get_spinlock_cprog_zoo]
  |> GEN_ALL

Theorem is_store_spinlock_concrete =
  REFL ``is_store spinlock_concrete pc a_e``
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [is_load_def,is_store_def,bir_get_spinlock_cprog_zoo]
  |> GEN_ALL

Theorem spinlock_concrete_wf_ext:
  !cid tp s M. wf_ext spinlock_concrete cid tp s M
Proof
  fs[wf_ext_def,bir_get_stmt_spinlock_cprog_BSExt]
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

Theorem bir_eval_exp_BExp_Const =
  EVAL ``bir_eval_exp (BExp_Const v) env``
  |> GEN_ALL

Theorem bir_eval_exp_view_BExp_Const =
  EVAL ``bir_eval_exp_view (BExp_Const v) env viewenv = (SOME l,v_addr)``
  |> GEN_ALL

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

(* spinlock concrete invariants *)

Definition slc_inv_def:
  slc_inv lock_entry unlock_entry cid s M <=>
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
     \/ (lbl = unlock_entry /\ index = 0) ==>
      bir_read_reg_zero "success" s.bst_environ
      ==> mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ ((lbl = unlock_entry + 8w ==> index = 0)
       /\ unlock_entry <= lbl /\ lbl <= unlock_entry + 8w
      ==>
      mem_read M lock_addr_val (s.bst_coh lock_addr_val) = SOME $ BVal_Imm $ Imm64 1w)
    /\ ((lbl = unlock_entry ==> index = 1)
       /\ unlock_entry <= lbl /\ lbl <= unlock_entry + 8w
      ==> bir_read_reg "x5" s.bst_environ 0w)
End

Theorem slc_inv_init:
  !cid. slc_inv 4w 24w cid (bmc_state_init spinlock_concrete) []
Proof
  rw[bir_init_progTheory.bmc_state_init_def,bir_pc_first_def,spinlock_concrete_def,bir_programTheory.bir_label_of_block_def,bir_programTheory.bir_block_pc_def,bst_pc_tuple_def]
  >> rw[slc_inv_def,bst_pc_tuple_def,slc_mem_inv_def]
  >> imp_res_tac mem_read_some
  >> fs[mem_read_def,mem_get_def,mem_default_value_def,mem_default_def]
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

Theorem bir_eval_exp_BExp_Den_update_eq:
  !name v f. bir_eval_exp (BExp_Den (BVar name (BType_Imm Bit64)))
    (BEnv f(|name |-> SOME (BVal_Imm (Imm64 v ))|)) =
      SOME (BVal_Imm (Imm64 v))
Proof
  fs[bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,PULL_EXISTS,bir_valuesTheory.type_of_bir_val_EQ_ELIMS,type_of_bir_imm_EQ_ELIMS,combinTheory.APPLY_UPDATE_THM]
QED

Theorem fulfil_update_env_BVar_eq:
  !env new_env name.
  fulfil_update_env (BVar name (BType_Imm Bit64)) T env = SOME new_env
  <=> ?f. env = BEnv f /\ f name <> NONE
    /\ new_env = BEnv f(|name |-> SOME $ BVal_Imm v_succ |)
Proof
  Cases >> rpt gen_tac
  >> CONV_TAC $ LAND_CONV EVAL
  >> fs[EQ_IMP_THM,v_succ_def]
QED

Theorem bir_dest_bool_val_false =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 0w``

Theorem bir_dest_bool_val_true =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 $ -1w``

Theorem bir_dest_bool_val_true' =
  EVAL ``bir_dest_bool_val $ BVal_Imm $ Imm1 1w``

Theorem clstep_slc_inv:
  !cid tp s M prom s'.
  slc_inv 4w 24w cid s M
  /\ well_formed cid M s
  /\ clstep spinlock_concrete cid tp s M prom s'
  ==> slc_inv 4w 24w cid s' M
Proof
  rpt strip_tac
  >> drule_at (Pat `clstep`) clstep_preserves_wf
  >> fs[spinlock_concrete_wf_ext] >> strip_tac
  >> gvs[clstep_cases,bir_get_spinlock_cprog_zoo,bir_state_read_view_updates_def,bir_state_fulful_view_updates_def,bir_eval_exp_view_BExp_Const,GSYM
  lock_addr_val_def,combinTheory.APPLY_UPDATE_THM,fence_updates_def]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    fs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,combinTheory.APPLY_UPDATE_THM]
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
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`xclfail_update_viewenv`]
  >- gvs[AllCaseEqs(),PULL_EXISTS,slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_read_reg_zero_def,bir_read_reg_def,CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV SYM_CONV) xclfail_update_env_SOME,bir_eval_exp_BExp_Den_update_eq,v_fail_def]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]
  >- (
    gvs[CONV_RULE (ONCE_DEPTH_CONV $ LAND_CONV SYM_CONV) fulfil_update_env_BVar_eq,bir_eval_exp_view_def,bir_eval_exp_BExp_Den_update_eq]
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_read_reg_zero_def,v_succ_def,bir_read_reg_def,bir_eval_exp_BExp_Den_update_eq,combinTheory.APPLY_UPDATE_THM]
    >> qhdtm_assum `fulfil_atomic_ok` $ irule_at Any
    >> imp_res_tac mem_get_mem_read_imp
    >> fs[listTheory.MEM_FILTER,slc_mem_inv_def]
    >> dsimp[listTheory.MEM_FILTER]
    >> fs[well_formed_def,well_formed_xclb_def]
    >> asm_rewrite_tac[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address $ Imm64 8w`,`s.bst_pc.bpc_index = 0`]
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
    >> fs[bst_pc_tuple_def,bir_pc_next_def,slc_inv_def,bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_reg_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 20w)`,`s.bst_pc.bpc_index = 0`]
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
    >> fs[bst_pc_tuple_def,bir_pc_next_def,slc_inv_def,bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_reg_zero_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    Cases_on `s.bst_environ`
    >> fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def]
    >> drule $ GSYM bir_read_reg_env_update_cast64
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
  )
  >~ [`bmc_exec_general_stmt`]
  >- (
    gvs[bmc_exec_general_stmt_exists,bir_get_spinlock_cprog_zoo,bir_exec_stmt_assert_def,bir_state_set_typeerror_def,bir_exec_stmt_assume_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_eval_exp_BExp_Const,bir_dest_bool_val_true',slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
    >> goal_assum drule
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]
  >- (
    gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,fulfil_update_env_def,slc_mem_inv_def]
    >> dsimp[listTheory.MEM_FILTER]
    >> imp_res_tac mem_get_mem_read_imp
    >> asm_rewrite_tac[]
    >> rw[] >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    fs[bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,slc_mem_inv_def]
    >> drule_then assume_tac $ GSYM bir_read_reg_env_update_cast64
    >> gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def,bir_eval_exp_view_BExp_Const]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 0`]
  >- gvs[slc_inv_def,bst_pc_tuple_def,bir_pc_next_def]
QED

Theorem slc_inv_prom:
  !cid s M msg.
  slc_inv 4w 24w cid s M
  /\ well_formed cid M s
  ==> slc_inv 4w 24w cid
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

Theorem cstep_seq_slc_inv:
  !cid tp s M s' M'.
  slc_inv 4w 24w cid s M
  /\ well_formed cid M s
  /\ cstep_seq spinlock_concrete cid tp (s, M) (s', M')
  ==> slc_inv 4w 24w cid s' M'
Proof
  rpt strip_tac
  >> gvs[cstep_seq_cases,cstep_cases]
  >- drule_all_then irule clstep_slc_inv
  >> irule clstep_slc_inv
  >> goal_assum $ drule_at Any
  >> fs[slc_inv_prom,well_formed_promise_self]
QED

Theorem cstep_seq_NRC_slc_inv:
  !cid tp n seM seM'.
  NRC (cstep_seq spinlock_concrete cid tp) n seM seM'
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

Theorem is_certified_locking:
  !cid tp s M msg t.
  is_certified spinlock_concrete cid tp s (M ++ [msg])
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
  >> qmatch_asmsub_rename_tac `cstep_seq spinlock_concrete cid tp sM2 sM3`
  >> PairCases_on `sM3` >> PairCases_on `sM2`
  >> fs[]
  >> qmatch_asmsub_rename_tac
    `NRC (cstep_seq spinlock_concrete cid tp) m (s,M ++ [msg]) (s1,M1)`
  >> qmatch_asmsub_rename_tac
    `cstep_seq spinlock_concrete cid tp (s1,M1) (s2,M2)`
  >> `slc_inv 4w 24w cid s1 M1 /\ well_formed cid M1 s1` by (
    rev_drule_at (Pat `NRC`) cstep_seq_NRC_slc_inv
    >> rev_drule_at (Pat `NRC`) cstep_seq_NRC_wf
    >> fs[spinlock_concrete_wf_ext,wf_ext_p_def]
  )
  >> imp_res_tac cstep_seq_NRC_prom_subset
  >> fs[listTheory.NULL_EQ]
  >> qmatch_asmsub_rename_tac `cstep_seq _ cid tp (s1,M1) (s2,M2)`
  >> `is_certified spinlock_concrete cid tp s2 M2
    /\ is_certified spinlock_concrete cid tp s1 M1` by (
    conj_asm1_tac
    >> simp[is_certified_def,cstep_seq_rtc_def,arithmeticTheory.RTC_eq_NRC,PULL_EXISTS]
    >- (
      irule_at Any arithmeticTheory.NRC_ADD_I
      >> goal_assum drule
      >> irule_at Any $ iffRL arithmeticTheory.NRC_0
      >> qmatch_asmsub_rename_tac `NRC (cstep_seq _ cid tp) _ (s2,M2) sM4`
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
  >> disch_then $ drule_then assume_tac
  >> dxrule_at_then Any assume_tac is_certified_promises
  >> rev_drule_then strip_assume_tac cstep_seq_NRC_mem_mono
  >> dxrule_then drule cstep_seq_is_clstep
  >> impl_tac >- fs[listTheory.NULL_EQ] >> strip_tac
  >> dxrule_then assume_tac $ iffLR slc_inv_def
  >> gvs[clstep_cases,bst_pc_tuple_def,bir_get_spinlock_cprog_zoo,listTheory.MEM_FILTER]
  >> gvs[bst_pc_tuple_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_eval_exp_view_BExp_Const]
  >> first_x_assum $ drule_then assume_tac
  >> gvs[GSYM lock_addr_val_def,rich_listTheory.IS_PREFIX_APPEND,mem_read_append,fulfil_atomic_ok_append,mem_get_append]
  >> qmatch_asmsub_abbrev_tac `is_certified _ cid`
  >~ [`s1.bst_pc.bpc_index = 0`,`s1.bst_pc.bpc_label = BL_Address (Imm64 32w)`]
  >- gs[mem_get_def,GSYM arithmeticTheory.ADD1,listTheory.oEL_THM,rich_listTheory.EL_APPEND2]
  >~ [`s1.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s1.bst_pc.bpc_index = 0`]
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
    >> ntac 2 $ first_x_assum $ qspec_then `t'` assume_tac
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
  >> dxrule_all_then assume_tac latest_t_add
  >> dxrule_then (fs o single) latest_t_latest_is_lowest
  >> imp_res_tac mem_get_mem_read
  >> fs[latest_exact]
QED

Theorem is_certified_unlocking:
  !cid tp s M msg t.
  is_certified spinlock_concrete cid tp s (M ++ [msg])
  /\ slc_inv 4w 24w cid s (M ++ [msg])
  /\ well_formed cid (M ++ [msg]) s
  /\ MEM (LENGTH M + 1) s.bst_prom
  /\ msg.loc = lock_addr_val
  /\ msg.cid = cid
  /\ msg.val = BVal_Imm $ Imm64 0w (* 0w = free *)
  /\ t = latest lock_addr_val (LENGTH M) M
  ==> ?m. mem_get M lock_addr_val t = SOME m
    /\ m.val = BVal_Imm $ Imm64 1w (* 1w = locked *)
    /\ m.cid = cid
Proof
  cheat
QED


(* refinement without weak memory model behaviour

CONV_RULE (RHS_CONV EVAL) spinlock_concrete_def
*)

Definition spinlock_ref1_def:
  spinlock_ref1 cid
    ((cores :num |->
      (unit bmc_stmt_basic_t, unit, (bir_state_t -> bool) # mem_msg_t list)
        core_t),
    (M :mem_msg_t list))
    ((acores :num |-> (ext_state bmc_stmt_basic_t, ext_state, (bir_state_t -> bool) # mem_msg_t list) core_t),
      (aM :mem_msg_t list)) <=>
  !lbl index.
    core_pc cid cores = (BL_Address $ Imm64 lbl, index)
      ==>
    (lbl = 16w /\ 0 < index ==> ?v. bir_read_core_reg "success" cid cores v)
    /\ (lbl = 20w ==> ?v. bir_read_core_reg "success" cid cores v)
    (* not (yet) taking the lock *)
    /\ (lbl <= 16w /\ (lbl = 16w ==> index = 0)
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    /\ (
      (lbl = 12w /\ index = 1) \/
      (lbl = 16w /\ index = 0)
      ==> bir_read_core_reg "x5" cid cores 1w (* 'lock not free' value *)
    )
    (* unsuccessful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_core_reg_nonzero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_core_reg_nonzero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    (* successful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_core_reg_zero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_core_reg_zero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0))
    (* after lock, before unlock *)
    /\ (
      20w < lbl /\ lbl <= 32w /\ (lbl = 32w ==> index = 0)
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
      32w <= lbl /\ (lbl = 32w ==> index = 1)
      ==> core_pc cid acores = (BL_Address $ Imm64 8w,0)
    )
End

Theorem spinlock_ref1_promises:
  !cid cores M acores ae aM m M' s.
  spinlock_ref1 cid (cores,M) (acores,aM)
  /\ FLOOKUP cores cid = SOME (Core cid spinlock_concrete s)
  ==> spinlock_ref1 cid
    (cores |+
      (cid,
        Core cid spinlock_concrete $ s with bst_prom updated_by (λx. x ++ [m])),M ++ M')
    (acores,ae,aM)
Proof
  rpt strip_tac
  >> fs[spinlock_ref1_def,core_zoo,FLOOKUP_UPDATE,bir_read_core_reg_zero_def,bir_read_core_reg_def,bir_read_core_reg_nonzero_def]
  >> fs[FEVERY_prog_def]
  >> dsimp[FEVERY_FUPDATE]
  >> rw[AllCaseEqs()]
  >> first_x_assum $ drule_then assume_tac
  >> gvs[AllCaseEqs()]
QED

val simple_refl_step =
    disj1_tac
    >> fs[spinlock_ref1_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def]

Theorem parstep_preserves_spinlock_ref1:
  !cid cores M cores' M' acores ae aM as.
    parstep_tr cid (cores,M) (cores',M')
    /\ run_progc cores spinlock_concrete
    /\ spinlock_ref1 cid (cores,M) (acores,aM)
    /\ run_prog acores spinlock_abstract
    /\ FLOOKUP acores cid = SOME $ Core cid (spinlock_abstract cid) as
    ==>
    spinlock_ref1 cid (cores',M') (acores,aM)
    \/ ?acores' ae' aM'.
      parstep_tr cid (acores,ae,aM) (acores',aM')
      /\ spinlock_ref1 cid (cores',M') (acores',aM')
Proof
  rpt strip_tac
  >> dxrule_then assume_tac $ iffLR run_progc_def
  >> dxrule_then assume_tac $ iffLR run_prog_def
  >> dxrule_then assume_tac $ iffLR parstep_tr_def
  >> gvs[parstep_cases,clstep_cases]
  >> first_x_assum $ drule_then $ fs o single
  >> gvs[cstep_cases]
  >~ [`M ++ [msg]`]
  >- (
    disj1_tac >> fs[spinlock_ref1_promises]
  )
  >> gvs[clstep_cases,bir_get_spinlock_cprog_zoo]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`xclfail_update_viewenv`]
  >- (
    disj1_tac
    >> qpat_x_assum `SOME _ = xclfail_update_env spinlock_concrete _` mp_tac
    >> dsimp[xclfail_update_env_def,bir_get_spinlock_cprog_zoo,AllCaseEqs()]
    >> Cases_on `s.bst_environ`
    >> fs[spinlock_ref1_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def]
    >> disch_then $ mp_tac o CONV_RULE EVAL
    >> disch_then assume_tac
    >> gvs[combinTheory.APPLY_UPDATE_THM]
    >> dsimp[bir_envTheory.bir_env_read_def,bir_read_var_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]
  >- (
    disj2_tac
    >> gvs[spinlock_ref1_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_read_core_reg_nonzero_def,
      bir_read_core_reg_zero_def,
      bir_state_fulful_view_updates_def]
    >> qpat_x_assum `SOME _ = fulfil_update_env spinlock_concrete _` mp_tac
    >> Cases_on `s.bst_environ`
    >> disch_then $ mp_tac o CONV_RULE EVAL
    >> csimp[fulfil_update_env_def,bir_get_spinlock_cprog_zoo,AllCaseEqs(),bir_read_var_def]
    >> disch_then $ assume_tac o CONV_RULE EVAL
    >> gvs[combinTheory.APPLY_UPDATE_THM]
    >> csimp[core_zoo,FLOOKUP_UPDATE,bir_read_var_def,bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,bir_state_read_view_updates_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_core_reg_nonzero_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
    >> qmatch_goalsub_rename_tac `(acores,ae,aM)`
    >> CONV_TAC $ RESORT_EXISTS_CONV rev
    >> qexists_tac `aM`
    (* parstep_tr_spinlock_abstract_next_step *)
    >> fs[parstep_tr_def,parstep_cases,crit_is_empty_def]
    >> dsimp[cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt,crit_is_empty_def,FLOOKUP_UPDATE]
    >> fs[PULL_EXISTS,core_zoo]
    >> qexists_tac `<|crit := ae.crit |+ (cid,T)|>`
    >> cheat (* TODO atomicity_ok, mem_is_loc, is_certified *)
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    (* transition one abstrace step *)
    disj2_tac
    >> dxrule_then assume_tac $ iffLR spinlock_ref1_def
    >> gs[core_zoo,bst_pc_tuple_def]
    >> CONV_TAC $ RESORT_EXISTS_CONV rev
    >> qmatch_goalsub_rename_tac `(acores,ae,aM)`
    >> qexists_tac `aM`
    >> dsimp[parstep_cases,parstep_tr_def,cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt]
    >> `?loc. mem_is_loc aM (LENGTH aM) loc` by (
      cheat (* TODO choose proper location *)
    )
    >> qmatch_asmsub_rename_tac `mem_is_loc _ _ loc`
    >> qexists_tac `<| crit := (ae.crit |+ (cid,F)) |>`
    >> fs[bir_state_t_component_equality,combinTheory.APPLY_UPDATE_THM]
    >> qhdtm_assum `mem_is_loc` $ irule_at Any
    >> irule_at Any $ iffRL $ cj 1 listTheory.EVERY_DEF (* *)
    >> fs[]
    >> conj_tac >- cheat (* atomicity_ok obsolete *)
    >> conj_tac >- cheat (* TODO: as.bst_status = BST_Running *)
    >> conj_tac >- cheat (* TODO: is_certified holds for abstract program *)
    >> unabbrev_all_tac
    >> fs[spinlock_ref1_def,core_zoo,bst_pc_tuple_def,FLOOKUP_UPDATE,bir_pc_next_def,bir_state_fulful_view_updates_def]
    >> cheat
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 8w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> Cases_on `s.bst_environ`
    >> csimp[spinlock_ref1_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,
      bir_programTheory.bir_exec_stmt_jmp_def,
      bir_programTheory.bir_exec_stmt_jmp_to_label_def,
      bir_eval_label_exp_def,bir_block_pc_def,
      bir_labels_of_program_spinlock_concrete]
    >> BasicProvers.every_case_tac
    >> gs[AllCaseEqs(),bir_programTheory.bir_state_set_typeerror_def,spinlock_ref1_def,core_zoo,bst_pc_tuple_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 20w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> dxrule_then strip_assume_tac $ iffLR spinlock_ref1_def
    >> gs[core_zoo,FLOOKUP_UPDATE,
      bst_pc_tuple_def,bir_read_core_reg_zero_def,
      bir_read_core_reg_nonzero_def,bir_pc_next_def]
    >> qmatch_assum_rename_tac `bir_read_core_reg _ cid cores _ v'`
    >> Cases_on `v' = 0w`
    >> gvs[bir_read_core_reg_def,bir_read_var_def]
    >- (
      drule_then assume_tac bir_exec_stmt_cjmp_second
      >> gs[core_zoo,bst_pc_tuple_def,core_zoo,spinlock_ref1_def,FLOOKUP_UPDATE]
    )
    >> drule_then assume_tac bir_exec_stmt_cjmp_first
    >> gs[core_zoo,bst_pc_tuple_def,core_zoo,spinlock_ref1_def,FLOOKUP_UPDATE]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
    >> Cases_on `s.bst_environ`
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` mp_tac
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` mp_tac
    >> EVAL_TAC
    >> rw[]
    >> fs[env_update_cast64_def]
    >> qpat_x_assum `_ = bir_env_update _ _ _ _` mp_tac
    >> EVAL_TAC
    >> rw[]
    >> csimp[core_zoo,FLOOKUP_UPDATE,bir_read_var_def,bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,bir_state_read_view_updates_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_core_reg_nonzero_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
  )
  (* jump statements *)
  >~ [`bmc_exec_general_stmt`]
  >> gvs[bir_get_stmt_spinlock_cprog_BSGen,bmc_exec_general_stmt_def]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    gvs[bir_exec_stmtB_noop_unchanged]
    >> simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
    >> Cases_on `s.bst_environ`
    >> qhdtm_x_assum `bir_read_var` mp_tac
    >> EVAL_TAC
    >> rw[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 1`]
  >- (
      dxrule_then assume_tac $ iffLR spinlock_ref1_def
      >> gvs[core_zoo,bst_pc_tuple_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_spinlock_concrete,bir_block_pc_def]
      >> qmatch_assum_rename_tac `bir_read_core_reg _ cid cores v`
      >> Cases_on `v = 0w`
      >- (
        (* success *)
        disj2_tac
        >> gvs[bir_read_core_reg_zero_def,bir_read_core_reg_nonzero_def,bir_read_core_reg_def,bir_read_var_def,core_zoo,FLOOKUP_UPDATE,spinlock_ref1_def,bst_pc_tuple_def]
        >> qmatch_goalsub_rename_tac `(acores,ae,aM)`
        >> CONV_TAC $ RESORT_EXISTS_CONV rev
        >> qexists_tac `aM`
        >> dsimp[parstep_cases,parstep_tr_def,cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt]
        >> `?loc. mem_is_loc aM (LENGTH aM) loc` by (
          cheat
        )
        >> qmatch_asmsub_rename_tac `mem_is_loc _ _ loc`
        >> qexists_tac `<| crit := (ae.crit |+ (cid,F)) |>`
        >> cheat (* TODO *)
      )
      >> disj1_tac (* unsuccessful *)
      >> gs[core_zoo,spinlock_ref1_def,FLOOKUP_UPDATE,bst_pc_tuple_def,bir_read_core_reg_def,bir_read_var_def,bir_read_core_reg_nonzero_def,bir_read_core_reg_zero_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
QED

(*
    dxrule_then strip_assume_tac $ iffLR spinlock_ref1_def
    >> gs[core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_pc_next_def]
*)

(* refinement with weak memory model behaviour *)
(* use with latestP_mem_get *)
Definition ccrit_empty_prop_def:
  ccrit_empty_prop M cid coh env =
  !m t l. t = latestP (λmsg. msg.loc = l /\ msg.cid = cid) (coh l) M /\ t <> 0
    /\ l = lock_addr_val
    /\ mem_get M l t = SOME m
    ==> m.val = BVal_Imm $ Imm64 0w (* 0w = free *)
End

Theorem ccrit_empty_prop_promises:
  !cid M s msg.
  well_formed cid M s
  ==>
    ccrit_empty_prop (M ⧺ [msg]) cid s.bst_coh s.bst_environ
    = ccrit_empty_prop M cid s.bst_coh s.bst_environ
Proof
  rw[ccrit_empty_prop_def]
  >> qmatch_goalsub_abbrev_tac `latestP _ t (M ++ _)`
  >> `t <= LENGTH M` by fs[well_formed_def,Abbr`t`]
  >> fs[latestP_APPEND]
  >> qmatch_goalsub_abbrev_tac `mem_get (M ++ M') v_addr t'`
  >> `t' <= LENGTH M` by (
    unabbrev_all_tac
    >> irule arithmeticTheory.LESS_EQ_TRANS
    >> irule_at Any latestP_bound
    >> fs[]
  )
  >> fs[mem_get_append]
QED

Theorem well_formed_mem_read_view_zero:
  !cid M s l.
  well_formed cid M s ==> mem_read_view (s.bst_fwdb l) 0 = 0
Proof
  rw[mem_read_view_def,well_formed_fwdb_def,well_formed_def]
  >> qmatch_asmsub_rename_tac `s.bst_fwdb l`
  >> first_x_assum $ qspec_then `l` assume_tac
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

(* the lock is free if every core that at its time of coherence reads
 * from the lock address  l  a message by itself, reads 'free' *)
Definition ccrit_empty_def:
  ccrit_empty cores M =
    !cid s. FLOOKUP cores cid = SOME $ Core cid spinlock_concrete s
    ==> ccrit_empty_prop M cid s.bst_coh s.bst_environ
End

(* all cores running the spinlock use same address *)

Theorem ccrit_empty_thm:
  !cores M. ccrit_empty cores M <=>
    FEVERY_prog spinlock_concrete
      (λcid s. ccrit_empty_prop M cid s.bst_coh s.bst_environ)
      cores
Proof
  dsimp[ccrit_empty_def,FEVERY_prog_def,FLOOKUP_FEVERY]
QED

Theorem ccrit_empty_prop_update:
  !cores M cid s' s p.
    FLOOKUP cores cid = SOME $ Core cid spinlock_concrete s
    /\ (ccrit_empty_prop M cid s'.bst_coh s'.bst_environ
    = ccrit_empty_prop M cid s.bst_coh s.bst_environ)
    ==>
    (ccrit_empty (cores |+ (cid, Core cid spinlock_concrete s')) M <=>
      ccrit_empty cores M)
Proof
  rpt strip_tac
  >> dsimp[ccrit_empty_thm,FEVERY_FUPDATE',FEVERY_prog_def]
  >> dsimp[FLOOKUP_FEVERY]
  >> rw[EQ_IMP_THM]
  >> first_x_assum drule
  >> qmatch_goalsub_abbrev_tac `(B ==> _) ==> _` >> Cases_on `B`
  >> fs[]
QED

Theorem ccrit_empty_equiv1 =
  Q.ISPECL [`spinlock_concrete`,`λcid s. ccrit_empty_prop M cid s.bst_coh s.bst_environ`] FEVERY_prog_eq1
  |> SIMP_RULE std_ss [GSYM ccrit_empty_thm]
  |> GEN_ALL

Theorem ccrit_empty_equiv2 =
  Q.ISPECL [`spinlock_concrete`,`λcid s. ccrit_empty_prop M cid s.bst_coh s.bst_environ`] FEVERY_prog_eq2
  |> SIMP_RULE std_ss [GSYM ccrit_empty_thm]
  |> GEN_ALL

Definition spinlock_ref_def:
  spinlock_ref cid
    ((cores :num |->
      (unit bmc_stmt_basic_t, unit, (bir_state_t -> bool) # mem_msg_t list)
        core_t),
    (M :mem_msg_t list))
    ((acores :num |-> (ext_state bmc_stmt_basic_t, ext_state, (bir_state_t -> bool) # mem_msg_t list) core_t),
    (aM :mem_msg_t list)) <=>
  !lbl index.
    core_pc cid cores = (BL_Address $ Imm64 lbl, index)
      ==>
      (ccrit_empty cores M <=> crit_is_empty ae.crit)
    /\ (lbl = 16w /\ 0 < index ==> ?v. bir_read_core_reg "success" cid cores v)
    /\ (lbl = 20w ==> ?v. bir_read_core_reg "success" cid cores v)
    (* not (yet) taking the lock *)
    /\ (lbl <= 16w /\ (lbl = 16w ==> index = 0)
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    /\ (
      (lbl = 12w /\ index = 1) \/
      (lbl = 16w /\ index = 0)
      ==> bir_read_core_reg "x5" cid cores 1w (* 'lock not free' value *)
    )
    (* unsuccessful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_core_reg_nonzero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_core_reg_nonzero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 0w,0))
    (* successful store *)
    /\ (lbl = 16w /\ 0 < index /\ bir_read_core_reg_zero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0))
    /\ (lbl = 20w /\ index = 0 /\ bir_read_core_reg_zero "success" cid cores
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0))
    (* after lock, before unlock *)
    /\ (
      20w < lbl /\ lbl <= 32w /\ (lbl = 32w ==> index = 0)
      ==> core_pc cid acores = (BL_Address $ Imm64 4w,0)
    )
    (* after unlock *)
    /\ (
      32w <= lbl /\ (lbl = 32w ==> index = 1)
      ==> core_pc cid acores = (BL_Address $ Imm64 8w,0)
    )
End

Theorem spinlock_ref_promises:
  !cid cores M acores ae aM m s msg.
  spinlock_ref cid (cores,M) (acores,ae,aM)
  /\ FLOOKUP cores cid = SOME (Core cid spinlock_concrete s)
  /\ well_formed_cores cores M
  ==> spinlock_ref cid
    (cores |+
      (cid,
        Core cid spinlock_concrete $ s with bst_prom updated_by (λx. x ++ [m])),M ++ [msg])
    (acores,ae,aM)
Proof
  rpt strip_tac
  >> fs[spinlock_ref_def,core_zoo,FLOOKUP_UPDATE,bir_read_core_reg_zero_def,bir_read_core_reg_def,bir_read_core_reg_nonzero_def,bst_pc_tuple_def]
  >> dsimp[]
  >> rw[AllCaseEqs()]
  >> first_x_assum $ drule_then assume_tac
  >> gvs[FLOOKUP_UPDATE]
  >> qpat_x_assum `_ = _` $ ONCE_REWRITE_TAC o single o GSYM
  >> qhdtm_x_assum `FLOOKUP` mp_tac
  >> qhdtm_x_assum `well_formed_cores` mp_tac
  >> rpt $ pop_assum kall_tac
  >> rpt strip_tac
  >> dsimp[ccrit_empty_thm,FEVERY_FUPDATE',FEVERY_prog_def]
  >> dsimp[FLOOKUP_FEVERY]
  >> fs[well_formed_cores_def,ccrit_empty_prop_promises]
  >> rw[EQ_IMP_THM]
  >> first_x_assum drule
  >> qmatch_goalsub_abbrev_tac `(A ==> _) ==> _`
  >> Cases_on `A` >> fs[]
QED

val simple_refl_step =
    disj1_tac
    >> fs[spinlock_ref_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def]

Theorem parstep_preserves_spinlock_ref:
  !cid cores M cores' M' acores ae aM as.
    parstep_tr cid (cores,M) (cores',M')
    /\ run_progc cores spinlock_concrete
    /\ spinlock_ref cid (cores,M) (acores,aM)
    /\ run_prog acores spinlock_abstract
    /\ FLOOKUP acores cid = SOME $ Core cid (spinlock_abstract cid) as
    /\ well_formed_cores cores M
    /\ well_formed_ext_cores cores
    ==>
    spinlock_ref cid (cores',M') (acores,aM)
    \/ ?acores' ae' aM'.
      parstep_tr cid (acores,aM) (acores',aM')
      /\ spinlock_ref cid (cores',M') (acores',aM')
Proof
  rpt strip_tac
  >> dxrule_then assume_tac $ iffLR run_progc_def
  >> dxrule_then assume_tac $ iffLR run_prog_def
  >> dxrule_then assume_tac $ iffLR parstep_tr_def
  >> drule_at_then Any assume_tac parstep_preserves_wf
  >> gvs[parstep_cases,clstep_cases]
  >> first_x_assum $ drule_then $ fs o single
  >> gvs[cstep_cases]
  >~ [`M ++ [msg]`] >- fs[spinlock_ref_promises]
  >> gvs[clstep_cases,bir_get_spinlock_cprog_zoo]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
    >> qpat_x_assum `_ = crit_is_empty ae.crit` $ ONCE_REWRITE_TAC o single o GSYM
    >> drule_then irule ccrit_empty_prop_update
    >> fs[]
    >> qmatch_asmsub_rename_tac `(SOME l,_)=bir_eval_exp_view _ _ _ _`
    >> `l = lock_addr_val` by (
      qpat_x_assum `(SOME l,_)=bir_eval_exp_view _ _ _ _` mp_tac
      >> EVAL_TAC >> fs[]
    )
    >> gvs[]
    >> qmatch_goalsub_abbrev_tac `s.bst_coh(| lock_addr_val |-> coh |)`
    >> `coh <= LENGTH M` by (
      fs[well_formed_cores_def]
      >> qmatch_asmsub_rename_tac `(cid,_)`
      >> first_x_assum $ qspec_then `cid` assume_tac
      >> fs[FLOOKUP_UPDATE]
      >> dxrule_then strip_assume_tac $ iffLR well_formed_def
      >> fs[]
      >> ntac 2 $ first_x_assum $ qspec_then `lock_addr_val` mp_tac
      >> fs[combinTheory.APPLY_UPDATE_THM]
    )
    >> cheat
    (*
     * any future store were unfulfillable if the coh updated were a value
     * such that the own core's store comes into sight
     * contradiction via is_certified
    *)
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`xclfail_update_viewenv`]
  >- (
    disj1_tac
    >> qpat_x_assum `SOME _ = xclfail_update_env spinlock_concrete _` mp_tac
    >> dsimp[xclfail_update_env_def,bir_get_spinlock_cprog_zoo,AllCaseEqs()]
    >> Cases_on `s.bst_environ`
    >> fs[spinlock_ref_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def]
    >> disch_then $ assume_tac o CONV_RULE EVAL
    >> gvs[combinTheory.APPLY_UPDATE_THM]
    >> dsimp[bir_envTheory.bir_env_read_def,bir_read_var_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
    >> qpat_x_assum `_ = crit_is_empty ae.crit` $ ONCE_REWRITE_TAC o single o GSYM
    >> drule_then irule ccrit_empty_prop_update
    >> simp[ccrit_empty_prop_def]
    (* coh of lock_var unchanged since entering the lock *)
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 0`,`fulfil_update_env`]

  >- (
    disj2_tac
    >> fs[spinlock_ref_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def]
    >> qpat_x_assum `SOME _ = fulfil_update_env spinlock_concrete _` mp_tac
    >> Cases_on `s.bst_environ`
    >> disch_then $ mp_tac o CONV_RULE EVAL
    >> csimp[fulfil_update_env_def,bir_get_spinlock_cprog_zoo,AllCaseEqs()]
    >> disch_then $ assume_tac o CONV_RULE EVAL
    >> gvs[combinTheory.APPLY_UPDATE_THM]
    >> csimp[core_zoo,FLOOKUP_UPDATE,bir_read_var_def,bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,bir_state_read_view_updates_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_core_reg_nonzero_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
    >> gvs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,optionTheory.IS_SOME_EXISTS]
    >> fs[parstep_tr_def,parstep_cases]
    >> dsimp[cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt,FLOOKUP_UPDATE,core_zoo]
    >> qpat_x_assum `bir_read_var _ _ _ = SOME _` $ assume_tac o CONV_RULE EVAL
    >> ntac 2 $ qpat_x_assum `(SOME _,_) = bir_eval_exp_view _ _ _ _` mp_tac
    >> Cases_on `s.bst_environ`
    >> fs[]
    >> ntac 2 $ disch_then $ assume_tac o CONV_RULE EVAL
    >> gvs[]
    >> qmatch_goalsub_abbrev_tac `ccrit_empty (cores |+ (cid, Core cid spinlock_concrete s')) M`
    >> `~ccrit_empty (cores |+ (cid, Core cid spinlock_concrete s')) M` by (
      simp[ccrit_empty_thm,FEVERY_FUPDATE,FEVERY_prog_def]
      >> disj1_tac
      >> unabbrev_all_tac
      >> fs[ccrit_empty_prop_def,GSYM lock_addr_val_def,combinTheory.APPLY_UPDATE_THM]
      >> drule mem_get_latestP_exact
      >> fs[ETA_THM]
    )
    >> qexists_tac `<|crit := ae.crit |+ (cid,T)|>`
    >> fs[crit_is_empty_thm,FEVERY_FUPDATE]
    (*
     * needs to take the certification of other cores into account
     * in order to prove the following
     *)
    >> `ccrit_empty cores M` by (
      cheat
    )
    >> cheat (* TODO atomicity_ok, mem_is_loc (with proper time), is_certified *)
  )

  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
    >> qpat_x_assum `_ = crit_is_empty ae.crit` $ ONCE_REWRITE_TAC o single o GSYM
    >> drule_then irule ccrit_empty_prop_update
    >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 0`]
  >- (

    (* transition one abstrace step *)
    disj2_tac
    >> dxrule_then assume_tac $ iffLR spinlock_ref_def
    >> gs[core_zoo,bst_pc_tuple_def]
    >> CONV_TAC $ RESORT_EXISTS_CONV rev
    >> qmatch_goalsub_rename_tac `(acores,ae,aM)`
    >> qexists_tac `aM`
    >> `mem_is_loc aM (LENGTH aM) lock_addr_val` by (
      cheat (* TODO choose proper time *)
    )
    >> dsimp[parstep_cases,parstep_tr_def,cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt]
    >> qexists_tac `<| crit := (ae.crit |+ (cid,F)) |>`
    >> fs[bir_state_t_component_equality,combinTheory.APPLY_UPDATE_THM]
    >> qhdtm_assum `mem_is_loc` $ irule_at Any
    >> conj_tac >- cheat (* atomicity_ok obsolete *)
    >> conj_tac >- cheat (* TODO: as.bst_status = BST_Running *)
    >> conj_tac >- cheat (* TODO: is_certified holds for abstract program *)
    >> qpat_x_assum `SOME _ = fulfil_update_env _ _` mp_tac
    >> ntac 2 $ qpat_x_assum `(SOME _,_) = bir_eval_exp_view _ _ _ _` mp_tac
    >> Cases_on `s.bst_environ`
    >> fs[]
    >> ntac 3 $ disch_then $ assume_tac o CONV_RULE EVAL
    >> gvs[spinlock_ref_def,core_zoo,bst_pc_tuple_def,bir_pc_next_def,bir_state_fulful_view_updates_def,fulfil_update_env_def,bir_get_spinlock_cprog_zoo,AllCaseEqs()]
    >> simp[FLOOKUP_UPDATE,core_zoo,bst_pc_tuple_def,bir_pc_next_def]
    >> cheat
    (*
     * show that overwriting
     *)
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 8w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> Cases_on `s.bst_environ`
    >> csimp[spinlock_ref_def,core_zoo,FLOOKUP_UPDATE,
      bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,
      bir_state_read_view_updates_def,bir_pc_next_def,
      bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,
      bir_programTheory.bir_exec_stmt_jmp_def,
      bir_programTheory.bir_exec_stmt_jmp_to_label_def,
      bir_eval_label_exp_def,bir_block_pc_def,
      bir_labels_of_program_spinlock_concrete]
    >> BasicProvers.every_case_tac
    >> gs[AllCaseEqs(),bir_programTheory.bir_state_set_typeerror_def,spinlock_ref_def,core_zoo,bst_pc_tuple_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 20w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    disj1_tac
    >> dxrule_then strip_assume_tac $ iffLR spinlock_ref_def
    >> gs[core_zoo,FLOOKUP_UPDATE,
      bst_pc_tuple_def,bir_read_core_reg_zero_def,
      bir_read_core_reg_nonzero_def,bir_pc_next_def]
    >> qmatch_assum_rename_tac `bir_read_core_reg _ cid cores _ v'`
    >> Cases_on `v' = 0w`
    >> gvs[bir_read_core_reg_def,bir_read_var_def]
    >- (
      drule_then assume_tac bir_exec_stmt_cjmp_second
      >> gs[core_zoo,bst_pc_tuple_def,core_zoo,spinlock_ref_def,FLOOKUP_UPDATE]
    )
    >> drule_then assume_tac bir_exec_stmt_cjmp_first
    >> gs[core_zoo,bst_pc_tuple_def,core_zoo,spinlock_ref_def,FLOOKUP_UPDATE]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
    >> Cases_on `s.bst_environ`
    >> qpat_x_assum `_ = bir_eval_exp_view _ _ _ _` mp_tac
    >> qpat_x_assum `_ = env_update_cast64 _ _ _ _` mp_tac
    >> EVAL_TAC
    >> rw[]
    >> fs[env_update_cast64_def]
    >> qpat_x_assum `_ = bir_env_update _ _ _ _` mp_tac
    >> EVAL_TAC
    >> rw[]
    >> csimp[core_zoo,FLOOKUP_UPDATE,bir_read_var_def,bir_read_core_reg_zero_def,bir_read_core_reg_def,bst_pc_tuple_def,bir_state_read_view_updates_def,bir_pc_next_def,bir_state_fulful_view_updates_def,bir_exec_stmt_cjmp_def,bir_programTheory.bir_exec_stmt_jmp_def,bir_programTheory.bir_exec_stmt_jmp_to_label_def,bir_eval_label_exp_def,bir_block_pc_def,bir_labels_of_program_spinlock_concrete,bir_read_core_reg_nonzero_def,bir_expTheory.bir_eval_exp_def,bir_envTheory.bir_env_check_type_def,bir_envTheory.bir_var_type_def,bir_envTheory.bir_var_name_def,bir_envTheory.bir_env_lookup_def,bir_envTheory.bir_env_lookup_type_def,bir_envTheory.bir_env_read_def,combinTheory.APPLY_UPDATE_THM,bir_valuesTheory.type_of_bir_val_def,bir_immTheory.type_of_bir_imm_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    simple_refl_step
  )
  (* jump statements *)
  >~ [`bmc_exec_general_stmt`]
  >> gvs[bir_get_stmt_spinlock_cprog_BSGen,bmc_exec_general_stmt_def]
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 0w)`,`s.bst_pc.bpc_index = 0`]
  >- (
    gvs[bir_exec_stmtB_noop_unchanged]
    >> simple_refl_step
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 4w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 12w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
    >> Cases_on `s.bst_environ`
    >> qhdtm_x_assum `bir_read_var` mp_tac
    >> EVAL_TAC
    >> rw[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 16w)`,`s.bst_pc.bpc_index = 1`]
  >- (
      dxrule_then assume_tac $ iffLR spinlock_ref_def
      >> gvs[core_zoo,bst_pc_tuple_def,bir_exec_stmtE_def,bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_exec_stmt_jmp_to_label_def,bir_labels_of_program_spinlock_concrete,bir_block_pc_def]
      >> qmatch_assum_rename_tac `bir_read_core_reg _ cid cores v`
      >> Cases_on `v = 0w`
      >- (
        (* success *)
        disj2_tac
        >> gvs[bir_read_core_reg_zero_def,bir_read_core_reg_nonzero_def,bir_read_core_reg_def,bir_read_var_def,core_zoo,FLOOKUP_UPDATE,spinlock_ref_def,bst_pc_tuple_def]
        >> qmatch_goalsub_rename_tac `(acores,ae,aM)`
        >> CONV_TAC $ RESORT_EXISTS_CONV rev
        >> qexists_tac `aM`
        >> dsimp[parstep_cases,parstep_tr_def,cstep_cases,clstep_cases,bir_get_current_statement_spinlock_abstract_BSGen,bir_get_current_statement_spinlock_abstract_BSExt]
        >> `?loc. mem_is_loc aM (LENGTH aM) loc` by (
          cheat
        )
        >> qmatch_asmsub_rename_tac `mem_is_loc _ _ loc`
        >> qexists_tac `<| crit := (ae.crit |+ (cid,F)) |>`
        >> cheat (* TODO *)
      )
      >> disj1_tac (* unsuccessful *)
      >> gs[core_zoo,spinlock_ref_def,FLOOKUP_UPDATE,bst_pc_tuple_def,bir_read_core_reg_def,bir_read_var_def,bir_read_core_reg_nonzero_def,bir_read_core_reg_zero_def]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 24w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 28w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
  >~ [`s.bst_pc.bpc_label = BL_Address (Imm64 32w)`,`s.bst_pc.bpc_index = 1`]
  >- (
    simple_refl_step >> EVAL_TAC >> fs[]
  )
QED


(* at most one core in the critical section *)
(* TODO not sufficient *)
Definition c_invariant_def:
  c_invariant cores <=>
    !cid cid' p s s'.
      FLOOKUP cores cid = SOME $ Core cid p s
      /\ FLOOKUP cores cid' = SOME $ Core cid' p s'
      /\ c_in_crit s /\ c_in_crit s'
      ==> cid = cid'
End

Theorem spinlock_ref_c_inv_ext_inv:
  !cid cores e M acores ae aM.
  spinlock_ref cid (cores,e,M) (acores,ae,aM)
  ==> c_invariant cores <=> ext_invariant ae
Proof
  fs[spinlock_ref_def]
  >> cheat
QED

(* at most one core in crit *)

Theorem parstep_preserves_c_inv:
  !cid cores e M cores' e' M'.
    parstep_tr cid (cores,e,M) (cores',e',M')
    /\ run_progc cores spinlock_concrete
    /\ c_invariant cores
    ==> c_invariant cores'
Proof
  rpt strip_tac
  >> `?acores ae aM as.
    spinlock_ref cid (cores,e,M) (acores,ae,aM) /\
    run_prog acores spinlock_abstract /\
    FLOOKUP acores cid = SOME (Core cid (spinlock_abstract cid) as)` by (
    cheat
  )
  >> drule_all_then strip_assume_tac parstep_preserves_spinlock_ref
  >> drule
  >> qspecl_then [`cid`] assume_tac spinlock_ref_c_inv_ext_inv
  >> gs[]
  >> gs[spinlock_ref_c_inv_ext_inv]

  >> drule_all_then assume_tac
  >> fs[parstep_tr_def]
  >> drule_then assume_tac spinlock_abstract_ext_invariant
  >> gvs[]
  >> cheat
QED


val _ = export_theory();
