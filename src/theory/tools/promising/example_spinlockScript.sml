(*
  Spinlock abstract and concrete implementation in multicore BIR syntax
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory llistTheory wordsLib
     finite_mapTheory string_numTheory relationTheory
     bir_programTheory bir_promisingTheory
     bir_promising_wfTheory bir_programLib
     listTheory rich_listTheory arithmeticTheory
     promising_thmsTheory;

val _ = new_theory "example_spinlock";

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

(* program specific instantiations *)

Definition lock_var_def:
  lock_var = BVar "x7" $ BType_Imm Bit64
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

Definition bir_pc_label_def:
  bir_pc_label lbl s <=>
    s.bst_pc = <| bpc_label := lbl; bpc_index := 0 |>
End

Definition bir_pc_label_upd_def:
  bir_pc_label_upd lbl s <=>
    s with bst_pc := <| bpc_label := lbl; bpc_index := 0 |>
End

Definition in_lock_abstract_def:
  in_lock_abstract pc =
  !lbl index.
    bst_pc_tuple pc = (BL_Address $ Imm64 lbl, index)
    ==> 0w <= lbl /\ lbl <= 20w
      /\ (lbl = 0w ==> index = 1)
End

Definition in_unlock_abstract_def:
  in_unlock_abstract pc =
  !lbl index.
    bst_pc_tuple pc = (BL_Address $ Imm64 lbl, index)
    ==> 24w <= lbl /\ lbl <= 36w
      /\ (lbl = 24w ==> index = 1)
End

Definition spinlock_abstract_locking_def:
  spinlock_abstract_locking lock_addr label jump_after = [
  BBlock_Ext <|
      beb_label    := label
    ; beb_relation := (λ(s,(M,prom)) s'.
      ?t.
        prom = [t] /\
        if (?m. mem_get M lock_addr t = SOME m
          /\ m.val = BVal_Imm $ Imm64 1w) (* 1w = locked *)
        then
          s' = (λs. s with bst_prom updated_by (remove_prom prom))
                $ bir_pc_label_upd jump_after
                $ bir_state_fulful_view_updates s t lock_addr s.bst_v_CAP 0 T F F s
        else s = s'
    )
  |>]
End

Definition spinlock_abstract_unlocking_def:
  spinlock_abstract_unlocking lock_addr label jump_after = [
  BBlock_Ext <|
      beb_label    := label
    ; beb_relation := (λ(s,(M,prom)) s'.
      ?t. mem_is_loc M t lock_addr /\ prom = [t]
      (* bir_state_read_view_updates s t loc v_addr v_post acq rel xcl *)
      /\ s' = (λs. s with bst_prom updated_by (remove_prom prom))
              $ fence_updates BM_ReadWrite BM_Write
              $ bir_pc_label_upd jump_after
              $ bir_state_fulful_view_updates s t lock_addr s.bst_v_CAP 0 F F F s
    )
  |>]
End

Theorem bir_get_current_statement_spinlock_abstract_locking_BSExt =
  `bir_get_current_statement (BirProgram (spinlock_abstract_locking lock_addr_val lock_entry jump_after_lock) : progc_t) s.bst_pc = SOME $ BSExt R`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_current_statement_spinlock_abstract_locking_BSGen =
  `bir_get_current_statement (BirProgram (spinlock_abstract_locking lock_addr_val lock_entry jump_after_lock) : progc_t) s.bst_pc = SOME $ BSGen stmt`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

Theorem bir_get_current_statement_spinlock_abstract_unlocking_BSExt =
  `bir_get_current_statement (BirProgram (spinlock_abstract_unlocking lock_addr_val unlock_entry jump_after_unlock) : progc_t) s.bst_pc = SOME $ BSExt R`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_current_statement_spinlock_abstract_unlocking_BSGen =
  `bir_get_current_statement (BirProgram (spinlock_abstract_unlocking lock_addr_val unlock_entry jump_after_unlock) : progc_t) s.bst_pc = SOME $ BSGen stmt`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

(* abstract spinlock program without other blocks *)

Definition spinlock_abstract_def:
  spinlock_abstract : progc_t
  = BirProgram (
    spinlock_abstract_locking lock_addr_val (BL_Address $ Imm64 0w) (BL_Address $ Imm64 4w)
    ++ spinlock_abstract_unlocking lock_addr_val (BL_Address $ Imm64 4w) (BL_Address $ Imm64 8w)
  )
End

Theorem bir_get_current_statement_spinlock_abstract_BSExt =
  `bir_get_current_statement spinlock_abstract s.bst_pc = SOME $ BSExt R`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []

Theorem bir_get_current_statement_spinlock_abstract_BSGen =
  `bir_get_current_statement spinlock_abstract as.bst_pc = SOME $ BSGen stmt`
  |> EVAL o Term
  |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AllCaseEqs(),wordsTheory.NUMERAL_LESS_THM]
  |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss) []
  |> GEN_ALL

(* abstract spinlock program with blocks *)

Definition spinlock_abstract2_def:
  spinlock_abstract2
  blocks lock_entry jump_after_lock unlock_entry jump_after_unlock : progc_t
  = BirProgram (
    spinlock_abstract_locking lock_addr_val lock_entry jump_after_lock
    ++ spinlock_abstract_unlocking lock_addr_val unlock_entry jump_after_unlock
    ++ blocks
  )
End

(* lock blocks with entry *)
Definition lock_def:
  lock lock_addr lock_entry jump_after = MAP BBlock_Stmts [
(* lr.w.aq	t0,(t2) *)
    <|bb_label := BL_Address $ Imm64 lock_entry;
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
      bb_statements := [];
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
      bb_statements := [
        BMCStmt_Assign (BVar "x5" $ BType_Imm Bit64) (BExp_Const $ Imm64 1w)
      ];
      bb_last_statement :=
        BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ lock_entry + 12w|>;
(* sc.w	t1,t0,(t2) *)
    <|bb_label := BL_Address $ Imm64 $ lock_entry + 12w;
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
      bb_statements := [];
      bb_last_statement :=
        BStmt_CJmp
          (BExp_UnaryExp BIExp_Not
              (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "success" (BType_Imm Bit64)))
                (BExp_Const v_succ)))
          (BLE_Label (BL_Address $ Imm64 lock_entry))
          (* jump to next instruction (in sequence) *)
          (BLE_Label jump_after)|>
  ]
End

Definition unlock_def:
  unlock lock_addr unlock_entry jump_after_unlock = MAP BBlock_Stmts [
(* li	t0,0 *)
    <|bb_label := BL_Address $ Imm64 unlock_entry;
      bb_statements :=
        [BMCStmt_Assign (BVar "x5" $ BType_Imm Bit64) (BExp_Const $ Imm64 0w)];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ unlock_entry + 4w |>;
(* fence	rw,w *)
    <|bb_label := BL_Address $ Imm64 $ unlock_entry + 4w ;
      bb_statements := [BMCStmt_Fence BM_ReadWrite BM_Write];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ unlock_entry + 8w |>;
(* sw	zero,0(t2) *)
    <|bb_label := BL_Address $ Imm64 $ unlock_entry + 8w;
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
      (* jump to next instruction (in sequence) *)
      bb_last_statement := BStmt_Jmp $ BLE_Label $ jump_after_unlock |>
  ]
End

Theorem lock_NOT_NULL =
  EVAL o Term $ `NULL $ lock _ _ _`
Theorem lock_bir_pc_first =
  EVAL o Term $ `bir_pc_first $ BirProgram (lock _ _ _) : progc_t`
Theorem bir_labels_of_program_lock =
  blop_prog_labels_thm ``BirProgram $ lock lock_addr' lock_entry jump_after``

Theorem unlock_NOT_NULL =
  EVAL o Term $ `NULL $ unlock _ _ _`
Theorem unlock_bir_pc_first =
  EVAL o Term $ `bir_pc_first $ BirProgram (unlock _ _ _) : progc_t`
Theorem bir_labels_of_program_unlock =
  blop_prog_labels_thm ``BirProgram $ unlock lock_addr' unlock_entry _``


(* old definition without additional blocks *)
Definition spinlock_concrete_def:
  spinlock_concrete : progc_t
  = BirProgram $
  [
    BBlock_Stmts <|bb_label := BL_Address (Imm64 0w);
        bb_statements :=
          [
          (* no-op *)
          BMCStmt_Assert (BExp_Const $ Imm1 1w)
          (* BMCStmt_Assign lock_var (BExp_Const $ Imm64 42w) *)
          ];
        bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 4w|>;
  ]
  (* lock lock_addr lock_entry jump_after *)
  ++ lock lock_addr 4w (BL_Address $ Imm64 24w)
  (* unlock lock_addr unlock_entry jump_after_unlock *)
  ++ unlock lock_addr 24w (BL_Address $ Imm64 $ 24w+12w)
End

Definition lock_wrap_def:
  lock_wrap lock_addr lock_entry jump_after unlock_entry blocks =
    lock lock_addr lock_entry jump_after ++ blocks
    ++ unlock lock_addr unlock_entry (BL_Address $ Imm64 $ unlock_entry + 12w)
End

Definition spinlock_concrete2_def:
  spinlock_concrete2 blocks jump_after unlock_entry : progc_t =
  (BirProgram $ lock_wrap lock_addr 0w jump_after unlock_entry blocks)
    : progc_t
End

Theorem bgcs_lock_zoo =
  bgcs_bmc_prog_thms ``BirProgram $ lock lock_addr 0w jump_after``;

Theorem bgcs_unlock_zoo =
  bgcs_bmc_prog_thms ``BirProgram $ unlock lock_addr' unlock_entry jump_after_unlock``;

Theorem bir_get_spinlock_cprog_zoo =
  bgcs_bmc_prog_thms ``spinlock_concrete``

val _ = export_theory();
