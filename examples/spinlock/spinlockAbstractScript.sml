open HolKernel Parse boolLib bossLib;
open bir_multicoreTheory ;

val _ = new_theory "spinlockAbstract";

(*
  (* reg, address, cast, xcl, acq rel *)
  | BMCStmt_Load bir_var_t bir_exp_t ((bir_cast_t # bir_immtype_t) option) bool bool bool
  (* success reg, address, value, xcl, acq, rel *)
  | BMCStmt_Store bir_var_t bir_exp_t bir_exp_t bool bool bool
  (* success reg, address, value, acq, rel *)
  | BMCStmt_Amo bir_var_t bir_exp_t bir_exp_t bool bool
  | BMCStmt_Expr bir_var_t bir_exp_t
  | BMCStmt_Fence bmc_memop_t bmc_memop_t
  | BMCStmt_Branch bir_exp_t bir_label_exp_t bir_label_exp_t
  | BMCStmt_Generic ('a bir_stmt_t) (* TODO remove polymorphism *)
*)

Definition spinlock_aprog_def:
  spinlock_aprog dummy_loc =
  BirProgram [
  (* lock block *)
  <|bb_label := BL_Address_HC (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [
        BMCStmt_Expr (BVar "_is_locked" $ BType_Imm Bit64)
          $ BExp_Den $ BVar "_crit" $ BType_Imm Bit64 ;
        (* note core id in critical section *)
        BMCStmt_Expr (BVar "_crit_cid" $ BType_Imm Bit64)
            $ BExp_IfThenElse
                (BExp_Cast BIExp_SignedCast
                  (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
                (BExp_Den $ BVar "_crit_cid" $ BType_Imm Bit64)
                (BExp_Const $ Imm64 $ n2w cid);
        (* lock if possible *)
        BMCStmt_Expr (BVar "_crit" $ BType_Imm Bit64)
            $ BExp_IfThenElse
                (BExp_Cast BIExp_SignedCast
                  (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
                (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
                (BExp_Const $ Imm64 1w);
      ];
    (* spin on _is_locked *)
    bb_last_statement :=
        BStmt_CJmp
          (BExp_Cast BIExp_SignedCast
            (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
          (BLE_Label $ BL_Address $ Imm64 0w)
          (BLE_Label $ BL_Address $ Imm64 4w);
  |>;

  (* load reserved on fresh dummy variable *)

  <|bb_label := BL_Address_HC (Imm64 4w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := T; mc_rel := F|>; (* TODO remove all but atomic *)
    bb_statements :=
      [
        BMCStmt_Generic $ BStmtB $ BStmt_Assert
          $ BExp_Aligned Bit64 2 $ BExp_Den $ BVar dummy_loc $ BType_Imm Bit64;
        BMCStmt_Load (BVar "_ignore" (BType_Imm Bit64))
          (BExp_Den $ BVar dummy_loc $ BType_Imm Bit64)
          cast T T F
      ];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;

  (* unlock *)
  <|bb_label := BL_Address_HC (Imm64 8w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>; (* TODO remove all but atomic *)
    bb_statements :=
      [
      (* free *)
      BMCStmt_Expr (BVar "_crit" $ BType_Imm Bit64) $ BExp_Const $ Imm64 0w;
      ];
    bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 12w
  |>;

  (* store conditional on same dummy variable *)
  <|bb_label := BL_Address_HC (Imm64 12w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements :=
      [ BMCStmt_Generic $ BStmtB $ BStmt_Assert
          (BExp_Aligned Bit64 2 $ BExp_Den $ BVar dummy_loc $ BType_Imm Bit64);
        BMCStmt_Generic $ BStmtB $ BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
            (BExp_Den (BVar dummy_loc $ BType_Imm Bit64)) 4);
        BMCStmt_Store (BVar "_ignore" (BType_Imm Bit64))  
          (BExp_Den (BVar dummy_loc $ BType_Imm Bit64))
          (BExp_Const (Imm64 0w))
          F F T
        ];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;

  ] : string bir_program_t
End

val _ = export_theory();
