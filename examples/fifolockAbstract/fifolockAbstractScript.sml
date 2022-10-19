open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
val _ = new_theory "fifolockAbstract";

(*****************************************************************************)
(* Abstract fifo lock specification ******************************************)
(*****************************************************************************)
(* Pre:                                                                      *)
(* Post:                                                                     *)
(* Model variables:                                                          *)
(*  - queue: bool[32] list                                                   *)
(*  - cid: bool[32]                                                          *)
(*  - crit: bool initial 0 - Critical region flag                            *)
(* Specify the ghost state as record                                         *)
(*****************************************************************************)

Definition fifo_lock_aprog_def:
  fifo_lock_aprog cid =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* queue := queue::[cid] *) 
        BStmt_Gassign (fn gs => gs with queue updated_by fn x => APPEND x [cid]) ; 
      ];
    bb_last_statement :=
      (* goto 4w *)
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
  <|bb_label := BL_Address (Imm64 4w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
      ];
    bb_last_statement :=
      (* if head(queue) = cid then goto 8w else goto 4w *)
      BStmt_CJmp
        (BExp_BinPred BIExp_Equal
          (BExp_Const (BExp_Gexp (fn gs => (fn (hd::tl) => hd) gs.queue)))
          (BExp_Const (Imm32 cid)))
        (BLE_Label (BL_Address (Imm64 8w)))
        (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
  <|bb_label := BL_Address (Imm64 8w) "";
    bb_mc_tags := SOME <| mc_atomic := F; mc_acq := F; mc_rel := F|>
    bb_statements :=
      [
        (* crit = 1 *)
        BStmt_Gassign (fn gs => gs with crit updated_with fn x => 1) ;
      ];
    bb_last_statement :=
      (* goto 12w *)
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))
  |> ;
] ;
                
Definition fifo_unlock_aprog_def:
  fifo_unlock_aprog cid =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := F; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* crit = 0 *)
        BStmt_Gassign (fn gs => gs with crit updated_with fn x => 0) ;
        (* queue := tail(queue) *)
        BStmt_Gassign (fn gs => gs with queue updated_by fn (hd::tl) => tl) ;
      ];
    bb_last_statement :=
      (* goto 4w *)
      BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
] ;


