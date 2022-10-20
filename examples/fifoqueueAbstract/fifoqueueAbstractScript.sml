open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_lifter_interfaceLib ;
open bir_promisingTheory ;
open tracesTheory ;
val _ = new_theory "fifoqueueAbstract";

Definition noop_def:
  BStmt_Noop = BStmt_Assert (BExp_Const (Imm64 1w)) ;

(*****************************************************************************)
(* Abstract blocking fifo queue specification ********************************)
(*****************************************************************************)

(*****************************************************************************)
(* fifo_queue_enq_aprog                                                      *)
(* Pre:                                                                      *)
(* Post: queue' = APPEND queue [R]                                           *)
(* Model variables:                                                          *)
(*  - queue: bool[64] list                                                   *)
(*  - qSize: nat                                                             *)
(*  - capacity: nat                                                          *)
(*****************************************************************************)

(* fifo_queue_enq_aprog: Argument bool[64] passed in register arg0           *)

Definition fifo_queue_enq_aprog_def:
  fifo_queue_enq_aprog =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* tryagain := qSize = capacity *)
        BStmt_Assign
          (BVar "tryagain" (BType_Imm Bit1))
          (BIExp_Equal
            (BExp_Gexp (fn gs => (fn (hd::tl) => hd) gs.qSize))
            (BExp_Gexp (fn gs => (fn (hd::tl) => hd) gs.capacity))) ;
        (* if tryagain then ignore = ignore else queue = APPEND queue [v] *)
        BStmt_IfThenElse
          (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
          (BStmt_Noop)
          (BStmt_Gassign ((fn gs => gs with queue updated_with fn x => APPEND x (BExp_Den BVar "arg0" (BType_Imm Bit64))))) ;
        BStmt_IfThenElse
          (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
          (BStmt_Noop)
          (BStmt_Gassign ((fn gs => gs with qSize updated_with fn x => x + 1)))
      ] ;
    bb_last_statement :=
      BStmt_CJmp 
        (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
        (BLE_Label (BL_Address (Imm64 0w)))
        (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
] ;

Definition fifo_queue_deq_aprog_def:
  fifo_queue_enq_aprog =
  BirProgram [
  <|bb_label := BL_Address (Imm64 0w) "";
    bb_mc_tags := SOME <|mc_atomic := T; mc_acq := F; mc_rel := F|>;
    bb_statements := 
      [
        (* tryagain := qSize = capacity *)
        BStmt_Assign
          (BVar "tryagain" (BType_Imm Bit1))
          (BIExp_Equal
            (BExp_Gexp (fn gs => gs.qSize))
            (BExp_Gexp (fn gs => 0))) ;
        (* if tryagain then ignore = ignore else queue = APPEND queue [v] *)
        BStmt_IfThenElse
          (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
          (BStmt_Noop)
          (BStmt_Gassign ((fn gs => gs with queue updated_with fn (hd::tl) => tl))) ;
        BStmt_IfThenElse
          (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
          (BStmt_Noop)
          (BStmt_Gassign ((fn gs => gs with qSize updated_with fn x => x - 1)))
      ] ;
    bb_last_statement :=
      BStmt_CJmp 
        (BExp_Den (BVar "tryagain" (BType_Imm Bit1)))
        (BLE_Label (BL_Address (Imm64 0w)))
        (BLE_Label (BL_Address (Imm64 4w)))
  |> ;
] ;



