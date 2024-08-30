(*
  Single Producer Single Consumer Queue implementation in multicore BIR syntax

  Requires the semantics to allow memory updates containing generic algebraic datatypes, like below `msg` with Enqueue and Dequeue
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory llistTheory wordsLib
     finite_mapTheory string_numTheory relationTheory
     bir_programTheory bir_promisingTheory
     bir_promising_wfTheory;

val _ = new_theory "example_spsc";

(*
 * memory contains the usual values and enqueue/dequeue messages
 * invariants:
 *  #dequeue <= #enqueue
 *  and dequeue_prop (TAKE (PRE n) M) (EL n M) holds for any 0 < n < LENGTH M
 *)

Datatype:
  msg = Enqueue bir_val_t | Dequeue bir_val_t
End

Definition is_dequeue_def:
  is_dequeue x = case x of Dequeue _ => T | _ => F
End

Definition dequeue_prop_def:
  dequeue_prop M msg =
    case msg of
    | INR $ Dequeue v =>
        (let enq = FILTER (λx. ISR x /\ ~(is_dequeue $ OUTR x)) M in
        let m = LENGTH $ FILTER (λx. ISR x /\ is_dequeue $ OUTR x) M
        and n = LENGTH enq
        in m < n /\ EL (m+1) enq = INR $ Enqueue v)
    | _ => T
End

(*
hd_addr: address where hd pointer resides
value: the w64 value to enqueue
enqueue_entry: pc of the enqueue method
jump_after: pc of where to jump after enqueuing
*)
Definition enqueue_def:
  enqueue hd_addr value enqueue_entry jump_after = MAP BBlock_Stmts [
    <|bb_label := BL_Address $ Imm64 enqueue_entry;
      bb_statements := [
        BMCStmt_Load (BVar "R2" $ BType_Imm Bit64)
          hd_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ enqueue_entry + 4w
    |>;
    <|bb_label := BL_Address $ Imm64 $ enqueue_entry + 4w;
      bb_statements := [
        BMCStmt_Store
          (BVar "success" $ BType_Imm Bit64)
          (BExp_Den $ BVar "R2" $ BType_Imm Bit64)
          (BExp_Const $ Imm64 value)
          F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ enqueue_entry + 8w
    |>;
    <|bb_label := BL_Address $ Imm64 $ enqueue_entry + 8w;
      bb_statements := [
        BMCStmt_Store
          (BVar "success" $ BType_Imm Bit64)
          hd_addr
          (BExp_BinExp BIExp_Plus
            (BExp_Den $ BVar "R2" $ BType_Imm Bit64)
            (* TODO correct assumption on memory layout? *)
            (BExp_Const $ Imm64 64w))
          F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 jump_after
    |>
  ]
End

(*
hd_addr: address where hd pointer resides (reg R2)
tl_addr: address where tl pointer resides (reg R1)
reg: register where to dequeue
dequeue_entry: pc of the dequeue method
jump_after: pc of where to jump after dequeuing
*)
Definition dequeue_def:
  dequeue hd_addr tl_addr reg dequeue_entry jump_after = MAP BBlock_Stmts [
    <|bb_label := BL_Address $ Imm64 dequeue_entry;
      bb_statements := [
        BMCStmt_Load (BVar "R1" $ BType_Imm Bit64)
          tl_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 4w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 4w;
      bb_statements := [
        BMCStmt_Load (BVar "R2" $ BType_Imm Bit64)
          hd_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 8w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 8w;
      bb_statements := [];
      bb_last_statement := 
        BStmt_CJmp
          (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "R1" (BType_Imm Bit64)))
              (BExp_Den (BVar "R2" (BType_Imm Bit64))))
          (BLE_Label $ BL_Address $ Imm64 dequeue_entry)
          (BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 12w)
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 12w;
      bb_statements := [
        BMCStmt_Load (BVar reg $ BType_Imm Bit64)
          (BExp_Den (BVar "R1" (BType_Imm Bit64)))
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 16w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 16w;
      bb_statements := [
        BMCStmt_Store
          (BVar "success" $ BType_Imm Bit64)
          tl_addr
          (BExp_BinExp BIExp_Plus
            (BExp_Den $ BVar "R1" $ BType_Imm Bit64)
            (* TODO correct assumption on memory layout? *)
            (BExp_Const $ Imm64 1w))
          F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 jump_after
    |>
  ]
End

(* TODO not currently compiling
   requires changed message type to sum-type *)

(*
(* use with tl_addr *)
Definition dequeue_abstract_def:
  dequeue_abstract addr label jump_after = [
  BBlock_Ext <|
      beb_label    := label
    ; beb_relation := (λ(s,((tp,M),prom)) s'.
      ?t.
        prom = [t] /\
        if (?m x. mem_get M addr t = SOME m
          /\ m.val = INR $ Dequeue x)
        then
          s' = (λs. s with bst_prom updated_by (remove_prom prom))
                $ bir_pc_label_upd jump_after
                $ bir_state_fulful_view_updates s t addr s.bst_v_CAP 0 F F F s
        else s = s'
    )
  |>]
End
*)

(*
(* use with hd_addr *)
Definition enqueue_abstract_def:
  enqueue_abstract addr label jump_after = [
  BBlock_Ext <|
      beb_label    := label
    ; beb_relation := (λ(s,((tp,M),prom)) s'.
      ?t.
        prom = [t] /\
        if (?m x. mem_get M addr t = SOME m
          /\ m.val = INR $ Enqueue x)
        then
          s' = (λs. s with bst_prom updated_by (remove_prom prom))
                $ bir_pc_label_upd jump_after
                $ bir_state_fulful_view_updates s t addr s.bst_v_CAP 0 F F F s
        else s = s'
    )
  |>]
End
*)

Definition spsc_enqueue_rel_def:
  (* head increased *)
  spsc_enqueue_rel as aM cs cM = T
End

val _ = export_theory();
