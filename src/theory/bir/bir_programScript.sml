open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_expTheory;
open llistTheory wordsLib;
open finite_mapTheory;
open string_numTheory;
open relationTheory;

val _ = new_theory "bir_program";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_label_t =
    BL_Label string
  | BL_Address bir_imm_t
`;

val _ = Datatype `bir_label_exp_t =
    BLE_Label bir_label_t
  | BLE_Exp ('ext_state_t bir_exp_t)
`;

val _ = Datatype `bir_memop_t =
    BM_Read
  | BM_Write
  | BM_ReadWrite
`;

(*
  Assign variable expression
  Assert expression
  Assume expression
  ExtPut externName expression
*)
Datatype:
  bir_stmt_basic_t =
  | BStmt_Assign bir_var_t ('ext_state_t bir_exp_t)
  | BStmt_Assert ('ext_state_t bir_exp_t)
  | BStmt_Assume ('ext_state_t bir_exp_t)
(*  | BStmt_ExtPut string bir_exp_t (* string should be looked up as a (bir_val_t -> 'ext_state_t -> 'ext_state_t option) *) *)
End

Datatype:
  bmc_stmt_basic_t =
  (* reg, address, cast, xcl, acq rel *)
  | BMCStmt_Load bir_var_t ('ext_state_t bir_exp_t) ((bir_cast_t # bir_immtype_t) option) bool bool bool
  (* success reg, address, value, xcl, acq, rel *)
  | BMCStmt_Store bir_var_t ('ext_state_t bir_exp_t) ('ext_state_t bir_exp_t) bool bool bool
  (* success reg, address, value, acq, rel *)
  | BMCStmt_Amo bir_var_t ('ext_state_t bir_exp_t) ('ext_state_t bir_exp_t) bool bool
  | BMCStmt_Assign bir_var_t ('ext_state_t bir_exp_t)
  | BMCStmt_Fence bir_memop_t bir_memop_t
  (* TODO: Should take view of the input *)
(*  | BMCStmt_ExtPut string ('ext_state_t bir_exp_t) *)
  | BMCStmt_Assert ('ext_state_t bir_exp_t)
  | BMCStmt_Assume ('ext_state_t bir_exp_t)
End

Datatype:
  bir_stmt_end_t =
  | BStmt_Jmp     ('ext_state_t bir_label_exp_t)
  | BStmt_CJmp    ('ext_state_t bir_exp_t) ('ext_state_t bir_label_exp_t) ('ext_state_t bir_label_exp_t)
  | BStmt_Halt    ('ext_state_t bir_exp_t)
End

Datatype:
  bir_generic_stmt_t =
  | BStmtB 'a
  | BStmtE ('ext_state_t bir_stmt_end_t)
End

Type bir_stmt_t = ``:('ext_state_t bir_stmt_basic_t,'ext_state_t) bir_generic_stmt_t``
Type bmc_stmt_t = ``:('ext_state_t bmc_stmt_basic_t,'ext_state_t) bir_generic_stmt_t``

val _ = Datatype `bir_mc_tags_t = <|
  mc_acq            : bool;
  mc_rel            : bool;
  mc_atomic         : bool |>`;

val _ = Datatype `bir_programcounter_t = <| bpc_label:bir_label_t; bpc_index:num |>`;

val bir_pc_ss = rewrites (type_rws ``:bir_programcounter_t``);

val _ = Datatype `bir_status_t =
    BST_Running                  (* BIR program is still running *)
  | BST_TypeError                (* BIR program execution encountered a type error *)
  | BST_Failed                   (* BIR program execution failed, should not happen when starting in a state where pc is available in the program to execute *)
  | BST_AssumptionViolated       (* BIR program execution aborted, because assumption was violated *)
  | BST_AssertionViolated       (* BIR program execution failed, because assertion was violated *)
  | BST_Halted bir_val_t        (* Halt called *)
  | BST_JumpOutside bir_label_t (* Jump to unknown label *)`;

(* forward buffer, part of the core-local state *)
Datatype:
  fwdb_t = <| fwdb_time : num; fwdb_view : num; fwdb_xcl : bool |>
End

(* exclusives bank, part of the core-local state *)
Datatype:
  xclb_t = <| xclb_time : num; xclb_view : num |>
End

Datatype:
  bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t;
  bst_viewenv  : bir_var_t |-> num;
  bst_coh      : bir_val_t -> num;
  bst_v_rOld   : num;
  bst_v_wOld   : num;
  bst_v_rNew   : num;
  bst_v_wNew   : num;
  bst_v_CAP    : num;
  bst_v_Rel    : num;
  bst_prom     : num list;
  bst_fwdb     : bir_val_t -> fwdb_t;
  bst_xclb     : xclb_t option;
|>
End

Type beb_relation_t =
  ``: (bir_state_t # (bir_state_t -> bool) # 'ext_state_t)
    -> (bir_state_t # 'ext_state_t) -> bool``

val _ = Datatype `bir_generic_stmt_block_t = <|
  bb_label          : bir_label_t;
  bb_mc_tags        : bir_mc_tags_t option;
  bb_statements     : 'a list;
  bb_last_statement : 'ext_state_t bir_stmt_end_t |>`;

val _ = Datatype `bir_ext_block_t = <|
  beb_label          : bir_label_t;
  (* TODO: If this relation also has the BIR program on LHS, we can model block-relative jumps (i.e. "next block") *)
  beb_relation     : 'ext_state_t beb_relation_t |>`;

val _ = Datatype `bir_generic_block_t =
  | BBlock_Stmts (('a,'ext_state_t)  bir_generic_stmt_block_t)
  | BBlock_Ext ('ext_state_t bir_ext_block_t)`;

Datatype:
  bir_generic_program_t = BirProgram ((('a, 'ext_state_t) bir_generic_block_t) list)
End

Type bir_block_t = `` :('ext_state_t bir_stmt_basic_t, 'ext_state_t) bir_generic_block_t``
Type bmc_block_t = `` :('ext_state_t bmc_stmt_basic_t, 'ext_state_t) bir_generic_block_t``

Type bir_program_t = ``:('ext_state_t bir_stmt_basic_t, 'ext_state_t) bir_generic_program_t``
Type bmc_program_t = ``:('ext_state_t bmc_stmt_basic_t, 'ext_state_t) bir_generic_program_t``

val bir_state_t_component_equality = DB.fetch "-" "bir_state_t_component_equality";
val bir_programcounter_t_component_equality = DB.fetch "-" "bir_programcounter_t_component_equality";

(*
TODO
val bir_state_ss = rewrites (type_rws ``:bir_state_t``);
val bir_status_ss = rewrites (type_rws ``:bir_status_t``);

val bir_stmt_ss = rewrites ((type_rws ``:'ext_state_t bir_stmt_t``)
                    @ (type_rws ``:'ext_state_t bir_stmt_end_t``)
                    @ (type_rws ``:'ext_state_t bir_stmt_basic_t``));
*)

(* ------------------------------------------------------------------------- *)
(* Programs                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition bir_block_is_extern_def:
  bir_block_is_extern bl =
    case bl of
    | BBlock_Stmts stmts_bl => F
    | BBlock_Ext ext_bl => T
End

val bir_label_of_block_def = Define `bir_label_of_block bl =
  case bl of
  | BBlock_Stmts stmts_bl => stmts_bl.bb_label
  | BBlock_Ext ext_bl => ext_bl.beb_label`;

val bir_labels_of_program_def = Define `bir_labels_of_program (BirProgram p) =
  MAP (\bl. bir_label_of_block bl) p`;

val bir_get_program_block_info_by_label_def = Define `bir_get_program_block_info_by_label
  (BirProgram p) l = INDEX_FIND 0 (\ x. bir_label_of_block x = l) p
`;

val bir_get_program_block_info_by_label_THM = store_thm ("bir_get_program_block_info_by_label_THM",
  ``(!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bir_label_of_block bl <> l)))) /\

    (!p l i bl.
          (bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
          ((((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bir_label_of_block bl = l) /\
             (!j'. j' < i ==> bir_label_of_block (EL j' p) <> l))))``,

SIMP_TAC list_ss [bir_get_program_block_info_by_label_def, INDEX_FIND_EQ_NONE,
  listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0]);


val bir_get_program_block_info_by_label_MEM = store_thm ("bir_get_program_block_info_by_label_MEM",
  ``!p l. MEM l (bir_labels_of_program p) <=>
          (?i bl. bir_get_program_block_info_by_label p l = SOME (i, bl))``,

Cases_on `p` >> rename1 `BirProgram p` >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_labels_of_program_def, listTheory.MEM_MAP] >>
Cases_on `bir_get_program_block_info_by_label (BirProgram p) l` >| [
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM] >>
  METIS_TAC[],

  rename1 `_ = SOME ibl` >>
  Cases_on `ibl` >>
  FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM, listTheory.MEM_EL,
    GSYM RIGHT_EXISTS_AND_THM] >>
  METIS_TAC[]
]);


(* ------------------------------------------------------------------------- *)
(*  Program Counter                                                          *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_stmt_kind_t =
    | BSGen (('a,'ext_state_t) bir_generic_stmt_t)
    | BSExt ('ext_state_t beb_relation_t)
End

val bir_get_current_statement_def = Define `bir_get_current_statement p pc =
  option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE
    (\ (_, bl).
      case bl of
      | BBlock_Stmts stmts_bl =>
        if (pc.bpc_index < LENGTH stmts_bl.bb_statements)
        then SOME (BSGen $ BStmtB (EL (pc.bpc_index) stmts_bl.bb_statements))
        else if pc.bpc_index = LENGTH stmts_bl.bb_statements
          then SOME $ BSGen $ BStmtE stmts_bl.bb_last_statement else NONE
      | BBlock_Ext ext_bl => SOME $ BSExt ext_bl.beb_relation )`;

Definition bir_get_current_block_def:
  bir_get_current_block p pc =
  option_CASE (bir_get_program_block_info_by_label p pc.bpc_label) NONE
    (\ (_, bl). SOME bl)
End

val bir_pc_next_def = Define `
  bir_pc_next pc = pc with bpc_index updated_by SUC`;

val bir_block_pc_def = Define `bir_block_pc l = <| bpc_label := l; bpc_index := 0 |>`

val bir_block_pc_11 = store_thm ("bir_block_pc_11",
``!l1 l2. (bir_block_pc l1 = bir_block_pc l2) <=> (l1 = l2)``,
SIMP_TAC (std_ss++bir_pc_ss) [bir_block_pc_def, bir_programcounter_t_component_equality]);

val bir_pc_first_def = Define
  `bir_pc_first (BirProgram p) = bir_block_pc (bir_label_of_block (HD p))`;


(* ------------------------------------------------------------------------- *)
(*  Program State                                                            *)
(* ------------------------------------------------------------------------- *)

val bir_state_is_terminated_def = Define `bir_state_is_terminated st =
  (st.bst_status <> BST_Running)`;

val bir_state_is_terminated_IMP = store_thm ("bir_state_is_terminated_IMP",
  ``(!st. (st.bst_status = BST_Running) ==> ~(bir_state_is_terminated st)) /\
    (!st. (st.bst_status <> BST_Running) ==> (bir_state_is_terminated st))``,
  SIMP_TAC std_ss [bir_state_is_terminated_def]);

val bir_state_set_typeerror_def = Define `bir_state_set_typeerror st =
  (st with bst_status := BST_TypeError)`;
val bir_state_set_failed_def = Define `bir_state_set_failed st =
  (st with bst_status := BST_Failed)`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

Definition bir_exec_stmt_assign_def:
  bir_exec_stmt_assign v ex (st:bir_state_t, ext_st:'ext_state_t) =
   case bir_eval_exp ex st.bst_environ ext_st of
     | SOME va => (case bir_env_write v va st.bst_environ of
                     | SOME env => (st with bst_environ := env)
                     | NONE => bir_state_set_typeerror st
                  )
     | NONE => bir_state_set_typeerror st
End

Definition bir_exec_stmt_assert_def:
  bir_exec_stmt_assert ex (st:bir_state_t, ext_st :'ext_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ ext_st) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssertionViolated)
    | NONE => bir_state_set_typeerror st
End

Definition bir_exec_stmt_assume_def:
  bir_exec_stmt_assume ex (st:bir_state_t, ext_st : 'ext_state_t) =
  case (option_CASE (bir_eval_exp ex st.bst_environ ext_st) NONE bir_dest_bool_val) of
    | SOME T => st
    | SOME F => (st with bst_status := BST_AssumptionViolated)
    | NONE => bir_state_set_typeerror st
End

(*
val bir_exec_stmt_ext_put_def = Define `bir_exec_stmt_ext_put (ext_name:string) ex (st:bir_state_t, ext_st:'ext_state_t) =
  case bir_eval_exp ex st.bst_environ ext_st of
    | SOME va =>
     (case bir_lookup_put ext_name of
      | SOME f =>
       (case f va ext_st of
         | SOME ext_st' => (st, ext_st')
         | NONE => (bir_state_set_typeerror st, ext_st)
       )
      | NONE => (bir_state_set_typeerror st, ext_st)
     )
    | NONE => (bir_state_set_typeerror st, ext_st)`;
*)

val bir_exec_stmtB_def = Define `
  (bir_exec_stmtB (BStmt_Assert ex) (st: bir_state_t, ext_st:'ext_state_t) = (bir_exec_stmt_assert ex (st, ext_st), ext_st)) /\
  (bir_exec_stmtB (BStmt_Assume ex) (st, ext_st) = (bir_exec_stmt_assume ex (st, ext_st), ext_st)) /\
  (bir_exec_stmtB (BStmt_Assign v ex) (st, ext_st) = (bir_exec_stmt_assign v ex (st, ext_st), ext_st)) (*/\
  (bir_exec_stmtB (BStmt_ExtPut ext_name ex) (st, ext_st) = bir_exec_stmt_ext_put ext_name ex (st, ext_st))*)`;

val bir_exec_stmtB_exists =
  store_thm("bir_exec_stmtB_exists",
  ``!h st ext_st:'ext_state_t.
      ?st' ext_st'.
        bir_exec_stmtB h (st, ext_st) = (st', ext_st')``,

Cases_on `h` >> (
  rpt strip_tac >>
  fs [bir_exec_stmtB_def]
)(* >>
fs [bir_exec_stmt_ext_put_def] >>
Cases_on `bir_eval_exp b st.bst_environ ext_st` >> (
  fs []
) >>
Cases_on `bir_lookup_put s` >> (
  fs []
) >>
Cases_on `x' x ext_st` >> (
  fs []
) *)
);

val bir_exec_stmt_halt_def = Define `bir_exec_stmt_halt ex (st:bir_state_t, ext_st:'ext_state_t) =
  case bir_eval_exp ex st.bst_environ ext_st of
    | NONE => bir_state_set_typeerror st
    | SOME v => st with bst_status := BST_Halted v`;

val bir_exec_stmt_jmp_to_label_def = Define `bir_exec_stmt_jmp_to_label p l st =
    if (MEM l (bir_labels_of_program p)) then
      st with bst_pc := bir_block_pc l
    else (st with bst_status := (BST_JumpOutside l))`;

val bir_eval_label_exp_def = Define `
   (bir_eval_label_exp (BLE_Label l) env (ext_st:'ext_state_t) = SOME l) /\
   (bir_eval_label_exp (BLE_Exp e) env ext_st = case bir_eval_exp e env ext_st of
      | SOME (BVal_Imm i) => SOME (BL_Address i)
      | _ => NONE
   )`;

val bir_exec_stmt_jmp_def = Define `bir_exec_stmt_jmp p le (st, ext_st:'ext_state_t) =
    case bir_eval_label_exp le st.bst_environ ext_st of
      | NONE => bir_state_set_typeerror st
      | SOME l => bir_exec_stmt_jmp_to_label p l st`;

val bir_exec_stmt_cjmp_def = Define `bir_exec_stmt_cjmp p ec l1 l2 (st, ext_st:'ext_state_t) =
  let
    vobc = option_CASE (bir_eval_exp ec st.bst_environ ext_st) NONE bir_dest_bool_val
  in
  case vobc of
    | SOME T => bir_exec_stmt_jmp p l1 (st, ext_st)
    | SOME F => bir_exec_stmt_jmp p l2 (st, ext_st)
    | NONE => bir_state_set_typeerror st`;


val bir_exec_stmtE_def = Define `
  (bir_exec_stmtE p (BStmt_Jmp l) (st, ext_st:'ext_state_t) = bir_exec_stmt_jmp p l (st, ext_st)) /\
  (bir_exec_stmtE p (BStmt_CJmp e l1 l2) (st, ext_st) = bir_exec_stmt_cjmp p e l1 l2 (st, ext_st)) /\
  (bir_exec_stmtE p (BStmt_Halt ex) (st, ext_st) = bir_exec_stmt_halt ex (st, ext_st))`;


val bir_exec_stmt_def = Define `
  (bir_exec_stmt p (BStmtB (bst:'ext_state_t bir_stmt_basic_t)) (st:bir_state_t, ext_st:'ext_state_t) =
     let (st', ext_st') = bir_exec_stmtB bst (st, ext_st) in
     if bir_state_is_terminated st' then (st', ext_st') else (st' with bst_pc updated_by bir_pc_next, ext_st')) /\
  (bir_exec_stmt p (BStmtE bst) (st, ext_st) = (bir_exec_stmtE p bst (st, ext_st), ext_st))`;

(* bmc_exec_block_ext is defined later, in the promising semantics *)
Definition bir_exec_block_ext_def:
  bir_exec_block_ext ext_fun (st:bir_state_t, ext_st:'ext_state_t) =
    (CHOICE (ext_fun (st, EMPTY:bir_state_t -> bool, ext_st))):(bir_state_t # 'ext_state_t)
End

Definition bir_exec_step_def:
  bir_exec_step p (state : bir_state_t, ext_st:'ext_state_t) =
  if (bir_state_is_terminated state) then (state, ext_st) else
  case (bir_get_current_block p state.bst_pc) of
  | NONE => (bir_state_set_failed state, ext_st)
  | SOME bl =>
    (case bl of
     | BBlock_Stmts stmts_bl =>
       (case (bir_get_current_statement p state.bst_pc) of
        | NONE => (bir_state_set_failed state, ext_st)
        | SOME $ BSGen stm => bir_exec_stmt p stm (state, ext_st)
        | SOME $ BSExt rel => bir_exec_block_ext rel (state, ext_st))
     | BBlock_Ext ext_bl => bir_exec_block_ext ext_bl.beb_relation (state, ext_st))
End


(* ------------------------------------------------------------------------- *)
(*  Executing multiple steps                                                 *)
(* ------------------------------------------------------------------------- *)

(* In the following, we really try to define bir_exec_steps_opt below. However,
   doing so is a bit tricky. To get there, first multiple definitions about
   observations and iterating infinitely often are needed. *)


(******************************)
(* executing infinitely often *)
(******************************)

val bir_exec_infinite_steps_fun_def = Define `
  (bir_exec_infinite_steps_fun p (st, ext_st:'ext_state_t) n = FUNPOW (bir_exec_step p) n (st,ext_st))`;


val bir_exec_infinite_steps_fun_REWRS = store_thm ("bir_exec_infinite_steps_fun_REWRS",
``(!p st ext_st. (bir_exec_infinite_steps_fun p (st, ext_st:'ext_state_t) 0 = (st, ext_st))) /\
  (!p st ext_st n. (bir_exec_infinite_steps_fun p (st, ext_st:'ext_state_t) (SUC n) =
     (bir_exec_infinite_steps_fun p (bir_exec_step p (st, ext_st)) n)))``,

SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def, arithmeticTheory.FUNPOW] >>
rpt strip_tac >>
Cases_on `(bir_exec_step p (st,ext_st))` >>
fs[bir_exec_infinite_steps_fun_def]);


val bir_state_COUNT_PC_def = Define `bir_state_COUNT_PC (count_failing:bool, pc_cond) (st, ext_st:'ext_state_t) =
  case st.bst_status of
    | BST_JumpOutside l => pc_cond (bir_block_pc l)
    | BST_Running => pc_cond st.bst_pc
    | _ => count_failing
`;


(* How often was a PC with a certain property reached. *)
val bir_exec_infinite_steps_fun_COUNT_PCs_def = Define
  `(bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p (st, ext_st:'ext_state_t) 0 = 0) /\
   (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p (st, ext_st) (SUC n) =
    let r = bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p
               (bir_exec_step p (st, ext_st)) n in
    if (bir_state_COUNT_PC pc_cond (bir_exec_step p (st, ext_st))) then SUC r else r)`



(* After how many steps do we terminate ? *)
val bir_exec_infinite_steps_COUNT_STEPS_def = Define `
  bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p (st, ext_st:'ext_state_t) = (OLEAST i.
     bir_state_is_terminated $ FST (bir_exec_infinite_steps_fun p (st, ext_st) i) \/
     (max_steps_opt = SOME (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p (st, ext_st) i))
)`;


(*************************)
(* Now full execution    *)
(*************************)

val _ = Datatype `bir_execution_result_t =
    (* The termination ends. "BER_Ended step_count pc_count st" means
       that the execution ended after "step_count" steps in state "st". During
       execution "pc_count" pcs that satisfy the given predicate where encountered
       (counting the pc of the final state st, but not the one of the initial state). *)
    BER_Ended   num num (bir_state_t # 'ext_state_t)

    (* The execution does not terminate. Since the programs are finite, this means
       it loops. Therefore there are no step counts and no final state. *)
  | BER_Looping
`;

val bir_execution_result_ss = rewrites (type_rws ``:'ext_state_t bir_execution_result_t``);

val IS_BER_Ended_def = Define `
   (IS_BER_Ended (BER_Ended _ _ _) = T) /\
   (IS_BER_Ended (BER_Looping ) = F)`;


val IS_BER_Ended_EXISTS = store_thm ("IS_BER_Ended_EXISTS",
``!ber. IS_BER_Ended ber <=> (?step_count pc_count final_st final_ext_st:'ext_state_t.
        ber = BER_Ended step_count pc_count (final_st, final_ext_st))``,

Cases_on `ber`
>- (Cases_on `p` >> SIMP_TAC (std_ss++bir_execution_result_ss) [IS_BER_Ended_def])
>> SIMP_TAC (std_ss++bir_execution_result_ss) [IS_BER_Ended_def]);


val valOf_BER_Ended_def = Define `valOf_BER_Ended (BER_Ended step_count pc_count (final_st, final_ext_st:'ext_state_t)) =
  (step_count, pc_count, (final_st, final_ext_st))`;

val valOf_BER_Ended_steps_def = Define `valOf_BER_Ended_steps (BER_Ended step_count pc_count (final_st, final_ext_st:'ext_state_t)) =
  (step_count, (final_st, final_ext_st))`;


(* Now real execution. This is a clear definition, which is not well suited for evalation
   though. More efficient versions are derived later. We compute the no of steps and
   then execute this number of steps, recomputing values multiple times. *)
val bir_exec_steps_GEN_def = Define `bir_exec_steps_GEN pc_cond p (state, ext_st:'ext_state_t) max_steps_opt =
  let step_no = bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p (state, ext_st) in
  (case step_no of
    | NONE => BER_Looping
    | SOME i => BER_Ended i
                (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p (state, ext_st) i)
                (bir_exec_infinite_steps_fun p (state, ext_st) i))`;


(* A simple instance that just runs till termination. *)
val bir_exec_steps_def = Define `
  (bir_exec_steps p (state, ext_st:'ext_state_t) = bir_exec_steps_GEN (T, (\_. T)) p (state, ext_st) NONE)`;

(* A simple instance that counts all steps and has a fixed no of steps given.
   We are sure it terminates, therefore, the result is converted to a tuple. *)
val bir_exec_step_n_def = Define `
  bir_exec_step_n p (state, ext_st:'ext_state_t) n =
  valOf_BER_Ended_steps (bir_exec_steps_GEN (T, (\_. T)) p (state, ext_st) (SOME n))`

(* We might be interested in executing a certain no of blocks. *)
val bir_exec_block_n_def = Define `
  bir_exec_block_n p (state, ext_st:'ext_state_t) n =
  valOf_BER_Ended (bir_exec_steps_GEN (F, (\pc. pc.bpc_index = 0)) p (state, ext_st) (SOME n))`

(* Executing till a certain set of labels is useful as well. Since we might loop
   outside this set of labels, infinite runs are possible. *)
val bir_exec_to_labels_n_def = Define `
  bir_exec_to_labels_n ls p (state, ext_st:'ext_state_t) n =
  bir_exec_steps_GEN (F, \pc. (pc.bpc_index = 0) /\ (pc.bpc_label IN ls)) p (state, ext_st) (SOME n)`

val bir_exec_to_labels_def = Define `
  bir_exec_to_labels ls p (state, ext_st:'ext_state_t) = bir_exec_to_labels_n ls p (state, ext_st) 1`

val _ = export_theory();
