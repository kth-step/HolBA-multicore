(*
  The notions of valid states and programs, and their uses
*)

open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory bir_auxiliaryLib;
open bir_envTheory bir_valuesTheory
open bir_programTheory HolBACoreSimps bir_init_progTheory;

val _ = new_theory "bir_program_valid_state";


(* -------------------------------------------------------------------------
   We call a program valid, if all its labels are distinct and it is not empty
   ------------------------------------------------------------------------- *)

val bir_is_valid_labels_def = Define `bir_is_valid_labels p =
  ALL_DISTINCT (bir_labels_of_program p)`;

val bir_program_is_empty_def = Define `bir_program_is_empty (BirProgram p) <=> NULL p`

val bir_is_valid_program_def = Define `bir_is_valid_program p <=>
   (bir_is_valid_labels p) /\ ~(bir_program_is_empty p)`;


(* This allows some nice rewrites *)
Theorem bir_is_valid_labels_blocks_EQ_EL:
  !p n1 n2. (bir_is_valid_labels (BirProgram p) /\ n1 < LENGTH p /\ n2 < LENGTH p /\
                (bir_label_of_block (EL n1 p) = bir_label_of_block (EL n2 p))) ==> (n1 = n2)
Proof
  SIMP_TAC list_ss [bir_is_valid_labels_def, bir_labels_of_program_def] >>
  REPEAT STRIP_TAC >>
  MP_TAC (Q.ISPEC `MAP (\bl. bir_label_of_block bl) (p:(('a, 'b) bir_generic_block_t) list)` listTheory.EL_ALL_DISTINCT_EL_EQ) >>
  ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_IMP_THM] >>
  Q.EXISTS_TAC `n1` >> Q.EXISTS_TAC `n2` >>
  ASM_SIMP_TAC list_ss [listTheory.EL_MAP]
QED

Theorem bir_is_valid_labels_blocks_EQ:
  !p bl1 bl2. (bir_is_valid_labels (BirProgram p) /\ MEM bl1 p /\ MEM bl2 p /\
                (bir_label_of_block bl1 = bir_label_of_block bl2)) ==> (bl1 = bl2)
Proof
METIS_TAC [listTheory.MEM_EL, bir_is_valid_labels_blocks_EQ_EL]
QED


Theorem bir_get_program_block_info_by_label_valid_THM:
  (!p l. ((bir_get_program_block_info_by_label (BirProgram p) l = NONE) <=> (!bl. MEM bl p ==> (bir_label_of_block bl <> l)))) /\

    (!p l i bl. bir_is_valid_labels (BirProgram p) ==>
          ((bir_get_program_block_info_by_label (BirProgram p) l = SOME (i, bl)) <=>
           ((i:num) < LENGTH p) /\ (EL i p = bl) /\ (bir_label_of_block bl = l)))
Proof
SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_get_program_block_info_by_label_def,
  INDEX_FIND_EQ_NONE, listTheory.EVERY_MEM, INDEX_FIND_EQ_SOME_0] >>
REPEAT STRIP_TAC >>
`j' < LENGTH p` by DECIDE_TAC >>
`j' = i` by METIS_TAC[bir_is_valid_labels_blocks_EQ_EL] >>
FULL_SIMP_TAC arith_ss []
QED



(* -------------------------------------------------------------------------
   Next we define what we mean by a PC being valid.
   Later this is then used to define valid states
   ------------------------------------------------------------------------- *)

Definition bir_is_valid_index_of_block_def:
  bir_is_valid_index_of_block bl i =
    case bl of
    | BBlock_Stmts stmts_bl => (i <= LENGTH stmts_bl.bb_statements)
    | BBlock_Ext ext_bl => T
End

Theorem bir_is_valid_index_of_block_0:
  !bl. bir_is_valid_index_of_block bl 0
Proof
  Cases_on `bl` >>
  fs[bir_is_valid_index_of_block_def]
QED

(* TODO: Move? *)
Definition bir_current_block_is_extern_def:
  bir_current_block_is_extern p pc =
    ?i bl. bir_get_program_block_info_by_label p pc.bpc_label = SOME (i,bl) /\
           bir_block_is_extern bl
End
Theorem bir_current_block_is_extern_BSExt:
  !p pc. bir_current_block_is_extern p pc <=>
         ?rel. bir_get_current_statement p pc = SOME (BSExt rel)
Proof
rpt gen_tac >> eq_tac >> (
  strip_tac
) >- (
fs[bir_current_block_is_extern_def, bir_get_current_statement_def] >>
Cases_on `bl` >> fs[bir_block_is_extern_def]
) >>
fs[bir_current_block_is_extern_def, bir_get_current_statement_def] >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> fs[] >>
Cases_on `x` >> fs[] >>
Cases_on `r` >> fs[bir_block_is_extern_def] >>
Cases_on `pc.bpc_index < LENGTH b.bb_statements` >> fs[]
QED

Definition bir_is_valid_pc_def:
  bir_is_valid_pc p pc =
    ?i bl. bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, bl) /\
           bir_is_valid_index_of_block bl pc.bpc_index
End

Theorem bir_is_valid_pc_of_valid_blocks:
  !p pc. bir_is_valid_labels (BirProgram p) ==>
           (bir_is_valid_pc (BirProgram p) pc <=> (?bl. MEM bl p /\ (pc.bpc_label = bir_label_of_block bl) /\
             (bir_is_valid_index_of_block bl pc.bpc_index)))
Proof
SIMP_TAC std_ss [bir_is_valid_pc_def, bir_is_valid_index_of_block_def, bir_get_program_block_info_by_label_valid_THM,
  listTheory.MEM_EL, GSYM LEFT_EXISTS_AND_THM] >>
METIS_TAC[]
QED


Theorem bir_get_program_block_info_by_label_valid_pc:
  !p pc. bir_is_valid_pc p pc ==> IS_SOME (bir_get_program_block_info_by_label p pc.bpc_label)
Proof
SIMP_TAC std_ss [bir_is_valid_pc_def, GSYM LEFT_FORALL_IMP_THM]
QED


Theorem bir_get_current_statement_IS_SOME:
  !p pc. IS_SOME (bir_get_current_statement p pc) <=> bir_is_valid_pc p pc
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def, bir_is_valid_pc_def,
                       bir_is_valid_index_of_block_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss) [] >>
Cases_on `SND x` >> (
  fs[] >>
  SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
)
QED



(* -------------------------------------------------------------------------
   The next PC is valid iff and only if the current one is valid and pointing
   to a basic statement
   ------------------------------------------------------------------------- *)

Theorem bir_get_current_statement_SOME_B:
  !p pc stmt. bir_get_current_statement p pc = SOME (BSGen (BStmtB stmt)) <=>
                ?i bl_stmts. bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, BBlock_Stmts bl_stmts) /\
                  pc.bpc_index < LENGTH bl_stmts.bb_statements /\
                  stmt = EL pc.bpc_index bl_stmts.bb_statements
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss) [] >>
Cases_on `SND x` >> (
  fs[]
) >>
Cases_on `pc.bpc_index < LENGTH b.bb_statements` >> (
  fs[]
) >- (
  eq_tac >> (
    rpt strip_tac
  ) >- (
    ASSUME_TAC (ISPEC ``b:'a bir_generic_stmt_block_t`` bir_generic_stmt_block_t_literal_nchotomy) >>
    gs[]
  ) >>
  gs[]
) >>
rpt strip_tac >>
fs[]
QED


Theorem bir_get_current_statement_SOME_E:
  !p pc stmt. bir_get_current_statement p pc = SOME (BSGen (BStmtE stmt)) <=>
              ?i bl_stmts. bir_get_program_block_info_by_label p pc.bpc_label = SOME (i, BBlock_Stmts bl_stmts) /\
                pc.bpc_index = LENGTH bl_stmts.bb_statements /\
                stmt = bl_stmts.bb_last_statement
Proof
REPEAT GEN_TAC >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  ASM_SIMP_TAC std_ss [bir_get_current_statement_def]
) >>
SIMP_TAC (arith_ss++QI_ss++pairSimps.gen_beta_ss) [] >>
Cases_on `SND x` >> (
  fs[]
) >>
Cases_on `pc.bpc_index < LENGTH b.bb_statements` >> (
  fs[]
) >- (
  rpt strip_tac >>
  gs[]
) >>
eq_tac >> (
  rpt strip_tac
) >- (
  ASSUME_TAC (ISPEC ``b:'a bir_generic_stmt_block_t`` bir_generic_stmt_block_t_literal_nchotomy) >>
  gs[]
) >> (
  gs[]
)
QED


(* Only holds if current block is not an extern block *)
Theorem bir_pc_next_valid:
  !p pc. ~bir_current_block_is_extern p pc ==>
         (bir_is_valid_pc p (bir_pc_next pc) <=>
          ?stmt. bir_get_current_statement p pc = SOME (BSGen (BStmtB stmt)))
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [bir_is_valid_pc_def, bir_pc_next_def,
  bir_get_current_statement_SOME_B, bir_current_block_is_extern_def] >>
eq_tac >> (
  rpt strip_tac
) >- (
  Cases_on `bl` >- (
    qexistsl_tac [`i`, `b`] >>
    gs[bir_is_valid_index_of_block_def]
  ) >>
  fs[bir_block_is_extern_def]
) >>
qexistsl_tac [`i`, `BBlock_Stmts bl_stmts`] >>
gs[bir_is_valid_index_of_block_def]
QED



(* -------------------------------------------------------------------------
   The block PC is valid iff the label exists, therefore, the first pc is
   valid for all valid programs
   ------------------------------------------------------------------------- *)

Theorem bir_is_valid_pc_block_pc:
  !l p. bir_is_valid_pc p (bir_block_pc l) <=>
        MEM l (bir_labels_of_program p)
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_def,
  bir_get_program_block_info_by_label_MEM, bir_block_pc_def, bir_is_valid_index_of_block_0]
QED


Theorem bir_pc_first_valid:
  !p. bir_is_valid_program p ==> bir_is_valid_pc p (bir_pc_first p)
Proof
Cases >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_pc_first_def, bir_is_valid_pc_block_pc] >>
Cases_on `p` >> (
  SIMP_TAC list_ss [bir_is_valid_program_def, bir_labels_of_program_def,
    bir_program_is_empty_def]
)
QED


Theorem bir_is_valid_pc_label_OK:
  !p pc. bir_is_valid_pc p pc ==> MEM pc.bpc_label (bir_labels_of_program p)
Proof
Cases_on `p` >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_valid_pc_def, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_labels_of_program_def,
  bir_get_program_block_info_by_label_THM] >>
SIMP_TAC std_ss [listTheory.MEM_EL, GSYM RIGHT_EXISTS_AND_THM] >>
METIS_TAC[]
QED



(* -------------------------------------------------------------------------
   Finally, we can define what a valid state is.

   A valid state has a well-typed environment and a valid PC
   ------------------------------------------------------------------------- *)

val bir_is_valid_state_def = Define `bir_is_valid_state p st <=>
  ((bir_is_well_typed_env st.bst_environ) /\ bir_is_valid_pc p st.bst_pc)`;

(* The initial state is valid for all valid programs *)
Theorem bir_state_init_valid:
  !p. bir_is_valid_program p ==> bir_is_valid_state p (bir_state_init p)
Proof
SIMP_TAC (std_ss++holBACore_ss++holBACore_ss) [bir_is_valid_state_def, bir_state_init_def,
  bir_pc_first_valid, bir_env_oldTheory.bir_is_well_typed_env_THM]
QED

(* TODO: (Re)Move? *)
Theorem bir_get_current_statement_NONE_BBlock_Ext:
  !p pc b. bir_get_current_statement p pc = NONE ==>
  ~(bir_get_current_block p pc = SOME (BBlock_Ext b))
Proof
gs[bir_get_current_statement_def, bir_get_current_block_def] >>
Cases_on `bir_get_program_block_info_by_label p pc.bpc_label` >> (
  fs[]
) >>
rpt strip_tac >>
Cases_on `x` >> (
  fs[]
)
QED


Theorem bir_exec_step_invalid_pc_THM:
  !p st.
   ~bir_is_valid_pc p st.bst_pc ==>
    (bir_exec_step p st = if (bir_state_is_terminated st) then st else bir_state_set_failed st)
Proof
metis_tac[bir_exec_step_def, bir_get_current_statement_IS_SOME, optionTheory.option_CLAUSES]
QED


(* valid states allow some nice rewrite for bir_exec_step *)
(* Only holds if current block is not an extern block *)
Theorem bir_exec_step_valid_THM:
  !p st.
     ~bir_current_block_is_extern p st.bst_pc ==>
     bir_is_valid_pc p st.bst_pc ==>
     if bir_state_is_terminated st then
       bir_exec_step p st = st
     else
       ?stmt. bir_get_current_statement p st.bst_pc = SOME (BSGen stmt) /\
              bir_exec_step p st = bir_exec_stmt p stmt st
Proof
rpt strip_tac >>
FULL_SIMP_TAC std_ss [bir_exec_step_def, bir_current_block_is_extern_BSExt] >>
Cases_on `bir_state_is_terminated st` >> ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] >>
fs[GSYM bir_get_current_statement_IS_SOME, optionTheory.IS_SOME_EXISTS] >>
Cases_on `x` >> fs[]
QED


Theorem bir_exec_step_state_valid_THM:
  !p st.
     ~bir_current_block_is_extern p st.bst_pc ==>
     bir_is_valid_pc p st.bst_pc ==>
     (if bir_state_is_terminated st then
        (bir_exec_step p st = st)
      else
        (?stmt. (bir_get_current_statement p st.bst_pc = SOME (BSGen stmt)) /\
                (bir_exec_step p st = (bir_exec_stmt p stmt st))))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st`] bir_exec_step_valid_THM) >>
ASM_SIMP_TAC std_ss [bir_exec_step_def, bir_exec_stmt_def]
QED


(* -------------------------------------------------------------------------
   bir_is_valid_state is an invariant
   ------------------------------------------------------------------------- *)

val bir_exec_stmtB_well_typed_env_assign = prove (
  ``!st v ex. bir_is_well_typed_env st.bst_environ ==>
              bir_is_well_typed_env (bir_exec_stmt_assign v ex st).bst_environ``,
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]);


val bir_exec_stmtB_well_typed_env_assert = prove (
  ``!st ex. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmt_assert ex st).bst_environ``,
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]);


val bir_exec_stmtB_well_typed_env_assume = prove (
  ``!st ex. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmt_assume ex st).bst_environ``,
METIS_TAC[bir_env_oldTheory.bir_is_well_typed_env_THM]);

Theorem bir_exec_stmtB_well_typed_env:
  !st stmt. bir_is_well_typed_env st.bst_environ ==>
            bir_is_well_typed_env (bir_exec_stmtB stmt st).bst_environ
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_def,
    bir_exec_stmtB_well_typed_env_assign,
    bir_exec_stmtB_well_typed_env_assume,
    bir_exec_stmtB_well_typed_env_assert]
)
QED


Theorem bir_exec_stmtB_pc_unchanged:
  !st stmt. (bir_exec_stmtB stmt st).bst_pc = st.bst_pc
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def] >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
)
QED

Theorem bir_exec_stmtB_valid_state_invar:
  !p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtB stmt st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_stmtB_pc_unchanged, bir_exec_stmtB_well_typed_env]
QED


Theorem bir_exec_stmt_jmp_to_label_valid_pc:
  !p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmt_jmp_to_label p l st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_pc_block_pc],

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
QED


Theorem bir_exec_stmt_jmp_valid_pc:
  !p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmt_jmp p l st).bst_pc
Proof
SIMP_TAC std_ss [bir_exec_stmt_jmp_def] >>
REPEAT STRIP_TAC >> CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [
     bir_exec_stmt_jmp_to_label_valid_pc,
     bir_state_set_typeerror_def]
)
QED


val bir_exec_stmtE_valid_pc_jmp = prove (
  ``!p st l. bir_is_valid_pc p st.bst_pc ==>
             bir_is_valid_pc p (bir_exec_stmtE p (BStmt_Jmp l) st).bst_pc``,
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_valid_pc]);


val bir_exec_stmtE_valid_pc_cjmp = prove (
  ``!p st ex l1 l2.
       bir_is_valid_pc p st.bst_pc ==>
       bir_is_valid_pc p (bir_exec_stmtE p (BStmt_CJmp ex l1 l2) st).bst_pc``,
SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
REPEAT STRIP_TAC >>
Cases_on `option_CASE (bir_eval_exp ex st.bst_environ) NONE bir_dest_bool_val` >- (
  Cases_on `bir_eval_exp ex st.bst_environ` >> (
    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_typeerror_def, LET_DEF]
  )
) >>
rename1 `SOME c` >>
Cases_on `c` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_jmp_valid_pc, LET_DEF]
));


val bir_exec_stmtE_valid_pc_halt = prove (
  ``!p st ex.
      bir_is_valid_pc p st.bst_pc ==>
      bir_is_valid_pc p (bir_exec_stmtE p (BStmt_Halt ex) st).bst_pc``,
  SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def, bir_exec_stmt_halt_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `bir_eval_exp ex st.bst_environ` >> (
    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_typeerror_def, LET_DEF]
  )
);


Theorem bir_exec_stmtE_valid_pc:
  !p st stmt. bir_is_valid_pc p st.bst_pc ==>
              bir_is_valid_pc p (bir_exec_stmtE p stmt st).bst_pc
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [
    bir_exec_stmtE_valid_pc_cjmp,
    bir_exec_stmtE_valid_pc_jmp,
    bir_exec_stmtE_valid_pc_halt]
)
QED


Theorem bir_exec_stmtE_env_unchanged:
  !p st stmt. (bir_exec_stmtE p stmt st).bst_environ = st.bst_environ
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def,
    bir_exec_stmt_halt_def, bir_exec_stmt_jmp_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_to_label_def,
    bir_state_set_typeerror_def] >>
  REPEAT CASE_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [LET_DEF] >>
  Cases_on `bir_eval_exp b st.bst_environ` >> (
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    rename1 `bir_dest_bool_val x''` >> Cases_on `bir_dest_bool_val x''`
  ) >> (
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    COND_CASES_TAC >>
    SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  )
)
QED


Theorem bir_exec_stmtE_valid_state_invar:
  !p st stmt. bir_is_valid_state p st ==>
              bir_is_valid_state p (bir_exec_stmtE p stmt st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_stmtE_env_unchanged, bir_exec_stmtE_valid_pc]
QED


Theorem bir_exec_stmtE_block_pc:
  !p st stmt.
  ~(bir_state_is_terminated (bir_exec_stmtE p stmt st)) ==>
  ((bir_exec_stmtE p stmt st).bst_pc.bpc_index = 0)
Proof
REPEAT GEN_TAC >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def,
    bir_exec_stmt_halt_def, bir_exec_stmt_jmp_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_to_label_def,
    bir_state_set_typeerror_def] >>
  REPEAT CASE_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF] >>
  Cases_on `bir_eval_exp b st.bst_environ` >> (
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  ) >> (
    rename1 `bir_dest_bool_val x''` >> Cases_on `bir_dest_bool_val x''`
  ) >> (
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  ) >> (
    COND_CASES_TAC >>
    SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def, LET_DEF]
  )
)
QED

(* TODO: Relax to allowing some kind of well-formed extern block? *)
Theorem bir_exec_step_valid_pc:
  !p st.
  ~bir_current_block_is_extern p st.bst_pc ==>
  (bir_is_valid_pc p (bir_exec_step p st).bst_pc <=>
    bir_is_valid_pc p st.bst_pc)
Proof
REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated st` >- (
  FULL_SIMP_TAC std_ss [bir_exec_step_def, bir_exec_step_def]
) >>
EQ_TAC >> REPEAT STRIP_TAC >- (
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_step_invalid_pc_THM, bir_exec_step_def] >>
  REV_FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_failed_def]
) >>
IMP_RES_TAC bir_exec_step_state_valid_THM >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_stmtE_valid_pc, LET_DEF]
) >>
rename1 `bir_exec_stmtB stmt st` >>
Q.ABBREV_TAC `st' = bir_exec_stmtB stmt st` >>
rename1 `st' = bir_exec_stmtB stmt st` >>
subgoal `st'.bst_pc = st.bst_pc` >- (
  subgoal `(bir_exec_stmtB stmt st).bst_pc = st.bst_pc` >- (
    fs[bir_exec_stmtB_pc_unchanged]
  ) >>
  gvs[pairTheory.FST]
) >>
fs[] >>
COND_CASES_TAC >> ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_pc_next_valid]
QED


Theorem bir_exec_step_well_typed_env:
  !p st.
  ~bir_current_block_is_extern p st.bst_pc ==>
  bir_is_well_typed_env st.bst_environ ==>
  bir_is_well_typed_env (bir_exec_step p st).bst_environ
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_def, bir_exec_step_def] >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_set_failed_def]
) >>
Cases_on `x` >> (
 fs[bir_current_block_is_extern_BSExt]
) >>
DISJ2_TAC >>
rename1 `_ = SOME (BSGen stmt)` >>
Cases_on `stmt` >> (
  ASM_SIMP_TAC std_ss [bir_exec_stmt_def, LET_DEF,
    bir_exec_stmtE_env_unchanged]
) >>
fs[] >>
CASE_TAC >> (
  fs[] >>
  metis_tac[pairTheory.FST, bir_exec_stmtB_well_typed_env]
)
QED


Theorem bir_exec_step_valid_state_invar:
  !p st.
  ~bir_current_block_is_extern p st.bst_pc ==>
  bir_is_valid_state p st ==>
  bir_is_valid_state p (bir_exec_step p st)
Proof
SIMP_TAC std_ss [bir_is_valid_state_def,
  bir_exec_step_well_typed_env, bir_exec_step_valid_pc]
QED


val _ = export_theory();
