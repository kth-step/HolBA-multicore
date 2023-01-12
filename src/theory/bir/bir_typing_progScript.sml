open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_expTheory bir_typing_expTheory bir_programTheory;
open wordsLib pred_setTheory;

val _ = new_theory "bir_typing_prog";


(* ------------------------------------------------------------------------- *)
(*  Statements of Programs                                                   *)
(* ------------------------------------------------------------------------- *)

Definition bir_stmts_of_block_def:
  bir_stmts_of_block bl =
  case bl of
  | BBlock_Stmts bl_stmts =>
    (BSGen $ BStmtE bl_stmts.bb_last_statement)
      INSERT (IMAGE (BSGen o BStmtB) (set bl_stmts.bb_statements))
  | BBlock_Ext bl_ext => {BSExt bl_ext.beb_relation}
End

val bir_stmts_of_prog_def = Define `bir_stmts_of_prog (BirProgram p) =
  BIGUNION (IMAGE bir_stmts_of_block (set p))`;

Theorem bir_get_current_statement_stmts_of_prog:
  !p pc stmt. bir_get_current_statement p pc = SOME stmt ==>
                stmt IN (bir_stmts_of_prog p)
Proof
  Cases >> rename1 `BirProgram p` >>
  SIMP_TAC std_ss [bir_get_current_statement_def, bir_stmts_of_prog_def,
    IN_BIGUNION, IN_IMAGE, PULL_EXISTS, bir_stmts_of_block_def,
    IN_INSERT, IN_IMAGE] >>
  REPEAT GEN_TAC >>
  Cases_on `(bir_get_program_block_info_by_label (BirProgram p) pc.bpc_label)` >- (
    ASM_SIMP_TAC std_ss []
  ) >>
  fs[] >>
  rename1 `_ = SOME xy` >> Cases_on `xy` >>
  rename1 `_ = SOME (i, bl)` >>
  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [] >>
  Cases_on `bl` >> fs[] >- (
    CASE_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >>
    Q.EXISTS_TAC `BBlock_Stmts b` >>
    fs[bir_get_program_block_info_by_label_THM] >>
    METIS_TAC[rich_listTheory.EL_MEM]
  ) >>
  strip_tac >>
  qmatch_asmsub_rename_tac `BBlock_Ext b` >>
  Q.EXISTS_TAC `BBlock_Ext b` >>
  fs[bir_get_program_block_info_by_label_THM] >>
  METIS_TAC[rich_listTheory.EL_MEM]
QED

Definition bir_blocks_of_prog_def:
  bir_blocks_of_prog (BirProgram p) = set p
End

(* ------------------------------------------------------------------------- *)
(*  Well-typed Programs                                                      *)
(* ------------------------------------------------------------------------- *)
(* These properties are used in the WP generator, as well as in the concrete execution *)

val bir_is_well_typed_label_exp_def = Define `
  (bir_is_well_typed_label_exp (BLE_Label _) = T) /\
  (bir_is_well_typed_label_exp (BLE_Exp e) = (case (type_of_bir_exp e) of
      NONE => F
    | SOME ty => (bir_type_is_Imm ty)))`;

val bir_is_well_typed_stmtE_def = Define `
  (bir_is_well_typed_stmtE (BStmt_Jmp le) = bir_is_well_typed_label_exp le) /\
  (bir_is_well_typed_stmtE (BStmt_CJmp c le1 le2) =
       ((type_of_bir_exp c = SOME BType_Bool) /\
       (bir_is_well_typed_label_exp le1) /\
       (bir_is_well_typed_label_exp le2))) /\
  (bir_is_well_typed_stmtE (BStmt_Halt e) = (type_of_bir_exp e <> NONE))`;

val bir_is_well_typed_stmtB_def = Define `
  (bir_is_well_typed_stmtB (BStmt_Assign v e) =
    (type_of_bir_exp e = SOME (bir_var_type v))) /\
  (bir_is_well_typed_stmtB (BStmt_Assert e) =
    (type_of_bir_exp e = SOME BType_Bool)) /\
  (bir_is_well_typed_stmtB (BStmt_Assume e) =
    (type_of_bir_exp e = SOME BType_Bool))`;

val bir_is_well_typed_stmt_def = Define `
  (bir_is_well_typed_stmt (BStmtE s) = bir_is_well_typed_stmtE s) /\
  (bir_is_well_typed_stmt (BStmtB s) = bir_is_well_typed_stmtB s)`;

Definition bir_is_well_typed_ext_rel_def:
  bir_is_well_typed_ext_rel R =
    !s other_cores ext s' ext' var_name.
      R (s,other_cores,ext) (s',ext')
      ==>
        bir_env_lookup_type var_name s.bst_environ =
        bir_env_lookup_type var_name s'.bst_environ
End

(* type preservation is well-typedness criteria for extern block *)
Definition bir_is_well_typed_ext_def:
  bir_is_well_typed_ext ext_fun =
    bir_is_well_typed_ext_rel ext_fun.beb_relation
End

val bir_is_well_typed_block_def = Define `bir_is_well_typed_block bl <=>
  case bl of
  | BBlock_Stmts bl_stmts =>
    EVERY bir_is_well_typed_stmtB bl_stmts.bb_statements /\
    bir_is_well_typed_stmtE bl_stmts.bb_last_statement
  | BBlock_Ext ext_fun => bir_is_well_typed_ext ext_fun`;

val bir_is_well_typed_program_def = Define `bir_is_well_typed_program (BirProgram p) <=>
  (EVERY bir_is_well_typed_block p)`;

Theorem bir_is_well_typed_block_ALT_DEF:
  !bl. bir_is_well_typed_block bl <=>
      case bl of
      | BBlock_Stmts bl_stmts =>
        (!stmt. BSGen stmt IN bir_stmts_of_block bl ==> bir_is_well_typed_stmt stmt)
      | BBlock_Ext ext_fun => bir_is_well_typed_ext ext_fun
Proof
  rpt strip_tac >>
  Cases_on `bl` >>
    fs [EQ_IMP_THM,bir_is_well_typed_block_def, bir_stmts_of_block_def,
      IN_INSERT, IN_IMAGE, DISJ_IMP_THM, PULL_EXISTS, FORALL_AND_THM,
      bir_is_well_typed_stmt_def, listTheory.EVERY_MEM]
QED

Theorem bir_is_well_typed_program_ALT_DEF:
  !p. bir_is_well_typed_program p <=>
    !bl. bl IN bir_blocks_of_prog p ==>
    (!stmt. BSGen stmt IN bir_stmts_of_block bl ==> bir_is_well_typed_stmt stmt)
    /\ (!stmt. BSExt stmt IN bir_stmts_of_block bl ==> bir_is_well_typed_ext_rel stmt)
Proof
  Cases >>
  rw[EQ_IMP_THM,bir_is_well_typed_program_def,
    bir_stmts_of_prog_def, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
    listTheory.EVERY_MEM, bir_is_well_typed_block_ALT_DEF,
    bir_blocks_of_prog_def] >>
  first_x_assum drule
  >- (
    qmatch_asmsub_rename_tac `bir_stmts_of_block bl` >>
    Cases_on `bl` >>
    fs[bir_is_well_typed_stmt_def,bir_stmts_of_block_def,bir_is_well_typed_ext_def]
  ) >- (
    qmatch_asmsub_rename_tac `bir_stmts_of_block bl` >>
    Cases_on `bl` >>
    fs[bir_is_well_typed_stmt_def,bir_stmts_of_block_def,bir_is_well_typed_ext_def]
  ) >- (
    qmatch_asmsub_rename_tac `MEM e l` >>
    Cases_on `e` >>
    fs[bir_blocks_of_prog_def,bir_is_well_typed_ext_def,bir_stmts_of_block_def]
  )
QED

Theorem bir_get_current_statement_well_typed:
  !p pc stmt. bir_is_well_typed_program p /\
    bir_get_current_statement p pc = SOME $ BSGen stmt ==>
      bir_is_well_typed_stmt stmt
Proof
  Cases >> rpt strip_tac >>
  imp_res_tac bir_get_current_statement_stmts_of_prog >>
  gvs[bir_is_well_typed_program_ALT_DEF,bir_stmts_of_prog_def,bir_blocks_of_prog_def] >>
  fs[IMP_CONJ_THM,FORALL_AND_THM] >>
  first_x_assum $ drule_then irule >>
  fs[]
QED

(* ------------------------------------------------------------------------- *)
(*  Variables of statements and programs                                     *)
(* ------------------------------------------------------------------------- *)

val bir_vars_of_stmtB_def = Define `
  (bir_vars_of_stmtB (BStmt_Assert ex) = bir_vars_of_exp ex) /\
  (bir_vars_of_stmtB (BStmt_Assume ex) = bir_vars_of_exp ex) /\
  (bir_vars_of_stmtB (BStmt_Assign v ex) = (v INSERT (bir_vars_of_exp ex))) (*/\
  (bir_vars_of_stmtB (BStmt_ExtPut _ ex) = bir_vars_of_exp ex)*)`;

Definition bmc_vars_of_stmtB_def:
     bmc_vars_of_stmtB (BMCStmt_Load var exp _ _ _ _) = { var } UNION bir_vars_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Store var exp exp' _ _ _) = { var } UNION bir_vars_of_exp exp UNION bir_vars_of_exp exp'
  /\ bmc_vars_of_stmtB (BMCStmt_Amo var exp exp' _ _) = { var } UNION bir_vars_of_exp exp UNION bir_vars_of_exp exp'
  /\ bmc_vars_of_stmtB (BMCStmt_Assign var exp) = { var } UNION bir_vars_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Fence _ _) = {}
  /\ bmc_vars_of_stmtB (BMCStmt_Assert exp) = bir_vars_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Assume exp) = bir_vars_of_exp exp
End

val bir_vars_of_label_exp_def = Define `
  (bir_vars_of_label_exp (BLE_Label l) = {}) /\
  (bir_vars_of_label_exp (BLE_Exp e) = bir_vars_of_exp e)`;

val bir_vars_of_stmtE_def = Define `
  (bir_vars_of_stmtE (BStmt_Jmp l) = bir_vars_of_label_exp l) /\
  (bir_vars_of_stmtE (BStmt_CJmp e l1 l2) =
    (bir_vars_of_exp e UNION (bir_vars_of_label_exp l1) UNION (bir_vars_of_label_exp l2))) /\
  (bir_vars_of_stmtE (BStmt_Halt ex) = bir_vars_of_exp ex)`;

val bir_vars_of_stmt_def = Define `
  (bir_vars_of_stmt (BStmtE s) = bir_vars_of_stmtE s) /\
  (bir_vars_of_stmt (BStmtB s) = bir_vars_of_stmtB s)`;

Definition bmc_vars_of_stmt_def:
  bmc_vars_of_stmt (BStmtE s) = bir_vars_of_stmtE s /\
  bmc_vars_of_stmt (BStmtB s) = bmc_vars_of_stmtB s
End

Definition bir_vars_of_stmt_kind_def:
  bir_vars_of_stmt_kind (BSGen stmt) = bir_vars_of_stmt stmt /\
  bir_vars_of_stmt_kind _ = {}
End

Definition bmc_vars_of_stmt_kind_def:
  bmc_vars_of_stmt_kind (BSGen stmt) = bmc_vars_of_stmt stmt /\
  bmc_vars_of_stmt_kind _ = {}
End

val bir_vars_of_block_def = Define `bir_vars_of_block bl <=>
  ((BIGUNION (IMAGE bir_vars_of_stmtB (LIST_TO_SET bl.bb_statements))) UNION
   (bir_vars_of_stmtE bl.bb_last_statement))`;

val bmc_vars_of_block_def = Define `bmc_vars_of_block bl <=>
  ((BIGUNION (IMAGE bmc_vars_of_stmtB (LIST_TO_SET bl.bb_statements))) UNION
   (bir_vars_of_stmtE bl.bb_last_statement))`;

Definition bir_vars_of_generic_block_def:
  bir_vars_of_generic_block (BBlock_Stmts bl) = bir_vars_of_block bl /\
  bir_vars_of_generic_block _ = {}
End

Definition bmc_vars_of_generic_block_def:
  bmc_vars_of_generic_block (BBlock_Stmts bl) = bmc_vars_of_block bl /\
  bmc_vars_of_generic_block _ = {}
End

val bir_vars_of_program_def = Define `bir_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bir_vars_of_generic_block (LIST_TO_SET p)))`;

val bmc_vars_of_program_def = Define `bmc_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bmc_vars_of_generic_block (LIST_TO_SET p)))`;

Theorem bir_vars_of_generic_block_ALT_DEF:
  !bl. bir_vars_of_generic_block bl  = BIGUNION (IMAGE bir_vars_of_stmt_kind (bir_stmts_of_block bl))
Proof
  SIMP_TAC std_ss [EXTENSION] >>
  Induct >>
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_stmts_of_block_def,
    IN_BIGUNION, PULL_EXISTS, IN_UNION,
    IN_IMAGE, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM] >>
  dsimp[AllCaseEqs(),bir_vars_of_generic_block_def,bir_vars_of_stmt_kind_def,bir_vars_of_stmt_def,bir_vars_of_block_def] >>
  fs[LEFT_AND_OVER_OR,EXISTS_OR_THM,PULL_EXISTS,AC DISJ_ASSOC DISJ_COMM]
QED

Theorem bmc_vars_of_generic_block_ALT_DEF:
  !bl. bmc_vars_of_generic_block bl  = BIGUNION (IMAGE bmc_vars_of_stmt_kind (bir_stmts_of_block bl))
Proof
  SIMP_TAC std_ss [EXTENSION] >>
  Induct >>
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_stmts_of_block_def,
    IN_BIGUNION, PULL_EXISTS, IN_UNION,
    IN_IMAGE, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM] >>
  dsimp[AllCaseEqs(),bmc_vars_of_generic_block_def,bmc_vars_of_stmt_kind_def,bmc_vars_of_stmt_def,bmc_vars_of_block_def] >>
  fs[LEFT_AND_OVER_OR,EXISTS_OR_THM,PULL_EXISTS,AC DISJ_ASSOC DISJ_COMM]
QED

Theorem bir_vars_of_program_ALT_DEF:
  !p. bir_vars_of_program p =
        BIGUNION (IMAGE bir_vars_of_stmt_kind (bir_stmts_of_prog p))
Proof
  Cases >>
  SIMP_TAC std_ss [EXTENSION] >>
  SIMP_TAC std_ss [bir_vars_of_program_def, bir_stmts_of_prog_def,
    IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bir_vars_of_generic_block_ALT_DEF] >>
  fs[AC CONJ_ASSOC CONJ_COMM,Once SWAP_EXISTS_THM]
QED

Theorem bmc_vars_of_program_ALT_DEF:
  !p. bmc_vars_of_program p =
        BIGUNION (IMAGE bmc_vars_of_stmt_kind (bir_stmts_of_prog p))
Proof
  Cases >>
  SIMP_TAC std_ss [EXTENSION] >>
  SIMP_TAC std_ss [bmc_vars_of_program_def, bir_stmts_of_prog_def,
    IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bmc_vars_of_generic_block_ALT_DEF] >>
  fs[AC CONJ_ASSOC CONJ_COMM,Once SWAP_EXISTS_THM]
QED

Theorem bir_get_current_statement_vars_of:
  !p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
                bir_vars_of_stmt_kind stmt SUBSET bir_vars_of_program p
Proof
  SIMP_TAC std_ss [bir_vars_of_program_ALT_DEF, SUBSET_DEF, IN_BIGUNION,
    IN_IMAGE, PULL_EXISTS] >>
  METIS_TAC[bir_get_current_statement_stmts_of_prog]
QED

Theorem bmc_get_current_statement_vars_of:
  !p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
                bmc_vars_of_stmt_kind stmt SUBSET bmc_vars_of_program p
Proof
  SIMP_TAC std_ss [bmc_vars_of_program_ALT_DEF, SUBSET_DEF, IN_BIGUNION,
    IN_IMAGE, PULL_EXISTS] >>
  METIS_TAC[bir_get_current_statement_stmts_of_prog]
QED

val bir_vars_of_label_exp_THM_EQ_FOR_VARS = store_thm ("bir_vars_of_label_exp_THM_EQ_FOR_VARS",
``!env1 env2 (ext_st:'ext_state_t) e. (bir_env_EQ_FOR_VARS (bir_vars_of_label_exp e) env1 env2) ==>
                (bir_eval_label_exp e env1 ext_st = bir_eval_label_exp e env2 ext_st)``,
Cases_on `e` >>
SIMP_TAC std_ss [bir_eval_label_exp_def, bir_vars_of_label_exp_def] >>
METIS_TAC[bir_vars_of_exp_THM_EQ_FOR_VARS]);


(* ------------------------------- *)
(*  Variables modified by program  *)
(* ------------------------------- *)

val bir_changed_vars_of_stmtB_def = Define `
  (bir_changed_vars_of_stmtB (BStmt_Assert ex) = {}) /\
  (bir_changed_vars_of_stmtB (BStmt_Assume ex) = {}) /\
  (bir_changed_vars_of_stmtB (BStmt_Assign v ex) = {v})`;

val bir_changed_vars_of_stmt_def = Define `
  (bir_changed_vars_of_stmt (BStmtE s) = {}) /\
  (bir_changed_vars_of_stmt (BStmtB s) = bir_changed_vars_of_stmtB s)`;

Definition bmc_changed_vars_of_stmtB_def:
  bmc_changed_vars_of_stmtB (BMCStmt_Load var _ _ _ _ _) = { var } /\
  bmc_changed_vars_of_stmtB (BMCStmt_Store var _ _ _ _ _) = { var } /\
  bmc_changed_vars_of_stmtB (BMCStmt_Amo var _ _ _ _) = { var } /\
  bmc_changed_vars_of_stmtB (BMCStmt_Assign var _) = { var } /\
  bmc_changed_vars_of_stmtB _ = {}
End

Definition bmc_changed_vars_of_stmt_def:
  bmc_changed_vars_of_stmt (BStmtE s) = {} /\
  bmc_changed_vars_of_stmt (BStmtB s) = bir_changed_vars_of_stmtB s
End

val bir_changed_vars_of_block_def = Define `bir_changed_vars_of_block bl <=>
  (BIGUNION (IMAGE bir_changed_vars_of_stmtB (LIST_TO_SET bl.bb_statements)))`;

Definition bir_changed_vars_of_generic_block_def:
  bir_changed_vars_of_generic_block (BBlock_Stmts x) = bir_changed_vars_of_block x /\
  bir_changed_vars_of_generic_block (BBlock_Ext _) = {} (* may be state-dependent *)
End

val bir_changed_vars_of_program_def = Define `bir_changed_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bir_changed_vars_of_generic_block (LIST_TO_SET p)))`;

val bir_changed_vars_of_stmtB_SUBST_all_vars = store_thm (
  "bir_changed_vars_of_stmtB_SUBST_all_vars",
``!stmt. bir_changed_vars_of_stmtB stmt SUBSET bir_vars_of_stmtB stmt``,
Cases >> (
  SIMP_TAC std_ss [bir_vars_of_stmtB_def, bir_changed_vars_of_stmtB_def,
    SUBSET_DEF, NOT_IN_EMPTY, IN_INSERT]
));


val bir_changed_vars_of_stmt_SUBST_all_vars = store_thm (
  "bir_changed_vars_of_stmt_SUBST_all_vars",
``!stmt. bir_changed_vars_of_stmt stmt SUBSET bir_vars_of_stmt stmt``,
Cases >> (
   SIMP_TAC std_ss [bir_changed_vars_of_stmt_def, bir_vars_of_stmt_def,
     bir_changed_vars_of_stmtB_SUBST_all_vars, EMPTY_SUBSET]
));


val bir_changed_vars_of_block_SUBST_all_vars = store_thm (
  "bir_changed_vars_of_block_SUBST_all_vars",
``!bl. bir_changed_vars_of_block bl SUBSET bir_vars_of_block bl``,

SIMP_TAC std_ss [bir_changed_vars_of_block_def, bir_vars_of_block_def,
  SUBSET_DEF, IN_UNION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[SUBSET_DEF, bir_changed_vars_of_stmtB_SUBST_all_vars]);

val bir_changed_vars_of_program_SUBST_all_vars = store_thm (
  "bir_changed_vars_of_program_SUBST_all_vars",
``!p. bir_changed_vars_of_program p SUBSET bir_vars_of_program p``,

Cases >>
SIMP_TAC std_ss [bir_changed_vars_of_program_def, bir_vars_of_program_def,
  SUBSET_DEF, IN_UNION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[SUBSET_DEF, bir_changed_vars_of_block_SUBST_all_vars]);


val bir_changed_vars_of_block_ALT_DEF = store_thm ("bir_changed_vars_of_block_ALT_DEF",
  ``!bl. bir_changed_vars_of_block bl = BIGUNION (IMAGE bir_changed_vars_of_stmt (bir_stmts_of_block bl))``,

SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_changed_vars_of_block_def, bir_stmts_of_block_def,
  IN_BIGUNION, PULL_EXISTS, IN_UNION, bir_changed_vars_of_stmt_def,
  IN_IMAGE, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM, NOT_IN_EMPTY]);


val bir_changed_vars_of_program_ALT_DEF = store_thm ("bir_changed_vars_of_program_ALT_DEF",
  ``!p. bir_changed_vars_of_program p =
        BIGUNION (IMAGE bir_changed_vars_of_stmt (bir_stmts_of_prog p))``,

Cases >>
SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC std_ss [bir_changed_vars_of_program_def, bir_stmts_of_prog_def,
  IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bir_changed_vars_of_block_ALT_DEF] >>
METIS_TAC[]);


val bir_get_current_statement_changed_vars_of = store_thm ("bir_get_current_statement_changed_vars_of",
  ``!p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
                bir_changed_vars_of_stmt stmt SUBSET bir_changed_vars_of_program p``,

SIMP_TAC std_ss [bir_changed_vars_of_program_ALT_DEF, SUBSET_DEF, IN_BIGUNION,
  IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[bir_get_current_statement_stmts_of_prog]);


(* ------------------------ *)
(*  Expressions of program  *)
(* ------------------------ *)

val bir_exps_of_stmtB_def = Define `
  (bir_exps_of_stmtB (BStmt_Assert ex) = {ex}) /\
  (bir_exps_of_stmtB (BStmt_Assume ex) = {ex}) /\
  (bir_exps_of_stmtB (BStmt_Assign v ex) = {ex}) /\
  (bir_exps_of_stmtB (BStmt_ExtPut en ex) = {ex})`;

val bir_exps_of_label_exp_def = Define `
  (bir_exps_of_label_exp (BLE_Label l) = {}) /\
  (bir_exps_of_label_exp (BLE_Exp e) = {e})`;

val bir_exps_of_stmtE_def = Define `
  (bir_exps_of_stmtE (BStmt_Jmp l) = bir_exps_of_label_exp l) /\
  (bir_exps_of_stmtE (BStmt_CJmp e l1 l2) =
    ({e} UNION (bir_exps_of_label_exp l1) UNION (bir_exps_of_label_exp l2))) /\
  (bir_exps_of_stmtE (BStmt_Halt ex) = {ex})`;

val bir_exps_of_stmt_def = Define `
  (bir_exps_of_stmt (BStmtE s) = bir_exps_of_stmtE s) /\
  (bir_exps_of_stmt (BStmtB s) = bir_exps_of_stmtB s)`;

val bir_exps_of_block_def = Define `bir_exps_of_block bl <=>
  (bir_exps_of_stmtE bl.bb_last_statement) UNION (BIGUNION (IMAGE bir_exps_of_stmtB (LIST_TO_SET bl.bb_statements)))`;

val bir_exps_of_program_def = Define `bir_exps_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bir_exps_of_block (LIST_TO_SET p)))`;

val bir_exps_of_block_ALT_DEF = store_thm ("bir_exps_of_block_ALT_DEF",
  ``!bl. bir_exps_of_block bl = BIGUNION (IMAGE bir_exps_of_stmt (bir_stmts_of_block bl))``,

SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exps_of_block_def, bir_stmts_of_block_def,
  IN_BIGUNION, PULL_EXISTS, IN_UNION, bir_exps_of_stmt_def,
  IN_IMAGE, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM, NOT_IN_EMPTY]);


val bir_exps_of_program_ALT_DEF = store_thm ("bir_exps_of_program_ALT_DEF",
  ``!p. bir_exps_of_program p =
        BIGUNION (IMAGE bir_exps_of_stmt (bir_stmts_of_prog p))``,

Cases >>
SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC std_ss [bir_exps_of_program_def, bir_stmts_of_prog_def,
  IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bir_exps_of_block_ALT_DEF] >>
METIS_TAC[]);


val bir_get_current_statement_exps_of = store_thm ("bir_get_current_statement_exps_of",
  ``!p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
                bir_exps_of_stmt stmt SUBSET bir_exps_of_program p``,

SIMP_TAC std_ss [bir_exps_of_program_ALT_DEF, SUBSET_DEF, IN_BIGUNION,
  IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[bir_get_current_statement_stmts_of_prog]);


val bir_exp_vars_of_stmtB = store_thm ("bir_exp_vars_of_stmtB",
``!stmt. BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_stmtB stmt)) SUBSET
         bir_vars_of_stmtB stmt``,

Cases >> (
  SIMP_TAC list_ss [bir_vars_of_stmtB_def, bir_exps_of_stmtB_def,
    SUBSET_DEF, NOT_IN_EMPTY, IN_INSERT, IN_BIGUNION, IN_IMAGE, PULL_EXISTS] >>
  METIS_TAC[]
));

val bir_exp_vars_of_label_exp = store_thm ("bir_exp_vars_of_label_exp",
``!le. bir_vars_of_label_exp le =
       BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_label_exp le))``,

Cases >> (
  SIMP_TAC std_ss [bir_vars_of_label_exp_def,
    bir_exps_of_label_exp_def, IMAGE_EMPTY, BIGUNION_EMPTY,
    IMAGE_INSERT, BIGUNION_INSERT, UNION_EMPTY]
));


val bir_exp_vars_of_stmtE = store_thm ("bir_exp_vars_of_stmtE",
``!stmt. bir_vars_of_stmtE stmt =
         BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_stmtE stmt))
         ``,

Cases >> (
  SIMP_TAC list_ss [bir_vars_of_stmtE_def, bir_exps_of_stmtE_def,
    bir_exp_vars_of_label_exp, IMAGE_UNION, BIGUNION_UNION,
    IMAGE_INSERT, IMAGE_EMPTY, BIGUNION_INSERT, BIGUNION_EMPTY,
    UNION_EMPTY]
));


val bir_exp_vars_of_stmt = store_thm ("bir_exp_vars_of_stmt",
``!stmt. BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_stmt stmt)) SUBSET
         bir_vars_of_stmt stmt``,

Cases >> (
  SIMP_TAC std_ss [bir_exp_vars_of_stmtB, bir_exps_of_stmt_def,
    bir_vars_of_stmt_def, bir_exp_vars_of_stmtE, SUBSET_REFL]
));


val bir_exp_vars_of_block = store_thm ("bir_exp_vars_of_block",
``!bl. BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_block bl)) SUBSET
       bir_vars_of_block bl``,

SIMP_TAC std_ss [bir_exps_of_block_def,
  bir_vars_of_block_def, SUBSET_DEF, IN_UNION,
  IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bir_exp_vars_of_stmtE] >>
REPEAT STRIP_TAC >- METIS_TAC[] >>
DISJ1_TAC >>
rename1 `MEM stmt _` >>
Q.EXISTS_TAC `stmt` >>
MP_TAC (Q.SPECL [`stmt`] bir_exp_vars_of_stmtB) >>
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[]);


val bir_exp_vars_of_program = store_thm ("bir_exp_vars_of_program",
``!p. BIGUNION (IMAGE bir_vars_of_exp (bir_exps_of_program p)) SUBSET
       bir_vars_of_program p``,
Cases >>
MP_TAC bir_exp_vars_of_block >>
SIMP_TAC std_ss [bir_exps_of_program_def,
  bir_vars_of_program_def, SUBSET_DEF, IN_UNION,
  IN_BIGUNION, PULL_EXISTS, IN_IMAGE] >>
METIS_TAC[]);

(* ------------------- *)
(*  Initial BIR state  *)
(* ------------------- *)

val bir_state_init_def = Define `bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_env_default (bir_envty_of_vs (bir_vars_of_program p))
  ; bst_status := BST_Running
  ; bst_viewenv := FEMPTY
  ; bst_coh := \x.0
  ; bst_v_rOld := 0
  ; bst_v_CAP := 0
  ; bst_v_rNew := 0
  ; bst_v_wNew := 0
  ; bst_v_wOld := 0
  ; bst_v_Rel := 0
  ; bst_prom := []
  ; bst_fwdb := (\l. <| fwdb_time:= 0; fwdb_view:=0; fwdb_xcl:=F |>)
  ; bst_xclb := NONE
|>`;


val _ = export_theory();
