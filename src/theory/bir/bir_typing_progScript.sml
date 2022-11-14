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

val bir_stmts_of_block_def = Define `bir_stmts_of_block bl =
  (BStmtE (bl.bb_last_statement) INSERT (IMAGE BStmtB (set bl.bb_statements)))`;

val bir_stmts_of_prog_def = Define `bir_stmts_of_prog (BirProgram p) =
  BIGUNION (IMAGE bir_stmts_of_block (set p))`;

Theorem bir_get_current_statement_stmts_of_prog:
  !p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
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
  rename1 `_ = SOME xy` >> Cases_on `xy` >>
  rename1 `_ = SOME (i, bl)` >>
  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [] >>
  CASE_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >> (
    FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_THM] >>
    METIS_TAC[rich_listTheory.EL_MEM]
  )
QED


(* ------------------------------------------------------------------------- *)
(*  Well-typed Programs                                                      *)
(* ------------------------------------------------------------------------- *)

val bir_is_well_typed_label_exp_def = Define `
  (bir_is_well_typed_label_exp ext_map (BLE_Label _) = T) /\
  (bir_is_well_typed_label_exp ext_map (BLE_Exp e) = (case (type_of_bir_exp ext_map e) of
      NONE => F
    | SOME ty => (bir_type_is_Imm ty)))`;

val bir_is_well_typed_stmtE_def = Define `
  (bir_is_well_typed_stmtE ext_map (BStmt_Jmp le) = bir_is_well_typed_label_exp ext_map le) /\
  (bir_is_well_typed_stmtE ext_map (BStmt_CJmp c le1 le2) =
       ((type_of_bir_exp ext_map c = SOME BType_Bool) /\
       (bir_is_well_typed_label_exp ext_map le1) /\
       (bir_is_well_typed_label_exp ext_map le2))) /\
  (bir_is_well_typed_stmtE ext_map (BStmt_Halt e) = (type_of_bir_exp ext_map e <> NONE))`

val bir_is_well_typed_stmtB_def = Define `
  (bir_is_well_typed_stmtB ext_map (BStmt_Assign v e) =
    (type_of_bir_exp ext_map e = SOME (bir_var_type v))) /\
  (bir_is_well_typed_stmtB ext_map (BStmt_Assert e) =
    (type_of_bir_exp ext_map e = SOME BType_Bool)) /\
  (bir_is_well_typed_stmtB ext_map (BStmt_Assume e) =
    (type_of_bir_exp ext_map e = SOME BType_Bool)) /\
  (bir_is_well_typed_stmtB ext_map (BStmt_ExtPut en e) =
    (type_of_bir_exp ext_map e <> NONE /\ FLOOKUP (SND ext_map) en <> NONE))`;

val bir_is_well_typed_stmt_def = Define `
  (bir_is_well_typed_stmt ext_map (BStmtE s) = bir_is_well_typed_stmtE ext_map s) /\
  (bir_is_well_typed_stmt ext_map (BStmtB s) = bir_is_well_typed_stmtB ext_map s)`;

val bir_is_well_typed_block_def = Define `bir_is_well_typed_block ext_map bl <=>
  EVERY (bir_is_well_typed_stmtB ext_map) bl.bb_statements /\
  bir_is_well_typed_stmtE ext_map bl.bb_last_statement`;

val bir_is_well_typed_program_def = Define `bir_is_well_typed_program ext_map (BirProgram p) <=>
  (EVERY (bir_is_well_typed_block ext_map) p)`;

val bir_is_well_typed_block_ALT_DEF = store_thm ("bir_is_well_typed_block_ALT_DEF",
  ``!ext_map bl. bir_is_well_typed_block ext_map bl <=>
    (!stmt. stmt IN bir_stmts_of_block bl ==> bir_is_well_typed_stmt ext_map stmt)``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_well_typed_block_def, bir_stmts_of_block_def,
  IN_INSERT, IN_IMAGE, DISJ_IMP_THM, PULL_EXISTS, FORALL_AND_THM,
  bir_is_well_typed_stmt_def, listTheory.EVERY_MEM]);

val bir_is_well_typed_program_ALT_DEF = store_thm ("bir_is_well_typed_program_ALT_DEF",
  ``!ext_map p. bir_is_well_typed_program ext_map p <=>
    (!stmt. stmt IN bir_stmts_of_prog p ==> bir_is_well_typed_stmt ext_map stmt)``,

GEN_TAC >> Cases >>
SIMP_TAC std_ss [bir_is_well_typed_program_def,
  bir_stmts_of_prog_def, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
  listTheory.EVERY_MEM, bir_is_well_typed_block_ALT_DEF] >>
METIS_TAC[]);


val bir_get_current_statement_well_typed = store_thm ("bir_get_current_statement_well_typed",
  ``!ext_map p pc stmt. (bir_is_well_typed_program ext_map p /\
                (bir_get_current_statement p pc = SOME stmt)) ==>
                bir_is_well_typed_stmt ext_map stmt``,
METIS_TAC[bir_is_well_typed_program_ALT_DEF, bir_get_current_statement_stmts_of_prog]);




(* ------------------------------------------------------------------------- *)
(*  Variables of statements and programs                                     *)
(* ------------------------------------------------------------------------- *)

val bir_vars_of_stmtB_def = Define `
  (bir_vars_of_stmtB (BStmt_Assert ex) = bir_vars_of_exp ex) /\
  (bir_vars_of_stmtB (BStmt_Assume ex) = bir_vars_of_exp ex) /\
  (bir_vars_of_stmtB (BStmt_Assign v ex) = (v INSERT (bir_vars_of_exp ex))) /\
  (bir_vars_of_stmtB (BStmt_ExtPut _ ex) = bir_vars_of_exp ex)`;

Definition bmc_vars_of_stmtB_def:
     bmc_vars_of_stmtB (BMCStmt_Load var exp _ _ _ _) = { var } UNION bir_varset_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Store var exp exp' _ _ _) = { var } UNION bir_varset_of_exp exp UNION bir_varset_of_exp exp'
  /\ bmc_vars_of_stmtB (BMCStmt_Amo var exp exp' _ _) = { var } UNION bir_varset_of_exp exp UNION bir_varset_of_exp exp'
  /\ bmc_vars_of_stmtB (BMCStmt_Assign var exp) = { var } UNION bir_varset_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Fence _ _) = {}
  /\ bmc_vars_of_stmtB (BMCStmt_Assert exp) = bir_varset_of_exp exp
  /\ bmc_vars_of_stmtB (BMCStmt_Assume exp) = bir_varset_of_exp exp
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

val bir_vars_of_block_def = Define `bir_vars_of_block bl <=>
  ((BIGUNION (IMAGE bir_vars_of_stmtB (LIST_TO_SET bl.bb_statements))) UNION
   (bir_vars_of_stmtE bl.bb_last_statement))`;

val bmc_vars_of_block_def = Define `bmc_vars_of_block bl <=>
  ((BIGUNION (IMAGE bmc_vars_of_stmtB (LIST_TO_SET bl.bb_statements))) UNION
   (bir_vars_of_stmtE bl.bb_last_statement))`;

val bir_vars_of_program_def = Define `bir_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bir_vars_of_block (LIST_TO_SET p)))`;

val bmc_vars_of_program_def = Define `bmc_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bmc_vars_of_block (LIST_TO_SET p)))`;

val bir_vars_of_block_ALT_DEF = store_thm ("bir_vars_of_block_ALT_DEF",
  ``!bl. bir_vars_of_block bl = BIGUNION (IMAGE bir_vars_of_stmt (bir_stmts_of_block bl))``,

SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_vars_of_block_def, bir_stmts_of_block_def,
  IN_BIGUNION, PULL_EXISTS, IN_UNION, bir_vars_of_stmt_def,
  IN_IMAGE, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM]);


val bir_vars_of_program_ALT_DEF = store_thm ("bir_vars_of_program_ALT_DEF",
  ``!p. bir_vars_of_program p =
        BIGUNION (IMAGE bir_vars_of_stmt (bir_stmts_of_prog p))``,

Cases >>
SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC std_ss [bir_vars_of_program_def, bir_stmts_of_prog_def,
  IN_BIGUNION, PULL_EXISTS, IN_IMAGE, bir_vars_of_block_ALT_DEF] >>
METIS_TAC[]);


val bir_get_current_statement_vars_of = store_thm ("bir_get_current_statement_vars_of",
  ``!p pc stmt. (bir_get_current_statement p pc = SOME stmt) ==>
                bir_vars_of_stmt stmt SUBSET bir_vars_of_program p``,

SIMP_TAC std_ss [bir_vars_of_program_ALT_DEF, SUBSET_DEF, IN_BIGUNION,
  IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[bir_get_current_statement_stmts_of_prog]);


val bir_vars_of_label_exp_THM_EQ_FOR_VARS = store_thm ("bir_vars_of_label_exp_THM_EQ_FOR_VARS",
``!ext_map env1 env2 ext_st e. (bir_env_EQ_FOR_VARS (bir_vars_of_label_exp e) env1 env2) ==>
                (bir_eval_label_exp ext_map e env1 ext_st = bir_eval_label_exp ext_map e env2 ext_st)``,
Cases_on `e` >> (
  SIMP_TAC std_ss [bir_eval_label_exp_def, bir_vars_of_label_exp_def]
) >>
METIS_TAC[bir_vars_of_exp_THM_EQ_FOR_VARS]);



(* ------------------------------- *)
(*  Variables modified by program  *)
(* ------------------------------- *)


val bir_changed_vars_of_stmtB_def = Define `
  (bir_changed_vars_of_stmtB (BStmt_Assert ex) = {}) /\
  (bir_changed_vars_of_stmtB (BStmt_Assume ex) = {}) /\
  (bir_changed_vars_of_stmtB (BStmt_Assign v ex) = {v}) /\
  (bir_changed_vars_of_stmtB (BStmt_ExtPut _ _) = {})`;

val bir_changed_vars_of_stmt_def = Define `
  (bir_changed_vars_of_stmt (BStmtE s) = {}) /\
  (bir_changed_vars_of_stmt (BStmtB s) = bir_changed_vars_of_stmtB s)`;

val bir_changed_vars_of_block_def = Define `bir_changed_vars_of_block bl <=>
  (BIGUNION (IMAGE bir_changed_vars_of_stmtB (LIST_TO_SET bl.bb_statements)))`;

val bir_changed_vars_of_program_def = Define `bir_changed_vars_of_program (BirProgram p) <=>
  (BIGUNION (IMAGE bir_changed_vars_of_block (LIST_TO_SET p)))`;

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


val _ = export_theory();
