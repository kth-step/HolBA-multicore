open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory
open bir_programTheory HolBACoreSimps;
open bir_program_multistep_propsTheory;
open bir_program_env_orderTheory;
open bir_typing_progTheory;
open bir_typing_expTheory
open bir_program_valid_stateTheory
open pred_setTheory;

val _ = new_theory "bir_program_vars";

(* This theory shows that the variable sets of changed and used vars of
   a program are sensibly defined.

   At most the changed var set is modified. Moreover the behaviour of a program
   only depends on the vars in the full var set. *)



(**************************)
(* Complement of var sets *)
(**************************)

(* For sets of BIR variables, we need a special complement function. The lookup
   only considers the name, not the type. So, our special complement should ignore the
   type as well. *)
Definition bir_varset_COMPL_def:
  bir_varset_COMPL vs =
  {v | !v'. v' IN vs ==> (bir_var_name v <> bir_var_name v')}
End

Theorem IN_bir_varset_COMPL:
  !v vs. v IN bir_varset_COMPL vs <=> (!v'. v' IN vs ==> (bir_var_name v <> bir_var_name v'))
Proof
SIMP_TAC std_ss [bir_varset_COMPL_def, GSPECIFICATION]
QED

Theorem bir_varset_COMPL_EMPTY:
  bir_varset_COMPL EMPTY = UNIV
Proof
SIMP_TAC std_ss [EXTENSION, IN_bir_varset_COMPL, NOT_IN_EMPTY, IN_UNIV]
QED

Theorem bir_varset_COMPL_UNIV:
  bir_varset_COMPL UNIV = EMPTY
Proof
SIMP_TAC std_ss [EXTENSION, IN_bir_varset_COMPL, NOT_IN_EMPTY, IN_UNIV] >>
METIS_TAC[]
QED

Theorem bir_varset_COMPL_SUBSET_COMPL:
  !vs. bir_varset_COMPL vs SUBSET COMPL vs
Proof
SIMP_TAC std_ss [SUBSET_DEF, IN_bir_varset_COMPL, IN_COMPL] >>
METIS_TAC[]
QED

Theorem bir_varset_COMPL_UNION:
  !vs1 vs2. bir_varset_COMPL (vs1 UNION vs2) =
             bir_varset_COMPL vs1 INTER bir_varset_COMPL vs2
Proof
SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_bir_varset_COMPL] >>
METIS_TAC[]
QED


Theorem bir_varset_COMPL_SING:
  !v. bir_varset_COMPL {v} = {v' | bir_var_name v' <> bir_var_name v}
Proof
SIMP_TAC std_ss [bir_varset_COMPL_def, IN_INSERT, NOT_IN_EMPTY]
QED

Theorem bir_varset_COMPL_INSERT:
  !v vs. bir_varset_COMPL (v INSERT vs) =
          (bir_varset_COMPL vs INTER {v' | bir_var_name v' <> bir_var_name v})
Proof
SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_bir_varset_COMPL, IN_INSERT,
  GSPECIFICATION] >>
METIS_TAC[]
QED

Theorem bir_varset_COMPL_SUBSET:
  !vs1 vs2. vs2 SUBSET vs1 ==> (bir_varset_COMPL vs1 SUBSET bir_varset_COMPL vs2)
Proof
SIMP_TAC std_ss [SUBSET_DEF, IN_bir_varset_COMPL]
QED


Theorem bir_varset_COMPL_IN_EVAL:
  (!v. v IN bir_varset_COMPL EMPTY) /\
  (!v. ~(v IN bir_varset_COMPL UNIV)) /\
  (!v vs1 vs2. (v IN bir_varset_COMPL (vs1 UNION vs2)) <=>
       (v IN bir_varset_COMPL vs1 /\
        v IN bir_varset_COMPL vs2)) /\
  (!v vs v'. (v IN bir_varset_COMPL (v' INSERT vs)) <=>
       (bir_var_name v <> bir_var_name v') /\
       (v IN bir_varset_COMPL vs))
Proof
SIMP_TAC std_ss [IN_bir_varset_COMPL, IN_INSERT, IN_UNIV,
  NOT_IN_EMPTY, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM] >>
METIS_TAC[]
QED



(****************)
(* Changed vars *)
(****************)

(* At most the vars in the changed var set are modified *)
Theorem bir_changed_vars_of_stmtB_THM:
  !st stmt.
   (bir_env_EQ_FOR_VARS (bir_varset_COMPL (bir_changed_vars_of_stmtB stmt))
        (bir_exec_stmtB_state stmt st).bst_environ (st.bst_environ))
Proof
Cases_on `stmt` >> (
  (* Interesting case is only assign. In all other cases
     the env is not changed. *)
  SIMP_TAC std_ss [bir_changed_vars_of_stmtB_def,
    bir_exec_stmt_assume_SAME_ENV,
    bir_exec_stmt_assert_SAME_ENV,
    bir_exec_stmt_observe_SAME_ENV,
    bir_exec_stmtB_state_def, bir_exec_stmtB_def,
    bir_env_EQ_FOR_VARS_EQUIV
  ]
) >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_EQ_FOR_VARS_def, bir_varset_COMPL_IN_EVAL]
) >>
  (* assign *)
  GEN_TAC >>
  Cases_on `st.bst_environ` >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assign_def,
    bir_env_write_def, LET_DEF, bir_env_update_def] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def,
      bir_env_lookup_UPDATE]
  )
QED


Theorem bir_changed_vars_of_stmt_THM:
  !st p stmt.
   (bir_env_EQ_FOR_VARS (bir_varset_COMPL (bir_changed_vars_of_stmt stmt))
        (bir_exec_stmt_state p stmt st).bst_environ (st.bst_environ))
Proof
REPEAT GEN_TAC >>
Cases_on `stmt` >- (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [bir_exec_stmt_state_REWRS, LET_THM,
    bir_changed_vars_of_stmt_def] >>
  METIS_TAC[bir_changed_vars_of_stmtB_THM]
) >>
SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, bir_exec_stmtE_env_unchanged,
  bir_env_EQ_FOR_VARS_EQUIV]
QED


Theorem bir_changed_vars_exec_step_THM:
  !(p:'a bir_program_t) st.
   (bir_env_EQ_FOR_VARS (bir_varset_COMPL (bir_changed_vars_of_program p))
        ((bir_exec_step_state p st).bst_environ) (st.bst_environ))
Proof
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def,
  bir_env_EQ_FOR_VARS_EQUIV] >>
Cases_on ` bir_get_current_statement p st.bst_pc` >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def,
    bir_env_EQ_FOR_VARS_EQUIV]
) >>
rename1 `_ = SOME stmt` >>
ASM_SIMP_TAC std_ss [GSYM bir_exec_stmt_state_def] >>
DISJ2_TAC >>

`bir_changed_vars_of_stmt stmt SUBSET (bir_changed_vars_of_program p)` by (
  METIS_TAC[bir_get_current_statement_changed_vars_of]
) >>
METIS_TAC[bir_changed_vars_of_stmt_THM, bir_env_EQ_FOR_VARS_SUBSET,
    bir_varset_COMPL_SUBSET, bir_env_EQ_FOR_VARS_EQUIV]
QED


Theorem bir_changed_vars_exec_step_n_THM:
  !(p:'a bir_program_t) n st.
   (bir_env_EQ_FOR_VARS (bir_varset_COMPL (bir_changed_vars_of_program p))
        ((let (ol, n', st') = bir_exec_step_n p st n in st').bst_environ) (st.bst_environ))
Proof
GEN_TAC >> Induct >- (
  SIMP_TAC std_ss [bir_exec_step_n_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_n_SUC, LET_THM,
  bir_env_EQ_FOR_VARS_EQUIV] >>
GEN_TAC >> DISJ2_TAC >>
Cases_on `bir_exec_step p st` >> rename1 `_ = (fe, st')` >>
`?l c st''.  (bir_exec_step_n p st' n) = (l, c, st'')` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `st`] bir_changed_vars_exec_step_THM) >>
Q.PAT_X_ASSUM `!st. _` (MP_TAC o Q.SPEC `st'`) >>
ASM_SIMP_TAC std_ss [bir_exec_step_state_def, LET_THM] >>
METIS_TAC[bir_env_EQ_FOR_VARS_EQUIV]
QED




(************)
(* All vars *)
(************)

Definition bir_state_EQ_FOR_VARS_def:
  bir_state_EQ_FOR_VARS vs st1 st2 <=> (
    ?env.
      (st2 = st1 with bst_environ := env) /\
      bir_env_EQ_FOR_VARS vs env (st1.bst_environ))
End

Theorem bir_state_EQ_FOR_VARS_ALT_DEF:
  !vs st1 st2.
  bir_state_EQ_FOR_VARS vs st1 st2 <=>
  (st1.bst_pc = st2.bst_pc) /\ (st1.bst_status = st2.bst_status) /\
  bir_env_EQ_FOR_VARS vs st1.bst_environ st2.bst_environ
Proof
SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_state_t_component_equality,
  bir_state_EQ_FOR_VARS_def, bir_env_EQ_FOR_VARS_EQUIV]
QED

Theorem bir_state_EQ_FOR_VARS_SYM_thm:
  !vs st1 st2.
  bir_state_EQ_FOR_VARS vs st1 st2 <=>
  bir_state_EQ_FOR_VARS vs st2 st1
Proof
  METIS_TAC [bir_state_EQ_FOR_VARS_ALT_DEF, bir_env_EQ_FOR_VARS_EQUIV_EQ]
QED

Theorem bir_vars_EQ_state_restrict_vars_THM:
  !vs st.
    bir_state_EQ_FOR_VARS vs st (bir_state_restrict_vars vs st)
Proof
  FULL_SIMP_TAC std_ss [bir_state_EQ_FOR_VARS_ALT_DEF, bir_env_EQ_FOR_VARS_def] >>
  METIS_TAC [bir_state_restrict_vars_ALT_THM, bir_env_oldTheory.bir_env_restrict_vars_IN_THM]
QED


(* At most the vars in the changed var set are modified *)
Theorem bir_vars_of_stmtB_THM:
  !st1 st2 vs stmt.
    (bir_vars_of_stmtB stmt SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (oo1, st1') = bir_exec_stmtB stmt st1 in
     let (oo2, st2') = bir_exec_stmtB stmt st2 in
     ((oo1 = oo2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_state_EQ_FOR_VARS_ALT_DEF] >>
`bir_env_EQ_FOR_VARS (bir_vars_of_stmtB stmt) st1.bst_environ st2.bst_environ` by
  METIS_TAC[bir_env_EQ_FOR_VARS_SUBSET] >>
Cases_on `st1.bst_environ` >>
Cases_on `st2.bst_environ` >>
rename1 `bir_env_EQ_FOR_VARS _ (BEnv env1) (BEnv env2)` >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC std_ss [
    bir_exec_stmt_assume_SAME_ENV,
    bir_exec_stmt_assert_SAME_ENV,
    bir_exec_stmt_observe_SAME_ENV,
    bir_exec_stmtB_state_def, bir_exec_stmtB_def,
    bir_env_EQ_FOR_VARS_EQUIV, LET_THM
  ]
) >| [
  (* assign *)
  rename1 `bir_exec_stmt_assign v e` >>
  `bir_eval_exp e (BEnv env1) = bir_eval_exp e (BEnv env2)` by (
     MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
     FULL_SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, IN_INSERT, bir_vars_of_stmtB_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assign_def,
    bir_env_write_def, LET_DEF, bir_env_update_def, bir_vars_of_stmtB_def,
    IN_INSERT, DISJ_IMP_THM, bir_env_EQ_FOR_VARS_def, FORALL_AND_THM,
    bir_env_check_type_def, bir_env_lookup_type_def] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def,
      bir_env_lookup_UPDATE]
  ) >> (
    Q.PAT_X_ASSUM `!v. v IN vs ==> _` (fn thm => ASSUME_TAC (Q.SPEC `v` thm)) >>
    `v IN vs` by FULL_SIMP_TAC std_ss [INSERT_SUBSET] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_env_lookup_def]
  ),

  (* assert *)
  rename1 `bir_exec_stmt_assert e` >>
  `bir_eval_exp e (BEnv env1) = bir_eval_exp e (BEnv env2)` by (
     MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
     FULL_SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, IN_INSERT, bir_vars_of_stmtB_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assert_def] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
  ),

  (* assume *)
  rename1 `bir_exec_stmt_assume e` >>
  `bir_eval_exp e (BEnv env1) = bir_eval_exp e (BEnv env2)` by (
     MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
     FULL_SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, bir_vars_of_stmtB_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assume_def] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
  ),

  (* observe *)
  rename1 `bir_exec_stmt_observe oid e el fl` >>
  `!e'. MEM e' (e::el) ==> (bir_eval_exp e' (BEnv env1) = bir_eval_exp e' (BEnv env2))` by (
     REPEAT STRIP_TAC >>
     MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
     FULL_SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, bir_vars_of_stmtB_def,
       IN_BIGUNION, IN_IMAGE, PULL_EXISTS] >>
     METIS_TAC []
  ) >>

  FULL_SIMP_TAC (list_ss++holBACore_ss++pairSimps.gen_beta_ss) [bir_exec_stmt_observe_def,
    DISJ_IMP_THM, FORALL_AND_THM, LET_DEF] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_typeerror_def]
  ) >> (
    subgoal `(MAP (\e'. bir_eval_exp e' (BEnv env1)) el) =
               (MAP (\e'. bir_eval_exp e' (BEnv env2)) el)` >- (
      ASM_SIMP_TAC std_ss [listTheory.MAP_EQ_f]
    ) >>
    FULL_SIMP_TAC std_ss []
  )
]
QED


Theorem bir_vars_of_stmtB_state_THM:
  !st1 st2 vs stmt.
    (bir_vars_of_stmtB stmt SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>

    (bir_state_EQ_FOR_VARS vs
      (bir_exec_stmtB_state stmt st1)
      (bir_exec_stmtB_state stmt st2))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`st1`, `st2`, `vs`, `stmt`] bir_vars_of_stmtB_THM) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_DEF,
  bir_exec_stmtB_state_def]
QED


Theorem bir_vars_of_stmtE_THM:
  !st1 st2 vs p stmt.
    (bir_vars_of_stmtE stmt SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_EQ_FOR_VARS vs
      (bir_exec_stmtE p stmt st1)
      (bir_exec_stmtE p stmt st2))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_state_EQ_FOR_VARS_ALT_DEF] >>
`bir_env_EQ_FOR_VARS (bir_vars_of_stmtE stmt) st1.bst_environ st2.bst_environ` by
  METIS_TAC[bir_env_EQ_FOR_VARS_SUBSET] >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC std_ss [bir_vars_of_stmtE_def,
    bir_exec_stmtE_env_unchanged, bir_exec_stmtE_def]
) >| [
  (* Jmp *)
  rename1 `bir_exec_stmt_jmp _ le _` >>
  `bir_eval_label_exp le st1.bst_environ = bir_eval_label_exp le st2.bst_environ` by
    METIS_TAC[bir_vars_of_label_exp_THM_EQ_FOR_VARS] >>
  FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def, bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def] >>
  REPEAT CASE_TAC >> ASM_SIMP_TAC (std_ss++holBACore_ss) [],


  (* CJmp *)
  rename1 `bir_exec_stmt_cjmp _ ec le1 le2` >>
  `(bir_eval_label_exp le1 st1.bst_environ = bir_eval_label_exp le1 st2.bst_environ) /\
   (bir_eval_label_exp le2 st1.bst_environ = bir_eval_label_exp le2 st2.bst_environ) /\
   (bir_eval_exp ec st1.bst_environ = bir_eval_exp ec st2.bst_environ)` by
    METIS_TAC[bir_vars_of_label_exp_THM_EQ_FOR_VARS,
              bir_vars_of_exp_THM_EQ_FOR_VARS,
              SUBSET_UNION, bir_env_EQ_FOR_VARS_SUBSET] >>

  FULL_SIMP_TAC std_ss [bir_exec_stmt_cjmp_def, bir_state_set_typeerror_def,
     bir_exec_stmt_jmp_to_label_def, bir_exec_stmt_jmp_def] >>
  REPEAT CASE_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [LET_DEF] >>
  Cases_on `bir_eval_exp ec st2.bst_environ` >> (
    ASM_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    rename1 `bir_dest_bool_val abcde` >> Cases_on `bir_dest_bool_val abcde`
  ) >> (
    ASM_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ) >> (
    COND_CASES_TAC >>
    ASM_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF]
  ),


  (* Halt *)
  rename1 `bir_exec_stmt_halt e` >>
  `bir_eval_exp e st1.bst_environ = bir_eval_exp e st2.bst_environ` by
    METIS_TAC[bir_vars_of_exp_THM_EQ_FOR_VARS] >>
  Cases_on `bir_eval_exp e st2.bst_environ` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_halt_def, bir_state_set_typeerror_def]
  )
]
QED


Theorem bir_vars_of_stmt_THM:
  !st1 st2 vs p stmt.
    (bir_vars_of_stmt stmt SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (oo1, st1') = bir_exec_stmt p stmt st1 in
     let (oo2, st2') = bir_exec_stmt p stmt st2 in
     ((oo1 = oo2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))
Proof
REPEAT STRIP_TAC >>
Cases_on `stmt` >> (
  FULL_SIMP_TAC (std_ss++pairSimps.gen_beta_ss++boolSimps.LIFT_COND_ss++
      bir_TYPES_ss) [
    bir_vars_of_stmt_def, bir_exec_stmt_state_def,
    bir_exec_stmt_def, LET_DEF,
    bir_state_EQ_FOR_VARS_ALT_DEF,
    bir_program_valid_stateTheory.bir_exec_stmtB_pc_unchanged,
    bir_state_is_terminated_def]
) >| [
  rename1 `bir_vars_of_stmtB stmt` >>
  MP_TAC (Q.SPECL [`st1`, `st2`, `vs`, `stmt`] bir_vars_of_stmtB_THM) >>
  FULL_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [bir_state_EQ_FOR_VARS_ALT_DEF, LET_DEF],

  METIS_TAC[bir_state_EQ_FOR_VARS_ALT_DEF, bir_vars_of_stmtE_THM]
]
QED


Theorem bir_vars_of_stmt_state_THM:
  !st1 st2 vs p stmt.
    (bir_vars_of_stmt stmt SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_EQ_FOR_VARS vs
      (bir_exec_stmt_state p stmt st1)
      (bir_exec_stmt_state p stmt st2))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`st1`, `st2`, `vs`, `p`, `stmt`] bir_vars_of_stmt_THM) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_DEF, bir_exec_stmt_state_def]
QED


Theorem bir_vars_exec_step_THM:
  !p st1 st2 vs.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (oo1, st1') = bir_exec_step p st1 in
     let (oo2, st2') = bir_exec_step p st2 in
     ((oo1 = oo2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))
Proof
REPEAT STRIP_TAC >>
`(bir_state_is_terminated st2 = bir_state_is_terminated st1) /\
 (st1.bst_pc = st2.bst_pc)` by
  FULL_SIMP_TAC std_ss [bir_state_is_terminated_def, bir_state_EQ_FOR_VARS_ALT_DEF] >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def,
  bir_env_EQ_FOR_VARS_EQUIV, LET_THM] >>
Cases_on ` bir_get_current_statement p st2.bst_pc` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def,
    bir_state_EQ_FOR_VARS_ALT_DEF,
    bir_env_EQ_FOR_VARS_EQUIV]
) >>
rename1 `_ = SOME stmt` >>
ASM_SIMP_TAC std_ss [] >>
DISJ2_TAC >>

`bir_vars_of_stmt stmt SUBSET vs` by (
  METIS_TAC[bir_get_current_statement_vars_of, SUBSET_TRANS]
) >>

MP_TAC (Q.SPECL [`st1`, `st2`, `vs`, `p`, `stmt`] bir_vars_of_stmt_THM) >>
ASM_SIMP_TAC std_ss [LET_THM]
QED


Theorem bir_vars_exec_step_state_THM:
  !p st1 st2 vs.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_EQ_FOR_VARS vs (bir_exec_step_state p st1) (bir_exec_step_state p st2))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`p`, `st1`, `st2`, `vs`] bir_vars_exec_step_THM) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_THM, bir_exec_step_state_def]
QED



Theorem bir_vars_exec_infinite_step_fun_THM:
  !p vs i st1 st2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_EQ_FOR_VARS vs (bir_exec_infinite_steps_fun p st1 i) (bir_exec_infinite_steps_fun p st2 i))
Proof
NTAC 2 GEN_TAC >>
Induct >> (
  SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>
METIS_TAC[bir_vars_exec_step_state_THM]
QED


Theorem bir_vars_exec_step_n_THM:
  !p vs n st1 st2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (let (ol1, n1, st1') = bir_exec_step_n p st1 n in
     let (ol2, n2, st2') = bir_exec_step_n p st2 n in
     ((ol1 = ol2) /\ (n1 = n2) /\ (bir_state_EQ_FOR_VARS vs st1' st2')))
Proof
NTAC 2 GEN_TAC >> Induct >- (
  SIMP_TAC std_ss [bir_exec_step_n_REWRS, LET_THM, bir_env_EQ_FOR_VARS_EQUIV]
) >>
REPEAT STRIP_TAC >>
`?oo1 st1'. bir_exec_step p st1 = (oo1, st1')` by METIS_TAC[pairTheory.PAIR] >>
`?oo2 st2'. bir_exec_step p st2 = (oo2, st2')` by METIS_TAC[pairTheory.PAIR] >>
Q.PAT_X_ASSUM `!st1 st2. _` (MP_TAC o Q.SPECL [`st1'`, `st2'`]) >>
MP_TAC (Q.SPECL [`p`, `st1`, `st2`, `vs`] bir_vars_exec_step_THM) >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++pairSimps.gen_beta_ss) [LET_THM, bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def,
  bir_exec_step_n_SUC]
QED


Theorem bir_vars_exec_steps_THM_aux_SOME[local]:
  !p vs st1 st2 st1' ol c c'.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_steps p st1 = BER_Ended ol c c' st1') ==>
    (?st2'. (bir_exec_steps p st2 = BER_Ended ol c c' st2') /\
            (bir_state_EQ_FOR_VARS vs st1' st2'))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_TO_bir_exec_step_n] >>
`?l1 c1 st2'. bir_exec_step_n p st2 c = (l1, c1, st2')` by METIS_TAC[pairTheory.PAIR] >>
MP_TAC (Q.SPECL [`p`, `vs`, `c`, `st1`, `st2`] bir_vars_exec_step_n_THM) >>
FULL_SIMP_TAC std_ss [LET_THM, bir_state_is_terminated_def, bir_state_EQ_FOR_VARS_ALT_DEF] >>
METIS_TAC[]
QED



Theorem bir_vars_exec_steps_THM_aux_NONE[local]:
  !p vs st1 st2 st1' ll1 ll2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_steps p st1 = BER_Looping ll1) ==>
    (bir_exec_steps p st2 = BER_Looping ll2) ==>
    (ll1 = ll2)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_steps_EQ_Looping,
  bir_exec_steps_observe_llist_def] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
`!i. FST (bir_exec_step p (bir_exec_infinite_steps_fun p st1 i)) =
     FST (bir_exec_step p (bir_exec_infinite_steps_fun p st2 i))` suffices_by SIMP_TAC std_ss [] >>

GEN_TAC >>
MP_TAC (Q.SPECL [`p`, `bir_exec_infinite_steps_fun p st1 i`, `bir_exec_infinite_steps_fun p st2 i`, `vs`] bir_vars_exec_step_THM) >>
MP_TAC (Q.SPECL [`p`, `vs`, `i`, `st1`, `st2`] bir_vars_exec_infinite_step_fun_THM) >>
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [LET_THM]
QED



Theorem bir_vars_exec_steps_THM:
  !p vs st1 st2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_steps p st1, bir_exec_steps p st2) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n2' = n2) /\ (n1' = n2) /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
REPEAT STRIP_TAC >>
Cases_on `bir_exec_steps p st1` >- (
  MP_TAC (Q.SPECL [`p`, `vs`, `st1`, `st2`] bir_vars_exec_steps_THM_aux_SOME) >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [PULL_EXISTS, LET_THM, pairTheory.pair_case_thm] >>
  SIMP_TAC std_ss [bir_exec_steps_EQ_Ended]
) >- (
  Cases_on `bir_exec_steps p st2` >- (
    MP_TAC (Q.SPECL [`p`, `vs`, `st2`, `st1`] bir_vars_exec_steps_THM_aux_SOME) >>
    FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_EQ_FOR_VARS_ALT_DEF, bir_env_EQ_FOR_VARS_EQUIV]
  ) >>

  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [pairTheory.pair_case_thm] >>
  METIS_TAC[bir_vars_exec_steps_THM_aux_NONE]
)
QED

(* ------------------------------- *)

Theorem bir_vars_state_COUNT_PC_THM:
  !vs st1 st2 pc_cond.
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_state_COUNT_PC pc_cond st1 =
     bir_state_COUNT_PC pc_cond st2)
Proof
  REPEAT STRIP_TAC >>
  Cases_on `pc_cond` >>
  FULL_SIMP_TAC (std_ss) [bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_COUNT_PC_def]
QED

Theorem bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM:
  !vs st1 st2 pc_cond p i.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st1 i =
     bir_exec_infinite_steps_fun_COUNT_PCs pc_cond p st2 i)
Proof
  Induct_on `i` >> (
    REWRITE_TAC [bir_exec_infinite_steps_fun_COUNT_PCs_def]
  ) >>
  REPEAT STRIP_TAC >>

  IMP_RES_TAC (SIMP_RULE std_ss [LET_THM] bir_vars_exec_step_state_THM) >>
  PAT_X_ASSUM ``!x. A`` (IMP_RES_TAC) >>
  IMP_RES_TAC bir_vars_state_COUNT_PC_THM >>
  REPEAT (PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o Q.SPEC `pc_cond`)) >>

  FULL_SIMP_TAC std_ss [LET_THM]
QED

Theorem bir_vars_exec_infinite_steps_COUNT_STEPS_THM:
  !vs st1 st2 pc_cond p max_steps_opt.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st1 =
     bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st2)
Proof
  REPEAT STRIP_TAC >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st1` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_EQ_NONE] >>
    GEN_TAC >>
    POP_ASSUM (ASSUME_TAC o Q.SPEC `i`) >>
    FULL_SIMP_TAC std_ss [] >>
    IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
    IMP_RES_TAC bir_vars_exec_infinite_step_fun_THM >>
    METIS_TAC [bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
  ) >>

  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_COUNT_STEPS_def, whileTheory.OLEAST_EQ_SOME] >> (
    STRIP_TAC >- (
      IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
      IMP_RES_TAC bir_vars_exec_infinite_step_fun_THM >>
      METIS_TAC [bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
    ) >>
    ASM_SIMP_TAC std_ss [] >>
    POP_ASSUM (fn t => GEN_TAC >> DISCH_TAC >> IMP_RES_TAC t) >>
    STRIP_TAC >> (
      IMP_RES_TAC bir_vars_exec_infinite_step_fun_THM >>
      IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
      METIS_TAC [bir_state_EQ_FOR_VARS_ALT_DEF, bir_state_is_terminated_def]
    )
  )
QED

Theorem bir_vars_exec_steps_observe_llist_aux_THM:
  !vs st1 st2 p i.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (FST (bir_exec_step p (bir_exec_infinite_steps_fun p st1 i)) =
     FST (bir_exec_step p (bir_exec_infinite_steps_fun p st2 i)))
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_infinite_step_fun_THM >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `i`) >>
  IMP_RES_TAC bir_vars_exec_step_THM >>

  Cases_on `bir_exec_step p (bir_exec_infinite_steps_fun p st1 i)` >>
  Cases_on `bir_exec_step p (bir_exec_infinite_steps_fun p st2 i)` >>
  FULL_SIMP_TAC std_ss [LET_THM]
QED

Theorem bir_vars_exec_steps_observe_llist_THM:
  !vs st1 st2 p step_no.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_steps_observe_llist p st1 step_no =
     bir_exec_steps_observe_llist p st2 step_no)
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_steps_observe_llist_aux_THM >>
  ASM_SIMP_TAC std_ss [bir_exec_steps_observe_llist_def]
QED

Theorem bir_vars_exec_steps_GEN_THM:
  !vs st1 st2 pc_cond p max_steps_opt.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_steps_GEN pc_cond p st1 max_steps_opt, bir_exec_steps_GEN pc_cond p st2 max_steps_opt) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_infinite_steps_COUNT_STEPS_THM >>
  IMP_RES_TAC bir_vars_exec_infinite_steps_fun_COUNT_PCs_THM >>
  IMP_RES_TAC bir_vars_exec_steps_observe_llist_THM >>

  ASM_REWRITE_TAC [bir_exec_steps_GEN_def] >>
  Q.ABBREV_TAC `step_no = bir_exec_infinite_steps_COUNT_STEPS pc_cond max_steps_opt p st2` >>
  Q.ABBREV_TAC `ll = bir_exec_steps_observe_llist p st2 step_no` >>
  FULL_SIMP_TAC std_ss [LET_THM] >>

  CASE_TAC >>
  METIS_TAC [bir_vars_exec_infinite_step_fun_THM]
QED

Theorem bir_vars_exec_to_labels_n_THM:
  !vs st1 st2 p ls n.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_to_labels_n ls p st1 n, bir_exec_to_labels_n ls p st2 n) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REWRITE_TAC [bir_exec_to_labels_n_def, bir_vars_exec_steps_GEN_THM]
QED

Theorem bir_vars_exec_to_labels_THM:
  !ls p vs st1 st2.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (case (bir_exec_to_labels ls p st1, bir_exec_to_labels ls p st2) of
         | (BER_Looping ll1, BER_Looping ll2) => ll1 = ll2
         | (BER_Ended ol1 n1 n1' st1', BER_Ended ol2 n2 n2' st2') =>
              (ol1 = ol2) /\ (n1 = n2) /\ (n1' = n2') /\
              (bir_state_EQ_FOR_VARS vs st1' st2')
         | (_, _) => F)
Proof
  REWRITE_TAC [bir_exec_to_labels_def, bir_vars_exec_to_labels_n_THM]
QED

Theorem bir_vars_exec_to_labels_spec_THM:
  !ls p vs st1 st2 ol n n' st1'.
    (bir_vars_of_program p SUBSET vs) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_to_labels ls p st1 = BER_Ended ol n n' st1') ==>
    ?st2'. bir_exec_to_labels ls p st2 = BER_Ended ol n n' st2' /\
           bir_state_EQ_FOR_VARS vs st1' st2'
Proof
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_vars_exec_to_labels_THM >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `ls`) >>

  Cases_on `bir_exec_to_labels ls p st2` >> (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_execution_result_t_11, pairTheory.pair_CASE_def]
  )
QED

Theorem bir_vars_exec_to_labels_spec2_THM:
  !ls p vs st1 st2 ol n n' st1'.
    (vs = bir_vars_of_program p) ==>
    (bir_state_EQ_FOR_VARS vs st1 st2) ==>
    (bir_exec_to_labels ls p st1 = BER_Ended ol n n' st1') ==>
    ?st2'. bir_exec_to_labels ls p st2 = BER_Ended ol n n' st2' /\
           bir_state_EQ_FOR_VARS vs st1' st2'
Proof
  METIS_TAC [pred_setTheory.SUBSET_REFL, bir_vars_exec_to_labels_spec_THM]
QED



val _ = export_theory();
