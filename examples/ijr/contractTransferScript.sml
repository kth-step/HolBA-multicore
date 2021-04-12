open HolKernel Parse boolLib bossLib;

open listTheory;

open bir_programTheory bir_htTheory bir_program_multistep_propsTheory;
open HolBACoreSimps;

open resolutionTheory simulationTheory;

val _ = new_theory "contractTransfer";


Definition exec_to_prog_n_def:
  exec_to_prog_n p s pls n =
  bir_exec_to_labels_n (set (bir_labels_of_program pls)) p s n
End

(*TODO: Strenthen simulation definitions wrt observations and steps?*)
Definition simulated_n_def:
  simulated_n p p' =
  ∀n s l s' os2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒

    exec_to_prog_n p' s p n = BER_Ended os2 m2 n2 s' ⇒
    ~(∃l'. s'.bst_status = BST_JumpOutside l') ⇒
    (∃os1 m1 n1.
      exec_to_prog_n p s p n = BER_Ended os1 m1 n1 s')
End

Theorem simulated_simulated_n:
  ∀p p'. simulated p p' ⇒ simulated_n p p'
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [simulated_n_def, exec_to_prog_n_def] >>
Q.ABBREV_TAC ‘ls = bir_labels_of_program p’ >>

Induct_on ‘n’ >- (
  SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_0]
) >>

REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_n_REWR_SUC] >>

(*Program p' takes a step*)
Cases_on ‘bir_exec_to_labels (set ls) p' s’ >>
SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 ‘_ = BER_Ended os21 m21 n21 s2’ >>

(*There is a contradiction or p takes the same step*)
Cases_on ‘(∃l'. s2.bst_status = BST_JumpOutside l')’ >- (
  FULL_SIMP_TAC (list_ss++holBACore_ss) [bir_state_is_terminated_def,
                                         bir_exec_to_labels_n_REWR_TERMINATED] >>
  STRIP_TAC >> FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
subgoal ‘(∃os11 m11 n11.
            bir_exec_to_labels (set ls) p s = BER_Ended os11 m11 n11 s2)’ >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [simulated_def, exec_to_prog_def]
) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>

(*If programs are terminated, rest of steps are same (needed to use induction hypothesis)*)
Cases_on ‘(bir_state_is_terminated s2)’ >- (
  FULL_SIMP_TAC (list_ss++holBACore_ss) [bir_state_is_terminated_def,
                                         bir_exec_to_labels_n_REWR_TERMINATED]
) >>

(*Program p' takes the rest of the steps*)
Cases_on ‘bir_exec_to_labels_n (set ls) p' s2 n’ >>
SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 ‘_ = BER_Ended os22 m22 n22 s2'’ >>
NTAC 2 STRIP_TAC >>

(*Program p takes the same rest of steps*)
subgoal ‘∃os12 m12 n12.
           bir_exec_to_labels_n (set ls) p s2 n = BER_Ended os12 m12 n12 s2'’ >- (
  subgoal ‘∃l'. s2.bst_pc = bir_block_pc l' ∧ MEM l' ls’ >- (
    MP_TAC (Q.SPECL [‘set ls’, ‘p'’, ‘s’, ‘os21’, ‘1’, ‘m21’, ‘n21’, ‘s2’]
                    bir_exec_to_labels_n_ended_running) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_block_pc_def, bir_exec_to_labels_def,
                   bir_programcounter_t_component_equality]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [exec_to_prog_n_def]
) >>
ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem bir_exec_to_labels_expand_labels:
  ∀ls ls' p s s' os c1 c2.
    ls SUBSET ls' ⇒
    bir_exec_to_labels ls p s = BER_Ended os c1 c2 s' ⇒
    (∃n c2'.
       n > 0 ∧
       bir_exec_to_labels_n ls' p s n = BER_Ended os c1 c2' s' ∧
       (∀n'. 0 < n' ∧ n' < n ⇒
             ∃s'' os' c1' c2''.
               bir_exec_to_labels_n ls' p s n' = BER_Ended os' c1' c2'' s'' ∧
               ~(s''.bst_pc.bpc_label IN ls)))
Proof
cheat
QED

Theorem bir_exec_to_labels_restrict_labels:
  ∀ls ls' n p s s' os c1 c2.
    ls SUBSET ls' ⇒
    n > 0 ⇒
    bir_exec_to_labels_n ls' p s n = BER_Ended os c1 c2 s' ⇒
    s'.bst_pc.bpc_label IN ls ⇒
    (∀n'. 0 < n' ∧ n' < n ⇒
          ∃s'' os' c1' c2''.
            bir_exec_to_labels_n ls' p s n' = BER_Ended os' c1' c2'' s'' ∧
            ~(s''.bst_pc.bpc_label IN ls)) ⇒
    (∃c2'. bir_exec_to_labels ls p s = BER_Ended os c1 c2' s')
Proof
cheat
QED

Definition simulated_contract_def:
  simulated_contract p p' =
  ∀s l ls s' os2 m2 n2.
    s.bst_pc = bir_block_pc l ⇒
    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels ls p' s = BER_Ended os2 m2 n2 s' ⇒
    ~(bir_state_is_terminated s') ⇒
    (∃os1 m1 n1.
      bir_exec_to_labels ls p s = BER_Ended os1 m1 n1 s')
End

Theorem simulated_simulated_contract:
  ∀p p'. simulated p p' ⇒ simulated_contract p p'
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [simulated_contract_def, exec_to_prog_n_def] >>
Q.ABBREV_TAC ‘pls = bir_labels_of_program p’ >>

(*Expand label set*)
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [‘ls’, ‘set pls’, ‘p'’, ‘s’, ‘s'’, ‘os2’, ‘m2’, ‘n2’]
                bir_exec_to_labels_expand_labels) >>
ASM_SIMP_TAC std_ss [] >> STRIP_TAC >>
rename1 ‘_ = BER_Ended _ _ n2' _’ >>

(*Use simulation hypothesis*)
subgoal ‘∃os1 m1 n1. bir_exec_to_labels_n (set pls) p s n =
                     BER_Ended os1 m1 n1 s'’ >- (
  subgoal ‘~(∃l'. s'.bst_status = BST_JumpOutside l')’ >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
  ) >>
  METIS_TAC [simulated_simulated_n, simulated_n_def, exec_to_prog_n_def]
) >>

(*Restrict label set*)
subgoal ‘∃n1'.bir_exec_to_labels ls p s = BER_Ended os1 m1 n1' s'’ >- (
  IRULE_TAC bir_exec_to_labels_restrict_labels >>
  CONJ_TAC >- (
    ‘(1:num) > 0’ by SIMP_TAC arith_ss [] >>
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_labels_n_ended_running]
  ) >>

  Q.LIST_EXISTS_TAC [‘n1’, ‘set pls’, ‘n’] >> CONJ_TAC >- (
    REPEAT STRIP_TAC >>
    Q.PAT_X_ASSUM ‘∀n'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘n'’ thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    subgoal ‘~(∃l'. s''.bst_status = BST_JumpOutside l')’ >- (
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def] >>
      ‘~bir_state_is_terminated s''’ by
        IMP_RES_TAC bir_exec_steps_GEN_decrease_max_steps_Ended_terminated >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
    ) >>
    subgoal ‘∃os' c1' c2''. bir_exec_to_labels_n (set pls) p s n' =
                            BER_Ended os' c1' c2'' s''’ >- (
      METIS_TAC [simulated_simulated_n, simulated_n_def, exec_to_prog_n_def]
    ) >>

    PROVE_TAC []
  ) >>

  ASM_SIMP_TAC std_ss []
) >>
PROVE_TAC []
QED

Theorem contract_transfer:
  ∀ p p' l ls pre post.
    simulated p p' ⇒
    bir_vars_of_program p' = bir_vars_of_program p ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
SIMP_TAC std_ss [bir_exec_to_labels_triple_def] >>
REPEAT STRIP_TAC >>

Q.PAT_X_ASSUM ‘simulated p p'’
  (fn thm => ASSUME_TAC (MATCH_MP simulated_simulated_contract thm)) >>

Q.PAT_X_ASSUM ‘∀s'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘s’ thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
rename1 ‘_ = BER_Ended o2 m2 n2 s'’ >>

subgoal ‘∃s1 o1 m1 n1. bir_exec_to_labels ls p s =
                       BER_Ended o1 m1 n1 s'’ >- (
  ‘s.bst_pc = bir_block_pc l’ by (
    ASM_SIMP_TAC (std_ss++holBACore_ss)
                 [bir_block_pc_def,
                  bir_programcounter_t_component_equality]
  ) >>
  ‘~(bir_state_is_terminated s')’ by ASM_SIMP_TAC (std_ss++holBACore_ss) [] >>
  METIS_TAC [simulated_contract_def]
) >>

PROVE_TAC []
QED

(*Sanity check*)
Theorem resolved_contract_transfer:
  ∀l1 v sl p p' l ls pre post.
    resolved l1 v sl p p' ⇒
    bir_vars_of_program p' = bir_vars_of_program p ⇒

    MEM l (bir_labels_of_program p) ⇒
    ls SUBSET (set (bir_labels_of_program p)) ⇒

    bir_exec_to_labels_triple p' l ls pre post ⇒
    bir_exec_to_labels_triple p l ls pre post
Proof
PROVE_TAC [contract_transfer, resolved_simulated]
QED


val _ = export_theory();