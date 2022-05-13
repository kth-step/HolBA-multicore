open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;
open bir_promisingExecTheory;

val _ = new_theory "bir_promising_bisim";

open listTheory;
open arithmeticTheory;
open bir_programTheory;

(* NOTE: clstep does not include promises *)

(* TODO: Convert from mem_msg_t to exec_mem_msg_t *)

Triviality MAX_EQ:
!m m' n n'.
m = m' /\ n = n' ==>
MAX m n = MAX m' n'
Proof
fs []
QED

(* TODO: Might need something about length of M *)
Triviality emem_readable_t_ok:
!t M l v_max coh_l t'.
(?msg. MEM (msg, t) (emem_readable M l v_max)) ⇒
(t < t' ∧ (t' ≤ v_max ∨ t' ≤ coh_l) ⇒
 (EL (t' − 1) (emem_to_mem M)).loc ≠ l)
Proof
REPEAT STRIP_TAC >> (
 fs [emem_readable_def] >>
 Cases_on ‘emem_every
                (λ(m',t'). m'.succ ∧ 0 < t' ∧ t' ≤ v_max ⇒ m'.loc ≠ l) M’ >| [
  (* Contradiction: Holds for every, so should hold for element in list *)
  fs [emem_every_def] >| [
   cheat,

   fs [MEM_FILTER, emem_filter_def] >>
   cheat
  ],

  (* More contradictions on the result of the case splits *)
  cheat
 ]
)
QED

(* TODO: Problems with emem_to_mem *)
Triviality emem_readable_mem_read:
!t l v_max memory msg.
MEM (msg, t) (emem_readable memory l v_max) ⇒
mem_read (emem_to_mem memory) l t = SOME msg.val
Proof
REPEAT STRIP_TAC >>
fs [emem_readable_def] >>
Cases_on ‘emem_every (λ(m',t'). m'.succ ∧ 0 < t' ∧ t' ≤ v_max ⇒ m'.loc ≠ l) memory’ >|
[
 fs [] >|
 [
  fs [mem_read_def, emem_default_def, mem_default_value_def, mem_get_def, mem_default_def]
  ,
  fs [MEM_FILTER, emem_filter_def] >>
  (* TODO: Problems with emem_to_mem *)
  cheat
 ],

 fs [MEM_FILTER, emem_filter_def] >>
 (* TODO: Problems with emem_to_mem *)
 cheat
]
QED

Triviality emem_fulfil_atomic_ok:
!t_r memory l core_id v_w.
emem_atomic memory l core_id t_r v_w ⇒
fulfil_atomic_ok (emem_to_mem memory) l core_id t_r v_w
Proof
  REPEAT STRIP_TAC >>
  fs [emem_atomic_def, fulfil_atomic_ok_def] >>
  Cases_on ‘emem_get memory l x.xclb_time’ >>
  (fs []) >>
  cheat
QED

(*************)
(* Soundness *)
(*************)
(*
Theorem exec_sem_read_sound:
!prog core_id state memory state' state'_list r e cast_opt xcl acq rel.
eval_clstep_read state memory r e xcl acq rel = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Read r e cast_opt xcl acq rel ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_read_def] >>
Cases_on ‘bir_eval_exp_view e state.bst_environ state.bst_viewenv’ >> (
 fs []
) >>
Cases_on ‘q’ >> (
 fs []
) >| [
 rw [] >>
 fs [MEM],

 rename1 ‘bir_eval_exp_view e state.bst_environ state.bst_viewenv = (SOME l, v_addr)’ >>
 Q.EXISTS_TAC ‘[]’ >>
 irule (el 1 (CONJUNCTS clstep_rules)) >>
 Q.LIST_EXISTS_TAC [‘e’, ‘acq’, ‘l’] >>
 fs [LIST_BIND_def] >>
 Q.PAT_X_ASSUM ‘FLAT _ = _’ (fn thm => fs [GSYM thm]) >>
 fs [MEM_FLAT, MEM_MAP] >>
 Cases_on ‘y’ >> (
  fs []
 ) >>
 rename1 ‘MEM (msg, t) _’ >>
 Cases_on ‘env_update_cast64 (bir_var_name r) msg.val (bir_var_type r) state.bst_environ’ >> (
  fs []
 ) >- (
  rfs [] >>
  fs [MEM]
 ) >>
 Q.PAT_X_ASSUM ‘l' = _’ (fn thm => fs [thm]) >>
 fs [bir_state_t_component_equality, MAXL_def, ifView_def] >>
 Q.LIST_EXISTS_TAC [‘t’, ‘msg.val’,
                    ‘(MAXL [v_addr; state.bst_v_rNew; ifView (acq ∧ rel) state.bst_v_Rel;
                            ifView (acq ∧ rel) (MAX state.bst_v_rOld state.bst_v_wOld)])’] >>
 REPEAT CONJ_TAC >> (
  fs [MAX_COMM]
 ) >| [
  (* t list correctness *)
  fs [MAXL_def, ifView_def] >>
  STRIP_TAC >>
  DISCH_TAC >>
  irule emem_readable_t_ok >>
  Q.EXISTS_TAC ‘state.bst_coh l’ >>
  Q.EXISTS_TAC ‘t’ >>
  Q.EXISTS_TAC ‘(MAX (state.bst_coh l)
               (MAX
                  (if acq ∧ rel then MAX state.bst_v_rOld state.bst_v_wOld
                   else 0)
                  (MAX (MAX v_addr state.bst_v_rNew)
                     (if acq ∧ rel then state.bst_v_Rel else 0))))’ >>
  CONJ_TAC >| [
   METIS_TAC [],

   fs []
  ],

  (* pc updates *)
  Cases_on ‘xcl’ >> (
   fs []
  ),

  (* coherence view updates *)
  irule EQ_EXT >>
  STRIP_TAC >>
  fs [] >>
  Cases_on ‘x' = l’ >> (
   fs [updateTheory.APPLY_UPDATE_THM]
  ),

  (* bst_v_rNew *)
  rw [],

  (* bst_v_wNew *)
  rw [],

  (* TODO: mem_read *)
  METIS_TAC [emem_readable_mem_read]
 ]
]
QED

(* Note: This also includes exclusive fail *)
Theorem exec_sem_write_sound:
!prog core_id state memory state' state'_list e1 e2 xcl acq rel.
eval_clstep_fulfil prog core_id state memory e1 e2 xcl acq rel ⧺
 eval_clstep_xclfail prog core_id state memory e1 e2 xcl = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Write e1 e2 xcl acq rel ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_fulfil_def, eval_clstep_xclfail_def] >>

 fs []
) >>
Cases_on ‘q’ >> (
 fs []
) >- (
 rw [] >>
 fs [MEM] >| [
  Cases_on ‘bir_eval_exp_view e2 state.bst_environ state.bst_viewenv’ >> (
   fs []
  ),

  Q.EXISTS_TAC ‘[]’ >>
  irule (el 2 (CONJUNCTS clstep_rules)) >>
  fs [] >>
  Cases_on ‘xcl’ >> (
   fs [eval_clstep_xclfail_def, bir_eval_exp_view_def]
  )
 ]
) >>
Cases_on ‘bir_eval_exp_view e2 state.bst_environ state.bst_viewenv’ >> (
 fs []
) >>
Cases_on ‘q’ >> (
 fs []
) >- (
 Q.EXISTS_TAC ‘[]’ >>
 irule (el 2 (CONJUNCTS clstep_rules)) >>
 fs [] >>
 Cases_on ‘xcl’ >> (
  fs [eval_clstep_xclfail_def, bir_eval_exp_view_def] >>
  rfs [MEM]
 )
) >>
rename1 ‘bir_eval_exp_view e1 state.bst_environ state.bst_viewenv = (SOME l, v_addr)’ >>
rename1 ‘bir_eval_exp_view e2 state.bst_environ state.bst_viewenv = (SOME v, v_data)’ >>
fs [LIST_BIND_def] >>
Q.PAT_X_ASSUM ‘A ⧺ B = _’ (fn thm => fs [GSYM thm]) >| [
 fs [MEM_FLAT, MEM_MAP] >>
 Q.PAT_X_ASSUM ‘l' = _’ (fn thm => fs [thm]) >>
 Cases_on ‘fulfil_update_env prog state xcl’ >> (
  fs []
 ) >>
 Cases_on ‘fulfil_update_viewenv prog state xcl v_post’ >> (
  fs []
 ) >>
 Q.EXISTS_TAC ‘[v_post]’ >>
 irule (el 3 (CONJUNCTS clstep_rules)) >>
 fs [] >>
 REPEAT STRIP_TAC >> (
  fs [MEM_FILTER, MAXL_def, ifView_def]
 ) >| [
  (* TODO: bst_counter problem *)
  fs [bir_state_t_component_equality, MAXL_def, ifView_def] >>
  cheat,

  Cases_on ‘v_post’ >> (
   fs [emem_get_def, emem_default_def]
  ) >>
  (* TODO: emem_to_mem problem *)
  cheat,

  fs [emem_fulfil_atomic_ok]
 ],

 Q.EXISTS_TAC ‘[]’ >>
 irule (el 2 (CONJUNCTS clstep_rules)) >>
 fs [] >>
 Cases_on ‘xcl’ >> (
  fs [eval_clstep_xclfail_def, bir_eval_exp_view_def]
 ) >>
 fs [LIST_BIND_def] >>
 fs [MEM_FLAT, MEM_MAP] >>
 Q.PAT_X_ASSUM ‘l' = _’ (fn thm => fs [thm]) >>
 Cases_on ‘xclfail_update_env prog state’ >> (
  fs []
 ) >>
 Cases_on ‘xclfail_update_viewenv prog state’ >> (
  fs []
 ) >>
 fs [bir_state_t_component_equality] >>
 (* TODO: bst_counter problem *)
 cheat
]
QED

Theorem exec_sem_amo_sound:
!prog core_id state memory state' state'_list r e1 e2 acq rel.
eval_clstep_amofulfil prog core_id state memory r e1 e2 acq rel = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Amo r e1 e2 acq rel ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_amofulfil_def] >>
Cases_on ‘bir_eval_exp_view e1 state.bst_environ state.bst_viewenv’ >> (
 fs []
) >>
Cases_on ‘q’ >> (
 rw [] >>
 fs [MEM]
) >>
fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
Q.PAT_X_ASSUM ‘l = _’ (fn thm => fs [thm]) >>
rename1 ‘bir_eval_exp_view e1 state.bst_environ state.bst_viewenv = (SOME l, v_addr)’ >>
Cases_on ‘y’ >> (
 fs []
) >>
Cases_on ‘env_update_cast64 (bir_var_name r) q.val (bir_var_type r) state.bst_environ’ >> (
 fs []
) >>
Cases_on ‘bir_eval_exp_view e2 x
              (state.bst_viewenv |+
               (r,
                MAX
                  (MAXL
                     [v_addr; state.bst_v_rNew;
                      ifView (acq ∧ rel) state.bst_v_Rel;
                      ifView (acq ∧ rel)
                        (MAX state.bst_v_rOld state.bst_v_wOld)])
                  (mem_read_view (state.bst_fwdb l) r')))’ >> (
 fs []
) >>
Cases_on ‘q'’ >> (
 fs []
) >>
fs [MEM_FLAT, MEM_MAP] >>
Q.PAT_X_ASSUM ‘l' = _’ (fn thm => fs [thm]) >>
(* TODO: Correct? *)
Q.EXISTS_TAC ‘[v_wPost]’ >>
irule (el 4 (CONJUNCTS clstep_rules)) >>
fs [] >>
REPEAT STRIP_TAC >| [
(*
 Q.LIST_EXISTS_TAC [‘x’, ‘r'’, ‘r''’,
                    ‘MAX
                      (MAXL
                         [v_addr; state.bst_v_rNew;
                          ifView (acq ∧ rel) state.bst_v_Rel;
                          ifView (acq ∧ rel)
                            (MAX state.bst_v_rOld state.bst_v_wOld)])
                      (mem_read_view (state.bst_fwdb l) r')’, ‘x'’] >>
*)
 Q.LIST_EXISTS_TAC [‘x’, ‘r'’, ‘r''’, ‘q.val’, ‘x'’] >>
 fs [] >>
 REPEAT CONJ_TAC >> (
  fs [MEM_FILTER, MAXL_def, ifView_def]
 ) >| [
  (* TODO: ??? *)
  cheat,

  rw [MEM_FILTER, MAXL_def, ifView_def] >> (
   fs [] 
  ),

  (* TODO: bst_counter, coherence view problems *)
  cheat,

  (* TODO: emem_to_mem problem *)
  cheat,

  (* TODO: emem_to_mem problem *)
  METIS_TAC [emem_readable_mem_read],

  (* TODO: Provable, subgoal resulting from change *)
  irule EQ_SYM >>
  rw [] >| [
   cheat,

   cheat
  ]
 ],

 fs [MEM_FILTER, MAXL_def]
]
QED

(* Assign *)
Theorem exec_sem_exp_sound:
!prog core_id state memory state' state'_list r e.
eval_clstep_exp state r e = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Expr r e ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_exp_def] >>
Cases_on ‘bir_eval_exp_view e state.bst_environ state.bst_viewenv’ >> (
 fs []
) >>
Cases_on ‘q’ >> (
 fs []
) >- (
 rw [] >>
 fs [MEM]
) >>
Cases_on ‘env_update_cast64 (bir_var_name r) x (bir_var_type r) state.bst_environ’ >> (
 rw [] >>
 fs [MEM]
) >>
Q.EXISTS_TAC ‘[]’ >>
irule (el 7 (CONJUNCTS clstep_rules)) >>
Q.LIST_EXISTS_TAC [‘e’, ‘x'’, ‘x’, ‘r'’, ‘r’] >>
fs [bir_get_stmt_def] >>
Cases_on ‘bir_get_current_statement prog state.bst_pc’ >> (
 fs []
) >>
Cases_on ‘x''’ >> (
 fs []
) >> (
 Cases_on ‘b’ >> (
  fs []
 )
) >>
Cases_on ‘is_amo prog state.bst_pc’ >> (
 fs []
) >| [
 Cases_on ‘get_read_args b0’ >> (
  fs []
 ) >| [
  Cases_on ‘get_fulfil_args b0’ >> (
   fs []
  ) >>
  rw [],

  Cases_on ‘x''’ >> (
   fs []
  ) >>
  Cases_on ‘bir_get_current_statement prog (bir_pc_next state.bst_pc)’ >> (
   fs []
  ) >>
  Cases_on ‘x''’ >> (
   fs []
  ) >>
  Cases_on ‘b’ >> (
   fs []
  ) >>
  Cases_on ‘get_fulfil_args b0'’ >> (
   fs []
  ) >>
  Cases_on ‘x''’ >> (
   fs []
  ) >>
  Cases_on ‘q = q'’ >> (
   fs []
  )
 ],

 Cases_on ‘get_read_args b0’ >> (
  fs []
 ) >| [
  Cases_on ‘get_fulfil_args b0’ >> (
   fs []
  ) >| [
   rw [],

   Cases_on ‘x''’ >> (
    fs []
   )
  ],

  Cases_on ‘x''’ >> (
   fs []
  )
 ]
]
QED


Theorem exec_sem_fence_sound:
!prog core_id state memory state' state'_list K1 K2.
eval_clstep_fence state K1 K2 = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Fence K1 K2 ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_fence_def] >>
rw [] >>
fs [MEM] >>
Q.EXISTS_TAC ‘[]’ >>
irule (el 5 (CONJUNCTS clstep_rules)) >>
Q.LIST_EXISTS_TAC [‘K1’, ‘K2’, ‘MAX (if is_read K1 then state.bst_v_rOld else 0) (if is_write K1 then state.bst_v_wOld else 0)’] >>
fs [bir_state_t_component_equality, MAX_COMM]
QED

(* Conditional jump *)
Theorem exec_sem_branch_sound:
!prog core_id state memory state' state'_list e l1 l2.
eval_clstep_branch prog state e l1 l2 = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Branch e l1 l2 ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_branch_def] >>
Cases_on ‘bir_eval_exp_view e state.bst_environ state.bst_viewenv’ >> (
 fs []
) >>
Cases_on ‘q’ >> (
 rw [] >>
 fs [MEM]
) >>
Cases_on ‘bir_exec_stmt prog (BStmtE (BStmt_CJmp e l1 l2)) state’ >> (
 fs []
) >>
Q.EXISTS_TAC ‘[]’ >>
irule (el 6 (CONJUNCTS clstep_rules)) >>
Q.LIST_EXISTS_TAC [‘e’, ‘l1’, ‘l2’, ‘q’, ‘r'’, ‘(BStmtE (BStmt_CJmp e l1 l2))’, ‘x’, ‘r’] >>
fs [bir_state_t_component_equality, MAX_COMM] >>
irule MAX_EQ >>
fs [] >>
irule EQ_SYM >>
METIS_TAC [bir_exec_stmt_mc_invar]
QED

Theorem exec_sem_generic_sound:
!prog core_id state memory state' state'_list stmt.
eval_clstep_bir_step prog state stmt = state'_list ⇒
MEM state' state'_list ⇒
bir_get_stmt prog state.bst_pc = BirStmt_Generic stmt ⇒
(∃promises.
 clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
REPEAT STRIP_TAC >>
fs [eval_clstep_bir_step_def] >>
Cases_on ‘bir_exec_stmt prog stmt state’ >> (
 fs []
) >>
rw [] >>
fs [MEM] >>
rw [] >>
Q.EXISTS_TAC ‘[]’ >>
irule (el 8 (CONJUNCTS clstep_rules)) >>
Q.LIST_EXISTS_TAC [‘q’, ‘stmt’] >>
fs []
QED

(* Soundness of exec sem with respect to relational semantics: *)
(* For trivial bisimulation relation: *)
Theorem exec_sem_sound:
!prog core_id state memory state'_list promises.
eval_clstep prog core_id state memory = state'_list ==>
(!state'.
 MEM state' state'_list ==>
 ?promises. clstep prog core_id state (emem_to_mem memory) promises state')
Proof
  cheat >>
(* Case split on bir_get_stmt? *)
REPEAT STRIP_TAC >>
Cases_on ‘bir_get_stmt prog state.bst_pc’ >> (
 fs [eval_clstep_def]
) >| [
 fs [exec_sem_read_sound],

 METIS_TAC [exec_sem_write_sound],

 fs [exec_sem_amo_sound],

 fs [exec_sem_exp_sound],

 fs [exec_sem_fence_sound],

 fs [exec_sem_branch_sound],

 fs [exec_sem_generic_sound],

 (* None *)
 rw [] >>
 fs [MEM]
]
QED

(* Completeness of exec sem with respect to relational semantics: *)
(* TODO: Relate executable and regular memory *)
Theorem exec_sem_complete:
!prog core_id state memory state'_list promises.
(* TODO: Caveats here *)
!state'. MEM state' state'_list ==> clstep prog core_id state memory promises state' ==>
eval_clstep prog core_id state (mem_to_emem memory) = state'_list
Proof
cheat
QED

(* 2: Do something similar for cstep, but now we have complications for the promises.
 * In the exec sem, promises are all done via eval_pmstepsO1 - for one promise, eval_pmstepO1
 *
 * Maybe the middle step can be a new exec sem resembling cstep, where the two possible steps either
 * use eval_pmstep01 or eval_clstepO1. Then prove a bisimulation relation between this and cstep.
 * Then, use the Diamond theorem to prove equivalence (in some sense) with this and the sequence of
 * eval_pmstepsO1 and eval_clstepsO1.
 *
 * Note that in the relational semantics the promise step has a choice of promises, but makes one,
 * while in the executable semantics, a list of these choices is returned (certification implicit). *)

(* 3: Then, the question remains what to do regarding the system step parstep, which chooses core and
 * performs certification. What this does is already baked into the *)

*)
val _ = export_theory();
