open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory arithmeticTheory relationTheory finite_mapTheory;

(* Bir theory *)
open bir_promisingTheory bir_programTheory bir_expTheory;


val _ = new_theory "bir_promisingExec";

(************************************************************
 * NAIVE EXECUTABLE SEMANTICS 
 ************************************************************)

(****************************************
 * DEFINITION: mem_every P M
 *
 * DESCRIPTION:
 *   Is true if !m t. oEL t M = SOME m ==> P (m, SUC t)
 *)
Definition mem_every_def:
  mem_every P M = EVERY P (ZIP (M, [1 .. LENGTH M]))
End 

(****************************************
 * DEFINITION: mem_filter P M
 *
 * DESCRIPTION:
 *   Returns pairs (m, SUC t) such that,
 *     EL t M = m /\ P (m, SUC t)
 *)
Definition mem_filter_def:
  mem_filter P M = FILTER P (ZIP (M, [1 .. LENGTH M]))
End

(****************************************
 * DEFINITION: mem_timestamps l M
 *
 * DESCRIPTION:
 *   Returns list of timestamps t such that,
 *     (EL t M).loc = l
 *)
Definition mem_timestamps_def:
  mem_timestamps l M = MAP SND (mem_filter (λ(m, t). m.loc = l) M)
End

(****************************************
 * DEFINITION: mem_atomic M l cid t_r t_w
 *
 * DESCRIPTION:
 *   Is true if
 *     mem_is_loc M t_r l ==>
 *       !t'. t_r < t' /\ t' < t_w /\ mem_is_loc M t' l ==>
 *         mem_is_cid M t' cid
 *)
Definition mem_atomic_def:
  mem_atomic M l cid t_r t_w =
  (mem_is_loc M t_r l ==>
   mem_every (λ(m,t'). (t_r < t' /\ t' < t_w /\ m.loc = l) ==> m.cid = cid) M)
End

(****************************************
 * DEFINITION: ifView p v
 *
 * DESCRIPTION:
 *   Return v if p else 0
 *
 * TODO: Move this to bir_promisingScript.sml
 *)
Definition ifView_def:
  ifView p (v:num) = if p then v else 0
End

(****************************************
 * DEFINITION: MAXL xs
 *
 * DESCRIPTION:
 *   Returns the maximum num of xs, 0 if list is empty.
 *
 * TODO: Move this to bir_promisingScript.sml
 *)
Definition MAXL_def:
  MAXL [] = 0
  /\
  MAXL (x::xs) = MAX x (MAXL xs)
End

(****************************************
 * DEFINITION: MAP_PARTIAL f l
 *
 * DESCRIPTION:
 *   Applies (f : a -> b option) to (l : 'a), removes NONE, unwraps SOME.
 *   Equivalent to
 *     MAP THE (FILTER IS_SOME (MAP f l))
 *)
Definition MAP_PARTIAL_def:
  MAP_PARTIAL f [] = []
  /\
  MAP_PARTIAL f (x::xs) =
  case f x of
  | SOME y => y::MAP_PARTIAL f xs
  | NONE => MAP_PARTIAL f xs
End

(****************************************
 * DEFINITION: mem_readable M l v_max
 *
 * DESCRIPTION:
 *   Returns the list of writes and timestamps (m, t) such that
 *   EL t M = m /\ !t'. t < t' /\ t' <= v_max ==> ~mem_is_loc M t' l
 *)
Definition mem_readable_def:
  mem_readable M l v_max =
  FILTER (λ(m,t). mem_every (λ(m',t'). t < t' /\ t' <= v_max ==> m'.loc <> l) M)
         ((mem_default l,0)::mem_filter (λ(m,t). m.loc = l) M)
End

(************************************************************
 * Naive Core-local execution
 ************************************************************)

(****************************************
 * DEFINITION: eval_clstep_load s M var a_e xcl acq rel
 *
 * DESCRIPTION:
 *   Implements an executable version of the core-local read rule.
 *)
Definition eval_clstep_load_def:
  eval_clstep_load s M var a_e xcl acq rel =
  case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
  | (SOME l, v_addr) =>
      let
        (* Pre-view of the memory *)
        v_pre = MAXL [v_addr; s.bst_v_rNew;
                      ifView (acq /\ rel) s.bst_v_Rel;
                      ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
        (* Get the readable writes/messages with timestamp *)
        msgs_ts  = mem_readable M l (MAX v_pre (s.bst_coh l)) 
      in
        (* Eval with readable message *)
        MAP_PARTIAL (λ(msg,t).
                       let
                         v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
                       in
                         (* env_update_cast64 returns an option, NONE if var is not in bst_environ. *)
                         OPTION_BIND (env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ))
                                     (λnew_env.
                                        SOME ([]: num list,
                                              s with <| bst_environ := new_env;
                                                        bst_viewenv updated_by (λenv. FUPDATE env (var, v_post));
                                                        bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_post);
                                                        bst_v_rOld  updated_by (MAX v_post);
                                                        bst_v_rNew  updated_by (MAX $ ifView acq v_post);
                                                        bst_v_wNew  updated_by (MAX $ ifView acq v_post);
                                                        bst_v_Rel   updated_by (MAX $ ifView (rel /\ acq) v_post);
                                                        bst_v_CAP   updated_by (MAX v_addr);
                                                        bst_pc      updated_by if xcl
                                                                               then (bir_pc_next o bir_pc_next)
                                                                               else bir_pc_next;
                                                        bst_xclb    := if xcl
                                                                       then SOME <| xclb_time := t; xclb_view := v_post |>
                                                                       else s.bst_xclb |>)))
                    msgs_ts
        | _ => []
End

(****************************************
 * DEFINITION: eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel
 *
 * DESCRIPTION:
 *   Implements an executable version of the core-local fulfil rule.
 *)
Definition eval_clstep_store_fulfil_def:
  eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel =
  let
    (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
  in
    case (l_opt,v_opt) of
    | (SOME l, SOME v) =>
        (let
           (* The pre-view *)
           v_pre = MAXL [v_addr;
                         v_data;
                         s.bst_v_wNew;
                         s.bst_v_CAP;
                         ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                         ifView (xcl /\ acq /\ rel) s.bst_v_Rel;
                         ifView xcl (get_xclb_view s.bst_xclb)];

           (* The message to fulfil. *)
           msg = <| loc := l; val := v; cid := cid |>;

           (* Get the timestamps that we can fulfil with the message *)
           ts = FILTER (\t. (mem_get M l t = SOME msg) /\
                            (MAX v_pre (s.bst_coh l) < t) /\
                            (xcl ==> IS_SOME (s.bst_xclb) /\
                                     mem_atomic M l cid (THE s.bst_xclb).xclb_time t))
                       s.bst_prom;
         in
           MAP_PARTIAL (\v_post. (* v_post = t *)
                          (* Updates the environ and viewenv if we have a store conditional *)
                          case (fulfil_update_env p s, fulfil_update_viewenv p s v_post) of
                          | (SOME new_env, SOME new_viewenv) => 
                              SOME ([v_post],
                                    s with <| bst_viewenv := new_viewenv;
                                              bst_environ := new_env;
                                              bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                              bst_coh    updated_by (l =+ v_post);
                                              bst_v_wOld updated_by MAX v_post;
                                              bst_v_CAP  updated_by MAX v_addr;
                                              bst_v_Rel  updated_by (MAX $ ifView (rel /\ acq) v_post);
                                              bst_v_rNew updated_by (MAX $ ifView (rel /\ acq /\ xcl) v_post);
                                              bst_v_wNew updated_by (MAX $ ifView (rel /\ acq /\ xcl) v_post);
                                              bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
                                                                             fwdb_view := MAX v_addr v_data;
                                                                             fwdb_xcl  := xcl |>);
                                              bst_pc     updated_by if xcl
                                                                    then (bir_pc_next o bir_pc_next o bir_pc_next)
                                                                    else bir_pc_next;
                                              bst_xclb := if xcl then NONE else s.bst_xclb |>)
                          | _ => NONE)
                       ts)
    | (_, _) => []
End

(****************************************
 * DEFINITION: eval_clstep_store_xclfail p cid s xcl
 *
 * DESCRIPTION:
 *   If xcl = T, then execute an xcl failure, a store-conditional that failed.
 *   Otherwise does nothing.
 *)
Definition eval_clstep_store_xclfail_def:
  (eval_clstep_store_xclfail p cid s T =
   case (xclfail_update_env p s, xclfail_update_viewenv p s) of
   | (SOME new_env, SOME new_viewenv) =>
       [([]: num list,
         s with <| bst_viewenv := new_viewenv;
                   bst_environ := new_env;
                   bst_xclb    := NONE;
                   bst_pc updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>)]
   | _ => [])
  /\
  eval_clstep_store_xclfail p cid s F = []
End

(****************************************
 * DEFINITION: eval_clstep_amo_fulfil cid s M a_e v_e acq rel
 *
 * DESCRIPTION:
 *   Implements our AMO fulfil rule.
 *   Basically a xcl read and fulfil without failure and xcl_bank.
 *)
Definition eval_clstep_amo_fulfil_def:
  eval_clstep_amo_fulfil cid s M var a_e v_e acq rel =
  case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
  | (NONE, v_addr) => []
  | (SOME l, v_addr) =>
      let
        (* Out read pre-view. *)
        v_rPre = MAXL [v_addr;
                       s.bst_v_rNew;
                       ifView (acq /\ rel) s.bst_v_Rel;
                       ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
        (* Readable writes # timestamps. *)
        msgs = mem_readable M l (MAX v_rPre (s.bst_coh l));
      in                                 
        LIST_BIND msgs
                  (\ (msg, t_r).
                     let
                       (* Read post-view *)
                       v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r);
                       (* Update the register view *)
                       new_viewenv = FUPDATE s.bst_viewenv (var, v_rPost);
                     in
                       (* Update the registers *)
                       (case env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ) of
                        | NONE => []
                        | SOME new_environ =>
                            (* Evaluate the AMO operation *)
                            (case bir_eval_exp_view v_e new_environ new_viewenv of
                             | (NONE, v_data) => []
                             | (SOME v, v_data) =>
                                 let
                                   (* Get the write pre-view *)
                                   v_wPre = MAXL [v_addr; v_data; s.bst_v_CAP; v_rPost; s.bst_v_wNew;
                                                  ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                                                  ifView (acq /\ rel) s.bst_v_Rel];
                                   (* Get the AMO message to fulfil *)
                                   msg = <| loc := l; val := v; cid := cid |>;
                                   (* Find promises that writes the message atomically *)
                                   t_ws = FILTER (\t_w.
                                                    t_r < t_w /\
                                                    (mem_get M l t_w = SOME msg) /\
                                                    (MAX v_wPre (s.bst_coh l) < t_w) /\
                                                    (* Check that there is no write to the same location between AMO read and write. *)
                                                    (mem_every (\ (msg,t'). t_r < t' /\ t' < t_w ==> msg.loc <> l) M))
                                                 s.bst_prom;
                                 in MAP (\v_wPost.
                                           ([v_wPost],
                                            s with <| bst_viewenv := new_viewenv;
                                                      bst_environ := new_environ;
                                                      bst_fwdb   updated_by (l =+ <| fwdb_time := v_wPost;
                                                                                     fwdb_view := MAX v_addr v_data;
                                                                                     fwdb_xcl  := T |>);
                                                      bst_prom   updated_by (FILTER (\t'. t' <> v_wPost));
                                                      bst_coh    updated_by (l =+ v_wPost);
                                                      bst_v_Rel  updated_by (MAX (ifView (acq /\ rel) v_wPost));
                                                      bst_v_rOld updated_by (MAX v_rPost);
                                                      bst_v_rNew updated_by (MAX (ifView acq (if rel then v_wPost else v_rPost)));
                                                      bst_v_wNew updated_by (MAX (ifView acq (if rel then v_wPost else v_rPost)));
                                                      bst_v_CAP  updated_by (MAX v_addr);
                                                      bst_v_wOld updated_by (MAX v_wPost);
                                                      bst_pc     updated_by bir_pc_next o bir_pc_next;
                                                   |>)) t_ws
                            )
                       )
                  )
End

(****************************************
 * DEFINITION: eval_clstep_fence s K1 K2 
 *
 * DESCRIPTION:
 *   Implements the fence rule, K1 is pre-set and K2 is post-set
 *)
Definition eval_clstep_fence_def:
  eval_clstep_fence s K1 K2 =
  let v = MAX (if is_read K1 then s.bst_v_rOld else 0)
              (if is_write K1 then s.bst_v_wOld else 0)
  in
    [([]: num list,
      s with <| bst_v_rNew updated_by MAX (if is_read K2 then v else 0);
                bst_v_wNew updated_by MAX (if is_write K2 then v else 0);
                bst_pc     updated_by bir_pc_next |>)]
End

(****************************************
 * DEFINITION: eval_clstep_branch p s cond_e lbl1 lb2
 *
 * DESCRIPTION:
 *   Implements the branch rule, main function to update bst_v_CAP with register view. 
 *)
Definition eval_clstep_branch_def:
  eval_clstep_branch p s cond_e lbl1 lbl2 =
  let
    (sv, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
  in
    case sv of
    | NONE => []
    | SOME v =>
        let s2 = bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s
        in [([]: num list,
             s2 with <| bst_v_CAP := MAX s.bst_v_CAP v_addr |>)]
End

(****************************************
 * DEFINITION: eval_clstep_exp s var ex 
 *
 * DESCRIPTION:
 *   Implements execution of an expression, the register rule.
 *   Mainly updates the register view.
 *)
Definition eval_clstep_assign_def:
  eval_clstep_assign s var ex =
  case bir_eval_exp_view ex s.bst_environ s.bst_viewenv
  of (SOME val, v_val) =>
       (case env_update_cast64 (bir_var_name var) val (bir_var_type var) (s.bst_environ) of
          SOME new_env =>
            [([]: num list,
              s with <| bst_environ := new_env;
                        bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                        bst_pc      updated_by bir_pc_next |>)]
        | _ => [])
  | _ => []
End

(****************************************
 * DEFINITION: eval_clstep_generic p s stm
 *
 * DESCRIPTION:
 *   Implments bir steps that do not have multicore semantics.
 *)
Definition eval_clstep_generic_def:
  eval_clstep_generic p s stm =
  case bmc_exec_general_stmt p stm s of
  | SOME (oo, s') => [([]: num list, s')]
  | NONE => []
End

(****************************************
 * DEFINITION: eval_clstep_def cid p s M
 *
 * DESCRIPTION:
 *   Implements the core-local step. Finds an instruction and
 *   executes the rule/s that corresponds to that instruction.
 *)
Definition eval_clstep_def:
  eval_clstep cid p s M =
  if s.bst_status = BST_Running then
    (case bir_get_current_statement p s.bst_pc of
     | SOME (BStmtB (BMCStmt_Load var a_e cast_opt xcl acq rel)) =>
         eval_clstep_load s M var a_e xcl acq rel
     | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
         eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel ++
         eval_clstep_store_xclfail p cid s xcl
     | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
         eval_clstep_amo_fulfil cid s M var a_e v_e acq rel
     | SOME (BStmtB (BMCStmt_Assign var e)) =>
         eval_clstep_assign s var e
     | SOME (BStmtB (BMCStmt_Fence K1 K2)) =>
         eval_clstep_fence s K1 K2
     | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
         eval_clstep_branch p s cond_e lbl1 lbl2
     | SOME stm =>
         eval_clstep_generic p s stm
     | NONE => [])
  else []
End

Definition eval_cstep_seq_store_def:
  eval_cstep_seq_store p cid s M a_e v_e xcl acq rel =
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <|val := v; loc := l; cid := cid|>;
           M' = SNOC msg M;
           t = LENGTH M';
           s' = s with <| bst_prom updated_by (λprom. prom ++ [t]) |>;
         in
           MAP (\ (l, s''). (s'', [msg])) (FILTER (\ (l,s''). l = [t]) (eval_clstep_store_fulfil p cid s' M' a_e v_e xcl acq rel))
        )
    | _ => []
End

Definition eval_cstep_seq_amo_def:
  eval_cstep_seq_amo cid s M var a_e v_e acq rel =
  case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
  | (NONE, v_addr) => []
  | (SOME l, v_addr) =>
      let
        v_rPre = MAXL [v_addr; s.bst_v_rNew; ifView (acq /\ rel) s.bst_v_Rel];
        msgs = mem_readable M l (MAX v_rPre (s.bst_coh l));
      in                                 
        LIST_BIND msgs
                  (\ (msg,t_r).
                     let
                       v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r);
                       new_viewenv = FUPDATE s.bst_viewenv (var, v_rPost);
                     in
                       (case env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ) of
                        | NONE => []
                        | SOME new_environ =>
                            (case bir_eval_exp_view v_e new_environ new_viewenv of
                             | (NONE, v_data) => []
                             | (SOME v, v_data) =>
                                 let
                                   msg = <| loc := l; val := v; cid := cid |>;
                                   M' = SNOC msg M;
                                   t = LENGTH M';
                                   s' = s with <| bst_prom updated_by (λprom. prom ++ [t]) |>;
                                 in
                                   MAP (\ (l,s''). (s'', [msg]))
                                       (FILTER (\ (l,s''). l = [t])
                                        (eval_clstep_amo_fulfil cid s' M' var a_e v_e acq rel))
                            )
                       )
                  )
End

Definition eval_cstep_seq_def:
  eval_cstep_seq cid p s M =
  if s.bst_status = BST_Running then
    (case bir_get_current_statement p s.bst_pc of
     | SOME (BStmtB (BMCStmt_Load var a_e cast_opt xcl acq rel)) =>
         MAP (\ (l,s'). (s', [])) (eval_clstep_load s M var a_e xcl acq rel)
     | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
         eval_cstep_seq_store p cid s M a_e v_e xcl acq rel ++
         MAP (\ (l,s'). (s', [])) (eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel) ++
         MAP (\ (l,s'). (s', [])) (eval_clstep_store_xclfail p cid s xcl)
     | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
         eval_cstep_seq_amo cid s M var a_e v_e acq rel ++
         MAP (\ (l,s'). (s', [])) (eval_clstep_amo_fulfil cid s M var a_e v_e acq rel)
     | SOME (BStmtB (BMCStmt_Assign var e)) =>
         MAP (\ (l,s'). (s', [])) (eval_clstep_assign s var e)
     | SOME (BStmtB (BMCStmt_Fence K1 K2)) =>
         MAP (\ (l,s'). (s', [])) (eval_clstep_fence s K1 K2)
     | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
         MAP (\ (l,s'). (s', [])) (eval_clstep_branch p s cond_e lbl1 lbl2)
     | SOME stm =>
         MAP (\ (l,s'). (s', [])) (eval_clstep_generic p s stm)
     | NONE => [])
  else []
End

Definition eval_is_certified_def:
  eval_is_certified 0 p cid s M = (s.bst_prom = [])
  /\
  eval_is_certified (SUC f) p cid s M =
  ((s.bst_prom = []) \/
   EXISTS (\ (s', msgs). eval_is_certified f p cid s' (M++msgs)) (eval_cstep_seq cid p s M))
End

(********* Promising-mode steps ***********)


(* eval_fpsteps FUEL PROGRAM CORE_ID BIR_STATE MEMORY (PROMISES + CID) *)
Definition eval_findprom_def:
  (
  eval_findprom 0 cid p s M = []
  ) /\ (
  eval_findprom (SUC f) cid p s M = 
  LIST_BIND (eval_cstep_seq cid p s M)
            (λ(s', msgs). msgs ++ eval_findprom f cid p s' (M ++ msgs)) 
  )
End

Definition eval_promstep_def:
  eval_cpstep f cid p s M =
  FILTER (\ (s',M'). eval_is_certified f p cid s' M')
         $ MAP (\msg. (s with bst_prom updated_by (SNOC (SUC (LENGTH M))), (M ++ [msg])))
         (eval_findprom f cid p s M)
End


(****************************************
 * THEOREM: EL_SNOC2
 *
 * DESCRIPTION:
 *   Self-explanatory. TODO: maybe add to rich_listTheory
 *)
Theorem EL_SNOC2:
  !x l.
    EL (LENGTH l) (SNOC x l) = x
Proof
  Induct_on ‘l’ >>
  (asm_rewrite_tac [LENGTH, SNOC, EL, HD, TL])
QED

Theorem mem_get_SNOC:
  !M l t msg.
    t < SUC (LENGTH M) ==>
    mem_get (SNOC msg M) l t = mem_get M l t
Proof
  Cases_on ‘t’
  >- (fs [mem_get_def])
  >- (fs [mem_get_def, oEL_THM, EL_SNOC])
QED

Theorem mem_get_SNOC2:
  !M l msg.
    mem_get (SNOC msg M) l (SUC (LENGTH M)) =
    if (msg.loc = l) then SOME msg else NONE 
Proof
  fs [mem_get_def, oEL_THM, EL_SNOC2]
QED

Theorem mem_read_correctness:
  !M l t v.
    mem_read M l t = SOME v <=>
    ?m. mem_get M l t = SOME m /\ m.val = v
Proof
  Cases_on ‘t’ >> fs [mem_read_def, mem_get_def, CaseEq"option"]
QED

Theorem mem_is_loc_correctness:
  !M t l.
    mem_is_loc M t l <=> (t = 0 \/
                          (t <> 0 /\ PRE t < LENGTH M /\ (EL (PRE t) M).loc = l))
Proof
  Cases_on ‘t’ >- fs [mem_is_loc_def] >>
  fs [mem_is_loc_def, oEL_THM] >>
  rpt gen_tac >>
  Cases_on ‘n < LENGTH M’ >> fs []
QED

Theorem mem_is_loc_mem_get:
  !M t l.
    mem_is_loc M t l <=> (mem_get M l t <> NONE)
Proof
  Cases_on ‘t’ >|
  [
    fs[mem_is_loc_def, mem_get_def]
    ,
    fs [mem_is_loc_def, mem_get_def] >>
    gen_tac >>
    Cases_on ‘oEL n M’ >> fs []
  ]
QED

Theorem mem_is_cid_correctness:
  !M t cid.
    mem_is_cid M t cid <=> (t <> 0 /\ PRE t < LENGTH M /\ (EL (PRE t) M).cid = cid)
Proof
  Cases_on ‘t’ >|
  [
    fs [mem_is_cid_def]
    ,
    fs [mem_is_cid_def, oEL_THM] >>
    rpt gen_tac >>
    Cases_on ‘n < LENGTH M’ >> fs []
  ]
QED

Theorem MEM_ZIP_memory_timestamp:
  !m t M.
    MEM (m, t) (ZIP (M, [1 .. LENGTH M])) = (t <> 0 /\ oEL (PRE t) M = SOME m)
Proof
  Cases_on ‘t’ >|
  [
    Induct_on ‘M’ using SNOC_INDUCT >>
    (fs [GENLIST, listRangeTheory.listRangeINC_def, rich_listTheory.ZIP_SNOC])
    ,
    Induct_on ‘M’ using SNOC_INDUCT >|
    [
      fs [listRangeTheory.listRangeINC_def, oEL_def]
      ,
      fs [GENLIST, listRangeTheory.listRangeINC_def, rich_listTheory.ZIP_SNOC, oEL_THM] >>
      simp [ADD1] >>
      rpt gen_tac >>
      eq_tac >|
      [
        rpt strip_tac >>
        fs [EL_SNOC2, EL_SNOC]
        ,
        rpt strip_tac >>
        fs [GSYM ADD1, EL_SNOC2, EL_SNOC] >>
        rename1 ‘t < SUC (LENGTH M)’ >>
        ‘t < LENGTH M \/ t = LENGTH M’ by (fs []) >>
        (fs [EL_SNOC, EL_SNOC2])
      ]
    ]
  ]
QED

Theorem mem_every_thm:
  !P M.
    mem_every P M = !m t. oEL t M = SOME m ==> P (m, SUC t)
Proof
  fs [mem_every_def, EVERY_MEM] >>
  rpt gen_tac >> eq_tac >|
  [
    rpt strip_tac >>
    fs [MEM_ZIP_memory_timestamp]
    ,
    rpt strip_tac >>
    rename1 ‘P e’ >>
    Cases_on ‘e’ >>
    rename1 ‘P (m, t)’ >>
    Cases_on ‘t’ >>
    (fs [MEM_ZIP_memory_timestamp])
  ]
QED

Theorem mem_filter_thm:
  !P M m t.
    MEM (m, t) (mem_filter P M) = (P (m, t) /\ t <> 0 /\ oEL (PRE t) M = SOME m)
Proof
  fs [MEM_ZIP_memory_timestamp, mem_filter_def, MEM_FILTER]
QED                           

Theorem mem_every_amo:
  !t_r t_w l M.
    mem_every (\ (msg,t'). t_r < t' /\ t' < t_w ==> msg.loc <> l) M
    <=> !t'. t_r < t' /\ t' < t_w ==> ~mem_is_loc M t' l
Proof
  rpt gen_tac >> eq_tac >|
  [
    rpt strip_tac >>
    fs [mem_every_thm, oEL_THM, mem_is_loc_correctness] >>
    Cases_on ‘t'’ >- fs[] >>
    fs [] >>
    res_tac
    ,
    rpt strip_tac >>
    fs [mem_every_thm, oEL_THM] >>
    rpt strip_tac >>
    fs [mem_is_loc_correctness] >>
    res_tac >>
    fs []
  ]
QED

Triviality IS_SOME_EQ_NOT_NONE:
  !x. IS_SOME x <=> (x <> NONE)
Proof
  Cases_on `x` >> fs[]
QED

Triviality MEM_MAP2:
  !l f x y.
    MEM (x, y) (MAP f l) <=> ?x' y'. (x, y) = f (x', y') /\ MEM (x', y') l
Proof
  rpt gen_tac >> eq_tac >|
  [
    fs [MEM_MAP] >>
    rpt strip_tac >>
    Cases_on ‘y'’ >>
    Q.EXISTS_TAC ‘q’ >> Q.EXISTS_TAC ‘r’ >>
    fs []
    ,
    fs [MEM_MAP] >>
    rpt strip_tac >>
    Q.EXISTS_TAC ‘(x', y')’  >>
    fs []
  ] 
QED

Triviality EXISTS_MEM2:
  !P l.
    EXISTS P l <=> ?x y. MEM (x, y) l /\ P (x, y)
Proof
  fs [EXISTS_MEM] >>
  rpt gen_tac >> eq_tac >-
   (rpt strip_tac >>
    Cases_on ‘e’ >> METIS_TAC []) >>
  METIS_TAC []
QED

Theorem MAP_PARTIAL_rwr:
  !f xs.
    MAP_PARTIAL f xs = MAP THE (FILTER IS_SOME (MAP f xs))
Proof
  Induct_on ‘xs’ >|
  [
    simp [MAP_PARTIAL_def]
    ,
    simp [MAP_PARTIAL_def] >>
    rpt gen_tac >> CASE_TAC >>
    (simp [])
  ]
QED

Theorem MEM_MAP_PARTIAL:
  !x f xs.
    MEM x (MAP_PARTIAL f xs) = MEM (SOME x) (MAP f xs)
Proof
  simp [MAP_PARTIAL_rwr] >>
  Induct_on ‘xs’ >|
  [
    simp []
    ,
    simp [] >>
    rpt gen_tac >> CASE_TAC >|
    [
      rename1 ‘IS_SOME (f h)’ >> Cases_on ‘f h’ >>
      (fs [])
      ,
      fs []
    ]
  ]
QED

Triviality EVERY_oEL:
  !P l.
    EVERY P l <=> !x n. oEL n l = SOME x ==> P x 
Proof
  fs [EVERY_EL, oEL_THM]
QED

Theorem mem_get_correctness:
  !M l t m.
    mem_get M l t = SOME m <=>
    ((t = 0 /\ m = mem_default l)
     \/
     (t <> 0 /\ oEL (PRE t) M = SOME m /\ m.loc = l))
Proof
  Cases_on ‘t’ >- fs [mem_get_def, EQ_SYM_EQ] >>
  fs [mem_get_def, CaseEq"option"]
QED

Triviality IS_SOME_mem_get_0_thm:
  !M l.
    IS_SOME (mem_get M l 0)
Proof
  fs [mem_get_def]
QED

Theorem mem_get_mem_read:
  !M l t m.
    mem_get M l t = SOME m ==> mem_read M l t = SOME m.val
Proof
  Cases_on ‘t’ >>
  (fs [mem_get_def, mem_default_def, mem_read_def])
QED

Theorem mem_atomic_correctness:
  !M l cid t_r t_w.
    mem_atomic M l cid t_r t_w = fulfil_atomic_ok M l cid t_r t_w
Proof
  fs [mem_atomic_def, fulfil_atomic_ok_def, mem_every_thm] >>
  rpt gen_tac >>
  eq_tac >|
  [
    rpt strip_tac >>
    Cases_on ‘t'’ >|
    [
      fs []
      ,
      fs [mem_is_loc_correctness, mem_is_cid_correctness, oEL_THM]
    ]
    ,
    rpt strip_tac >>
    rename1 ‘t_r < SUC t’ >>
    ‘mem_is_loc M (SUC t) l’ by (fs [mem_is_loc_correctness, oEL_THM]) >>
    ‘mem_is_cid M (SUC t) cid’ by (fs [mem_is_cid_correctness, oEL_THM]) >>
    LAST_X_ASSUM drule >>
    gs [mem_is_cid_correctness, oEL_THM]
  ]
QED

Theorem MEM_readable_thm:
  !m_t M v_max l.
    MEM m_t (mem_readable M l v_max)
    = (mem_get M l (SND m_t) = SOME (FST m_t) /\
       !t'. latest_t l M (SND m_t) v_max)
Proof
  tmCases_on “m_t” ["m t"] >>
  fs [latest_t_def] >>
  rpt gen_tac >>
  eq_tac >|
  [
    rewrite_tac [mem_readable_def, mem_every_thm, mem_filter_thm, MEM_FILTER] >>
    fs [] >>
    rpt strip_tac >|
    [
      fs [mem_get_def, mem_default_def]
      ,
      Cases_on ‘t'’ >|
      [
        fs []
        ,
        fs [mem_is_loc_correctness, oEL_THM] >>
        FIRST_X_ASSUM drule >>
        fs []
      ]
      ,
      Cases_on ‘t’ >|
      [
        fs [MEM, mem_filter_def, MEM_ZIP_memory_timestamp, MEM_FILTER]
        ,
        fs [mem_filter_thm, mem_get_def]
      ]
      ,
      Cases_on ‘t'’ >|
      [
        fs []
        ,
        fs [mem_is_loc_correctness, oEL_THM] >>
        FIRST_X_ASSUM drule >>
        fs []
      ]
    ]
    ,
    rewrite_tac [mem_readable_def, mem_every_thm, mem_filter_thm, MEM_FILTER] >>
    fs [] >>
    rpt strip_tac >|
    [
      FIRST_X_ASSUM drule >>
      fs [mem_is_loc_correctness, oEL_THM]
      ,
      Cases_on ‘t’ >|
      [
        fs [mem_get_def]
        ,
        fs [mem_get_correctness, mem_filter_thm]
      ]
    ]
  ]
QED

(************************************************************
 * Soundness proof of executable core-local step
 ************************************************************)
Theorem eval_clstep_load_soundness:
  !p cid M s s' var e acq rel xcl cast l.
    s.bst_status = BST_Running /\
    MEM (l, s') (eval_clstep_load s M var e acq rel xcl) ==>
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Load var e cast acq rel xcl)) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac
  >> fs [eval_clstep_load_def, bir_eval_exp_view_def]
  >> Cases_on ‘bir_eval_exp e s.bst_environ’ >- (fs [CaseEq"option"])
  >> fs [CaseEq"option"] 
  >> fs [MEM_MAP_PARTIAL, MEM_MAP]
  >> rename1 ‘MEM msg_t (mem_readable M loc _)’ >> tmCases_on “msg_t” ["msg t"]
  >> fs [MEM_readable_thm]
  >> fs [clstep_cases, bir_state_t_component_equality, bir_eval_exp_view_def]
  >> DISJ1_TAC
  >> imp_res_tac mem_get_mem_read
  >> Q.EXISTS_TAC ‘msg.val’ >> Q.EXISTS_TAC ‘t’
  >> fs [MAXL_def, ifView_def, combinTheory.UPDATE_def]
  >> every_case_tac
  >> (fs [AC MAX_ASSOC MAX_COMM, COND_RATOR] >> METIS_TAC [])
QED                                   

Theorem eval_clstep_store_fulfil_soundness:
  !p s s' var_succ a_e v_e xcl acq rel cid M l.
    s.bst_status = BST_Running /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) /\
    MEM (l, s') (eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_store_fulfil_def, bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp a_e s.bst_environ” ["", "loc"] >> fs[] >>
  tmCases_on “bir_eval_exp v_e s.bst_environ” ["", "val"] >> fs[] >>
  fs [MEM_MAP_PARTIAL, MEM_MAP, MEM_FILTER] >>
  tmCases_on “fulfil_update_env p s” ["", "new_env"] >> fs [] >>
  tmCases_on “fulfil_update_viewenv p s v_post” ["", "new_viewenv"] >> fs [] >>
  fs [clstep_cases, bir_eval_exp_view_def, bir_state_t_component_equality, combinTheory.UPDATE_def,
      mem_atomic_correctness, MAXL_def, ifView_def, IS_SOME_EQ_NOT_NONE] >>
  every_case_tac >> fs [AC MAX_ASSOC MAX_COMM] >> METIS_TAC []
QED

Theorem eval_clstep_store_xclfail_soundness:
  !p s s' var_succ a_e v_e xcl acq rel cid M l.
    s.bst_status = BST_Running /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) /\
    MEM (l, s') (eval_clstep_store_xclfail p cid s xcl) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  Cases_on ‘xcl’ >|
  [
    fs [eval_clstep_store_xclfail_def, clstep_cases] >>
    Cases_on ‘xclfail_update_env p s’ >- (fs []) >>
    Cases_on ‘xclfail_update_viewenv p s’ >- (fs []) >>
    rpt strip_tac >>
    fs [bir_state_t_component_equality]
    ,
    fs [eval_clstep_store_xclfail_def]
  ]
QED

Theorem eval_clstep_amo_fulfil_soundness:
  !p s var a_e v_e acq rel s' cid M l.
    s.bst_status = BST_Running /\
    MEM (l, s') (eval_clstep_amo_fulfil cid s M var a_e v_e acq rel) /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [eval_clstep_amo_fulfil_def, bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp a_e s.bst_environ” ["", "loc"] >> fs [] >>
  fs [LIST_BIND_def, MEM_FLAT] >>
  rename1 ‘MEM (l, s') state_list’ >>
  fs [MEM_MAP] >>
  rename1 ‘MEM x (mem_readable M loc _)’ >> tmCases_on “x” ["m_r t_r"] >>
  fs [MEM_readable_thm] >>
  Cases_on ‘env_update_cast64 (bir_var_name var) m_r.val (bir_var_type var) s.bst_environ’ >- (gs []) >>
  rename1 ‘SOME new_environ’ >>
  fs [bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp v_e new_environ” ["", "v"] >- rfs [] >>
  rfs [] >>
  fs [MEM_MAP, MEM_FILTER] >>
  fs [clstep_cases, bir_state_t_component_equality, combinTheory.UPDATE_def,
      MAXL_def, ifView_def, bir_eval_exp_view_def, mem_every_amo] >>
  imp_res_tac mem_get_mem_read >>
  Q.EXISTS_TAC ‘m_r.val’ >> Q.EXISTS_TAC ‘t_r’ >>
  every_case_tac >> fs []
QED

Theorem eval_clstep_assign_soundness:
  !p cid M s s' var e l.
    s.bst_status = BST_Running /\
    MEM (l, s') (eval_clstep_assign s var e) /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Assign var e)) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_assign_def] >>
  every_case_tac >> (fs [])
QED                                              

Theorem eval_clstep_fence_soundness:
  !p cid M s s' K1 K2 l.
    s.bst_status = BST_Running /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Fence K1 K2)) /\
    MEM (l, s') (eval_clstep_fence s K1 K2) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_fence_def, bir_state_t_component_equality] >>
  every_case_tac >> (fs [AC MAX_ASSOC MAX_COMM])
QED

Theorem eval_clstep_branch_soundness:
  !p cid M s s' cond_e lbl1 lbl2 l.
    s.bst_status = BST_Running /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) /\
    MEM (l,s') (eval_clstep_branch p s cond_e lbl1 lbl2) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_branch_def, bir_state_t_component_equality] >>
  Cases_on ‘bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv’ >>
  (fs [] >> every_case_tac >> (fs []))
QED


Theorem eval_clstep_generic_soundness:
  !p cid M s s' stmt l.
    s.bst_status = BST_Running /\
    bir_get_current_statement p s.bst_pc = SOME stmt /\
    MEM (l,s') (eval_clstep_generic p s stmt) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac
  >> fs [clstep_cases, eval_clstep_generic_def, bir_state_t_component_equality]
  >> fs [bmc_exec_general_stmt_def]
  >> every_case_tac
  >> (fs[])
QED

Theorem eval_clstep_soundness:
  !p cid M s s' l.
    MEM (l,s') (eval_clstep cid p s M) ==>
    clstep p cid s M l s'
Proof
  rpt strip_tac
  >> fs [eval_clstep_def]
  >> Cases_on ‘s.bst_status = BST_Running’
  >| [
    Cases_on ‘bir_get_current_statement p s.bst_pc’ >> fs[]
    >> FULL_CASE_TAC
    >| [ (* BStmtB *)
      fs []
      >> FULL_CASE_TAC
      >| [ (* load *)
        fs [eval_clstep_load_soundness]
        , (* store *)
        fs [eval_clstep_store_fulfil_soundness, eval_clstep_store_xclfail_soundness]
        , (* amo *)
        fs [eval_clstep_amo_fulfil_soundness]
        , (* assign *)
        fs [eval_clstep_assign_soundness]
        , (* fence *)
        fs [eval_clstep_fence_soundness]
        , (* assert *)
        fs [eval_clstep_generic_soundness]
        , (* assume *)
        fs [eval_clstep_generic_soundness]
      ]
      , (* BStmtE *)
      fs [] >>
      FULL_CASE_TAC >|
      [ (* jmp *)
        fs [eval_clstep_generic_soundness]
        , (* cjmp *)
        fs [eval_clstep_branch_soundness]
        , (* halt *)
        fs [eval_clstep_generic_soundness]
      ]
    ]
    ,
    fs []
  ]
QED

(************************************************************
 * Completeness proof of executable core-local step
 ************************************************************)

Theorem eval_clstep_load_completeness:
  !p cid M s s' var a_e acq rel xcl cast l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Load var a_e cast xcl acq rel)) ==>
    MEM (l,s') (eval_clstep_load s M var a_e xcl acq rel)
Proof
  rpt strip_tac
  >> gvs [clstep_cases, eval_clstep_load_def, bir_eval_exp_view_def]
  >| [ (* load *)
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- (fs [CaseEq"option"])
    (* MEM s' (MAP_PARTIAL (λ(msg,t). state option) (mem_readable M x (MAX ...)) *)
    >> fs [MEM_MAP_PARTIAL, MEM_MAP, mem_read_def, CaseEq"option"]
    >> Q.EXISTS_TAC ‘(m,t)’
    >> fs [MEM_readable_thm, bir_state_t_component_equality]
    >> fs [MAXL_def, ifView_def, combinTheory.UPDATE_def]
    >> rw []
    >> gvs [AC MAX_ASSOC MAX_COMM]
    >> METIS_TAC []
    , (* mismatch *)
    fs [bmc_exec_general_stmt_def]
  ]
QED                                   

Theorem eval_clstep_store_completeness:
  !p s s' var_succ a_e v_e xcl acq rel cid M l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) ==>
    MEM (l,s') (eval_clstep_store_fulfil p cid s M a_e v_e xcl acq rel ++ eval_clstep_store_xclfail p cid s xcl)
Proof
  rpt strip_tac
  >> fs [clstep_cases, eval_clstep_store_fulfil_def, eval_clstep_store_xclfail_def, bir_eval_exp_view_def]
  >| [
    (* xclfail *)
    DISJ2_TAC
    >> (Cases_on ‘xclfail_update_env p s’
        >>  Cases_on ‘xclfail_update_viewenv p s’)
    >> (fs [bir_state_t_component_equality, combinTheory.UPDATE_def])
    ,
    (* fulfill *)
    DISJ1_TAC
    >> (
      Cases_on ‘bir_eval_exp a_e s.bst_environ’
      >> Cases_on ‘bir_eval_exp v_e s.bst_environ’
      >> fs []
      )
    >> fs [MEM_MAP_PARTIAL, MEM_MAP, MEM_FILTER]
    >> Q.EXISTS_TAC ‘v_post’
    >> fs []
    >> (Cases_on ‘fulfil_update_env p s’ >> Cases_on ‘fulfil_update_viewenv p s v_post’ >> fs[])
    >> gvs [bir_state_t_component_equality, combinTheory.UPDATE_def, ifView_def, MAXL_def]
    >> fs [mem_atomic_correctness, IS_SOME_EQ_NOT_NONE]
    >> (
      every_case_tac
      >> (fs[] >> METIS_TAC [MAX_ASSOC, MAX_COMM])
      )
    , (* mismatch *)
    fs [bmc_exec_general_stmt_def]
  ] 
QED

Theorem eval_clstep_amo_completeness:
  !p s var a_e v_e acq rel s' cid M l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) ==>
    MEM (l,s') (eval_clstep_amo_fulfil cid s M var a_e v_e acq rel)
Proof
  rpt strip_tac >>
  fs [clstep_cases, eval_clstep_amo_fulfil_def, bir_eval_exp_view_def]
  >| [
    Cases_on ‘bir_eval_exp a_e s.bst_environ’
    >- (fs [])
    >> fs [LIST_BIND_def, MEM_FLAT, MEM_MAP]
    >> CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV)
    >> CONV_TAC SWAP_EXISTS_CONV
    >> fs [mem_read_correctness]
    >> Q.EXISTS_TAC ‘(m, t_r)’
    >> fs [MEM_readable_thm, latest_t_def]
    >> Cases_on ‘env_update_cast64 (bir_var_name var) v_r (bir_var_type var) s.bst_environ’ >- fs []
    >> Cases_on ‘bir_eval_exp v_e new_environ’ >- fs []
    >> gvs [MEM_FILTER, MEM_MAP]
    >> fs [bir_state_t_component_equality, mem_every_amo]
    >> fs [MAXL_def, ifView_def]
    >> every_case_tac
    >> (fs[])
    ,
    fs [bmc_exec_general_stmt_def]
  ]
QED                                              

Theorem eval_clstep_assign_completeness:
  !p cid M s s' var e l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Assign var e)) ==>
    MEM (l, s') (eval_clstep_assign s var e)
Proof
  rpt strip_tac
  >> gvs [clstep_cases, eval_clstep_assign_def, bir_eval_exp_view_def]
  >| [
    CASE_TAC >- (fs [])
    >> CASE_TAC >- (fs [])
    >> fs [combinTheory.UPDATE_def, bir_state_t_component_equality, MAX_COMM]
    ,
    fs [bmc_exec_general_stmt_def]
  ]
QED

Theorem eval_clstep_fence_completeness:
  !p cid M s s' K1 K2 l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Fence K1 K2)) ==>
    MEM (l, s') (eval_clstep_fence s K1 K2)
Proof
  rpt strip_tac
  >> gvs [clstep_cases, eval_clstep_fence_def, bir_eval_exp_view_def]
  >| [
    fs [combinTheory.UPDATE_def, bir_state_t_component_equality, MAX_COMM]
    ,
    fs [bmc_exec_general_stmt_def]
  ]
QED

Theorem eval_clstep_branch_completeness:
  !p cid M s s' cond_e lbl1 lbl2 l.
    clstep p cid s M l s' /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) ==>
    MEM (l,s') (eval_clstep_branch p s cond_e lbl1 lbl2)
Proof
  rpt strip_tac
  >> gvs [clstep_cases, eval_clstep_branch_def, bir_eval_exp_view_def]
  >| [
    Cases_on ‘bir_eval_exp cond_e s.bst_environ’
    >> (fs [])
    ,
    fs [bmc_exec_general_stmt_def]
  ]
QED

Theorem eval_clstep_completeness:
  !p cid s M s' l.
    clstep p cid s M l s' ==> MEM (l,s') (eval_clstep cid p s M)
Proof
  rpt strip_tac
  >> fs [eval_clstep_def]
  >> Cases_on ‘bir_get_current_statement p s.bst_pc’
  >| [ (* NONE *)
    fs [clstep_cases]
    , (* SOME *)
    Cases_on ‘s.bst_status = BST_Running’ >> (fs [])
    >| [ (* running *)
        FULL_CASE_TAC
        >| [ (* BStmtB *)
          FULL_CASE_TAC
          >| [(* read *)
            imp_res_tac eval_clstep_load_completeness
            , (* fulfil & xclfail *)
            imp_res_tac eval_clstep_store_completeness >> fs[]
            , (* amofulfil *)
            imp_res_tac eval_clstep_amo_completeness
            , (* expr *)
            imp_res_tac eval_clstep_assign_completeness
            , (* fence *)
            imp_res_tac eval_clstep_fence_completeness
            , (* assert *)
            fs [eval_clstep_generic_def, clstep_cases]
            , (* assume *)
            fs [eval_clstep_generic_def, clstep_cases]
          ]
          , (* BStmtE *)
          FULL_CASE_TAC
          >| [ (* jmp *)
              fs [eval_clstep_generic_def, clstep_cases]
              ,(* cjmp *)
              imp_res_tac eval_clstep_branch_completeness
              ,(* halt *)
              fs [eval_clstep_generic_def, clstep_cases]
            ]
        ]
        , (* not running *)
        fs [clstep_cases]
      ]
  ]
QED

(************************************************************
 * Correctness of executable core-local step
 ************************************************************)

Theorem eval_clstep_correctness:
  !p cid s M s' l.
    MEM (l,s') (eval_clstep cid p s M) = clstep p cid s M l s'
Proof
  rpt strip_tac >>
  eq_tac >|
  [
    simp [eval_clstep_soundness]
    ,
    simp [eval_clstep_completeness]
  ]
QED

(************************************************************
 * Definition of fueled core-step and its correctness
 ************************************************************)

(* rtc core-step with fuel *)
Definition cstep_seq_rtc_f_def:
  (cstep_seq_rtc_f 0 p cid (s,M) (s',M') <=> (s = s' /\ M = M'))
  /\
  (cstep_seq_rtc_f (SUC f) p cid (s,M) (s',M') <=>
   ((s = s' /\ M = M') \/
    ?s'' M''. cstep_seq p cid (s,M) (s'',M'') /\ cstep_seq_rtc_f f p cid (s'',M'') (s',M')))
End

(* certificate with fuel *)
Definition is_certified_f_def:
  is_certified_f f p cid s M <=>
  ?s' M'. cstep_seq_rtc_f f p cid (s, M) (s', M') /\ s'.bst_prom = []
End

(* If the promset is empty, then trivialy certified *)
Triviality NULL_prom_is_certified_triv:
  !p cid s M.
    s.bst_prom = [] ==> is_certified p cid s M
Proof
  rw [is_certified_def] >>
  Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘M’ >>
  fs [cstep_seq_rtc_def]
QED  

(* The fueled cstep is contained in the non-fueled cstep *)
Theorem cstep_seq_rtc_f_soundness:
  !f cid p s M s' M'.
    cstep_seq_rtc_f f p cid (s,M) (s', M') ==>
    cstep_seq_rtc p cid (s,M) (s',M')
Proof
  Induct_on ‘f’ >|
  [
    fs [cstep_seq_rtc_def, cstep_seq_rtc_f_def]
    ,
    simp [cstep_seq_rtc_def, Once RTC_CASES1] >>
    simp [cstep_seq_rtc_f_def] >>
    rpt strip_tac >|
    [
      fs []
      ,
      DISJ2_TAC >>
      Q.EXISTS_TAC ‘(s'', M'')’ >>
      res_tac >>
      fs [cstep_seq_rtc_def]
    ]
  ]
QED


(* For every non-fueled trace, there exists a fuel that gives an equivalent fieled trace. *)
Theorem cstep_seq_rtc_f_completeness:
  !cid p s M s' M'.
    cstep_seq_rtc p cid (s,M) (s',M') ==>
    ?f. cstep_seq_rtc_f f p cid (s,M) (s', M')
Proof
  rpt gen_tac >>
  qabbrev_tac ‘sM = (s, M)’ >> qabbrev_tac ‘sM' = (s', M')’ >>
  qid_spec_tac ‘sM'’ >> qid_spec_tac ‘sM’ >>
  fs [Abbr ‘sM’, Abbr ‘sM'’] >>
  fs [cstep_seq_rtc_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >|
  [
    Q.EXISTS_TAC ‘0’ >>
    Cases_on ‘sM’ >>
    fs [cstep_seq_rtc_f_def]
    ,
    Cases_on ‘sM’ >> Cases_on ‘sM'’ >> Cases_on ‘sM''’ >>
    Q.EXISTS_TAC ‘SUC f’ >>
    simp [cstep_seq_rtc_f_def] >>
    DISJ2_TAC >>
    rename1 ‘cstep_seq p cid (s,M) (s', M')’ >>
    Q.EXISTS_TAC ‘s'’ >> Q.EXISTS_TAC ‘M'’ >>
    fs []
  ]  
QED

(* For every non-fueled trace, there exists a fuel that gives an equivalent fieled trace. *)
Theorem cstep_seq_rtc_f_correctness:
  !cid p s M s' M'.
    (?f. cstep_seq_rtc_f f p cid (s,M) (s', M')) <=>
    cstep_seq_rtc p cid (s,M) (s',M')
Proof
  rpt gen_tac >> eq_tac >>
  simp [cstep_seq_rtc_f_completeness, cstep_seq_rtc_f_soundness]
QED

Theorem is_certified_f_correctness:
  !cid p s M.
    (?f. is_certified_f f p cid s M) <=> is_certified p cid s M
Proof
  METIS_TAC [cstep_seq_rtc_f_correctness, is_certified_f_def, is_certified_def]
QED


(************************************************************
 * Soundness proof for executable cstep
 ************************************************************)

Theorem eval_cstep_seq_store_soundness:
  !cid p s M s' M' var_succ a_e v_e xcl acq rel msgs.
    s.bst_status = BST_Running /\
    MEM (s', msgs) (eval_cstep_seq_store p cid s M a_e v_e xcl acq rel) /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel))
    ==> cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  gvs [eval_cstep_seq_store_def, bir_eval_exp_view_def] >>
  Cases_on ‘bir_eval_exp v_e s.bst_environ’ >- fs[] >>
  Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- fs[] >>
  fs [MEM_MAP, MEM_FILTER] >>
  rename1 ‘(s', msgs) = _ smsgs’ >> Cases_on ‘smsgs’ >>
  imp_res_tac eval_clstep_store_fulfil_soundness >>
  fs [cstep_seq_cases] >>
  Q.EXISTS_TAC ‘s with bst_prom updated_by (λprom. prom ++ [SUC (LENGTH M)])’ >>
  Q.EXISTS_TAC ‘SUC (LENGTH M)’ >>
  gvs [SNOC_APPEND, cstep_cases, bir_state_t_component_equality]
QED

Theorem eval_cstep_seq_amo_soundness:
  !cid p s M s' M' var a_e v_e acq rel msgs.
    s.bst_status = BST_Running /\
    MEM (s', msgs) (eval_cstep_seq_amo cid s M var a_e v_e acq rel) /\
    bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) ==>
    cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  (* Decompose assumptions *)
  gvs [eval_cstep_seq_def, MEM_MAP2, eval_cstep_seq_amo_def, bir_eval_exp_view_def] >>
  tmCases_on “bir_eval_exp a_e s.bst_environ” ["","a"] >- fs[] >>
  fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
  rename1 ‘MEM m_t_r (mem_readable _ _ _)’ >>
  tmCases_on “m_t_r” ["m t_r"] >>
  fs [MEM_readable_thm] >>
  tmCases_on “env_update_cast64 (bir_var_name var) m.val (bir_var_type var) s.bst_environ” ["","new_environ"] >- rfs [] >>
  tmCases_on “bir_eval_exp v_e new_environ” ["","v"] >- gvs [] >>
  gvs [MEM_MAP2, MEM_FILTER] >>
  imp_res_tac eval_clstep_amo_fulfil_soundness >>
  fs [cstep_seq_cases] >>
  Q.EXISTS_TAC ‘s with bst_prom updated_by (λprom. prom ++ [SUC (LENGTH M)])’ >>
  Q.EXISTS_TAC ‘SUC (LENGTH M)’ >>
  CONJ_TAC >|
  [
    fs [cstep_cases, bir_state_t_component_equality]
    ,
    gvs []
  ]
QED

Theorem eval_cstep_seq_soundness:
  !cid p s M s' msgs.
    MEM (s', msgs) (eval_cstep_seq cid p s M)
    ==>
    cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt strip_tac >>
  Cases_on ‘bir_get_current_statement p s.bst_pc’ >- fs [eval_cstep_seq_def] >>
  fs [eval_cstep_seq_def] >>
  Cases_on ‘s.bst_status = BST_Running’ >> (fs []) >>
  FULL_CASE_TAC >|
  [ (* BstmtB *)
    fs [] >>
    FULL_CASE_TAC >|
    [ (* load *)
      gvs [eval_cstep_seq_def, MEM_MAP2, cstep_seq_cases] >>
      rename1 ‘MEM (l, s') _’ >> Q.EXISTS_TAC ‘l’ >>
      fs [eval_clstep_load_soundness]
      , (* store *)
      fs [] >|
      [
        imp_res_tac eval_cstep_seq_store_soundness
        ,
        gvs [MEM_MAP2, cstep_seq_cases] >>
        imp_res_tac eval_clstep_store_fulfil_soundness >>
        HINT_EXISTS_TAC >>
        fs []
        ,
        gvs [MEM_MAP2, cstep_seq_cases] >>
        imp_res_tac eval_clstep_store_xclfail_soundness >>
        rename1 ‘clstep p cid s M l s'’ >>
        Q.EXISTS_TAC ‘l’ >>
        fs []
      ]
      , (* amo *)
      fs [] >|
      [
        imp_res_tac eval_cstep_seq_amo_soundness
        ,
        gvs [MEM_MAP2, cstep_seq_cases] >>
        imp_res_tac eval_clstep_amo_fulfil_soundness >>
        HINT_EXISTS_TAC >>
        fs []
      ]
      , (* assign *)
      gvs [MEM_MAP2, cstep_seq_cases] >>
      imp_res_tac eval_clstep_assign_soundness >>
      rename1 ‘clstep p cid s M l s'’ >>
      Q.EXISTS_TAC ‘l’ >>
      fs []
      , (* fence *)
      gvs [MEM_MAP2, cstep_seq_cases] >>
      imp_res_tac eval_clstep_fence_soundness >>
      rename1 ‘clstep p cid s M l s'’ >>
      Q.EXISTS_TAC ‘l’ >>
      fs []
      , (* assert *)
      gvs [MEM_MAP2, cstep_seq_cases, eval_clstep_generic_def,
           bmc_exec_general_stmt_def, clstep_cases, bir_exec_stmtB_def]
      , (* assume *)
      gvs [MEM_MAP2, cstep_seq_cases, eval_clstep_generic_def,
           bmc_exec_general_stmt_def, clstep_cases, bir_exec_stmtB_def]
    ]
    , (* BStmtE *)
    fs [] >>
    FULL_CASE_TAC >|
    [
      gvs [MEM_MAP2, cstep_seq_cases, eval_clstep_generic_def,
           bmc_exec_general_stmt_def, clstep_cases, bir_exec_stmtB_def]
      ,
      gvs [MEM_MAP2, cstep_seq_cases] >>
      imp_res_tac eval_clstep_branch_soundness >>
      rename1 ‘clstep p cid s M l s'’ >>
      Q.EXISTS_TAC ‘l’ >>
      fs[] 
      ,
      gvs [MEM_MAP2, cstep_seq_cases, eval_clstep_generic_def,
           bmc_exec_general_stmt_def, clstep_cases, bir_exec_stmtB_def]
    ]
  ]
QED

(************************************************************
 * Completeness proof of executable cstep
 ************************************************************)
Theorem eval_cstep_seq_store_completeness:
  !cid p s M s' var_succ a_e v_e xcl acq rel msgs.
    msgs <> [] /\
    (cstep_seq p cid (s,M) (s',M ++ msgs)) /\
    (bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel))) ==>
    MEM (s', msgs) (eval_cstep_seq_store p cid s M a_e v_e xcl acq rel)
Proof
  rpt strip_tac >>
  Cases_on ‘s.bst_status = BST_Running’ >|
  [ (* running *)
    gvs [cstep_seq_cases, MEM_MAP2] >>
    fs [eval_cstep_seq_def] >>
    fs [cstep_cases] >>
    fs [eval_cstep_seq_store_def, bir_eval_exp_view_def] >>
    Cases_on ‘bir_eval_exp v_e s.bst_environ’ >- gvs [bir_eval_exp_view_def, clstep_cases] >>
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- gvs [bir_eval_exp_view_def, clstep_cases] >>
    rename1 ‘bir_eval_exp v_e s.bst_environ = SOME v’ >>
    rename1 ‘bir_eval_exp a_e s.bst_environ = SOME l’ >>
    fs [MEM_MAP2, MEM_FILTER] >>
    imp_res_tac eval_clstep_store_completeness >>
    gvs [bir_state_t_accfupds] >|
    [
      ‘<| loc := l; val := v; cid := msg.cid |> = msg’ by
       (gvs [clstep_cases, bir_eval_exp_view_def, GSYM ADD1, GSYM SNOC_APPEND, mem_get_SNOC2]) >>
      ‘(\pr. pr ++ [LENGTH M + 1]) = SNOC (SUC (LENGTH M))’ by
        METIS_TAC [ADD1, GSYM SNOC_APPEND] >>
      gvs [GSYM ADD1, GSYM SNOC_APPEND]
      ,
      Cases_on ‘xcl’ >|
      [
        fs [eval_clstep_store_xclfail_def] >>
        Cases_on ‘xclfail_update_env p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))’ >- fs[] >>
        Cases_on ‘xclfail_update_viewenv p (s with bst_prom updated_by (\pr. pr ++ [LENGTH M + 1]))’ >- fs[] >>
        fs []
        ,
        fs [eval_clstep_store_xclfail_def]
      ]
    ]
    , (* not running *)
    gvs [cstep_seq_cases, clstep_cases, cstep_cases]
  ]
QED

Triviality not_mem_is_loc_SNOC:
  !t M l msg.
    t < LENGTH M + 1 /\
    ~mem_is_loc (SNOC msg M) t l ==>
    ~mem_is_loc M t l
Proof
  rpt gen_tac >>
  strip_tac >>
  Induct_on ‘t’ >|
  [
    fs [mem_is_loc_def]
    ,
    strip_tac >> strip_tac >>
    gvs [mem_is_loc_def, oEL_THM, EL_SNOC]
  ]
QED


Theorem eval_cstep_seq_amo_completeness:
  !cid p s M s' M a_e v_e xcl acq rel var msgs.
    msgs <> [] /\
    (cstep_seq p cid (s,M) (s',M ++ msgs)) /\
    (bir_get_current_statement p s.bst_pc = SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel))) ==>
    MEM (s', msgs) (eval_cstep_seq_amo cid s M var a_e v_e acq rel)
Proof
  rpt strip_tac >>
  Cases_on ‘s.bst_status = BST_Running’ >|
  [ (* running *)
    rfs [cstep_seq_cases, MEM_MAP2, cstep_cases] >>
    ‘bir_get_current_statement p s'''.bst_pc = SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel))’ by fs [bir_state_t_component_equality] >>
    imp_res_tac eval_clstep_amo_completeness >>
    first_x_assum kall_tac >>
    fs [eval_cstep_seq_def] >>
    fs [eval_cstep_seq_amo_def, bir_eval_exp_view_def] >>
    Cases_on ‘bir_eval_exp a_e s.bst_environ’ >- gvs [clstep_cases, bir_eval_exp_view_def] >>
    fs [LIST_BIND_def, MEM_FLAT, MEM_MAP] >>
    CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) >>
    CONV_TAC SWAP_EXISTS_CONV >>
    fs [clstep_cases, bir_eval_exp_view_def] >>
    fs [mem_read_correctness] >>
    rename1 ‘mem_get (M ++ [msg]) l t_r = SOME m_r’ >>
    Q.REFINE_EXISTS_TAC ‘(m_r, t_r)’ >>
    gvs [MEM_readable_thm] >>
    CONJ_TAC >|
    [
      fs [mem_get_SNOC, Once (GSYM SNOC_APPEND), MAXL_def] >>
      fs [latest_t_def] >>
      gen_tac >> strip_tac >>
      Cases_on ‘acq’ >> Cases_on ‘rel’ >>
      fs [ifView_def] >>
      ‘t_r < t' /\ t' < LENGTH M + 1’ by fs[] >>
      ‘~mem_is_loc (SNOC msg M) t' l’ by fs [] >>
      METIS_TAC [not_mem_is_loc_SNOC]
      ,
      Cases_on ‘env_update_cast64 (bir_var_name var) m_r.val (bir_var_type var) s.bst_environ’ >- fs[] >>
      Cases_on ‘bir_eval_exp v_e new_environ’ >- gvs [] >>
      gvs [MEM_MAP2, MEM_FILTER, latest_t_def, mem_get_SNOC2,ADD1] >>
      ‘<| loc := l; val := v_w; cid := msg.cid |> = msg’ by
        (gvs [GSYM ADD1, GSYM SNOC_APPEND, mem_get_SNOC2]) >>
      gvs []
    ]
    , (* not running *)
    gvs [cstep_seq_cases, clstep_cases, cstep_cases]
  ]
QED


Theorem eval_cstep_seq_completeness:
  !cid p s M s' msgs.
    cstep_seq p cid (s, M) (s', M ++ msgs) ==> MEM (s', msgs) (eval_cstep_seq cid p s M)
Proof
  rpt strip_tac >>
  Cases_on ‘s.bst_status = BST_Running’ >|
  [ (* running *)
    Cases_on ‘bir_get_current_statement p s.bst_pc’ >- gvs [clstep_cases, cstep_seq_cases, cstep_cases] >>
    Cases_on ‘msgs = []’ >|
    [ (* msgs = [] *)
      fs [cstep_seq_cases, eval_cstep_seq_def] >>
      CASE_TAC >|
      [ (* BStmtB *)
        CASE_TAC >|
        [ (* load *)
          imp_res_tac eval_clstep_load_completeness >>
          fs [eval_cstep_seq_def, MEM_MAP2] >>
          HINT_EXISTS_TAC >>
          fs []
          , (* store *)
          fs [MEM_APPEND, MEM_MAP2] >>
          imp_res_tac eval_clstep_store_completeness >>
          fs [MEM_APPEND] >|
          [
            DISJ1_TAC >> DISJ2_TAC >>
            HINT_EXISTS_TAC >>
            fs []
            ,
            DISJ2_TAC >>
            HINT_EXISTS_TAC >>
            fs []
          ]
          , (* amo *)
          fs [MEM_APPEND, MEM_MAP2] >>
          imp_res_tac eval_clstep_amo_completeness >>
          DISJ2_TAC >>
          HINT_EXISTS_TAC >>
          fs []
          , (* assign *)
          fs [MEM_MAP2] >>
          imp_res_tac eval_clstep_assign_completeness >>
          HINT_EXISTS_TAC >>
          fs []
          , (* fence *)
          fs [MEM_MAP2] >>
          imp_res_tac eval_clstep_fence_completeness >>
          HINT_EXISTS_TAC >>
          fs []
          , (* assert *)
          fs [MEM_MAP2, eval_clstep_generic_def, clstep_cases]
          , (* assume *)
          fs [MEM_MAP2, eval_clstep_generic_def, clstep_cases]
        ]
        , (* BStmtE *)
        FULL_CASE_TAC >|
        [ (* jmp *)
          gvs [MEM_MAP2, eval_clstep_generic_def, clstep_cases]
          , (* cjmp *)
          fs [MEM_MAP2] >>
          imp_res_tac eval_clstep_branch_completeness >>
          HINT_EXISTS_TAC >>
          fs []
          , (* halt*)
          gvs [MEM_MAP2, eval_clstep_generic_def, clstep_cases]
        ]
      ]
      , (* msgs <> [] *)
      fs [eval_cstep_seq_def] >>
      FULL_CASE_TAC >|
      [ (* BStmtB *)
        FULL_CASE_TAC >|
        [ (* load *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* store *)
          fs [MEM_APPEND, MEM_MAP2] >>
          imp_res_tac eval_cstep_seq_store_completeness
          , (* amo *)
          fs [MEM_APPEND, MEM_MAP2] >>
          imp_res_tac eval_cstep_seq_amo_completeness
          , (* assign *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* fence *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* assert *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* assume *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
        ]
        ,
        FULL_CASE_TAC >|
        [ (* jmp *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* cjmp *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
          , (* halt *)
          gvs [cstep_seq_cases, cstep_cases, clstep_cases]
        ]
      ]
    ]
    , (* not running *)
    gvs [cstep_seq_cases, cstep_cases, clstep_cases, bir_state_t_component_equality]
  ]
QED

Theorem eval_cstep_seq_correctness:
  !cid p s M s' msgs.
    MEM (s', msgs) (eval_cstep_seq cid p s M) <=> cstep_seq p cid (s, M) (s', M ++ msgs)
Proof
  rpt gen_tac >> eq_tac >> fs [eval_cstep_seq_soundness, eval_cstep_seq_completeness]
QED


(* ??? *)
Theorem cstep_seq_Msuffix:
  !p cid s M s' M'.
    cstep_seq p cid (s,M) (s', M') ==>
    ?suffix. M ++ suffix = M'
Proof
  fs [cstep_seq_cases, cstep_cases] >>
  rpt strip_tac >> (fs [cstep_cases])
QED

(************************************************************
 * Correctness of executable is_certified
 ************************************************************)

Theorem eval_is_certified_f_correctness:
  !cid f p s M.
    (eval_is_certified f p cid s M) <=> is_certified_f f p cid s M
Proof
  Induct_on ‘f’ >|
  [
    fs [eval_is_certified_def, is_certified_f_def, cstep_seq_rtc_f_def]
    ,
    fs [eval_is_certified_def, is_certified_f_def, EXISTS_MEM2, eval_cstep_seq_correctness] >>
    rpt gen_tac >> eq_tac >|
    [
      rpt strip_tac >|
      [
        Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘M’ >>
        fs [cstep_seq_rtc_f_def]
        ,
        Q.EXISTS_TAC ‘s'’ >> Q.EXISTS_TAC ‘M'’ >>
        fs [cstep_seq_rtc_f_def] >>
        DISJ2_TAC >>
        rename1 ‘cstep_seq p cid (s,M) (s'', M'')’ >>
        Q.EXISTS_TAC ‘s''’ >> Q.EXISTS_TAC ‘M''’ >>
        fs []
      ]
      ,
      rpt strip_tac >> 
      fs [cstep_seq_rtc_f_def] >>
      DISJ2_TAC >>
      imp_res_tac cstep_seq_Msuffix >>
      Q.EXISTS_TAC ‘s''’ >> Q.EXISTS_TAC ‘suffix’ >>
      fs [] >>
      rpt HINT_EXISTS_TAC >>
      fs []
    ]
  ]
QED

Theorem eval_is_certified_correctness:
  !cid p s M.
    (?f. eval_is_certified f p cid s M) <=> is_certified p cid s M
Proof
  fs [eval_is_certified_f_correctness, is_certified_f_correctness]
QED

Definition certifiable_view_inv_def:
  certifiable_view_inv cid (s, M) =
  (~MEM 0 s.bst_prom
   /\ (!t. MEM t s.bst_prom ==> t <= LENGTH M)
   /\ s.bst_v_rOld <= LENGTH M /\ ~MEM s.bst_v_rOld s.bst_prom
   /\ s.bst_v_wOld <= LENGTH M /\ ~MEM s.bst_v_wOld s.bst_prom
   /\ s.bst_v_rNew <= LENGTH M /\ ~MEM s.bst_v_rNew s.bst_prom
   /\ s.bst_v_wNew <= LENGTH M /\ ~MEM s.bst_v_wNew s.bst_prom
   /\ s.bst_v_CAP <= LENGTH M /\ ~MEM s.bst_v_CAP s.bst_prom
   /\ s.bst_v_Rel <= LENGTH M /\ ~MEM s.bst_v_Rel s.bst_prom
   /\ (!l. s.bst_coh l <= LENGTH M /\ ~MEM (s.bst_coh l) s.bst_prom)
   /\ (!r t. FLOOKUP s.bst_viewenv r = SOME t ==> (t <= LENGTH M) /\ ~MEM t s.bst_prom)
   /\ (!l. (s.bst_fwdb l).fwdb_time <= LENGTH M /\ ~MEM (s.bst_fwdb l).fwdb_time s.bst_prom)
   /\ (!l. (s.bst_fwdb l).fwdb_view <= LENGTH M /\ ~MEM (s.bst_fwdb l).fwdb_view s.bst_prom)
   /\ (!l. (s.bst_fwdb l).fwdb_view <= (s.bst_fwdb l).fwdb_time)
   /\ (!xclb. s.bst_xclb = SOME xclb
              ==> xclb.xclb_time <= LENGTH M /\ ~MEM xclb.xclb_time s.bst_prom
                  /\ xclb.xclb_view <= LENGTH M /\ ~MEM xclb.xclb_view s.bst_prom))
End

Theorem is_certified_coh:
  !p cid s M.
    is_certified p cid s M ==>
    !t l. MEM t s.bst_prom /\ mem_is_loc M t l
          ==> s.bst_coh l < t
Proof
  cheat
QED

Triviality MAX_NOT_MEM:
  !m n l.
    ~MEM (MAX n m) l <=> if n < m then ~MEM m l else ~MEM n l
Proof
  METIS_TAC [MAX_DEF]
QED

Theorem certifiable_view_inv_IMP_bir_eval_view_of_exp:
  !cid s M.
    certifiable_view_inv cid (s, M) ==>
    !e. (bir_eval_view_of_exp e s.bst_viewenv <= LENGTH M) /\ ~MEM (bir_eval_view_of_exp e s.bst_viewenv) s.bst_prom
Proof
  rpt gen_tac >> strip_tac
  >> Induct >> fs [certifiable_view_inv_def, bir_eval_view_of_exp_def]
  >| [
    gen_tac >> CASE_TAC >- (fs [])
    >> res_tac
    >> asm_rewrite_tac []
    ,
    fs [MAX_NOT_MEM]
    ,
    fs [MAX_NOT_MEM]
  ]
QED

Theorem certifiable_view_inv_IMP_bir_eval_view_of_exp_upd:
  !cid s M t.
    certifiable_view_inv cid (s, M)
    /\ t <= LENGTH M /\ ~MEM t s.bst_prom
    ==> !r e. (bir_eval_view_of_exp e (s.bst_viewenv |+ (r, t)) <= LENGTH M)
              /\ ~MEM (bir_eval_view_of_exp e (s.bst_viewenv |+ (r, t))) s.bst_prom
Proof
  rpt gen_tac >> strip_tac >> gen_tac 
  >> imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
  >> Induct >> (fs [bir_eval_view_of_exp_def, certifiable_view_inv_def])
  >| [
    gen_tac
    >> CASE_TAC
    >> fs [FLOOKUP_UPDATE]
    >> FULL_CASE_TAC
    >> res_tac
    >> gvs []
    ,
    fs [MAX_NOT_MEM]
    ,
    fs [MAX_NOT_MEM]
  ]
QED

Theorem certifiable_view_inv_IMP_mem_read_view:
  !cid s M t.
    certifiable_view_inv cid (s, M)
    /\ t <= LENGTH M /\ ~MEM t s.bst_prom
    ==> !l. (mem_read_view (s.bst_fwdb l) t) <= LENGTH M
            /\ ~MEM (mem_read_view (s.bst_fwdb l) t) s.bst_prom
Proof
  fs [certifiable_view_inv_def]
  >> rpt gen_tac >> strip_tac >> gen_tac
  >> fs [mem_read_view_def]
  >> CASE_TAC
QED

Theorem is_certified_cstep_seq_ext:
  !p cid s1 M1 s2 M2.
    cstep_seq p cid (s1, M1) (s2,M2)
    /\ is_certified p cid s2 M2
    ==> is_certified p cid s1 M1
Proof
  fs [is_certified_def, cstep_seq_rtc_def]
  >> rpt strip_tac
  >> rewrite_tac [Once RTC_CASES1]
  >> rpt HINT_EXISTS_TAC
  >> fs []
  >> DISJ2_TAC
  >> HINT_EXISTS_TAC
  >> fs []
QED

Theorem is_certified_clstep_ext:
  !p cid s1 M s2 l.
    clstep p cid s1 M l s2
    /\ is_certified p cid s2 M 
    ==> is_certified p cid s1 M
Proof
  fs [is_certified_def, cstep_seq_rtc_def]
  >> rpt strip_tac
  >> rewrite_tac [Once RTC_CASES1]
  >> rpt HINT_EXISTS_TAC
  >> fs []
  >> DISJ2_TAC
  >> HINT_EXISTS_TAC
  >> fs [cstep_seq_cases]
  >> HINT_EXISTS_TAC
  >> fs []
QED

Theorem bir_exec_general_stmt_view_noninterference:
  !p stmt s.
    IS_SOME $ bmc_exec_general_stmt p stmt s
    ==> ?status pc oo. bmc_exec_general_stmt p stmt s = SOME (oo, s with <| bst_status := status; bst_pc := pc |>)
Proof
  rpt strip_tac
  >> fs [bmc_exec_general_stmt_def, bir_exec_stmtB_def, bir_exec_stmtE_def, bir_exec_stmt_halt_def, bir_exec_stmt_assert_def,
         bir_exec_stmt_assume_def, bir_exec_stmt_jmp_def, bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def]
  >> every_case_tac >> (fs [bir_state_t_component_equality])
QED

Theorem bir_exec_stmt_cjmp_view_noninterference:
  !p cond_e lbl1 lbl2 s1.
    ?status pc. bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s1 = s1 with <| bst_status := status; bst_pc := pc |>
Proof
  rpt strip_tac
  >> fs [bir_exec_stmt_cjmp_def, bir_exec_stmt_jmp_def, bir_state_set_typeerror_def, bir_exec_stmt_jmp_to_label_def]
  >> every_case_tac >> (fs [bir_state_t_component_equality])
QED

Theorem certifiable_view_inv_clstep:
  !p cid s1 s2 M l.
    clstep p cid s1 M l s2
    /\ is_certified p cid s2 M
    /\ certifiable_view_inv cid (s1, M)
    ==> certifiable_view_inv cid (s2, M)
Proof
  rpt strip_tac
  >> imp_res_tac is_certified_clstep_ext
  >> fs [clstep_cases, bir_eval_exp_view_def]
  >| [ (* load *)
    qsuff_tac ‘~MEM t s1.bst_prom /\ t <= LENGTH M’
    >| [
      strip_tac
      >> imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
      >> imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp_upd
      >> imp_res_tac certifiable_view_inv_IMP_mem_read_view
      >> gvs [certifiable_view_inv_def, bir_state_t_component_equality, bir_eval_exp_view_def,
              FLOOKUP_UPDATE, AC MAX_ASSOC MAX_COMM, AC CONJ_ASSOC CONJ_COMM, PULL_FORALL]
      >> rpt gen_tac
      >> rpt conj_tac
      >~ [‘(if var = r then SOME _ else _) = SOME xclb ==> _’]
      >- (
      disch_then (assume_tac o GSYM)
      >> Cases_on ‘var = r’ >> Cases_on ‘acq /\ rel’
      >> gvs [MAX_NOT_MEM]
      >> METIS_TAC []
      )
      >~ [‘(if xcl then SOME _ else s1.bst_xclb) = SOME xclb ==> _’]
      >- (
      disch_then (assume_tac o GSYM)
      >> Cases_on ‘xcl’ >> Cases_on ‘acq /\ rel’
      >> gvs [MAX_NOT_MEM]
      )
      >> rpt CASE_TAC >> (gvs [MAX_NOT_MEM])
      ,
      (* goal: ~MEM t s1.bst_prom /\ t <= LENGTH M *)
      imp_res_tac is_certified_coh
      >> pop_assum kall_tac
      >> pop_assum kall_tac
      >> qpat_x_assum ‘is_certified _ _ _ _’ kall_tac
      >> qpat_x_assum ‘is_certified _ _ _ _’ kall_tac
      >> gvs [bir_state_t_component_equality]
      >> conj_asm2_tac
      >| [
          spose_not_then assume_tac
          >> first_x_assum (qspec_then ‘t’ assume_tac)
          >> rfs []
          >> pop_assum mp_tac
          >> fs []
          >> qexists_tac ‘l'’
          >> conj_tac
          >| [
            fs [mem_is_loc_mem_get]
            >> fs [mem_read_def]
            >> Cases_on ‘mem_get M l' t’ >> (fs [])
            ,   
            fs [AC DISJ_ASSOC DISJ_COMM]
            >> DISJ2_TAC >> DISJ2_TAC >> DISJ2_TAC >> DISJ1_TAC
            >> fs [mem_read_view_def]
            >> CASE_TAC
            >> gvs [certifiable_view_inv_def]
          ]
          ,
          qpat_x_assum ‘mem_read _ _ _ = SOME v’ mp_tac
          >> Cases_on ‘t’ >- fs []
          >> fs [mem_read_def, mem_get_def, oEL_THM]
          >> rpt CASE_TAC
          >> fs []
        ]
    ]
    , (* store xclfail *)
    qpat_x_assum ‘is_certified _ _ _ _’ kall_tac
    >> fs [certifiable_view_inv_def, bir_state_t_component_equality, xclfail_update_viewenv_def]
    >> every_case_tac >> (fs[])
    >> fs [FLOOKUP_UPDATE]
    >> gen_tac >> gen_tac
    >> CASE_TAC
    >> rw []
    , (* store fulfil *)
    imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
    >> qpat_x_assum ‘is_certified _ _ _ _’ kall_tac
    >> fs [certifiable_view_inv_def, bir_state_t_component_equality]
    >> fs [MAX_NOT_MEM, GSYM FORALL_AND_THM, AC CONJ_ASSOC CONJ_COMM]
    >> gvs [fwdb_t_component_equality, MEM_FILTER, MAX_NOT_MEM, combinTheory.APPLY_UPDATE_THM,
            bir_eval_exp_view_def, fulfil_update_viewenv_def, FLOOKUP_UPDATE]
    >> rpt (CHANGED_TAC $ fs [GSYM FORALL_AND_THM, AC CONJ_ASSOC CONJ_COMM, Once PULL_FORALL])
    >> rpt gen_tac
    >> Cases_on ‘xcl’
    >| [
        rpt CASE_TAC
        >> (
        gvs [FLOOKUP_UPDATE]
        >> FULL_CASE_TAC
        >> gvs [MAX_NOT_MEM, FLOOKUP_UPDATE, MAX_DEF]
        >> METIS_TAC []
        )
        ,
        fs [] >>
        rpt CASE_TAC
        >> (
          gvs [FLOOKUP_UPDATE]
          >> rpt strip_tac
          >> METIS_TAC [MAX_NOT_MEM]
          )
      ]                                                                                              
    , (* amo *)
    cheat
    , (* fence *)
    qpat_x_assum ‘is_certified _ _ _ _’ kall_tac
    >> fs [certifiable_view_inv_def, bir_state_t_component_equality]
    >> rpt CASE_TAC >> gvs [MAX_NOT_MEM]
    , (* cjmp *)
    qspecl_then [‘p’, ‘cond_e’, ‘lbl1’, ‘lbl2’, ‘s1’] assume_tac bir_exec_stmt_cjmp_view_noninterference
    >> imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
    >> fs [bir_state_t_component_equality]
    >> fs [certifiable_view_inv_def, MAX_NOT_MEM]
    >> strip_tac >> strip_tac >> strip_tac
    >> first_x_assum ho_match_mp_tac
    >> goal_assum $ drule_at Any
    , (* assign *)
    imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
    >> fs [certifiable_view_inv_def, bir_state_t_component_equality, FLOOKUP_UPDATE]
    >> rpt gen_tac
    >> CASE_TAC
    >> strip_tac
    >> gvs []
    , (* general *)
    ‘IS_SOME (bmc_exec_general_stmt p stm s1)’ by fs []
    >> imp_res_tac bir_exec_general_stmt_view_noninterference
    >> gvs [certifiable_view_inv_def]
    >> rpt gen_tac >> strip_tac
    >> first_x_assum ho_match_mp_tac
    >> goal_assum $ drule_at Any
  ]
QED

Triviality LE_1:
  !(a:num) b.
    a <= b <=> a < b + 1
Proof
  fs [LESS_OR_EQ]
QED

Theorem certifiable_view_inv:
  !p cid s1 M1 s2 M2.
    cstep_seq p cid (s1, M1) (s2, M2)
    /\ is_certified p cid s2 M2
    /\ certifiable_view_inv cid (s1, M1)
    ==> certifiable_view_inv cid (s2, M2)
Proof
  rpt strip_tac
  >> imp_res_tac certifiable_view_inv_IMP_bir_eval_view_of_exp
  >> fs [cstep_seq_cases]
  >| [ (* clstep *)
    ho_match_mp_tac certifiable_view_inv_clstep
    >> goal_assum $ drule_at Any
    >> goal_assum $ drule_at Any
    >> rfs []
    , (* prom + clstep *)
    fs [cstep_cases]
    >> qsuff_tac ‘certifiable_view_inv cid (s', M2)’
    >| [
        strip_tac
        >> ho_match_mp_tac certifiable_view_inv_clstep
        >> qexistsl_tac [‘p’ ,‘s'’, ‘[t]’]
        >> rfs []
        ,
        fs [certifiable_view_inv_def, bir_state_t_component_equality, MEM_APPEND]
        >> rpt conj_tac
        >| [
            rpt strip_tac
            >> qpat_x_assum ‘!t. MEM t s1.bst_prom ==> _’ imp_res_tac
            >> fs [LE_1]
            ,
            rpt gen_tac
            >> qpat_x_assum ‘!l. s1.bst_coh l <= _ /\ _ ’ (qspec_then ‘l’ assume_tac)
            >> fs [LE_1]
            ,
            rpt gen_tac
            >> strip_tac
            >> res_tac
            >> fs [LE_1]
            ,
            rpt gen_tac
            >> qpat_x_assum ‘!l. (s1.bst_fwdb l).fwdb_time <= _ /\ _ ’ (qspec_then ‘l’ assume_tac)
            >> fs [LE_1]
            ,
            rpt gen_tac
            >> qpat_x_assum ‘!l. (s1.bst_fwdb l).fwdb_view <= _ /\ _ ’ (qspec_then ‘l’ assume_tac)
            >> fs [LE_1]
            ,
            rpt gen_tac
            >> strip_tac
            >> res_tac
            >> fs [LE_1]
          ]
      ]
  ]          
QED

Definition sim_time_def:
  sim_time i j t =
  if t < i \/ j < t then t
  else if i = t then j
  else t - 1
End

val _ = export_theory();
