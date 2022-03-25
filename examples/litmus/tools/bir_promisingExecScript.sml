open HolKernel Parse boolLib bossLib;
open bir_promisingTheory;

val _ = new_theory "bir_promisingExec";

(* This datatype has extra information for the promising execution *)
val _ = Datatype‘
         exec_core_t = ExecCore num (string bir_program_t) bir_state_t bool
        ’;

val _ = Datatype‘
         exec_mem_msg_t = <| loc:bir_val_t ; val:bir_val_t ; cid:num ; succ:bool ; n:num |>
        ’;

(* Returns if all pairs (timestamp * message) satisfies P. *)
val mem_every_def = Define‘
  mem_every P M = EVERY P (ZIP (M, [1 .. LENGTH M]))
’;

(* Returns pairs (timestamp * message) satisfying P *)
val mem_filter_def = Define‘
  mem_filter P M = FILTER P (ZIP (M, [1 .. LENGTH M]))
’;

(* Returns timestamps of messages with location l. *)
val mem_timestamps_def = Define‘
  mem_timestamps l M = MAP SND (mem_filter (λ(m, t). m.loc = l) M)
’;

(* The atomic predicate from promising-semantics. *)
val mem_atomic_def = Define‘
  mem_atomic M l cid t_r t_w =
  (((EL (t_r - 1) M).loc = l ∨ t_r = 0)⇒
     mem_every (λ(m,t'). (t_r < t' ∧ t' < t_w ∧ m.loc = l) ⇒ m.cid = cid) M)
’;

(* Checks 
 * (∀t'. ((t:num) < t' ∧ t' ≤ (MAX v_pre (s.bst_coh l))) ⇒ (EL (t'-1) M).loc ≠ l)
 * letting t_max = (MAX v_pre (s.bst_coh l))
 *)
val mem_readable_def = Define‘
  mem_readable M l t_max t =
  mem_every (λ(m,t'). (t < t' ∧ t' ≤ t_max) ⇒ m.loc ≠ l) M
’;

val emem_default_def = Define‘
  emem_default l = <| loc := l ; val := BVal_Imm (Imm64 0w) ; succ := T ; n := 0 |>
’;

val emem_get_def = Define‘
  (emem_get M l 0 = SOME $ emem_default l)
  ∧
  (emem_get M l (SUC t) = oEL t M)
’;

val emem_read_def = Define‘
  emem_read M l t = OPTION_BIND (emem_get M l t) (λm. SOME m.val)
’;

val emem_filter_def = Define‘
  emem_filter P M = FILTER P (ZIP(M,[1..LENGTH M]))
’;

val emem_every_def = Define‘
  emem_every P M = EVERY P (ZIP(M,[1..LENGTH M]))
’;

val emem_readable_def = Define‘
  emem_readable M l v_max =
  FILTER (λ(m,t). emem_every (λ(m',t'). m'.succ ∧ t < t' ∧ t' ≤ v_max ⇒ m'.loc ≠ l) M)
         ((emem_default l,0)::emem_filter (λ(m,t). m.loc = l ∧ m.succ) M)
’;

val emem_atomic_def = Define‘
  emem_atomic M l cid t_r t_w =
  case emem_get M l t_r of
  | SOME msg =>
      msg.succ ⇒
      emem_every (λ(m,t'). t_r < t' ∧ t' < t_w ∧ m.loc = l ∧ m.succ ⇒ m.cid = cid) M
  | NONE => T
’;

val emem_to_mem_def = Define ‘
  emem_to_mem [] = ([]: mem_msg_t list)
  /\
  (emem_to_mem (m::ms) =
  if m.succ
  then ((<| loc := m.loc; val := m.val; cid := m.cid |>)::emem_to_mem ms)
  else emem_to_mem ms)
’;

val ifView_def = Define‘
  ifView p (v:num) = if p then v else 0
’;

val MAXL_def = Define‘
  MAXL (x::xs) = FOLDL MAX x xs
’;

val MINL_def = Define‘
  MINL (x::xs) = FOLDL MIN x xs
’;

(* Core-local execution *)
val eval_clstep_read_def = Define‘
  eval_clstep_read s M var a_e xcl acq rel =
  case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
  | (SOME l, v_addr) =>
      let
        v_pre = MAXL [ v_addr
                       ; s.bst_v_rNew
                       ; ifView (acq /\ rel) s.bst_v_Rel
                       ; ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)
                     ];
        msgs  = emem_readable M l (MAX v_pre (s.bst_coh l)) 
      in
        LIST_BIND msgs (λ(msg,t).
                          let
                            v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
                          in
                            (case env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ) of
                             | SOME new_env =>
                                 [s with <| bst_environ := new_env;
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
                                                           else s.bst_xclb |>] 
                             | _ => []))
        | _ => []
’;

val eval_clstep_xclfail_def = Define‘
  (eval_clstep_xclfail p cid s M a_e v_e T =
  let
    (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
  in
    case (l_opt, v_opt) of
    | (SOME l, SOME v) =>
        let
          msg = <| loc := l ; val := v ; cid := cid ; succ := F ; n := SUC s.bst_counter |>;
          ts = FILTER (λt. emem_get M l t = SOME msg) s.bst_prom
        in
          LIST_BIND ts 
                    (λt.
                       case (xclfail_update_env p s, xclfail_update_viewenv p s) of
                       | (SOME new_env, SOME new_viewenv) =>
                           [s with <| bst_viewenv := new_viewenv;
                                      bst_environ := new_env;
                                      bst_xclb    := NONE;
                                      bst_counter updated_by SUC;
                                      bst_prom    updated_by (FILTER (λp. p ≠ t));
                                      bst_pc updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>]
                       | _ => [])
          | _ => [])
  ∧
  eval_clstep_xclfail p cid s M a_e v_e F = []
’;

val eval_clstep_amofulfil_def = Define‘
  eval_clstep_amofulfil p cid s M var a_e v_e acq rel =
    case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
    | (NONE, v_addr) => []
    | (SOME l, v_addr) =>
    let
      v_rPre = MAXL [v_addr; s.bst_v_rNew; ifView (acq /\ rel) s.bst_v_Rel; ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
      msgs = emem_readable M l (MAX v_rPre (s.bst_coh l));
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
                                v_wPre = MAXL [v_addr; v_data; s.bst_v_CAP; v_rPost; s.bst_v_wNew;
                                               ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                                               ifView (acq /\ rel) s.bst_v_Rel
                                              ];
                                msg = <| loc := l; val := v; cid := cid; succ := T; n := SUC s.bst_counter |>;
                                t_ws = FILTER (\t_w.
                                                 (emem_get M l t_w = SOME msg) /\
                                                 (MAX v_wPre (s.bst_coh l) < t_w) /\
                                                 (mem_every (\ (msg,t'). t_r < t' /\ t' < t_w ==> msg.loc <> l) M))
                                              s.bst_prom;
                              in LIST_BIND t_ws (\v_wPost.
                                                   [ s with <| bst_viewenv := new_viewenv;
                                                               bst_environ := new_environ;
                                                               bst_fwdb   updated_by (l =+ <| fwdb_time := v_wPost;
                                                                                              fwdb_view := MAX v_addr v_data;
                                                                                              fwdb_xcl  := T |>);
                                                               bst_prom   updated_by (FILTER (\t'. t' <> v_wPost));
                                                               bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_wPost);
                                                               bst_v_Rel  updated_by (MAX (ifView (acq /\ rel) v_wPost));
                                                               bst_v_rOld updated_by (MAX v_rPost);
                                                               bst_v_rNew updated_by (MAX (ifView acq (if rel then v_wPost else v_rPost)));
                                                               bst_v_wNew updated_by (MAX (ifView acq (if rel then v_wPost else v_rPost)));
                                                               bst_v_CAP  updated_by (MAX v_addr);
                                                               bst_v_wOld updated_by (MAX v_wPost);
                                                               bst_pc     updated_by bir_pc_next o bir_pc_next;
                                                               bst_counter updated_by SUC;
                                                     |> ])
                           )
                      )
                 )
’;

val eval_clstep_fulfil_def = Define‘
  eval_clstep_fulfil p cid s M a_e v_e xcl acq rel =
    let
      (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
      (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
    in
      case (l_opt,v_opt) of
      | (SOME l, SOME v) =>
          (let
             v_pre = MAXL [ v_addr
                          ; v_data
                          ; s.bst_v_wNew
                          ; s.bst_v_CAP
                          ; ifView rel (MAX s.bst_v_rOld s.bst_v_wOld)
                          ; ifView (xcl /\ acq /\ rel) s.bst_v_Rel
                          ; ifView xcl (get_xclb_view s.bst_xclb)
                          ];
             msg = <| loc := l; val := v; cid := cid ; succ := T ; n := SUC s.bst_counter |>;
             ts = FILTER (\t. (emem_get M l t = SOME msg)
                              /\ (MAX v_pre (s.bst_coh l) < t)
                              /\ (xcl ==> ((s.bst_xclb <> NONE) /\
                                             emem_atomic M l cid (THE s.bst_xclb).xclb_time t)))
                         s.bst_prom;
           in
             LIST_BIND ts
                       (\v_post.
                          case (fulfil_update_env p s xcl, fulfil_update_viewenv p s xcl v_post) of
                          | (SOME new_env, SOME new_viewenv) => 
                              [s with <| bst_viewenv := new_viewenv;
                                         bst_environ := new_env;
                                         bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                         bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
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
                                         bst_counter updated_by SUC;
                                         bst_xclb := if xcl then NONE else s.bst_xclb |>]
                          | _ => []))
      | (_, _) => []
’;

val eval_clstep_fence_def = Define‘
  eval_clstep_fence s K1 K2 =
  let v = MAX (if is_read K1 then s.bst_v_rOld else 0)
              (if is_write K1 then s.bst_v_wOld else 0)
  in
    [s with <| bst_v_rNew updated_by MAX (if is_read K2 then v else 0);
               bst_v_wNew updated_by MAX (if is_write K2 then v else 0);
               bst_pc     updated_by bir_pc_next |>]
’;

val eval_clstep_branch_def = Define‘
  eval_clstep_branch p s cond_e lbl1 lbl2 =
  let
    stmt = BStmtE (BStmt_CJmp cond_e lbl1 lbl2);
    (sv, v_addr) = bir_eval_exp_view cond_e s.bst_environ s.bst_viewenv
  in
    case sv of
      SOME v =>
        let (oo,s2) = bir_exec_stmt p stmt s
        in [s2 with <| bst_v_CAP updated_by MAX v_addr |>]
    | _ => []
’;

val eval_clstep_exp_def = Define‘
  eval_clstep_exp s var ex =
  case bir_eval_exp_view ex s.bst_environ s.bst_viewenv
  of (SOME val, v_val) =>
       (case env_update_cast64 (bir_var_name var) val (bir_var_type var) (s.bst_environ) of
          SOME new_env =>
            [s with <| bst_environ := new_env;
                       bst_viewenv updated_by (λe. FUPDATE e (var,v_val));
                       bst_pc      updated_by bir_pc_next |>]
        | _ => [])
  | _ => []
’;

val eval_clstep_bir_step_def = Define‘
  eval_clstep_bir_step p s stm =
   let (oo,s') = bir_exec_stmt p stm s
   in [s']
’;

val eval_clstep_def = Define‘
  eval_clstep p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        eval_clstep_read s M var a_e xcl acq rel
    | BirStmt_Write a_e v_e xcl acq rel =>
        eval_clstep_fulfil p cid s M a_e v_e xcl acq rel ++
        eval_clstep_xclfail p cid s M a_e v_e xcl
    | BirStmt_Amo var a_e v_e acq rel =>
        eval_clstep_amofulfil p cid s M var a_e v_e acq rel
    | BirStmt_Expr var e =>
        eval_clstep_exp s var e
    | BirStmt_Fence K1 K2 =>
        eval_clstep_fence s K1 K2
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        eval_clstep_branch p s cond_e lbl1 lbl2
    | BirStmt_Generic stm =>
        eval_clstep_bir_step p s stm
    | BirStmt_None => []
’;


(*** Non-promising-mode execution ***)
val eval_clsteps_def = Define‘
  (
  eval_clsteps 0 cid p s M =
  case s.bst_status of
  | BST_Running => [s]
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  ) /\ (
  eval_clsteps (SUC f) cid p s M = 
  case s.bst_status of
  | BST_Running => LIST_BIND (eval_clstep p cid s M)
                             (λs'. eval_clsteps f cid p s' M)
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  )
’;

val eval_clsteps_core_def = Define‘
  eval_clsteps_core fuel (Core cid p s) M =
    MAP (Core cid p) (eval_clsteps fuel cid p s M)
’;

(* Returns true if certified step. *)
val eval_certify_def = Define‘
  (
  eval_certify prog cid st M 0 =
  NULL st.bst_prom
  ) ∧ (
  eval_certify prog cid st M (SUC f) =
  (NULL st.bst_prom ∨
   EXISTS (λst'. eval_certify prog cid st' M f) (eval_clstep prog cid st M))
  )
’;

val eval_certify_core_def = Define‘
  eval_certify_core M f (Core cid prog st) =
  eval_certify prog cid st M f
’;

(********* Promising-mode steps ***********)

val has_write_def = Define‘
  has_write M cid n = EXISTS (\m. m.cid = cid ∧ m.n = n) M
’;

(* Find promise write step (promise-step + fulfil) *)
val eval_fpstep_write_def = Define‘
  eval_fpstep_write p cid s M a_e v_e xcl acq rel =
  if ~has_write M cid (SUC s.bst_counter) then
    let
      (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
      (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    in
      case (val_opt, loc_opt) of
      | (SOME v, SOME l) =>
          (let
             msg = <| val := v; loc := l; cid := cid ; succ := T ; n := SUC s.bst_counter |>;
             M' = SNOC msg M;
             s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
             v_prom = MAXL [ v_addr ; v_data ; s.bst_v_wNew ; s.bst_v_CAP
                             ; if rel then (MAX s.bst_v_rOld s.bst_v_wOld) else 0
                             ; if (xcl /\ acq /\ rel) then s.bst_v_Rel else 0
                             ; if xcl then get_xclb_view s.bst_xclb else 0
                             ; s.bst_coh l
                           ];
           in
             MAP (\s''. (SOME (msg,v_prom), s''))
                 (eval_clstep_fulfil p cid s' M' a_e v_e xcl acq rel)
          )
      | _ => []
  else
    []
’;

val eval_fpstep_amowrite_def = Define‘
  eval_fpstep_amowrite p cid s M var a_e v_e acq rel =
    if ~has_write M cid (SUC s.bst_counter) then
    case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
    | (NONE, v_addr) => []
    | (SOME l, v_addr) =>
    let
      v_rPre = MAXL [v_addr; s.bst_v_rNew; ifView (acq /\ rel) s.bst_v_Rel];
      msgs = emem_readable M l (MAX v_rPre (s.bst_coh l));
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
                                msg = <| loc := l; val := v; cid := cid; succ := T; n := SUC s.bst_counter |>;
                                M' = SNOC msg M;
                                s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
                                v_prom = MAXL [v_addr; v_data; s.bst_v_CAP; v_rPost; s.bst_v_wNew; ifView rel (MAX s.bst_v_rOld s.bst_v_wOld); s.bst_coh l];
                              in
                                MAP (\s''. (SOME (msg, v_prom), s''))
                                    (eval_clstep_amofulfil p cid s' M' var a_e v_e acq rel)
                           )
                      )
                 )
    else []
’;

val eval_fpstep_write_xclfail_def = Define‘
  (eval_fpstep_write_xclfail p cid s M a_e v_e T =
   if ~has_write M cid (SUC s.bst_counter) then
  let
    (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
  in
    case (l_opt, v_opt) of
    | (SOME l, SOME v) =>
        let
          msg = <| loc := l ; val := v ; cid := cid ; succ := F ; n := SUC s.bst_counter|>;
          M' = SNOC msg M;
          s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
        in
          MAP (\s''. (SOME (msg,0:num), s''))
              (eval_clstep_xclfail p cid s' M' a_e v_e T)
          | _ => []
   else
     [])
  ∧
  eval_fpstep_write_xclfail p cid s M a_e v_e F = []
’;

(* Find-promise step *)
val eval_fpstep_def = Define‘
  eval_fpstep p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        MAP (\s. (NONE,s)) (eval_clstep_read s M var a_e xcl acq rel)
    | BirStmt_Write a_e v_e xcl acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_fulfil p cid s M a_e v_e xcl acq rel)) ++
        (MAP (\s. (NONE,s)) (eval_clstep_xclfail p cid s M a_e v_e xcl)) ++
        (eval_fpstep_write p cid s M a_e v_e xcl acq rel) ++
        (eval_fpstep_write_xclfail p cid s M a_e v_e xcl)
    | BirStmt_Amo var a_e v_e acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_amofulfil p cid s M var a_e v_e acq rel)) ++
        (eval_fpstep_amowrite p cid s M var a_e v_e acq rel)
    | BirStmt_Expr var e =>
        MAP (\s. (NONE,s)) (eval_clstep_exp s var e)
    | BirStmt_Fence K1 K2 =>
        MAP (\s. (NONE,s)) (eval_clstep_fence s K1 K2)
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        MAP (\s. (NONE,s)) (eval_clstep_branch p s cond_e lbl1 lbl2)
    | BirStmt_Generic stm =>
        MAP (\s. (NONE,s)) (eval_clstep_bir_step p s stm)
    | BirStmt_None => []
’;

(* Find-promise steps *)
val eval_fpsteps_def = Define‘
  (
  eval_fpsteps 0 prog cid st M = []
  ) ∧ (
  eval_fpsteps (SUC fuel) prog cid st M = 
  case st.bst_status of
  | BST_Running =>
      LIST_BIND (eval_fpstep prog cid st M)
                (λ(msg_opt,st').
                   case msg_opt of
                   | SOME (msg, v_prom) =>
                       if eval_certify prog cid st' (SNOC msg M) fuel
                       then ((msg, v_prom)::eval_fpsteps fuel prog cid st' (SNOC msg M))
                       else []
                   | NONE => eval_fpsteps fuel prog cid st' M)
  | _ => []
  )
’;

(* Find-promise steps on a core *)
val eval_fpsteps_core_def = Define‘
  eval_fpsteps_core fuel (Core cid p s) M =
    eval_fpsteps fuel p cid s M
’;

(* Find promise all promises *)
val eval_find_promises_def = Define‘
  eval_find_promises fuel (cores, M) =
  LIST_BIND cores (λcore. eval_fpsteps_core fuel core M)
’;

(* Make a promise step *)
val eval_make_promise_def = Define‘
  eval_make_promise ((Core cid p s)::cores,M) msg =
  if msg.cid = cid then
    let
      M' = SNOC msg M;
      t = LENGTH M';
      s' = s with <| bst_prom updated_by (CONS t) |>;
    in ((Core cid p s')::cores, M')
  else
    let
      (cores', M') = eval_make_promise (cores, M) msg;
    in ((Core cid p s)::cores', M')
’;

(* Promise-mode step *)
val eval_pmstep_def = Define‘
  eval_pmstep fuel cM =
  let
    promises = nub $ eval_find_promises fuel cM;
    t = SUC $ LENGTH $ SND cM;
    promises' = MAP FST $ FILTER (λx. SND x < t) promises
  in
  MAP (eval_make_promise cM) promises'
’;

val eval_pmsteps_def = Define‘
  eval_pmsteps fuel 0 cM = [cM]
  ∧
  eval_pmsteps fuel (SUC pfuel) cM =
  let cMs = eval_pmstep fuel cM in
  if NULL cMs
  then [cM]
  else LIST_BIND cMs (eval_pmsteps fuel pfuel)
’;

(*********** Optimized version of the executable semantics ***************)
(* Optimized fulfil *)
val eval_clstep_fulfilO1_def = Define‘
  eval_clstep_fulfilO1 p cid s M a_e v_e xcl acq rel =
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <| val := v; loc := l; cid := cid; succ := T ; n := SUC s.bst_counter |>;
           v_pre = MAXL [ v_addr ; v_data ; s.bst_v_wNew ; s.bst_v_CAP
                        ; if rel then (MAX s.bst_v_rOld s.bst_v_wOld) else 0
                        ; if (xcl /\ acq /\ rel) then s.bst_v_Rel else 0
                        ; if xcl then get_xclb_view s.bst_xclb else 0
                        ];
           (* Candidate t's *)
           ts = FILTER (\t. (emem_get M l t = SOME msg) /\
                            (MAX v_pre (s.bst_coh l) < t) /\
                            (xcl ==> ((s.bst_xclb <> NONE) /\
                                      emem_atomic M l cid (THE s.bst_xclb).xclb_time t)))
                       s.bst_prom
         in
           LIST_BIND ts
                     (λv_post.
                        case (fulfil_update_env p s xcl, fulfil_update_viewenv p s xcl v_post) of
                        | (SOME new_env, SOME new_viewenv) => 
                            [s with <| bst_viewenv := new_viewenv;
                                       bst_environ := new_env;
                                       bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                       bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
                                       bst_v_wOld updated_by MAX v_post;
                                       bst_v_CAP  updated_by MAX v_addr;
                                       bst_v_Rel  updated_by (if (rel /\ acq) then (MAX v_post) else (\v. v));
                                       bst_v_rNew updated_by if (rel /\ acq /\ xcl) then (MAX v_post) else (\v. v);
                                       bst_v_wNew updated_by if (rel /\ acq /\ xcl) then (MAX v_post) else (\v. v);
                                       bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
                                                                      fwdb_view := MAX v_addr v_data;
                                                                      fwdb_xcl := xcl |>);
                                       bst_pc     updated_by if xcl
                                                             then (bir_pc_next o bir_pc_next o bir_pc_next)
                                                             else bir_pc_next;
                                       bst_counter updated_by SUC;
                                       bst_xclb := if xcl then NONE else s.bst_xclb |>]
                        | _ => []
                     ) 
        )
    | _ => []
’;

(* Optimized xclfail *)
val eval_clstep_xclfailO1_def = Define‘
  (eval_clstep_xclfailO1 p cid s M a_e v_e T =
  let
    (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
  in
    case (l_opt, v_opt) of
    | (SOME l, SOME v) =>
        let
          msg = <| loc := l ; val := v ; cid := cid ; succ := F ; n := SUC s.bst_counter |>;
          ts = FILTER (λt. emem_get M l t = SOME msg) s.bst_prom;
        in
          LIST_BIND ts
                    (λt.
                       case (xclfail_update_env p s, xclfail_update_viewenv p s) of
                       | (SOME new_env, SOME new_viewenv) =>
                           [s with <| bst_viewenv := new_viewenv;
                                      bst_environ := new_env;
                                      bst_xclb    := NONE;
                                      bst_prom    updated_by (FILTER (λp. p ≠ t));
                                      bst_counter updated_by SUC;
                                      bst_pc      updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>]
                       | _ => [])
          | _ => [])
  ∧
  eval_clstep_xclfailO1 p cid s M a_e v_e F = []
’;

(* Optimized clstep *)
val eval_clstepO1_def = Define‘
  eval_clstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        eval_clstep_read s M var a_e xcl acq rel 
    | BirStmt_Write a_e v_e xcl acq rel =>
        eval_clstep_fulfilO1 p cid s M a_e v_e xcl acq rel ++
        eval_clstep_xclfailO1 p cid s M a_e v_e xcl
    | BirStmt_Amo var a_e v_e acq rel =>
        eval_clstep_amofulfil p cid s M var a_e v_e acq rel
    | BirStmt_Expr var e =>
        eval_clstep_exp s var e
    | BirStmt_Fence K1 K2 =>
        eval_clstep_fence s K1 K2
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        eval_clstep_branch p s cond_e lbl1 lbl2
    | BirStmt_Generic stm =>
        eval_clstep_bir_step p s stm
    | BirStmt_None => []
’;

(* Optimized clsteps *)
val eval_clstepsO1_def = Define‘
  (
  eval_clstepsO1 0 cid p s M =
  case s.bst_status of
  | BST_Running => [s]
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  ) /\ (
  eval_clstepsO1 (SUC f) cid p s M = 
  case s.bst_status of
  | BST_Running => LIST_BIND (eval_clstepO1 p cid s M)
                             (λs'. eval_clstepsO1 f cid p s' M)
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  )
’;

val eval_clsteps_coreO1_def = Define‘
  eval_clsteps_coreO1 fuel (ExecCore cid prog st prom_mode) M =
    MAP (\st'. ExecCore cid prog st' prom_mode) (eval_clstepsO1 fuel cid prog st M)
’;

val eval_certifyO1_def = Define‘
  (
  eval_certifyO1 prog cid st M 0 =
  NULL st.bst_prom
  ) ∧ (
  eval_certifyO1 prog cid st M (SUC f) =
  (NULL st.bst_prom ∨
   EXISTS (λst'. eval_certifyO1 prog cid st' M f) (eval_clstepO1 prog cid st M))
  )
’;

val eval_certify_coreO1_def = Define‘
  eval_certify_coreO1 M f (ExecCore cid prog st prom_mode) =
  eval_certifyO1 prog cid st M f
’;

(* Find promise write step (promise-step + fulfil) *)
val eval_fpstep_writeO1_def = Define‘
  eval_fpstep_writeO1 p cid s M a_e v_e xcl acq rel =
  if ~has_write M cid (SUC s.bst_counter) then
  let
    (val_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv;
    (loc_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
  in
    case (val_opt, loc_opt) of
    | (SOME v, SOME l) =>
        (let
           msg = <| val := v; loc := l; cid := cid; succ := T; n := SUC s.bst_counter |>;
           M' = SNOC msg M;
           s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
           v_prom = MAXL [ v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP
                         ; if rel then (MAX s.bst_v_rOld s.bst_v_wOld) else 0
                         ; if (xcl /\ acq /\ rel) then s.bst_v_Rel else 0
                         ; if xcl then get_xclb_view s.bst_xclb else 0
                         ; s.bst_coh l
                         ];
         in
           MAP (\s''. (SOME (msg, v_prom), s''))
               (eval_clstep_fulfilO1 p cid s' M' a_e v_e xcl acq rel)
        )
    | _ => []
  else []
’;

val eval_fpstep_write_xclfailO1_def = Define‘
  (eval_fpstep_write_xclfailO1 p cid s M a_e v_e T =
   if ~has_write M cid (SUC s.bst_counter) then
  let
    (l_opt, v_addr) = bir_eval_exp_view a_e s.bst_environ s.bst_viewenv;
    (v_opt, v_data) = bir_eval_exp_view v_e s.bst_environ s.bst_viewenv
  in
    case (l_opt, v_opt) of
    | (SOME l, SOME v) =>
        let
          msg = <| loc := l ; val := v ; cid := cid ; succ := F ; n := SUC s.bst_counter |>;
          M' = SNOC msg M;
          s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
        in
          MAP (\s''. (SOME (msg, 0:num), s''))
              (eval_clstep_xclfailO1 p cid s' M' a_e v_e T)
    | _ => []
   else [])
  ∧
  eval_fpstep_write_xclfailO1 p cid s M a_e v_e F = []
’;

(* Find promise step *)
val eval_fpstepO1_def = Define‘
  eval_fpstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        MAP (\s. (NONE,s)) (eval_clstep_read s M var a_e xcl acq rel)
    | BirStmt_Write a_e v_e xcl acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_fulfilO1 p cid s M a_e v_e xcl acq rel)) ++
        (MAP (\s. (NONE,s)) (eval_clstep_xclfailO1 p cid s M a_e v_e xcl)) ++
        (eval_fpstep_writeO1 p cid s M a_e v_e xcl acq rel) ++
        (eval_fpstep_write_xclfailO1 p cid s M a_e v_e xcl)
    | BirStmt_Amo var a_e v_e acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_amofulfil p cid s M var a_e v_e acq rel)) ++
        (eval_fpstep_amowrite p cid s M var a_e v_e acq rel)
    | BirStmt_Expr var e =>
        MAP (\s. (NONE,s)) (eval_clstep_exp s var e)
    | BirStmt_Fence K1 K2 =>
        MAP (\s. (NONE,s)) (eval_clstep_fence s K1 K2)
    | BirStmt_Branch cond_e lbl1 lbl2 =>
        MAP (\s. (NONE,s)) (eval_clstep_branch p s cond_e lbl1 lbl2)
    | BirStmt_Generic stm =>
        MAP (\s. (NONE,s)) (eval_clstep_bir_step p s stm)
    | BirStmt_None => []
’;

(* Find promise steps *)
val eval_fpstepsO1_def = Define‘
  (
  eval_fpstepsO1 0 (t:num) prog cid st M prom =
  if NULL st.bst_prom then prom else []
  ) ∧ (
  eval_fpstepsO1 (SUC fuel) t prog cid st M prom = 
  case st.bst_status of
  | BST_Running =>
      LIST_BIND (eval_fpstepO1 prog cid st M)
                (λ(msg_opt,st').
                   case msg_opt of
                   | SOME (msg, v_prom) =>
                       let
                         prom' = if v_prom < t then (msg::prom) else prom;
                         M' = SNOC msg M
                       in eval_fpstepsO1 fuel t prog cid st' M' prom'
                   | NONE => eval_fpstepsO1 fuel t prog cid st' M prom)
  | BST_Halted _ =>
      if NULL st.bst_prom then prom else []
  | BST_JumpOutside _ =>
      if NULL st.bst_prom then prom else []
  | _ => []
  )
’;

(* Find promise steps on a core *)
val eval_fpsteps_coreO1_def = Define‘
  eval_fpsteps_coreO1 fuel (ExecCore cid prog st prom_mode) M =
  if prom_mode then
    eval_fpstepsO1 fuel (SUC (LENGTH M)) prog cid st M []
  else []
’;

(* Find all next promises-steps *)
val eval_find_promisesO1_def = Define‘
  eval_find_promisesO1 fuel (cores, M) =
  LIST_BIND cores (λcore. eval_fpsteps_coreO1 fuel core M)
’;

val eval_make_promise_auxO1_def = Define‘
  eval_make_promise_auxO1 msg t (ExecCore cid prog st prom_mode) =
  if msg.cid = cid
  then (ExecCore cid prog (st with <| bst_prom updated_by (CONS t) |>) prom_mode)
  else (ExecCore cid prog st prom_mode) 
’;

val eval_make_promiseO1_def = Define‘
  eval_make_promiseO1 (cores,M) msg =
  let M' = SNOC msg M;
      t = LENGTH M';
      cores' = MAP (eval_make_promise_auxO1 msg t) cores
    in (cores', M')
’;


(* Promise-mode step *)
val eval_pmstepO1_def = Define‘
  eval_pmstepO1 fuel (cores, M) =
  let promises = nub $ eval_find_promisesO1 fuel (cores, M);
  in MAP (eval_make_promiseO1 (cores,M)) promises
’;

val eval_pmstepsO1_def = Define‘
  eval_pmstepsO1 fuel 0 cM = [cM]
  ∧
  eval_pmstepsO1 fuel (SUC pfuel) cM =
  let cMs = eval_pmstepO1 fuel cM in
  if NULL cMs
  then [cM]
  else LIST_BIND cMs (eval_pmstepsO1 fuel pfuel)
’;

val eval_finished_def = Define‘
  eval_finished s =
  case s.bst_status of
  | BST_Halted v => NULL s.bst_prom
  | BST_JumpOutside l => NULL s.bst_prom
  | _ => F
’;

val eval_finished_core_def = Define‘
  eval_finished_core (Core cid prog s) = eval_finished s
’;

val eval_finished_ecore_def = Define‘
  eval_finished_ecore (ExecCore cid prog s prom_mode) = eval_finished s
’;

val _ = export_theory();

(********************** Example ***********************)
(*
val bir_get_stmt_def = Define‘
  bir_get_stmt p pc = 
  case bir_get_current_statement p pc of
  | SOME (BStmtB (BStmt_Assign var e)) =>
      if is_amo p pc then
      (case get_read_args e of
       | SOME (a_e, cast_opt) =>
           (case bir_get_current_statement p (bir_pc_next pc) of
           | SOME (BStmtB (BStmt_Assign var' e')) =>
               (case get_fulfil_args e' of
               | SOME (a_e', v_e) =>
                   if a_e = a_e'
                   then BirStmt_Amo var a_e v_e (is_acq p pc) (is_rel p pc)
                   else BirStmt_None
               | NONE => BirStmt_None)
           | _ => BirStmt_None)
       | NONE =>
           (case get_fulfil_args e of
            | SOME (a_e, v_e) => BirStmt_None
            | NONE => BirStmt_Expr var e))
      else
       (case get_read_args e of
       | SOME (a_e, cast_opt) => BirStmt_Read var a_e cast_opt (is_xcl_read p pc) (is_acq p pc) (is_rel p pc)
       | NONE =>
           (case get_fulfil_args e of
           | SOME (a_e, v_e) => BirStmt_Write a_e v_e (is_xcl_write p pc) (is_acq p pc) (is_rel p pc)
           | NONE => BirStmt_Expr var e))
  | SOME (BStmtB (BStmt_Fence K1 K2)) => BirStmt_Fence K1 K2
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) => BirStmt_Branch cond_e lbl1 lbl2
  | SOME stmt => BirStmt_Generic stmt
  | NONE => BirStmt_None
’;

term_EVAL “bir_get_stmt ^core2_prog <|bpc_label := BL_Label "start"; bpc_index := 0|>”
val core1_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_mc_tags := NONE;
    bb_statements :=
    [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
     (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
      (BExp_Const (Imm64 1w)));
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Const (Imm64 2w))) ]
    ;
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val core2_prog =
“BirProgram
 [<|bb_label := BL_Label "start";
    bb_mc_tags := SOME <| mc_atomic := T; mc_acq := F; mc_rel := F |>;
    bb_statements :=
    [BStmt_Assign (BVar "x1" (BType_Imm Bit64))
                  (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
                   Bit8);
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                  (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "x2" (BType_Imm Bit64))) BEnd_LittleEndian
                   (BExp_Den (BVar "x1" (BType_Imm Bit64))));
                   ];
    bb_last_statement :=
    BStmt_Halt (BExp_Den (BVar "x2" (BType_Imm Bit64)))|>]: string bir_program_t”

val set_env1_def = Define‘
      set_env1 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env; bst_prom := []|>
’;
val set_env2_def = Define‘
      set_env2 s =
      let env = BEnv ((K NONE) (|
                      "x0" |-> SOME $ BVal_Imm $ Imm64 0w;
                      "x1" |-> SOME $ BVal_Imm $ Imm64 4w;
                      "x2" |-> SOME $ BVal_Imm $ Imm64 8w
                      |))
         in s with <| bst_environ := env |>
’;


val core1_st = term_EVAL “set_env1 (bir_state_init ^core1_prog)”;
val core2_st = term_EVAL “set_env2 (bir_state_init ^core2_prog)”;

(* core definitions *)
val cores = “[ Core 0 ^core1_prog ^core1_st
             ; Core 1 ^core2_prog ^core2_st ]”;
val exec_cores = “[ ExecCore 0 ^core1_prog ^core1_st T
                  ; ExecCore 1 ^core2_prog ^core2_st T ]”;

val term_EVAL = rand o concl o EVAL;

val pmstep = term_EVAL “eval_pmsteps 8 16 (^cores, [])”;
val pmstepO1 = term_EVAL “eval_pmstepsO1 8 16 (^exec_cores, [])”;
*)
