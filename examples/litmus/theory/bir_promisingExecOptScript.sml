
(*
(************************************************************
 * OPTIMIZED EXECUTABLE SEMANTICS 
 ************************************************************)

(* This datatype has extra information for the promising execution *)
val _ = Datatype‘
         exec_core_t = ExecCore num (string bir_program_t) bir_state_t bool
        ’;

(* This datatype has extra information for the promising execution *)
val _ = Datatype‘
         exec_mem_msg_t = <| loc:bir_val_t ; val:bir_val_t ; cid:num ; succ:bool ; n:num |>
        ’;

val emem_default_def = Define‘
  emem_default l = <| loc := l ; val := BVal_Imm (Imm64 0w) ; succ := T ; n := 0 |>
’;

val emem_get_def = Define‘
  (emem_get M l 0 = SOME $ emem_default l)
  /\
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
  FILTER (λ(m,t). emem_every (λ(m',t'). m'.succ /\ t < t' /\ t' <= v_max ==> m'.loc <> l) M)
         ((emem_default l,0)::emem_filter (λ(m,t). m.loc = l /\ m.succ) M)
’;

val emem_atomic_def = Define‘
  emem_atomic M l cid t_r t_w =
  case emem_get M l t_r of
  | SOME msg =>
      msg.succ ==>
      emem_every (λ(m,t'). t_r < t' /\ t' < t_w /\ m.loc = l /\ m.succ ==> m.cid = cid) M
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

val eval_clstep_readO1_def = Define‘
  eval_clstep_readO1 s M var a_e xcl acq rel =
  case bir_eval_exp_view a_e s.bst_environ s.bst_viewenv of
  | (SOME l, v_addr) =>
      let
        v_pre = MAXL [ v_addr;
                       s.bst_v_rNew;
                       ifView (acq /\ rel) s.bst_v_Rel;
                       ifView (acq /\ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
        msgs  = emem_readable M l (MAX v_pre (s.bst_coh l)) 
      in
        MAP_PARTIAL (λ(msg,t).
                          let
                            v_post = MAX v_pre (mem_read_view (s.bst_fwdb(l)) t)
                          in
                            (case env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ) of
                             | SOME new_env =>
                                 SOME (s with <| bst_environ := new_env;
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
                                                           else s.bst_xclb |>)
                             | NONE => NONE)) msgs
        | _ => []
’;

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
           msg = <| val := v; loc := l; cid := cid; n := SUC s.bst_counter |>;
           v_pre = MAXL [ v_addr ; v_data ; s.bst_v_wNew ; s.bst_v_CAP;
                          ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                          ifView (xcl /\ acq /\ rel) s.bst_v_Rel;
                          ifView xcl (get_xclb_view s.bst_xclb)];
           (* Candidate t's *)
           ts = FILTER (\t. (emem_get M l t = SOME msg) /\
                            (MAX v_pre (s.bst_coh l) < t) /\
                            (xcl ==> (IS_SOME s.bst_xclb) /\
                                     emem_atomic M l cid (THE s.bst_xclb).xclb_time t))
                       s.bst_prom
         in
           MAP_PARTIAL (λv_post.
                          case (fulfil_update_env p s xcl, fulfil_update_viewenv p s xcl v_post) of
                          | (SOME new_env, SOME new_viewenv) => 
                              SOME (s with <| bst_viewenv := new_viewenv;
                                              bst_environ := new_env;
                                              bst_prom   updated_by (FILTER (\t'. t' <> v_post));
                                              bst_coh    updated_by (l =+ MAX (s.bst_coh l) v_post);
                                              bst_v_wOld updated_by MAX v_post;
                                              bst_v_CAP  updated_by MAX v_addr;
                                              bst_v_Rel  updated_by MAX (ifView (rel /\ acq) v_post);
                                              bst_v_rNew updated_by MAX (ifView (rel /\ acq /\ xcl) v_post);
                                              bst_v_wNew updated_by MAX (ifView (rel /\ acq /\ xcl) v_post);
                                              bst_fwdb   updated_by (l =+ <| fwdb_time := v_post;
                                                                             fwdb_view := MAX v_addr v_data;
                                                                             fwdb_xcl := xcl |>);
                                              bst_pc     updated_by if xcl
                                                                    then (bir_pc_next o bir_pc_next o bir_pc_next)
                                                                    else bir_pc_next;
                                              bst_counter updated_by SUC;
                                              bst_xclb := if xcl then NONE else s.bst_xclb |>)
                          | _ => NONE
                       ) ts
        )
    | _ => []
’;

(* Optimized xclfail *)
val eval_clstep_xclfailO1_def = Define‘
  (eval_clstep_xclfailO1 p cid s M a_e v_e T =
   case (xclfail_update_env p s, xclfail_update_viewenv p s) of
   | (SOME new_env, SOME new_viewenv) =>
       [s with <| bst_viewenv := new_viewenv;
                  bst_environ := new_env;
                  bst_xclb    := NONE;
                  bst_counter updated_by SUC;
                  bst_pc      updated_by (bir_pc_next o bir_pc_next o bir_pc_next) |>]
   | _ => [])
  /\
  eval_clstep_xclfailO1 p cid s M a_e v_e F = []
’;

val eval_clstep_amofulfilO1_def = Define‘
  eval_clstep_amofulfilO1 cid s M var a_e v_e acq rel =
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
                                                  ifView (acq /\ rel) s.bst_v_Rel];
                                   msg = <| loc := l; val := v; cid := cid ; succ := T; n := SUC s.bst_counter |>;
                                   t_ws = FILTER (\t_w.
                                                    (emem_get M l t_w = SOME msg) /\
                                                    (MAX v_wPre (s.bst_coh l) < t_w) /\
                                                    (emem_every (\ (msg,t'). msg.succ /\ t_r < t' /\ t' < t_w ==> msg.loc <> l) M))
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
                                                               |> ])
                            )
                       )
                  )
’;

(* Optimized clstep *)
val eval_clstepO1_def = Define‘
  eval_clstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        eval_clstep_readO1 s M var a_e xcl acq rel
    | BirStmt_Write a_e v_e xcl acq rel =>
        eval_clstep_fulfilO1 p cid s M a_e v_e xcl acq rel ++
        eval_clstep_xclfailO1 p cid s M a_e v_e xcl
    | BirStmt_Amo var a_e v_e acq rel =>
        eval_clstep_amofulfilO1 cid s M var a_e v_e acq rel
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
                             (\s'. eval_clstepsO1 f cid p s' M)
  | BST_Halted _ => [s]
  | BST_JumpOutside _ => [s]
  | _ => []
  )
’;

val eval_clsteps_coreO1_def = Define‘
  eval_clsteps_coreO1 fuel (Core cid prog st) M =
    MAP (\st'. Core cid prog st') (eval_clstepsO1 fuel cid prog st M)
’;

val eval_certifyO1_def = Define‘
  (
  eval_certifyO1 prog cid st M 0 =
  NULL st.bst_prom
  ) /\ (
  eval_certifyO1 prog cid st M (SUC f) =
  (NULL st.bst_prom \/
   EXISTS (λst'. eval_certifyO1 prog cid st' M f) (eval_clstepO1 prog cid st M))
  )
’;

val eval_certify_coreO1_def = Define‘
  eval_certify_coreO1 M f (Core cid prog st) =
  eval_certifyO1 prog cid st M f
’;

(**** Promising mode execution, optimized ****)

val has_write = Define‘
  has_write M cid n = EXISTS (\m. m.cid = cid /\ m.n = n) M
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

val eval_fpstep_amowriteO1_def = Define‘
  eval_fpstep_amowriteO1 cid s M var a_e v_e acq rel =
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
                         case env_update_cast64 (bir_var_name var) msg.val (bir_var_type var) (s.bst_environ) of
                         | NONE => []
                         | SOME new_environ =>
                             (case bir_eval_exp_view v_e new_environ new_viewenv of
                              | (NONE, v_data) => []
                              | (SOME v, v_data) =>
                                  let
                                    msg = <| loc := l; val := v; cid := cid ; succ := T ; n := (SUC s.bst_counter) |>;
                                    M' = SNOC msg M;
                                    s' = s with <| bst_prom updated_by (CONS (LENGTH M')) |>;
                                    v_post = MAXL [v_addr; v_data; s.bst_v_CAP; v_rPost; s.bst_v_wNew;
                                                   ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                                                   ifView (acq /\ rel) s.bst_v_Rel;
                                                   s.bst_coh l
                                                  ];
                                  in
                                    map (\s''. (SOME (msg, v_post), s''))
                                        (eval_clstep_amofulfilO1 cid s' M' var a_e v_e acq rel)
                             )
                    )
  else []
’;

(* Find promise step *)
val eval_fpstepO1_def = Define‘
  eval_fpstepO1 p cid s M =
    case bir_get_stmt p s.bst_pc of
    | BirStmt_Read var a_e cast_opt xcl acq rel =>
        MAP (\s. (NONE,s)) (eval_clstep_readO1 s M var a_e xcl acq rel)
    | BirStmt_Write a_e v_e xcl acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_fulfilO1 p cid s M a_e v_e xcl acq rel)) ++
        (MAP (\s. (NONE,s)) (eval_clstep_xclfailO1 p cid s M a_e v_e xcl)) ++
        (eval_fpstep_writeO1 p cid s M a_e v_e xcl acq rel)
    | BirStmt_Amo var a_e v_e acq rel =>
        (MAP (\s. (NONE,s)) (eval_clstep_amofulfilO1 cid s M var a_e v_e acq rel)) ++
        (eval_fpstep_amowriteO1 cid s M var a_e v_e acq rel)
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
  ) /\ (
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
  eval_fpsteps_coreO1 fuel (Core cid prog st) M =
    eval_fpstepsO1 fuel (SUC (LENGTH M)) prog cid st M []
’;

(* Find all next promises-steps *)
val eval_find_promisesO1_def = Define‘
  eval_find_promisesO1 fuel (cores, M) =
  LIST_BIND cores (λcore. eval_fpsteps_coreO1 fuel core M)
’;

val eval_make_promise_auxO1_def = Define‘
  eval_make_promise_auxO1 msg t (Core cid prog st) =
  if msg.cid = cid
  then (Core cid prog (st with <| bst_prom updated_by (CONS t) |>))
  else (Core cid prog st) 
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
  /\
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
*)
