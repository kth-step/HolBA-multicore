open HolKernel boolLib Parse;

open listRangeTheory;

open bir_programTheory bir_promisingTheory;

val _ = new_theory "bir_promisingEval";
                 
Definition bir_eval_view_exp_def:
  (bir_eval_view_exp (BExp_BinExp op e1 e2) viewenv =
   MAX (bir_eval_view_exp e1 viewenv) (bir_eval_view_exp e2 viewenv))
∧ (bir_eval_view_exp (BExp_BinPred pred e1 e2) viewenv =
   MAX (bir_eval_view_exp e1 viewenv) (bir_eval_view_exp e2 viewenv))
∧ (bir_eval_view_exp (BExp_UnaryExp op e) viewenv = bir_eval_view_exp e viewenv)
∧ (bir_eval_view_exp (BExp_Cast cty e ity) viewenv = bir_eval_view_exp e viewenv)
∧ (bir_eval_view_exp (BExp_Den v) viewenv = 
    case FLOOKUP viewenv v of
    | NONE => 0
    | SOME t => t)
∧ (bir_eval_view_exp exp viewenv = 0)
End

Definition update_environ_def:
  update_environ env var (BVal_Imm v) = 
     bir_env_update (bir_var_name var) (BVal_Imm (n2bs (b2n v) Bit64)) (bir_var_type var) env
End 

Definition ifView_def:
  ifView p (v:num) = if p then v else 0
End

Definition MAXL_def:
  MAXL [] = 0
  ∧
  MAXL (x::xs) = MAX x (MAXL xs)
End

Definition last_t_def:
  last_t l M t =
    let 
      t' = LAST (FILTER (\t'. mem_is_loc M t' l) [0 ..< t])
    in (t', THE (mem_read M l t'))
End

Definition eval_clstep_read:
  eval_clstep_read s M t var a_e cast_opt xcl acq rel =
  let
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    v_opt = mem_read M l t;
    v_pre = MAXL [v_addr; s.bst_v_rNew; ifView (acq ∧ rel) s.bst_v_Rel;
                  ifView (acq ∧ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
    is_latest = EVERY (λt'. ~mem_is_loc M t' l) [SUC t.. (MAX v_pre (s.bst_coh l))];
    v = THE v_opt;
    v_post = MAX v_pre (mem_read_view (s.bst_fwdb l) t);
    new_environ_opt = update_environ s.bst_environ var v;
    new_environ = THE new_environ_opt;
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := (s.bst_viewenv |+ (var,v_post));
                   bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_post);
                   bst_v_rOld  updated_by MAX v_post;
                   bst_v_rNew  updated_by MAX $ ifView acq v_post;
                   bst_v_wNew  updated_by MAX $ ifView acq v_post;
                   bst_v_Rel   updated_by MAX $ ifView (rel ∧ acq) v_post;
                   bst_v_CAP   updated_by MAX v_addr;
                   bst_xclb    := if xcl then SOME <| xclb_time := t; xclb_view := v_post |> else s.bst_xclb;
                   bst_pc      updated_by bir_pc_next |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME v_opt ∧ IS_SOME new_environ_opt ∧ is_latest
    then [s']
    else []
End

Definition eval_clstep_xclfail:
  eval_clstep_xclfail s var xcl =
  let
        is_running = (s.bst_status = BST_Running);
        new_environ_opt = update_environ s.bst_environ var (BVal_Imm $ Imm64 1w);
        new_environ = THE new_environ_opt;
        s' = s with <| bst_environ := new_environ;
                       bst_viewenv := s.bst_viewenv |+ (var, 0);
                       bst_xclb    := NONE;
                       bst_pc      updated_by bir_pc_next |>
  in
    if is_running ∧ xcl ∧ IS_SOME new_environ_opt
    then [s']
    else []
End

Definition eval_clstep_fulfil_def:
  eval_clstep_fulfil cid s M t var a_e v_e xcl acq rel =
  let
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    v_opt = bir_eval_exp v_e s.bst_environ;
    v = THE v_opt;
    v_data = bir_eval_view_exp v_e s.bst_viewenv;
    xcl_check = (xcl ⇒ IS_SOME s.bst_xclb ∧ EVERY (λt'. mem_is_loc M t' l ⇒ mem_is_cid M cid t') [SUC ((THE s.bst_xclb).xclb_time)..< t]);
    mem_check = (mem_get M l t = SOME <| loc := l; val := v; cid := cid |>);
    v_pre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
                  ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                  ifView (xcl ∧ acq ∧ rel) s.bst_v_Rel;
                  ifView xcl (THE s.bst_xclb).xclb_view];
    view_check = (MAX v_pre (s.bst_coh l) < t);
    new_environ_opt = if xcl then update_environ s.bst_environ var (BVal_Imm $ Imm64 0w) else SOME s.bst_environ;
    new_environ = THE new_environ_opt;
    new_viewenv = if xcl then s.bst_viewenv |+ (var, t) else s.bst_viewenv;
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := new_viewenv;
                   bst_prom    updated_by FILTER ($≠ t);
                   bst_coh     updated_by (l =+ t);
                   bst_v_wOld  updated_by (MAX t);
                   bst_v_CAP   updated_by (MAX v_addr);
                   bst_v_Rel   updated_by (MAX $ ifView (rel ∧ acq) t);
                   bst_v_rNew  updated_by (MAX $ ifView (rel ∧ acq ∧ xcl) t);
                   bst_v_wNew  updated_by (MAX $ ifView (rel ∧ acq ∧ xcl) t);
                   bst_fwdb    updated_by (l =+ <| fwdb_time := t; fwdb_view := MAX v_addr v_data; fwdb_xcl := xcl |>);
                   bst_xclb    := if xcl then NONE else s.bst_xclb;
                   bst_pc      updated_by bir_pc_next |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME v_opt ∧ xcl_check ∧ mem_check ∧ view_check ∧ IS_SOME new_environ_opt
    then [s']
    else []
End

Definition eval_clstep_amo_def:
  eval_clstep_amo cid s M t_w var a_e v_e acq rel =
  let
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;

    (t_r, v_r) = last_t l M t_w;
    v_rPre = MAXL [v_addr; s.bst_v_rNew; 
                  ifView (acq ∧ rel) s.bst_v_Rel;
                  ifView (acq ∧ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
    v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r);

    new_environ_opt = update_environ s.bst_environ var v_r;
    new_environ = THE new_environ_opt;
    new_viewenv = s.bst_viewenv |+ (var, v_rPost);

    v_w_opt = bir_eval_exp v_e new_environ;
    v_w = THE v_w_opt;
    v_data = bir_eval_view_exp v_e new_viewenv;
    mem_check = (mem_get M l t_w = SOME <| loc := l; val := v_w; cid := cid |>);

    v_wPre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
              ifView (acq ∧ rel) s.bst_v_Rel;
              ifView (acq ∧ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
    v_wPost = t_w;
    view_check = (MAX v_wPre (s.bst_coh l) < t_w);

    s' = s with <| 
      bst_environ := new_environ;
      bst_viewenv := new_viewenv;
      bst_prom    updated_by FILTER ($≠ t_w);
      bst_coh     updated_by (l =+ t_w);
      bst_v_Rel   updated_by (MAX $ ifView (rel ∧ acq) v_wPost);
      bst_v_rOld  updated_by (MAX v_rPost);
      bst_v_rNew  updated_by (MAX $ ifView acq (if rel then v_wPost else v_rPost));
      bst_v_wNew  updated_by (MAX $ ifView acq (if rel then v_wPost else v_rPost));
      bst_v_CAP   updated_by MAX v_addr;
      bst_v_wOld  updated_by MAX v_wPost;
      bst_fwdb    updated_by (l =+ <| fwdb_time := t_w; fwdb_view := MAX v_addr v_data; fwdb_xcl := F |>);
      bst_pc updated_by bir_pc_next;
      |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME new_environ_opt ∧ IS_SOME v_w_opt ∧ mem_check ∧ view_check
    then [s']
    else []
End
        
Definition eval_clstep_fence_def:
  eval_clstep_fence s K1 K2 =
  let
    is_running = (s.bst_status = BST_Running);
    v = MAX (MAX (ifView (is_read K1) s.bst_v_rOld) (ifView (is_write K1) s.bst_v_wOld)) (ifView (is_control K1) s.bst_v_CAP);
    s' = s with <| bst_v_rNew updated_by MAX (ifView (is_read K2) v);
                   bst_v_wNew updated_by MAX (ifView (is_write K2) v);
                   bst_pc updated_by bir_pc_next |>;
  in
    if is_running
    then [s']
    else []
End

Definition eval_clstep_assign_def:
  eval_clstep_assign s var e =
  let
    is_running = (s.bst_status = BST_Running);
    v_opt = bir_eval_exp e s.bst_environ;
    v = THE v_opt;
    v_data = bir_eval_view_exp e s.bst_viewenv;
    new_environ_opt = update_environ s.bst_environ var v;
    new_environ = THE new_environ_opt;
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := s.bst_viewenv |+ (var, v_data);
                   bst_pc      updated_by bir_pc_next |>;
  in
    if is_running ∧ IS_SOME v_opt ∧ IS_SOME new_environ_opt
    then [s']
    else []
End

Definition eval_clstep_branch_def:
  eval_clstep_branch p s cond_e lbl1 lbl2 =
  let
      is_running = (s.bst_status = BST_Running);
      v_addr = bir_eval_view_exp cond_e s.bst_viewenv;
      s2 = bir_exec_stmt_cjmp p cond_e lbl1 lbl2 s;
      s' = s2 with <| bst_v_CAP updated_by MAX v_addr |>
  in
    if is_running
    then [s']
    else []
End

Definition eval_clstep_def:
  eval_clstep cid p M s =
  (case bir_get_current_statement p s.bst_pc of
  | NONE => []
  | SOME (BStmtB (BMCStmt_Load var a_e cast_opt xcl acq rel)) =>
      LIST_BIND [0..LENGTH M] (λt. eval_clstep_read s M t var a_e cast_opt xcl acq rel)
  | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
      eval_clstep_xclfail s var_succ xcl ++
      LIST_BIND s.bst_prom (λt. eval_clstep_fulfil cid s M t var_succ a_e v_e xcl acq rel)
  | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
      LIST_BIND s.bst_prom (λt_w.
          eval_clstep_amo cid s M t_w var a_e v_e acq rel)
  | SOME (BStmtB (BMCStmt_Fence K1 K2)) =>
      eval_clstep_fence s K1 K2
  | SOME (BStmtB (BMCStmt_Assign var e)) =>
      eval_clstep_assign s var e
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
      eval_clstep_branch p s cond_e lbl1 lbl2
  | SOME (BStmtB (BMCStmt_Assert e)) =>
      [bir_exec_stmt_assert e s]
  | SOME (BStmtB (BMCStmt_Assume e)) =>
      [bir_exec_stmt_assume e s]
  | SOME (BStmtE (BStmt_Jmp e)) =>
      [bir_exec_stmtE p (BStmt_Jmp e) s]
  | SOME (BStmtE (BStmt_Halt e)) =>
      [bir_exec_stmtE p (BStmt_Halt e) s])
End

Definition eval_cstep_seq_store_def:
  eval_cstep_seq_store cid s M var_succ a_e v_e xcl acq rel =
  let
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    v_opt = bir_eval_exp v_e s.bst_environ;
    v = THE v_opt;
    v_data = bir_eval_view_exp v_e s.bst_viewenv;
    msg = <| loc := l; val := v; cid := cid |>;
    M' = SNOC msg M;
    t = LENGTH M';
    s' = s with <| bst_prom updated_by (SNOC t) |>;
    v_pre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
                  ifView rel (MAX s.bst_v_rOld s.bst_v_wOld);
                  ifView (xcl ∧ acq ∧ rel) s.bst_v_Rel;
                  ifView xcl (THE s.bst_xclb).xclb_view];
    v = MAX v_pre (s.bst_coh l);
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME v_opt
    then MAP (λs'. (s', msg, v)) (eval_clstep_fulfil cid s' M' t var_succ a_e v_e xcl acq rel)
    else []
End

Definition eval_cstep_seq_amo_def:
  eval_cstep_seq_amo cid s M var a_e v_e acq rel =
  let
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;

    (t_r, v_r) = last_t l M (SUC (LENGTH M));
    v_rPre = MAXL [v_addr; s.bst_v_rNew; 
                  ifView (acq ∧ rel) s.bst_v_Rel;
                  ifView (acq ∧ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
    v_rPost = MAX v_rPre (mem_read_view (s.bst_fwdb l) t_r);

    new_environ_opt = update_environ s.bst_environ var v_r;
    new_environ = THE new_environ_opt;
    new_viewenv = s.bst_viewenv |+ (var, v_rPost);

    v_w_opt = bir_eval_exp v_e new_environ;
    v_w = THE v_w_opt;
    v_data = bir_eval_view_exp v_e new_viewenv;

    msg = <| loc := l; val := v_w; cid := cid |>;
    M' = SNOC msg M;
    t_w = LENGTH M';

    v_wPre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
              ifView (acq ∧ rel) s.bst_v_Rel;
              ifView (acq ∧ rel) (MAX s.bst_v_rOld s.bst_v_wOld)];
    v_wPost = t_w;
    v = MAX v_wPre (s.bst_coh l);
    view_check = (v < t_w);

    s' = s with <| 
      bst_environ := new_environ;
      bst_viewenv := new_viewenv;
      bst_prom    updated_by FILTER ($≠ t_w);
      bst_coh     updated_by (l =+ t_w);
      bst_v_Rel   updated_by (MAX $ ifView (rel ∧ acq) v_wPost);
      bst_v_rOld  updated_by (MAX v_rPost);
      bst_v_rNew  updated_by (MAX $ ifView acq (if rel then v_wPost else v_rPost));
      bst_v_wNew  updated_by (MAX $ ifView acq (if rel then v_wPost else v_rPost));
      bst_v_CAP   updated_by MAX v_addr;
      bst_v_wOld  updated_by MAX v_wPost;
      bst_fwdb    updated_by (l =+ <| fwdb_time := t_w; fwdb_view := MAX v_addr v_data; fwdb_xcl := F |>);
      bst_pc updated_by bir_pc_next;
      |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME new_environ_opt ∧ IS_SOME v_w_opt ∧ view_check
    then [(s', msg, v)]
    else []
End

Definition eval_cstep_seq_def:
  eval_cstep_seq cid p (s,M) =
  (case bir_get_current_statement p s.bst_pc of
  | NONE => []
  | SOME (BStmtB (BMCStmt_Load var a_e cast_opt xcl acq rel)) =>
      MAP (λs'. (s',[])) (LIST_BIND [0..LENGTH M] (λt. eval_clstep_read s M t var a_e cast_opt xcl acq rel))
  | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
      MAP (λs'. (s',[])) (eval_clstep_xclfail s var_succ xcl) ++
      MAP (λs'. (s',[])) (LIST_BIND s.bst_prom (λt. eval_clstep_fulfil cid s M t var_succ a_e v_e xcl acq rel)) ++
      MAP (λ(s', msg, v). (s', [(msg, v)])) (eval_cstep_seq_store cid s M var_succ a_e v_e xcl acq rel)
  | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
      MAP (λs'. (s',[])) (LIST_BIND s.bst_prom (λt_w.
          eval_clstep_amo cid s M t_w var a_e v_e acq rel)) ++
      MAP (λ(s', msg, v). (s', [(msg, v)])) (
        eval_cstep_seq_amo cid s M var a_e v_e acq rel)
  | SOME (BStmtB (BMCStmt_Fence K1 K2)) =>
      MAP (λs'. (s',[])) (eval_clstep_fence s K1 K2)
  | SOME (BStmtB (BMCStmt_Assign var e)) =>
      MAP (λs'. (s',[])) (eval_clstep_assign s var e)
  | SOME (BStmtE (BStmt_CJmp cond_e lbl1 lbl2)) =>
      MAP (λs'. (s',[])) (eval_clstep_branch p s cond_e lbl1 lbl2)
  | SOME (BStmtB (BMCStmt_Assert e)) =>
      [(bir_exec_stmt_assert e s, [])]
  | SOME (BStmtB (BMCStmt_Assume e)) =>
      [(bir_exec_stmt_assume e s, [])]
  | SOME (BStmtE (BStmt_Jmp e)) =>
      [(bir_exec_stmtE p (BStmt_Jmp e) s, [])]
  | SOME (BStmtE (BStmt_Halt e)) =>
      [(bir_exec_stmtE p (BStmt_Halt e) s, [])])
End 

Definition eval_certify_def:
  (eval_certify 0 cid p (s,M) =
   (s.bst_prom = []))
  ∧
  (eval_certify (SUC f) cid p (s,M) =
   ((s.bst_prom = []) ∨ EXISTS (λ(s',ml). eval_certify f cid p (s',M ++ (MAP FST ml))) (eval_cstep_seq cid p (s,M))))
End

Definition eval_pfind_def:
  eval_pfind 0 cid p (s,M) = []
  ∧
  eval_pfind (SUC f) cid p (s,M) =
  LIST_BIND (eval_cstep_seq cid p (s,M)) (λ(s',ml). ml ++ eval_pfind f cid p (s', M ++ (MAP FST ml)))
End

Definition UNIQ_def:
  UNIQ [] = []
  ∧
  UNIQ (x::xs) = x::(FILTER ($≠ x) (UNIQ xs))
End

Definition eval_pstep'_def:
  eval_pstep' f cid p (s, M) =
  let
    msgs = MAP FST (FILTER (λ(msg, v). v ≤ LENGTH M) (eval_pfind f cid p (s,M))) 
  in
  FILTER (λ(cid, s', M'). eval_certify f cid p (s',M'))
         (MAP (λmsg. (cid, s with bst_prom updated_by (CONS (LENGTH M + 1)), M ++ [msg]))
              (UNIQ msgs))
End        

Definition eval_update_cores_def:
  eval_update_cores [] (cid', s') = []
  ∧
  eval_update_cores ((cid,p,s)::rest) (cid', s') =
  if cid = cid'
  then (cid', p, s')::rest
  else (cid, p, s)::(eval_update_cores rest (cid', s'))
End

Definition eval_pstep_def:
  eval_pstep f (cores, M) =
    MAP (λ(cid, s', M'). (eval_update_cores cores (cid,s'), M'))
        (LIST_BIND cores (λ(cid,p,s). eval_pstep' f cid p (s, M)))
End

Definition is_halted_def:
  is_halted (BST_Running) = F
  ∧
  is_halted _ = T
End 
        

Definition eval_terminates_def:
  (eval_terminates 0 M (cid, p, s) = ((is_halted s.bst_status) ∧ s.bst_prom = []))
  ∧
  (eval_terminates (SUC f) M (cid, p, s) = 
  if is_halted s.bst_status ∧ s.bst_prom = []
  then T
  else (EXISTS (λs'. eval_terminates f M (cid, p, s')) (eval_clstep cid p M s)))
End

Definition eval_pstep_rep_def:
  (eval_pstep_rep 0 f (cores, M) =
   (if EVERY (eval_terminates f M) cores then [(cores,M)] else []))
  ∧
  (eval_pstep_rep (SUC r) f (cores, M) =
   (if EVERY (eval_terminates f M) cores then [(cores,M)] else []) ++
   LIST_BIND (eval_pstep f (cores, M)) (eval_pstep_rep r f))
End

Definition eval_promise_phase_def:
  eval_promise_phase f (cores, M) = eval_pstep_rep f f (cores, M)
End

Definition cross_list_def:
  cross_list [] = [[]]
  ∧
  cross_list (xs::xss) =
  LIST_BIND (cross_list xss) (λys. MAP (λx. x::ys) xs)
End

Definition eval_local_step_def:
  (eval_local_step 0 (cid, p, s) M =
  if is_halted s.bst_status ∧ s.bst_prom = [] then [s] else [])
  ∧ 
  (eval_local_step (SUC f) (cid, p, s) M =
  if is_halted s.bst_status ∧ s.bst_prom = [] 
  then [s]
  else LIST_BIND (eval_clstep cid p M s) (λs'. eval_local_step f (cid, p, s') M))
End

Definition eval_local_phase_def:
  eval_local_phase f (cores, M) =
  MAP (λcores. (cores,M))(cross_list (MAP (λcore. eval_local_step f core M) cores))
End

val _ = export_theory();
