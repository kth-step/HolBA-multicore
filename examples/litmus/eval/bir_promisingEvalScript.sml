open HolKernel boolLib Parse;

open bir_programTheory bir_promisingTheory;

val () = new_theory "bir_promisingEval";

Datatype:
  bmc_arch = RISCV | ARMv8
End

Datatype:
  OrdR = OrdR_PLN | OrdR_ACQ_PC | OrdR_ACQ 
End

Datatype:
  OrdW = OrdW_PLN | OrdW_REL_PC | OrdW_REL
End

Definition OrdR_mk_def:
  (OrdR_mk T T = OrdR_ACQ)
  ∧
  (OrdR_mk T F = OrdR_ACQ_PC)
  ∧ 
  (OrdR_mk _ _ = OrdR_PLN)
End

Definition OrdW_mk_def:
  (OrdW_mk T T = OrdW_REL)
  ∧
  (OrdW_mk F T = OrdW_REL_PC)
  ∧ 
  (OrdW_mk _ _ = OrdW_PLN)
End

Definition OrdR_ge_def:
  (OrdR_ge OrdR_ACQ _ = T)
  ∧
  (OrdR_ge _ OrdR_ACQ = F)
  ∧
  (OrdR_ge OrdR_ACQ_PC _ = T)
  ∧
  (OrdR_ge _ OrdR_ACQ_PC = F)
  ∧ 
  (OrdR_ge _ _ = T)
End

Definition OrdW_ge_def:
  (OrdW_ge OrdW_REL _ = T)
  ∧
  (OrdW_ge _ OrdW_REL = F)
  ∧
  (OrdW_ge OrdW_REL_PC _ = T)
  ∧
  (OrdW_ge _ OrdW_REL_PC = F)
  ∧
  (OrdW_ge _ _ = T)
End

(*
    if andb (fwd.(ts) == tsx) (negb (andb fwd.(ex) (orb (arch == riscv) (OrdR.ge ord OrdR.acquire_pc))))
*)

Definition eval_read_view_def:
  eval_read_view arch ord f t =
  if f.fwdb_time = t ∧ (f.fwdb_xcl ⇒ (arch = ARMv8 ∧ (OrdR_ge OrdR_ACQ_PC ord))) 
  then f.fwdb_view else t
End
                 
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
  eval_clstep_read arch s M t var a_e cast_opt xcl acq rel =
  let
    ordR = OrdR_mk acq rel;
    ordW = OrdW_mk acq rel;
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    v_opt = mem_read M l t;
    v_pre = MAXL [v_addr; 
                 s.bst_v_rNew; 
                 ifView (OrdW_ge ordW OrdW_REL_PC) (MAX s.bst_v_rOld s.bst_v_wOld);
                 ifView (OrdR_ge ordR OrdR_ACQ) s.bst_v_Rel];
    is_latest = EVERY (λt'. ~mem_is_loc M t' l) [SUC t.. (MAX v_pre (s.bst_coh l))];
    v = THE v_opt;
    v_post = MAX v_pre (eval_read_view arch ordR (s.bst_fwdb l) t);
    new_environ_opt = update_environ s.bst_environ var v;
    new_environ = THE new_environ_opt;
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := (s.bst_viewenv |+ (var,v_post));
                   bst_coh     updated_by (l =+ MAX (s.bst_coh l) v_post);
                   bst_v_rOld  updated_by MAX v_post;
                   bst_v_rNew  updated_by MAX $ ifView (OrdR_ge ordR OrdR_ACQ_PC) v_post;
                   bst_v_wNew  updated_by MAX $ ifView (OrdR_ge ordR OrdR_ACQ_PC) v_post;
                   bst_v_CAP   updated_by MAX v_addr;
                   bst_v_Rel   updated_by MAX $ ifView (OrdW_ge ordW OrdW_REL) v_post;
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

Definition eval_clstep_fulfil_aux_def:
  eval_clstep_fulfil_aux arch cid s M t var a_e v_e xcl acq rel =
  let
    is_running = (s.bst_status = BST_Running);

    (* Get acquire and release flags*)
    ordW = OrdW_mk acq rel;
    ordR = OrdR_mk acq rel;

    (* Get the location *)
    l_opt = bir_eval_exp a_e s.bst_environ;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    l = THE l_opt;

    (* Get the data to write *)
    v_opt = bir_eval_exp v_e s.bst_environ;
    v_data = bir_eval_view_exp v_e s.bst_viewenv;
    v = THE v_opt;

    (* Check that memory at location t is what we want to write. *)
    mem_check = (mem_get M l t = SOME <| loc := l; val := v; cid := cid |>);

    (* xcl_check = xcl ⇒ ts.xclb ≠ none ∧ atomic(M, l, tid, ts.xclb.time, t) *)
    xcl_check = (xcl ⇒ (IS_SOME s.bst_xclb) ∧ 
      (mem_is_loc M ((THE s.bst_xclb).xclb_time) l ⇒ EVERY (λt'. mem_is_loc M t' l ⇒ mem_is_cid M t' cid) [SUC ((THE s.bst_xclb).xclb_time)..< t]));

    (* We must fulfil the earliest promise made to the same location *)
    promise_check = (EVERY (λt'. t' < t ⇒ ¬mem_is_loc M t' l) s.bst_prom);

    (* Compute the preview: https://github.com/rems-project/rmem/blob/b2d346393eaa83d84c657eeec7d70b01b0656643/src_concurrency_model/promisingThread.lem#L569 *)
    v_pre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
                  ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_rOld;
                  ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_wOld;
                  ifView (OrdR_ge ordR OrdR_ACQ) s.bst_v_Rel;
                  ifView (xcl ∧ arch = RISCV) (THE s.bst_xclb).xclb_view];

    (* view constraint *)
    view_check = (MAX v_pre (s.bst_coh l) < t);

    (* for exclusive store, update success variable *)
    new_environ_opt = if xcl then update_environ s.bst_environ var (BVal_Imm $ Imm64 0w) else SOME s.bst_environ;
    new_environ = THE new_environ_opt;
    new_viewenv = if xcl then s.bst_viewenv |+ (var, ifView (arch = RISCV) t) else s.bst_viewenv;

    (* new state *)
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := new_viewenv;
                   bst_prom    updated_by FILTER ($≠ t);
                   bst_coh     updated_by (l =+ t);
                   bst_v_wOld  updated_by (MAX t);
                   bst_v_CAP   updated_by (MAX v_addr);
                   bst_v_Rel   updated_by (MAX $ ifView (OrdW_ge ordW OrdW_REL) t);
                   bst_v_wNew  updated_by (MAX $ ifView (OrdR_ge ordR OrdR_ACQ_PC) t);
                   bst_v_rNew  updated_by (MAX $ ifView (OrdR_ge ordR OrdR_ACQ_PC) t);
                   bst_fwdb    updated_by (l =+ <| fwdb_time := t; fwdb_view := MAX v_addr v_data; fwdb_xcl := xcl |>);
                   bst_xclb    := if xcl then NONE else s.bst_xclb;
                   bst_pc      updated_by bir_pc_next |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME v_opt ∧ xcl_check ∧ promise_check ∧ mem_check ∧ view_check ∧ IS_SOME new_environ_opt
    then [s']
    else []
End

Definition eval_clstep_fulfil_def:
  eval_clstep_fulfil arch cid s M var a_e v_e xcl acq rel =
  LIST_BIND (s.bst_prom) (λt. eval_clstep_fulfil_aux arch cid s M t var a_e v_e xcl acq rel)
End

Definition eval_clstep_amo_aux_def:
  eval_clstep_amo_aux arch cid s M t_w var a_e v_e acq rel =
  let
    ordR = OrdR_mk acq rel;
    ordW = OrdW_mk acq rel;
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    promise_check = (EVERY (λt'. t' < t_w ⇒ ¬mem_is_loc M t' l) s.bst_prom);

    (t_r, v_r) = last_t l M t_w;
    v_rPre = MAXL [v_addr; s.bst_v_rNew; 
                  ifView (OrdR_ge ordR OrdR_ACQ) s.bst_v_Rel];
    v_rPost = MAX v_rPre (eval_read_view arch ordR (s.bst_fwdb l) t_r);

    new_environ_opt = update_environ s.bst_environ var v_r;
    new_environ = THE new_environ_opt;
    new_viewenv = s.bst_viewenv |+ (var, v_rPost);

    v_w_opt = bir_eval_exp v_e new_environ;
    v_w = THE v_w_opt;
    v_data = bir_eval_view_exp v_e new_viewenv;
    mem_check = (mem_get M l t_w = SOME <| loc := l; val := v_w; cid := cid |>);

    v_wPre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
              ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_rOld;
              ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_wOld];
    v_wPost = t_w;
    view_check = (MAX v_wPre (s.bst_coh l) < t_w);

    s' = s with <| 
      bst_environ := new_environ;
      bst_viewenv := new_viewenv;
      bst_prom    updated_by FILTER ($≠ t_w);
      bst_coh     updated_by (l =+ t_w);
      bst_v_Rel   updated_by (MAX $ ifView (OrdW_ge ordW OrdW_REL_PC) v_wPost);
      bst_v_rOld  updated_by MAX v_rPost;
      bst_v_wOld  updated_by MAX v_wPost;
      bst_v_CAP   updated_by MAX v_addr;
      bst_v_rNew  updated_by MAX (ifView (OrdR_ge ordR OrdR_ACQ_PC) v_rPost);
      bst_v_wNew  updated_by MAX (ifView (OrdR_ge ordR OrdR_ACQ_PC) v_rPost);
      bst_fwdb    updated_by (l =+ <| fwdb_time := t_w; fwdb_view := MAX v_addr v_data; fwdb_xcl := F |>);
      bst_pc updated_by bir_pc_next;
      |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME new_environ_opt ∧ IS_SOME v_w_opt ∧ promise_check ∧ mem_check ∧ view_check
    then [s']
    else []
End

Definition eval_clstep_amo_def:
  eval_clstep_amo arch cid s M var a_e v_e acq rel =
  LIST_BIND (s.bst_prom) (λt. eval_clstep_amo_aux arch cid s M t var a_e v_e acq rel)
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
  eval_clstep arch cid p M s =
  (case bir_get_current_statement p s.bst_pc of
  | NONE => []
  | SOME (BStmtB (BMCStmt_Load var a_e cast_opt xcl acq rel)) =>
      LIST_BIND [0..LENGTH M] (λt. eval_clstep_read arch s M t var a_e cast_opt xcl acq rel)
  | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
    (eval_clstep_fulfil arch cid s M var_succ a_e v_e xcl acq rel) ++
    (eval_clstep_xclfail s var_succ xcl)
  | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
    (eval_clstep_amo arch cid s M var a_e v_e acq rel)
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
  eval_cstep_seq_store arch cid s M var_succ a_e v_e xcl acq rel =
  let
    ord = OrdW_mk acq rel;
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    promise_check = (EVERY (λt'. ¬mem_is_loc M t' l) s.bst_prom);
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;
    v_opt = bir_eval_exp v_e s.bst_environ;
    v = THE v_opt;
    msg = <| loc := l; val := v; cid := cid |>;
    t = LENGTH (SNOC msg M);
    v_data = bir_eval_view_exp v_e s.bst_viewenv;
    xcl_check = (xcl ⇒ (IS_SOME s.bst_xclb) ∧ 
      (mem_is_loc M ((THE s.bst_xclb).xclb_time) l ⇒ EVERY (λt'. mem_is_loc M t' l ⇒ mem_is_cid M t' cid) [SUC ((THE s.bst_xclb).xclb_time)..< t]));
    v_pre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
                  ifView (OrdW_ge ord OrdW_REL_PC) s.bst_v_rOld;
                  ifView (OrdW_ge ord OrdW_REL_PC) s.bst_v_wOld;
                  ifView (xcl ∧ arch = RISCV) (THE s.bst_xclb).xclb_view];
    view_check = (MAX v_pre (s.bst_coh l) < t);
    new_environ_opt = if xcl then update_environ s.bst_environ var_succ (BVal_Imm $ Imm64 0w) else SOME s.bst_environ;
    new_environ = THE new_environ_opt;
    new_viewenv = if xcl then s.bst_viewenv |+ (var_succ, ifView (arch = RISCV) t) else s.bst_viewenv;
    s' = s with <| bst_environ := new_environ;
                   bst_viewenv := new_viewenv;
                   bst_coh     updated_by (l =+ t);
                   bst_v_wOld  updated_by (MAX t);
                   bst_v_CAP   updated_by (MAX v_addr);
                   bst_v_Rel   updated_by (MAX $ ifView (OrdW_ge ord OrdW_REL) t);
                   bst_fwdb    updated_by (l =+ <| fwdb_time := t; fwdb_view := MAX v_addr v_data; fwdb_xcl := xcl |>);
                   bst_xclb    := if xcl then NONE else s.bst_xclb;
                   bst_pc      updated_by bir_pc_next |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME v_opt ∧ xcl_check ∧ view_check ∧ IS_SOME new_environ_opt
    then [(s', [msg, MAX v_pre (s.bst_coh l)])]
    else []
End

Definition eval_cstep_seq_amo_def:
  eval_cstep_seq_amo arch cid s M var a_e v_e acq rel =
  let
    ordR = OrdR_mk acq rel;
    ordW = OrdW_mk acq rel;
    is_running = (s.bst_status = BST_Running);
    l_opt = bir_eval_exp a_e s.bst_environ;
    l = THE l_opt;
    v_addr = bir_eval_view_exp a_e s.bst_viewenv;

    t_w = LENGTH M + 1;
    promise_check = (EVERY (λt'. ¬mem_is_loc M t' l) s.bst_prom);

    (t_r, v_r) = last_t l M t_w;
    v_rPre = MAXL [v_addr; s.bst_v_rNew; 
                  ifView (OrdR_ge ordR OrdR_ACQ) s.bst_v_Rel];
    v_rPost = MAX v_rPre (eval_read_view arch ordR (s.bst_fwdb l) t_r);

    new_environ_opt = update_environ s.bst_environ var v_r;
    new_environ = THE new_environ_opt;
    new_viewenv = s.bst_viewenv |+ (var, v_rPost);

    v_w_opt = bir_eval_exp v_e new_environ;
    v_w = THE v_w_opt;
    v_data = bir_eval_view_exp v_e new_viewenv;

    msg = <| loc := l; val := v_w; cid := cid |>;

    v_wPre = MAXL [v_addr; v_data; s.bst_v_wNew; s.bst_v_CAP;
              ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_rOld;
              ifView (OrdW_ge ordW OrdW_REL_PC) s.bst_v_wOld
              ];
    v_wPost = t_w;
    view_check = (MAX v_wPre (s.bst_coh l) < t_w);

    s' = s with <| 
      bst_environ := new_environ;
      bst_viewenv := new_viewenv;
      bst_coh     updated_by (l =+ t_w);
      bst_v_Rel   updated_by (MAX $ ifView (OrdW_ge ordW OrdW_REL_PC) v_wPost);
      bst_v_rOld  updated_by MAX v_rPost;
      bst_v_wOld  updated_by MAX v_wPost;
      bst_v_CAP   updated_by MAX v_addr;
      bst_v_rNew  updated_by MAX (ifView (OrdR_ge ordR OrdR_ACQ_PC) v_rPost);
      bst_v_wNew  updated_by MAX (ifView (OrdR_ge ordR OrdR_ACQ_PC) v_rPost);
      bst_fwdb    updated_by (l =+ <| fwdb_time := t_w; fwdb_view := MAX v_addr v_data; fwdb_xcl := F |>);
      bst_pc updated_by bir_pc_next;
      |>
  in
    if is_running ∧ IS_SOME l_opt ∧ IS_SOME new_environ_opt ∧ IS_SOME v_w_opt ∧ view_check
    then [(s', [msg, MAX v_wPre (s.bst_coh l)])]
    else []
End

Definition eval_cstep_seq_def:
  eval_cstep_seq arch cid p (s,M) =
  MAP (λs'. (s',[])) (eval_clstep arch cid p M s) ++
  (case bir_get_current_statement p s.bst_pc of
  | SOME (BStmtB (BMCStmt_Store var_succ a_e v_e xcl acq rel)) =>
      eval_cstep_seq_store arch cid s M var_succ a_e v_e xcl acq rel
  | SOME (BStmtB (BMCStmt_Amo var a_e v_e acq rel)) =>
      eval_cstep_seq_amo arch cid s M var a_e v_e acq rel
  | _ => [])
End 

Definition eval_certify_def:
  (eval_certify arch 0 cid p (s,M) =
   (s.bst_prom = []))
  ∧
  (eval_certify arch (SUC f) cid p (s,M) =
   ((s.bst_prom = []) ∨ EXISTS (λ(s',ml). eval_certify arch f cid p (s',M ++ (MAP FST ml))) (eval_cstep_seq arch cid p (s,M))))
End

Definition eval_pfind_def:
  (eval_pfind arch 0 cid p (s,M) v_max prom =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = []
  then MAP FST $ FILTER (λ(msg,v). v ≤ v_max) prom
  else [])
  ∧ 
  (eval_pfind arch (SUC f) cid p (s,M) v_max prom =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = []
  then MAP FST $ FILTER (λ(msg,v). v ≤ v_max) prom
  else LIST_BIND (eval_cstep_seq arch cid p (s,M)) 
      (λ(s',ml).  eval_pfind arch f cid p (s', M ++ (MAP FST ml)) v_max (ml ++ prom)))
End

Definition UNIQ_def:
  UNIQ [] = []
  ∧
  UNIQ (x::xs) = x::(FILTER ($≠ x) (UNIQ xs))
End

Definition eval_terminates_def:
  (eval_terminates arch M 0 (cid, p, s) =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = [] then T else F)
  ∧ 
  (eval_terminates arch M (SUC f) (cid, p, s) =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = [] then T
  else EXISTS (λs'. eval_terminates arch M f (cid, p, s')) (eval_clstep arch cid p M s))
End

Definition eval_clpstep_def:
  eval_clpstep arch f cid p (s, M) =
  let
    msgs = UNIQ $ eval_pfind arch f cid p (s,M) (LENGTH M) []
  in
  MAP (λmsg. (cid, p, s with bst_prom updated_by (SNOC (LENGTH M + 1)), M ++ [msg])) msgs
End

Definition eval_pstep_def:
  eval_pstep arch f (cores, M) =
    MAP (λ(cid, p, s', M'). (LUPDATE (cid, p, eval_terminates arch M' f (cid, p, s'), s') cid cores, M'))
        (LIST_BIND cores (λ(cid,p,term,s). eval_clpstep arch f cid p (s, M)))
End

Definition eval_pstep_rep_def:
  (eval_pstep_rep arch 0 f (cores, M) =
   (if EVERY (λ(cid, p, term, s). term) cores then [(cores,M)] else []))
  ∧
  (eval_pstep_rep arch (SUC r) f (cores, M) =
   (if EVERY (λ(cid, p, term, s). term) cores then [(cores,M)] else []) ++
   LIST_BIND (eval_pstep arch f (cores, M)) (eval_pstep_rep arch r f))
End

Definition eval_promise_phase_def:
  eval_promise_phase arch f (cores, M) = 
  let 
    cores' = MAP (λ(cid, p, s). (cid, p, eval_terminates arch M f (cid, p, s), s)) cores
  in eval_pstep_rep arch f f (cores', M)
End

Definition cross_list_def:
  cross_list [] = [[]]
  ∧
  cross_list (xs::xss) =
  LIST_BIND (cross_list xss) (λys. MAP (λx. x::ys) xs)
End

Definition eval_local_step_def:
  (eval_local_step arch f (cid, p, F, s) M = [])
  ∧ 
  (eval_local_step arch 0 (cid, p, T, s) M =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = [] then [s] else [])
  ∧ 
  (eval_local_step arch (SUC f) (cid, p, T, s) M =
  if s.bst_status ≠ BST_Running ∧ s.bst_prom = [] 
  then [s]
  else LIST_BIND (eval_clstep arch cid p M s) (λs'. eval_local_step arch f (cid, p, T, s') M))
End

Definition eval_local_phase_def:
  eval_local_phase arch f (cores, M) =
  MAP (λcores. (cores,M)) (cross_list (MAP (λcore. eval_local_step arch f core M) cores))
End

val () = export_theory();
