open HolKernel boolLib Parse;
open bir_programSyntax bir_expSyntax;

val () = new_theory "litmus_lifter";

Definition get_read_args_def:
  (get_read_args (BExp_Load mem_e a_e en ty) =
     SOME (a_e, NONE)) /\
  (get_read_args (BExp_Cast cast_ty load_e imm_ty) =
   case get_read_args load_e of
   | SOME (a_e, NONE) => SOME (a_e, SOME (cast_ty, imm_ty))
   | _ => NONE) /\
  (get_read_args _ = NONE)
End


(* Obtains an option type that contains the store arguments
 * needed to apply the fulfil rule *)
Definition get_fulfil_args_def:
  (get_fulfil_args (BExp_IfThenElse cond_e e1 e2) = get_fulfil_args e1) /\
  (get_fulfil_args (BExp_Store mem_e a_e en v_e) =
   SOME (a_e, v_e)) /\
  (get_fulfil_args _ = NONE)
End

Definition is_xcl_read_def:
  (is_xcl_read (h::l) =
    case h of
      BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8)))
                       (BExp_Den (BVar varname (BType_Imm Bit64))) BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))) => SOME l
     | BStmt_Assign (BVar "MEM_R" (BType_Mem Bit64 Bit8))
		     (BExp_Store (BExp_Den (BVar "MEM_Z" (BType_Mem Bit64 Bit8)))
                       (BExp_Den (BVar varname (BType_Imm Bit64))) BEnd_LittleEndian
		       (BExp_Const (Imm32 0x1010101w))) => SOME l
     | _ => NONE
  )  /\
  (is_xcl_read _ = NONE) 
End

Definition is_xcl_write_def:
  (is_xcl_write (h::l) =
    case LAST (h::l) of
    | BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))) => 
      (case h of
        BStmt_Assign (BVar varname (BType_Imm Bit64)) _ => SOME (BVar varname (BType_Imm Bit64))
      | _ => SOME (BVar "tmp" (BType_Imm Bit64)))
    | BStmt_Assign (BVar "MEM_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM_Z" (BType_Mem Bit64 Bit8))) => 
      (case h of
        BStmt_Assign (BVar varname (BType_Imm Bit64)) _ => SOME (BVar varname (BType_Imm Bit64))
      | _ => SOME (BVar "tmp" (BType_Imm Bit64)))
    | _ => NONE
  )  /\
  (is_xcl_write _ = NONE)
End

Definition is_acq_def:
  is_acq (SOME mc_tags) = mc_tags.mc_acq
  ∧ is_acq _ = F
End

Definition is_rel_def:
  is_rel (SOME mc_tags) = mc_tags.mc_rel
  ∧ is_rel _ = F
End

Definition is_amo_def:
  is_amo (SOME mc_tags) = mc_tags.mc_atomic
  ∧ is_amo _ = F
End

Definition bir2bmc_statements_def:
  (bir2bmc_statements amo acq rel [] = [])
∧ (bir2bmc_statements amo acq rel ((BStmt_Assert expr)::l) = 
     (bir2bmc_statements amo acq rel l))
∧ (bir2bmc_statements amo acq rel ((BStmt_Assume expr)::l) = 
     (bir2bmc_statements amo acq rel l))
∧ (bir2bmc_statements amo acq rel ((BStmt_Fence pre post)::l) = 
     (BMCStmt_Fence pre post)::(bir2bmc_statements amo acq rel l))
∧ (bir2bmc_statements amo acq rel ((BStmt_Observe _ _ _ _ )::l) = 
     bir2bmc_statements amo acq rel l)
∧ (bir2bmc_statements T acq rel ((BStmt_Assign var expr)::(BStmt_Assign var' expr')::l) =
     (case (get_read_args expr, get_fulfil_args expr') of
     | (SOME (a_e, cast_opt), SOME (a_e', v_e)) =>
          [BMCStmt_Amo var a_e v_e acq rel]
     | (NONE, NONE) => []))
∧ (bir2bmc_statements F acq rel ((BStmt_Assign var expr)::l) =
	(case (get_read_args expr, get_fulfil_args expr) of
	| (SOME (a_e, cast_opt), NONE) => 
		(case (is_xcl_read l) of
		| SOME l' => [BMCStmt_Load var a_e cast_opt T acq rel]
		| NONE => [BMCStmt_Load var a_e cast_opt F acq rel])
	| (NONE, SOME (a_e, v_e)) => 
		(case (is_xcl_write l) of
		| SOME var => [BMCStmt_Store var a_e v_e T acq rel]
		| NONE => [BMCStmt_Store (BVar "tmp" (BType_Imm Bit64)) a_e v_e F acq rel])
	| (NONE, NONE) => [BMCStmt_Assign var expr]
	| _ => []))
End

Definition bir2bmc_block_def:
    bir2bmc_block x = 
    <|
    bb_label := x.bb_label;
    bb_mc_tags := NONE;
    bb_statements := bir2bmc_statements (is_amo x.bb_mc_tags) (is_acq x.bb_mc_tags) (is_rel x.bb_mc_tags) x.bb_statements;
    bb_last_statement := x.bb_last_statement;
    |>
End

Definition bir2bmc_prog_def:
	bir2bmc_prog (BirProgram p) =
	  BirProgram (MAP bir2bmc_block p)
End

local
    open HolKernel bossLib boolLib Parse;
    open computeLib;
    open numSyntax bir_immSyntax wordsSyntax wordsLib;
    
    fun mk_constant_aux_thm n =
      let
        val vars = List.tabulate(n, fn i => mk_var("x" ^ (Int.toString i), “:word64”));
        fun mk_distinct [] = []
          | mk_distinct (x::xs) = map (fn y => “(^x <> ^y) /\ (^y <> ^x)”) xs @ mk_distinct xs;
        fun mk_addr_constraint var = [
          (* alignment *)
          “^var && 3w = 0w”,
          “^var && 7w = 0w”,
          (* range *)
          “(if ^var ≤₊ 0xFFFFFFFFFFFFFFFBw then (1w:word1)
          else 0w) &&
          ((if 0w <₊ ^var then 1w else 0w) ‖
            if 4w + ^var ≤₊ 0w then 1w else 0w) &&
          ((if ^var <₊ 0w then 1w else 0w) ‖
          if 1000w ≤₊ ^var then 1w else 0w) 
          = 1w”,
          “(if ^var ≤₊ 0xFFFFFFFFFFFFFFF7w then (1w:word1)
          else 0w) &&
          ((if 0w <₊ ^var then 1w else 0w) ‖
            if 8w + ^var ≤₊ 0w then 1w else 0w) &&
          ((if ^var <₊ 0w then 1w else 0w) ‖
          if 1000w ≤₊ ^var then 1w else 0w) 
          = 1w”,
	  (* arith *)
	  “^var + 0w = ^var”];
        val terms = mk_distinct vars @ List.concat (map mk_addr_constraint vars);
        val final_term = list_mk_exists (vars, list_mk_conj terms);
        fun mk_exists i = EXISTS_TAC (mk_wordii(1000+8*i, 64));
        val word_ss = bool_ss ++ WORD_ss
        val tactics = List.foldl (op>>)
                          (simp_tac word_ss [])
                          (List.tabulate(n, mk_exists));
      in
        TAC_PROOF (([],final_term), tactics)
      end;
    
    fun mk_constants_thm name l =
      new_specification(name, l, mk_constant_aux_thm (List.length l))

in

val LITMUS_CONSTANT_THM = mk_constants_thm "LitmusConstants" ["lc_x", "lc_y", "lc_z", "lc_u", "lc_t", "lc_a", "lc_b", "lc_c", "lc_d", "lc_ok", "lc_lock", "lc_v", "lc_p", "lc_q", "lc_A", "lc_B", "lc_C"]
end

val () = export_theory ();
