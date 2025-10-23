signature herdLitmusProgLib =
sig
    include Abbrev
    (* Argument: Program section
       Returns: List of BIR programs *)
    val parse_prog : string -> string list -> term list
end

structure herdLitmusProgLib : herdLitmusProgLib =
struct
open HolKernel Parse bossLib boolLib
open listSyntax;

open bir_lifter_interfaceLib
open bir_programSyntax bir_expSyntax;
open bslSyntax;
open UtilLib;

val SOURCE_DIR = valOf (Posix.ProcEnv.getenv ("PWD"))

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
     | _ => NONE
  )  /\
  (is_xcl_read _ = NONE) 
End

Definition is_xcl_write_def:
  (is_xcl_write (h::h'::l) =
    case h' of
      BStmt_Assign (BVar "MEM8_W" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))) => SOME l
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

(*
val bir_get_stmt_def = Define‘
  bir_get_stmt p pc =
  case bir_get_current_statement p pc of
  | SOME (BStmtB (BStmt_Assign var e)) =>
      if is_amo p pc then
      (case get_read_args e of
       | SOME (a_e, cast_opt) =>
           (case bir_get_current_statement p (bir_pc_next pc) of
           | SOME (BStmtB (BStmt_Assign var' e)) =>
               (case get_fulfil_args e of
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
*)

Definition bir2bmc_statements_def:
   bir2bmc_statements mc_tags [] = [] ∧ 
   bir2bmc_statements mc_tags (h::l) = 
   case h of
   | BStmt_Assert expr => (bir2bmc_statements mc_tags l)
   | BStmt_Assume expr => (bir2bmc_statements mc_tags l)
   | BStmt_Fence pre post => (BMCStmt_Fence pre post)::(bir2bmc_statements mc_tags l)
   | BStmt_Observe _ _ _ _ => bir2bmc_statements mc_tags l
   | BStmt_Assign var expr => 
	if is_amo mc_tags then
	(case (get_read_args expr, get_fulfil_args expr) of
	| (SOME (a_e, cast_opt), SOME (a_e', v_e)) => 
	    if a_e = a_e' then
		(BMCStmt_Amo var a_e v_e (is_acq mc_tags) (is_rel mc_tags))::(bir2bmc_statements mc_tags l)
	    else
		[]
	| (NONE, NONE) => (BMCStmt_Assign var expr)::(bir2bmc_statements mc_tags l)
	| _ => [])
	else 
	(case (get_read_args expr, get_fulfil_args expr) of
	| (SOME (a_e, cast_opt), NONE) => 
		(case (is_xcl_read l) of
		| SOME l' => (BMCStmt_Load var a_e cast_opt T (is_acq mc_tags) (is_rel mc_tags))::(bir2bmc_statements mc_tags l')
		| NONE => (BMCStmt_Load var a_e cast_opt F (is_acq mc_tags) (is_rel mc_tags))::(bir2bmc_statements mc_tags l))
	| (NONE, SOME (a_e, v_e)) => 
		(case (is_xcl_write l) of
		| SOME l' => (BMCStmt_Store var a_e v_e T (is_acq mc_tags) (is_rel mc_tags))::(bir2bmc_statements mc_tags l')
		| NONE => (BMCStmt_Store var a_e v_e F (is_acq mc_tags) (is_rel mc_tags))::(bir2bmc_statements mc_tags l))
	| (NONE, NONE) => (BMCStmt_Assign var expr)::(bir2bmc_statements mc_tags l)
	| _ => [])
Termination
  cheat
End

Definition bir2bmc_block_def:
    bir2bmc_block x = 
    <|
    bb_label := x.bb_label;
    bb_mc_tags := x.bb_mc_tags;
    bb_statements := bir2bmc_statements x.bb_mc_tags x.bb_statements;
    bb_last_statement := x.bb_last_statement;
    |>
End

Definition bir2bmc_prog_def:
	bir2bmc_prog (BirProgram p) =
	  BirProgram (MAP bir2bmc_block p)
End

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble arch prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [arch])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

fun remove_mc_tags_arb prog =
    let 
	    val (blocks, ty) = dest_list (dest_BirProgram prog)
	    fun f tm =
	    let
  		  val (ty, l) = TypeBase.dest_record tm
  		  val lbl = Lib.assoc "bb_label" l
  		  val mc_tags_opt = 
          (case (Lib.assoc1 "bb_mc_tags" l) of
           SOME (_, mc_tags) => mc_tags
          | NONE => bir_mc_tags_NONE);
  		  val stmts = Lib.assoc "bb_statements" l
  		  val last_stmt = Lib.assoc "bb_last_statement" l
		    val l' = [("bb_label", lbl),
			    ("bb_mc_tags", mc_tags_opt),
			    ("bb_statements", stmts),
			    ("bb_last_statement", last_stmt)]
	    in TypeBase.mk_record (ty, l') end
    in
	  mk_BirProgram (mk_list (map f blocks, ty))
    end

local 
	val i = ref 0
in
fun lift_prog arch prog =
    let
	(* Create a DA file, also put nop at end *)
	val da_file = compile_and_disassemble arch (prog ^ "\nnop\n")
	val name = "litmus" ^ Int.toString (!i)
	val _ = i := !i + 1
	(* Lift the DA file *)
	val (_, bir_litmus_prog_def, _) = 
	case arch of
	    "RISCV" => lift_da_and_store_mc_riscv name da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
	  | "AArch64" => lift_da_and_store_mc name da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
	  | _ => raise Fail ("Unsupported architecture: " ^ arch);
	(* Fetch the Program definition *)
	val bir_litmus_prog = (rhs o concl) bir_litmus_prog_def;
  val bir_litmus_prog = remove_mc_tags_arb bir_litmus_prog
	val bmc_litmus_prog = (rhs o concl) (EVAL ``bir2bmc_prog ^bir_litmus_prog``);
    in (* Return the program term *)
	  bmc_litmus_prog
    end
end
	
fun typed_prog p = inst [“:'observation_type” |-> Type`:string`] p;

fun parse_prog arch prog_list =
    let
	val bir_progs = map (typed_prog o (lift_prog arch)) prog_list
    in bir_progs end
end

(*
open herdLitmusProgLib
open listSyntax bir_programSyntax;
val arch = "RISCV"
val prog_list = ["amoadd.w.aqrl x5,x5,(x4)\nld x5,(x5)"]
val prog = last $ parse_prog arch prog_list
val x = EVAL ``bir_vars_of_program ^prog``
*)
