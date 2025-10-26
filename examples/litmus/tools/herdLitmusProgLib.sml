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
  (is_xcl_write (h::l) =
    case LAST (h::l) of
      BStmt_Assign (BVar "MEM8_R" (BType_Mem Bit64 Bit8))
                     (BExp_Den (BVar "MEM8_Z" (BType_Mem Bit64 Bit8))) => 
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

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble arch prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [arch])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

local 
	val i = ref 0
in
fun lift_prog arch prog =
    let
	(* Create a DA file, also put nop at end *)
	val da_file = compile_and_disassemble arch (prog ^ "\n")
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
val prog_list = ["amoswap.d.aqrl x2,x5,(x4)\nld x5,(x5)"]
val prog = last $ parse_prog arch prog_list
val x = EVAL ``bir_vars_of_program ^prog``
val filename = "/tmp/hZEOwW.s.da"
*)
