signature herdLitmusLib =
sig
    include Abbrev
    type litmus = {arch:string,
		   name:string,
		   regs: term list,
		   mem: term,
		   progs: term list,
		   final: term}

    (* Argument: path to herdtools litmus test
       Returns: Litmus test for BIR. *)
    val parse : string -> litmus
end



structure herdLitmusLib : herdLitmusLib =
struct
open HolKernel Parse boolLib bossLib;
open stringSyntax;
open bir_execLib;
open bir_valuesSyntax bir_immSyntax;

open herdLitmusProgLib herdLitmusInitLib herdLitmusFinalLib;
open UtilLib;
open JsonUtil;

Definition bmc_varset_of_basic_stmt_def:
   bmc_varset_of_basic_stmt (BMCStmt_Assign var exp) = { var } UNION bir_varset_of_exp exp
/\ bmc_varset_of_basic_stmt (BMCStmt_Assert exp) = bir_varset_of_exp exp
/\ bmc_varset_of_basic_stmt (BMCStmt_Assume exp) = bir_varset_of_exp exp
/\ bmc_varset_of_basic_stmt (BMCStmt_Load var exp _ _ _ _) =  { var } UNION bir_varset_of_exp exp
/\ bmc_varset_of_basic_stmt (BMCStmt_Store var exp exp' _ _ _) =  { var } UNION bir_varset_of_exp exp UNION bir_varset_of_exp exp'
/\ bmc_varset_of_basic_stmt (BMCStmt_Amo var exp exp' _ _) =  { var } UNION bir_varset_of_exp exp UNION bir_varset_of_exp exp'
/\ bmc_varset_of_basic_stmt _ = {}
End

Definition bmc_varset_of_label_exp_def:
   bmc_varset_of_label_exp (BLE_Label _) = {}
/\ bmc_varset_of_label_exp (BLE_Exp exp) = bir_varset_of_exp exp
End

Definition bmc_varset_of_end_stmt_def:
   bmc_varset_of_end_stmt (BStmt_Jmp lexp) = bir_varset_of_label_exp lexp
/\ bmc_varset_of_end_stmt (BStmt_CJmp cond exp1 exp2) = bir_varset_of_exp cond UNION bmc_varset_of_label_exp exp1 UNION bmc_varset_of_label_exp exp2
/\ bmc_varset_of_end_stmt (BStmt_Halt exp) = bir_varset_of_exp exp
End

Definition bmc_varset_of_stmt_def:
   bmc_varset_of_stmt (BStmtB bstmt) = bmc_varset_of_basic_stmt bstmt
/\ bmc_varset_of_stmt (BStmtE estmt) = bmc_varset_of_end_stmt estmt
End

Definition bmc_varset_of_program_def:
bmc_varset_of_program (BirProgram blocks) =
	FOLDR (\a b. a UNION b)
		{}
		(MAP (\bl. FOLDR (\a b. a UNION b)
							(bmc_varset_of_end_stmt bl.bb_last_statement)
							(MAP bmc_varset_of_basic_stmt bl.bb_statements))
				 blocks)
End


type litmus = {arch:string,
	       name:string,
	       regs: term list,
	       mem: term,
	       progs: term list,
	       final: term}
		  
exception CouldNotParseJsonFile
	      
val SOURCE_DIR = valOf (Posix.ProcEnv.getenv ("PWD"))

fun parse_litmus text = 
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/parser.py", [])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, text) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end
    

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end
		  
fun get_json_data (Json.OK json) = 
    let
	val arch = asString $ lookupField json "arch"  
	val name = asString $ lookupField json "name"  
	val regs = map asString (asArray $ lookupField json "regs")
	val decl = map asString (asArray $ lookupField json "decl")
	val mem = map asString (asArray $ lookupField json "mem")
	val progs = map asString (asArray $ lookupField json "prog")
	val final = asString $ lookupField json "final"
    in (arch, name, regs, decl, mem, progs, final) end
  | get_json_data (Json.ERROR _) = raise CouldNotParseJsonFile
		  
fun regs_of_prog prog =
    let
	val term_EVAL = rhs o concl o EVAL
	val bvars = strip_set $ term_EVAL “bmc_varset_of_program ^prog”
	val regs = filter (is_BType_Imm o snd)$ map dest_BVar bvars
	fun f (x,y) = (fromHOLstring x, size_of_bir_immtype_t $ dest_BType_Imm y)
    in map f regs end;

fun parse text =
    let
	val jsontext = parse_litmus text
	(* Split text into sections *)
	val json = Json.parse jsontext
	val (arch, name, regs, decl, mem, progs, final) = get_json_data json
	(* Parse the program section, create one bir_program per processes *)
	val progs = parse_prog arch progs 
	(* Get registers used by each program *)
	val progs_regs = map regs_of_prog progs
	(* Parse init section, get initial bir memory and thread environments *)
	val regs = parse_regs arch regs progs_regs
	(* Parse the constraint, returns a predicate for a set of bir states *)
	val final = parse_final final decl
	val mem = parse_mem mem decl
    in
	{arch=arch,
	 name=name,
	 regs=regs,
	 mem=mem,
	 progs=progs,
	 final=final}
    end
end (* herdLitmusLib *)

(*
val file = "/opt/litmus-tests-riscv/tests/non-mixed-size/BASIC_2_THREAD/S.litmus"
val file = "/opt/litmus-tests-riscv/tests/non-mixed-size/BASIC_2_THREAD/SB+fence.rw.rw+po.litmus"
val text = bir_fileLib.read_from_file file
val jsontext = parse_litmus text
(* Split text into sections *)
val json = Json.parse jsontext
val (arch, name, regs, decl, mem, progs, final) = get_json_data json
(* Parse the program section, create one bir_program per processes *)
val prog = hd (parse_prog arch progs)

val bvars = strip_set $ term_EVAL “bmc_varset_of_program ^prog”
*)
