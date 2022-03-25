signature herdLitmusLib =
sig
    include Abbrev
    type litmus = {arch:string,
		   name:string,
		   regs: term list,
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

type litmus = {arch:string,
	       name:string,
	       regs: term list,
(*	       mem: term list, *)
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
	val mem = map asString (asArray $ lookupField json "mem")
	val progs = map asString (asArray $ lookupField json "prog")
	val final = asString $ lookupField json "final"
    in (arch, name, regs, mem, progs, final) end
  | get_json_data (Json.ERROR _) = raise CouldNotParseJsonFile
		  
fun regs_of_prog prog =
    let
	val term_EVAL = rhs o concl o EVAL
	val bvars = strip_set $ term_EVAL “bir_varset_of_program ^prog”
	val regs = filter (is_BType_Imm o snd)$ map dest_BVar bvars
	fun f (x,y) = (fromHOLstring x, size_of_bir_immtype_t $ dest_BType_Imm y)
    in map f regs end;

fun parse text =
    let
	val jsontext = parse_litmus text
	(* Split text into sections *)
	val json = Json.parse jsontext
	val (arch, name, regs, mem, progs, final) = get_json_data json
	(* Parse the program section, create one bir_program per processes *)
	val progs = parse_prog progs 
	(* Get registers used by each program *)
	val progs_regs = map regs_of_prog progs
	(* Parse init section, get initial bir memory and thread environments *)
	val regs = parse_init regs progs_regs
	(* Parse the constraint, returns a predicate for a set of bir states *)
	val final = parse_final final
    in
	{arch=arch,
	 name=name,
	 regs=regs,
(*	 mem=[], *)
	 progs=progs,
	 final=final}
    end
end (* herdLitmusLib *)
