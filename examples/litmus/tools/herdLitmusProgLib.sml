signature herdLitmusProgLib =
sig
    include Abbrev
    (* Argument: Program section
       Returns: List of BIR programs *)
    val parse_prog : string list -> term list
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

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

fun lift_prog prog =
    let
	(* Create a DA file, also put nop at end *)
	val da_file = compile_and_disassemble (prog ^ "\nnop\n")
	(* Lift the DA file *)
	val _ = lift_da_and_store_mc_riscv "litmus_tmp" da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
	(* Fetch the Program definition *)
	val bir_litmus_tmp_prog_def = DB.fetch "scratch" "bir_litmus_tmp_prog_def"
    in (* Return the program term *)
	(rhs o concl) bir_litmus_tmp_prog_def
    end
	
fun typed_prog p = inst [“:'observation_type” |-> Type`:string`] p;

fun parse_prog prog_list =
    let
	val bir_progs = map (typed_prog o lift_prog) prog_list
    in bir_progs end
end

(*
open listSyntax bir_programSyntax;
val prog_list = ["ori x5,x0,1\nsw x5,0(x6)\nfence w,w\nori x7,x0,1\nsw x7,0(x8)", "lw x5,0(x6)\nbeq x5,x0,LC00\nori x7,x0,1\nsw x7,0(x8)\nlw x9,0(x8)\nandi x10,x9,128\nadd x13,x12,x10\nlw x11,0(x13)\nLC00:"]
val prog2 = last $ parse_prog example

*)
