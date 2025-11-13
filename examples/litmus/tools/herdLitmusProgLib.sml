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
open bslSyntax;
open UtilLib;

val SOURCE_DIR = valOf (Posix.ProcEnv.getenv ("PWD"))


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
