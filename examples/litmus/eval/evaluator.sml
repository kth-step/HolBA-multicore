open HolKernel bossLib boolLib Parse Drule;

open wordsTheory
open bir_promisingEvalTheory;

open bslSyntax pairSyntax numSyntax listSyntax
open bir_programSyntax

open computeLib
open herdLitmusValuesLib
open litmusInterfaceLib
	 
open wordsLib stringLib;

val LITMUS_CONSTANT_THM = DB.fetch "litmus_lifter" "LitmusConstants"

val _ = add_thms (CONJUNCTS LITMUS_CONSTANT_THM) the_compset;
val _ = add_words_compset true the_compset;

val _ = add_thms [WORD_ADD_0] the_compset;

val term_EVAL = rhs o concl o EVAL

(* Make cores *)
fun mk_cores programs environs t =
    let
	fun loop n [] = []
	  | loop n ((p,e)::l) = 
	    let val cid = term_of_int n;
		val s = “bmc_state_init ^p with <| 
                    bst_environ := BEnv ^e;
					bst_coh := \x. ^t
                  |>”;
		val core = term_EVAL “(^cid, ^p, ^s)”
	    in core::loop (n+1) l end;
	val cores = loop 0 (zip programs environs)
    in mk_list (cores, type_of (hd cores)) end;

(* Promise mode execution *)
fun promiseRun arch fuelTerm coresAndInitMemory =
    let
	    val newCoresAndMemory = term_EVAL “eval_promise_phase ^arch ^fuelTerm ^coresAndInitMemory”;
    in newCoresAndMemory end;

fun localRun arch fuelTerm coresAndMemory = 
    term_EVAL “LIST_BIND (^coresAndMemory) (eval_local_phase ^arch ^fuelTerm)”


Definition get_regs_and_mem:
    (get_regs_and_mem (ss,M) =
    let
        default = (K (SOME (BVal_Imm (Imm32 0w))));
        mem = FOLDL (λt m. t (|m.loc |-> SOME m.val|)) default M;
        regs = MAP (λs. case s.bst_environ of BEnv f => f) ss
    in (mem, regs))
End

fun getRegistersAndMemory coresAndMemory =
    term_EVAL “MAP get_regs_and_mem ^coresAndMemory”

fun to_exec_mem_msg_t mem =
    “MAP (\m. <| val:=m.val; cid:=1024; loc:=m.loc |>)^mem”
exception LoadLitmusError;
exception ExecLitmusError;
    
fun get_litmus filename =
    if String.isSuffix ".json" filename 
    then load_litmus filename
    else if String.isSuffix ".litmus" filename
    then lift_herd_litmus filename
    else raise LoadLitmusError;

fun final_check check regsMem =
    fromHOLstring $ term_EVAL 
    “if ^regsMem = [] then "Error"
     else if ^check ^regsMem
     then "Ok" else "No"”;

fun run_litmus fuel (litmus:litmus) =
   let 
       val arch = if #arch litmus = "RISCV" then ``RISCV`` else ``ARMv8``;
       (* Fuel used for promise and non-promise execution *)
       val fuelTerm = term_of_int fuel;
       (* Get the initial memory *)
       val initMemory = to_exec_mem_msg_t (#mem litmus);
       (* Set default state *)
       val cores = mk_cores (#progs litmus) (#regs litmus) (“LENGTH ^initMemory”);
       (* Initial State *)
       val initialState = mk_pair (cores, initMemory);
       (* Make promise run *)
       val promisedState = promiseRun arch fuelTerm initialState;
       (* Make local run *)
       val finalState = localRun arch fuelTerm promisedState;
       (* Get registers and memory *)
       val regsMemory = getRegistersAndMemory finalState;
       val expected = #expected litmus
    in 
        (final_check (#final litmus) regsMemory, expected)
    end;


fun main () =
    let
	val arguments = CommandLine.arguments ();
	val length     = List.length arguments;
	val inputfile  = List.nth (arguments, length-2);
	val outputfile = List.nth (arguments, length-1);
	val litmus    = get_litmus inputfile;
    val filename  = #filename litmus;
	val (result, expected) = run_litmus 64 litmus;
    val res_string = (filename ^ "\t" ^ result ^ "\t" ^ expected ^ "\n")
    in 
	    bir_fileLib.write_to_file outputfile res_string
    end;

val () = (
    PolyML.export ("evaluator.o", main);
    Unix.execute ("./polyc.sh", ["evaluator.o", "-o", "evaluator.out"]);
    Unix.exit (Word8.fromInt 0)
);


(* 
val filename = "../tests/riscv/BASIC_2_THREAD/LB.json";
val litmus = get_litmus filename
val fuel = 64;
val res = run_litmus fuel litmus
*)
