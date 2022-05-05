open wordsTheory
open bir_promisingTheory;

open bslSyntax pairSyntax numSyntax listSyntax
open bir_programSyntax

open computeLib
open herdLitmusValuesLib
open litmusInterfaceLib
	 
open wordsLib stringLib;


val _ = add_thms (CONJUNCTS LITMUS_CONSTANT_THM) the_compset;
val _ = add_words_compset true the_compset;

val term_EVAL = rhs o concl o EVAL

(* Make cores *)
fun mk_cores programs environs t =
    let
	fun loop n [] = []
	  | loop n ((p,e)::l) = 
	    let val cid = term_of_int n;
		val s = “bir_state_init ^p with <| bst_environ := BEnv ^e;
						   bst_coh := \x. ^t|>”;
		val core = term_EVAL “ExecCore ^cid ^p ^s T”
	    in core::loop (n+1) l end;
	val cores = loop 0 (zip programs environs)
    in mk_list (cores, “:exec_core_t”) end;

(* Promise mode execution *)
fun promiseRun fuelTerm coresAndInitMemory =
    let
	val newCoresAndMemory = term_EVAL “eval_pmstepsO1 ^fuelTerm (^fuelTerm * 8) ^coresAndInitMemory”;
	val (l, ty) = dest_list newCoresAndMemory;
    in l end;

local
    fun nonPromiseRunAux fuel memory core =
	let val term = “eval_clsteps_coreO1 ^fuel ^core ^memory”;
	    val term' = “FILTER eval_finished_ecore ^term”;
	in fst (dest_list(term_EVAL term')) end;

    (* Cartesian product *)
    fun cartProd [] = []
      | cartProd [h] = map (fn e => [e]) h
      | cartProd (h::l) = 
	let val l' = cartProd l in 
	    List.concat $ map (fn x => map (fn y => y::x) h) l'
        end;
in
fun nonPromiseRun fuel coresAndMemory =
    (* Non-promise mode execution *)


    let
	val (cores, memory) = dest_pair coresAndMemory;
	val (cores', core_ty) = dest_list cores;
	val coress = map (nonPromiseRunAux fuel memory) cores';
	val coress' = map (fn cs => mk_list(cs,core_ty)) (cartProd coress)
    in map (fn cs => mk_pair(cs,memory)) coress' end;
end

fun getRegistersAndMemory coresAndMemory =
    let
	val (cores, memory) = dest_pair coresAndMemory
	val regs = “MAP (\t. case t of (ExecCore _ _ s _) => case s.bst_environ of BEnv f => f) ^cores”
	val default_mem = “SOME (BVal_Imm (Imm32 0w))”;
	val memory_filtered = “FILTER (\m. m.succ) ^memory”;
	val memory' = “FOLDL (\t m. t (|m.loc |-> SOME m.val|)) (K ^default_mem) ^memory_filtered”;
    in term_EVAL $ mk_pair (memory', regs) end;

fun to_exec_mem_msg_t mem =
    “MAP (\m. <| val:=m.val; cid:=1024; loc:=m.loc; succ:=T; n:=0 |>)^mem”
exception LoadLitmusError;
exception ExecLitmusError;
    
fun get_litmus filename =
    if String.isSuffix ".json" filename 
    then load_litmus filename
    else if String.isSuffix ".litmus" filename
    then lift_herd_litmus filename
    else raise LoadLitmusError;

fun run_litmus fuel (litmus:litmus) =
   let 
       (* Fuel used for promise and non-promise execution *)
       val fuelTerm = term_of_int fuel;
       (* Get the initial memory *)
       val initMemory = to_exec_mem_msg_t (#mem litmus);
       (* Set default state *)
       val cores = mk_cores (#progs litmus) (#regs litmus) (“LENGTH ^initMemory”);
       (* Make promise only run *)
       val coresAndPromises = promiseRun fuelTerm (mk_pair(cores,initMemory));
       (* Make non-promising runs *)
       val coresAndPromisesFinal = List.concat (map (nonPromiseRun fuelTerm) coresAndPromises);
       (* Get the final states of registers and memory *)
       val finalStates = map getRegistersAndMemory coresAndPromisesFinal
       val finalStatesTerm = mk_list(finalStates, 
				     “:(bir_val_t -> bir_val_t option) # ((string -> bir_val_t option) list)”);
       val final = #final litmus
       (* Testing of post-condition *)
       val finalTest = term_EVAL “^final ^finalStatesTerm”
    in 
	if null finalStates then
	    (* If we have no states, exit *)
	    raise ExecLitmusError
	else
	    fromHOLstring $ term_EVAL “if ^finalTest then "Ok" else "No"”
    end;

(* 
fun getStatesAndMemory coresAndMemory = 
    let
        val (cores, memory) = dest_pair
	val states = “MAP (\t. case t of (Core cid p s) => s) ^cores”
     in (states, memory)

val filename = "./tests/BASIC_2_THREAD/LB.json";			(* Expected No *)
val filename = "./tests/ATOMICS/CO/2+2W+fence.rw.rws+pospx.litmus"; 	(* Expected No *)
val filename = "./tests/CO/R+poss.json";				(* Expected No *)
val filename = "./tests/ATOMICS/CO/CoWR0+fence.rw.rwsxx.json";		(* Expected No *)
val filename = "./tests/HAND/ISA-Rel-Acq.litmus";
val filename = "./tests/HAND/C-Will02+HEAD.litmus";
val filename = "./tests/HAND/ISA01.litmus";
val filename = "./tests/HAND/ISA13.litmus";
val filename = "./tests/HAND/ISA-DEP-CTRL.litmus";

val litmus = get_litmus filename
val fuel = 64;
val res = run_litmus fuel litmus
*)

fun main () =
    let
	val arguments = CommandLine.arguments ();
	val filename  = List.last arguments;
	val litmus    = get_litmus filename
	val result    = run_litmus 64 litmus
    in 
	print $ filename ^ "\t" ^ result ^ "\n" 
    end;

