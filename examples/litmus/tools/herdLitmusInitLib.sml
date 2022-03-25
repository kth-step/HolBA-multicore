signature herdLitmusInitLib =
sig
    include Abbrev
    (* Arguments: Init section, registers used by each program
       Returns: BIR environments for memory and threads *)
    val parse_init : string list -> (string * int) list list -> term list
end


structure herdLitmusInitLib : herdLitmusInitLib =
struct
(* Parse the init section *)
open HolKernel Parse boolLib bossLib

open stringSyntax numSyntax wordsSyntax combinSyntax
open pairSyntax optionSyntax listSyntax

open bir_immSyntax bir_envSyntax bir_valuesSyntax

open UtilLib herdLitmusValuesLib
open Listsort
	 
exception ParseException of string

fun padd_regs (init_regs, prog_regs) =
    let
	val defaults = map (fn (x,_) => (x, "0")) prog_regs
	fun eq_tid_reg ((x,_),(y,_)) = x = y
    in
	(* Merge regs and default_regs, keep the first tuple only *)
	nubBy eq_tid_reg (init_regs @ defaults)
    end

fun find_reg_size r prog_regs = 
    case List.find (fn x => fst x = r) prog_regs
     of SOME (r, sz) => sz
      | NONE => 64
		      
fun split_eq rv = 
    case String.tokens (fn c => c = #"=") rv 
     of [r, v] => (r, v)
      | _ => raise (ParseException $ "Could not parse register assignment "^rv);

fun norm_reg r =
    let 
	val translate = [("x1","ra"), ("x2","sp"), ("x3","gp"), ("x4","tp"), ("x5","t0"), 
			 ("x6","t1"), ("x7","t2"), ("x8","s0"), ("x7","fp"), ("x9","s1"), 
			 ("x10","a0"), ("x11","a1"), ("x12","a2"), ("x13","a3"), 
			 ("x14","a4"), ("x15","a5"), ("x16","a6"), ("x17","a7"), 
			 ("x18","s2"), ("x19","s3"), ("x20","s4"), ("x21","s5"), 
			 ("x22","s6"), ("x23","s7"), ("x24","s8"), ("x25","s9"), 
			 ("x26","s10"), ("x27","s11"), ("x28","t3"), ("x29","t4"), 
			 ("x30","t5"), ("x31","t6")]
    in case (List.find (fn (_,y) => y = r) translate)
	of SOME (x,_) => x
	 | NONE => r
    end

(* Make BIR environment for a thread *)
(* regs is a list of assignments (string * string), where the first string is the register name and the second is its initial value *)
(* prog_regs is a list register sizes (string * int), first string is the register name and the second is the size of the value,e.g., 64-bit *)
fun mk_thd_env (regs, prog_regs) =
    let
	(* Finds the imm size of r from prog_regs and returns immediate v with that size *)
	fun mk_imm r v = 
	    let 
		val sz = find_reg_size r prog_regs
	    in gen_mk_Imm $ word_of_string v sz end
	fun str2term (r, v) =
	    let val r' = norm_reg r 
	    in (fromMLstring r', mk_some (mk_BVal_Imm(mk_imm r' v))) end
	val list_mk_update = foldl (fn(r,e) => mk_comb(mk_update r, e))
	val empty = “(K NONE) : string -> bir_val_t option”
	val regs_hol = map str2term regs
	val env = list_mk_update empty regs_hol
    in env end
	
fun parse_init init_regs prog_regs =
    let
	(* Give register from program default values, 0 *)
	val default_regs = map (map (fn (r,sz) => (r, "0"))) prog_regs
	(* Split the init_regs on ";" *)
	val init_regs' = map (String.tokens (fn c => c = #";")) init_regs
	(* Split on = *)
	val init_regs'' = map (map split_eq) init_regs'
	(* Merge default values and initial values *)
	val init_regs''' = map padd_regs (zip init_regs'' default_regs)
	(* Make BIR environ *)
	val thd_envs = map mk_thd_env (zip init_regs''' prog_regs)
    in thd_envs end
	
(*
val init_regs = ["a1=x;a2=y;a3=z;a4=t;a0=lock", "a1=x;a2=y;a3=z;a4=t;a0=lock;a5=a"]
val prog_regs = [[("a0",64),("a1",64),("a2",64),("a3",64),("a4",64),("a5",32)],[("a0",64),("a1",64),("a2",64),("a3",64),("a4",64),("a5",64)]]
val v = parse_init init_regs prog_regs
*)
end
