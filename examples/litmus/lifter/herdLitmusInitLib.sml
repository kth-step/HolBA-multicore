signature herdLitmusInitLib =
sig
    include Abbrev
    (* Arguments: Init section, registers used by each program
       Returns: BIR environments for memory and threads *)
    val parse_init : string -> string -> (string * int) list list -> term list
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
	 
fun fst2 ((x,_),(y,_)) = (x,y)

fun snd2 ((_,x),(_,y)) = (x,y)

(* Get individual tokens *)
fun tokenize init_sec =
    let
	fun f x = (x = #";" orelse x = #"{" orelse x = #"}")
	val assigns = String.tokens f init_sec
    in map (trim Char.isSpace) assigns end

local
	fun aarch64 reg =
		if String.isPrefix "W" reg orelse String.isPrefix "X" reg then
			"R" ^ String.extract (reg, 1, NONE)
		else
			reg
	fun riscv reg = reg;
in

fun normalize arch (r, sz) =
	  case arch of
	    "AArch64" => (aarch64 r, sz)
	  | "RISCV" => (riscv r, sz)
	  | _ => raise Fail ("Unsupported architecture: " ^ arch)
end

(* Split initial assignments of memory and thread *)
fun partition arch assigns =
    let
	fun mk_reg (t,r,v) = (valOf $ Int.fromString t,normalize arch (r,v))
	fun loop [] = ([], [])
	  | loop (x::xs) =
	    let val (mem, thds) = loop xs
	    in (case split (eq #"=") x
		 of SOME(l, v) =>
		    (case split (eq #":") l
		      of SOME (t, r) =>
			 (mem,mk_reg (t,r,v)::thds)
		       | NONE => ((l,v)::mem, thds))
		  | NONE => raise Fail "Expected assignment")
	    end
    in loop assigns end

(* Pad missing registers with default value 0 *)

fun padd_regs regs prog_regs =
    let
	fun mk_defaults ([],_) = []
	  | mk_defaults (regs::rest,n) =
	    map (fn r => (n,(r,"0"))) regs @ mk_defaults (rest,n+1)
	val defaults = mk_defaults (prog_regs, 0)
	fun eq_tid_reg a = (op= o fst2) a andalso (op= o fst2 o snd2) a
    in
	(* Merge regs and default_regs, keep the first tuple only *)
	nubBy eq_tid_reg (regs @ defaults)
    end

(* Group register initial values by their threads *)
fun group_regs regs =
    let
	val sorted = sort (Int.compare o fst2) regs
	val grouped = groupBy (op= o fst2) sorted
    in map (map snd) grouped end

(* Make BIR environment for memory *)
fun mk_mem_env mem =
    let
	fun f s = mk_BVal_Imm (mk_Imm64 (word_of_string s 64))
	val mem' = map (fn (x,y) => (f x, f y)) mem
	val mem'' = map (fn (x,y) => “<| cid:=0; loc := ^x; val := ^y |>”) mem'
    in mk_list(mem'', “:mem_msg_t”) end

(* Make BIR environment for a thread *)
fun mk_thd_env (regs, prog_regs) =
    let
	fun f r v = 
	  let 
		val sz = snd $ valOf $ List.find (fn x => fst x = r) prog_regs
	  in 
		gen_mk_Imm $ word_of_string v 64
	  end
	fun str2term (r,v) = (fromMLstring r, mk_some (mk_BVal_Imm(f r v)))
	val list_mk_update = foldl (fn(r,e) => mk_comb(mk_update r, e))
	val empty = “(K NONE) : string -> bir_val_t option”
	val regs_hol = map str2term regs
	in list_mk_update empty regs_hol end
	
fun parse_init arch init_sec progs_regs =
    let
	val _ = print ("Parsing init section... \n")
	val assigns = tokenize init_sec
	val _ = print ("tokenizing...\n")
	val (mem, regs) = partition arch assigns
	val _ = print ("partitioning...\n")
	val progs_regs_names = map (map fst) progs_regs
	val grouped_regs = group_regs (padd_regs regs progs_regs_names)
	val _ = print ("grouping registers...\n")
	val thd_envs = map mk_thd_env (zip grouped_regs progs_regs)
	val _ = print ("making thread environments...\n")
	val mem_env = mk_mem_env mem
	val _ = print ("making initial memory\n")
	val _ = print ("Done!\n")
    in
	thd_envs
    end
end
