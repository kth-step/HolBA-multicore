signature herdLitmusProgLib =
sig
    include Abbrev
    (* Argument: Program section
       Returns: List of BIR programs *)
    val parse_prog : string -> string -> term list
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
fun compile_and_disassemble arch prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [arch])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

(* Replace the nop with Halt *)
fun patch_halt prog =
  let
    val prog_l = bir_programSyntax.dest_BirProgram prog;
    val (blocks,ty) = dest_list prog_l;
    val obs_ty = (hd o snd o dest_type o hd o snd o dest_type) ty;
    val (lbl,_,_,_) = bir_programSyntax.dest_bir_block (List.last blocks);
    val new_last_block =  bir_programSyntax.mk_bir_block
              (lbl, bir_programSyntax.bir_mc_tags_NONE, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
               ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);

    val blocks' = (List.take (blocks, (List.length blocks) - 1))@[new_last_block];
  in
    bir_programSyntax.mk_BirProgram (mk_list (blocks',ty))
  end;

local
	val i = ref 1
in
fun lift_prog arch prog =
    let
	(* Create a DA file, also put nop at end *)
	val da_file = compile_and_disassemble arch (prog ^ "\nnop\n")
	(* Lift the DA file *)
	val prog_name = "litmus" ^ Int.toString (!i)
	val _ = i := !i + 1
	val _ = case arch of
		  "RISCV" => lift_da_and_store_mc_riscv prog_name da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
		| "AArch64" => lift_da_and_store_mc prog_name da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
		| _ => raise Fail ("Unsupported architecture: " ^ arch)
	
	(* Fetch the Program definition *)
	val bir_litmus_tmp_prog_def = DB.fetch "-" ("bir_" ^ prog_name ^ "_prog_def")
    in (* Return the program term *)
	(rhs o concl) bir_litmus_tmp_prog_def
    end
end	

fun tokens p s = 
    let
	val length = String.size s
	fun tok i j =
	    if j = length then
		[String.substring (s, i, j-i)]
	    else if p (String.sub (s,j)) then
		String.substring (s, i, j-i) :: tok (j+1) (j+1)
	    else tok i (j+1)
    in tok 0 0 end

fun findSubstring ss s =
    let
	val s' = ref (Substring.full s)
	fun P s ss = String.size ss <= Substring.size s
    in
	while (P (!s') ss andalso not (Substring.isPrefix ss (!s'))) do 
	      s' := Substring.triml 1 (!s');
	if P (!s') ss 
	then SOME (String.size s - Substring.size (!s'))
	else NONE
    end;

fun replaceSubstring (ss, ss') s =
    case findSubstring ss s of
	SOME idx =>
	let
	    val len = String.size s
	    val idx' = idx + String.size ss
	in 
	    String.substring(s, 0, idx) 
	    ^ ss'
	    ^ String.substring(s, idx', len - idx')
	end
      | NONE => s;
    


fun fix_atomic_aqrl s =
  if String.isSubstring "aq.rl" s 
  then replaceSubstring ("aq.rl", "aqrl") s
  else s


fun parse_prog arch prog_sec =
  let
		val _ = print ("Lifting programs... \n")
	  fun split c = tokens (eq c)
	  val stmts = transpose (map (split #"|") (tl (split #";" prog_sec))) ""
	  val stmts = map (map fix_atomic_aqrl) stmts
	  val progs = map (String.concatWith "\n") stmts
	  val bir_progs = map (lift_prog arch) progs
		val _ = print ("Done!\n")
  in 
	  bir_progs 
	end

end

(*

val prog_sec = 
 "P0          | P1            | P2          | P3             ;"^
 "sw x5,0(x6) | lw x5,0(x6)   | sw x5,0(x6) | lw x5,0(x6)    ;"^
 "            | xor x7,x5,x5  |             | bne x5,x0,LC00 ;"^
 "            | add x10,x9,x7 |             | LC00:          ;"^
 "            | sw x8,0(x10)  |             | fence.i        ;"^
 "            |               |             | sw x7,0(x8)    ;";

val prog = last $ herdLitmusProgLib.parse_prog prog_sec "RISCV";
*)
