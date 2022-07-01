signature herdLitmusFinalLib =
sig
    include Abbrev
    (* Argument: Final/Constraint section
       Returns: Predicate on bir_environments *)
    val parse_final : string -> (string list) -> term
end

structure herdLitmusFinalLib : herdLitmusFinalLib =
struct
open HolKernel Parse boolLib bossLib;

open stringSyntax numSyntax wordsSyntax listSyntax;

open bir_immSyntax bir_envSyntax bir_valuesSyntax;

open UtilLib herdLitmusValuesLib;

(* The tokenizer and parser is based on the functional parser
   from 'ML for the Working Programmer, Chapter 9'. *)

datatype parse_tree = AND of parse_tree * parse_tree
		    | OR of parse_tree * parse_tree
		    | NOT of parse_tree
		    | FORALL of parse_tree
		    | EXISTS of parse_tree
		    | REG of int * (string * string)
		    | MEM of string * string
		    | TRUE
		    | FALSE

(* TOKENIZER *)
datatype token = SYM of string | ID of string | NUM of int | ERR

val alphas = ["T", "F"]
val symbols = ["?", "!", "~", "&", "|", "(", ")", ":", "="]

(* Make numeric token *)
val numTok = NUM o valOf o Int.fromString

(* Make an alphanumeric token *)
fun alphaTok a =
    if member (a, alphas)
    then SYM a
    else ID a

fun symbolic (sy, ss) =
    case Substring.getc ss
     of NONE => (SYM sy, ss)
      | SOME(c, ss1) =>
	if member (sy, symbols) orelse not (Char.isPunct c)
	then (SYM sy, ss)
	else symbolic (sy ^ String.str c, ss1)

(* Scan substring and making token list *)
fun scanning (toks, ss) =
    case Substring.getc ss
     of NONE => rev toks (* Done. *)
      | SOME (c,ss1) => 
	if Char.isDigit c
	then (* number *)
	    let val (num, ss2) = Substring.splitl Char.isDigit ss
		val tok = numTok (Substring.string num)
	    in scanning (tok::toks, ss2)
	    end
	else if Char.isAlphaNum c
	then (* identifier *)
	    let val (id, ss2) = Substring.splitl Char.isAlphaNum ss
		val tok = alphaTok (Substring.string id)
	    in scanning (tok::toks, ss2)
	    end
	else if Char.isPunct c
	then (* special symbol *)
	    let val (tok, ss2) = symbolic (String.str c, ss1)
	    in scanning (tok::toks, ss2)
	    end
	else (* non-printable characters *)
	    scanning (toks, Substring.dropl (not o Char.isGraph) ss)

fun scan a = scanning([], Substring.full a)

(* PARSER *)
exception SyntaxErr of string
infixr 6 $--
infixr 5 --
infix 3 >>
infix 0 ||

(* Identifier *)
fun id (ID x::xs) = (x, xs)
  | id _ = raise SyntaxErr("Expected id")

(* Number *)
fun num (NUM x::xs) = (x, xs)
  | num _ = raise SyntaxErr("Expected num")
		  
(* Symbol *)
fun sym a (SYM x::xs) =
    if a = x then (x, xs) else raise SyntaxErr ("Expected "^a)
  | sym a _ = raise SyntaxErr ("Expected "^a)

(* Concatenation *)
fun (ph1 -- ph2) xs =
    let val (x, xs') = ph1 xs
	val (y, xs'') = ph2 xs'
    in ((x,y), xs'') end
	
(* Alternative *)
fun (ph1 || ph2) xs = ph1 xs
		      handle SyntaxErr _ => ph2 xs
(* Application *)
fun (ph >> f) xs =
    let val (x, xs') = ph xs
    in (f x, xs') end

(* Must satisfy *)
fun !!ph xs = ph xs
	      handle SyntaxErr msg => raise Fail ("Syntax error: " ^msg)

(* Symbol followed by some expression *)
fun (a $-- ph) xs = ((sym a -- !!ph) >> snd) xs

fun empty a xs = (a, xs)

(* Scan the token stream ‘a’ with grammar ‘ph’ *)
fun reader ph a =
    case ph (scan a)
     of (x, []) => x
      | (_, l) => raise SyntaxErr "Extra characters in phrase"

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

(* FORALL || EXISTS *)
fun quant xs = ("!" $-- expr >> FORALL || 
                "?" $-- expr >> EXISTS) xs

(* OR *)
and expr xs = (term -- ("|" $-- expr || empty FALSE) >> OR) xs

(* AND *)
and term xs = (factor -- ("&" $-- term || empty TRUE) >> AND) xs
							
(* NOT || () *)
and factor xs = ("(" $-- expr -- (sym ")") >> fst
		     || "~" $-- expr >> NOT
		     || atom) xs

(* MEM || REG *)
and atom xs = ((id -- "=" $-- var >> MEM)
		   || num -- ":" $-- id -- "=" $-- var >> REG 
		   || "T" $-- empty TRUE
		   || "F" $-- empty FALSE) xs

(* Variable (will become word type) *)
and var xs = (id || num >> Int.toString) xs
					 
fun parse_tree_to_term TRUE _ = “T”
  | parse_tree_to_term FALSE _ = “F”
  | parse_tree_to_term (EXISTS pt) var_size = 
    let 
	val t = parse_tree_to_term pt var_size
    in 
	“EXISTS (\(M:bir_val_t -> bir_val_t option,TS:(string -> bir_val_t option) list). ^t)” 
    end
  | parse_tree_to_term (FORALL pt) var_size = 
    let 
	val t = parse_tree_to_term pt var_size
    in 
	“EVERY (\(M:bir_val_t -> bir_val_t option,TS:(string -> bir_val_t option) list). ^t)” 
    end
  | parse_tree_to_term (AND(pt,pt')) var_size = 
    let val t = parse_tree_to_term pt var_size
    val t' = parse_tree_to_term pt' var_size
    in “^t /\ ^t'” end
  | parse_tree_to_term (OR(pt,pt')) var_size = 
    let val t = parse_tree_to_term pt var_size
    val t' = parse_tree_to_term pt' var_size
    in “^t \/ ^t'” end
  | parse_tree_to_term (NOT(pt)) var_size = 
    let val t = parse_tree_to_term pt var_size
    in “~(^t)” end
  | parse_tree_to_term (REG(tid,(reg,value))) _ = 
    let
	val htid = term_of_int tid
	val hreg = fromMLstring (norm_reg reg)
	val hvalue = mk_Imm64 (word_of_string value 64)
    in
	“(EL ^htid TS) ^hreg = SOME (BVal_Imm ^hvalue)”
    end
  | parse_tree_to_term (MEM(addr,value)) var_size = 
    let
	fun f v n = mk_BVal_Imm $ gen_mk_Imm $ word_of_string v n
	val haddr = f addr 64
	val hvalue = f value (var_size addr)
    in
	“M ^haddr = SOME ^hvalue”
    end
	
fun find_var_size decl =
    let
	fun f d =
	    (case String.tokens (fn c => c = #" ") d of
		 [size, var] => (case Int.fromString size of
				     SOME isize => (var,isize)
				   | NONE =>  raise (SyntaxErr ("Declaration "^ d ^ "could not be parsed")))
	       | _ => raise (SyntaxErr ("Declaration "^ d ^ "could not be parsed")))
	fun find_size d var = 
	    (case List.find (fn (v,s) => v = var) d of
		SOME (v,s) => s
	      | NONE => 32)
    in find_size (map f decl) end
	
			      

(* Parse the final expression *)
fun parse_final final_sec decl =
    let val t = reader quant final_sec
        val var_size = find_var_size decl
    in (rhs o concl o EVAL) (parse_tree_to_term t var_size) end
end

(*
val x = "?((0:t0=0&1:t0=0|x=32&y=54))&((0:t2=0&1:t2=0)&(0:t4=0&1:t4=0))"

val t = parse_final x ["64 x", "32 y"]
*)
