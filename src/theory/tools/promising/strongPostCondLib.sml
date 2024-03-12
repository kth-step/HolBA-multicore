(*
  automate post condition generation for given program
*)

structure strongPostCondLib :> strongPostCondLib =
struct

open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_promisingTheory
     bir_programLib bir_promising_wfTheory;

(*
open wordsTheory bitstringTheory llistTheory wordsLib
     finite_mapTheory string_numTheory relationTheory
     bir_promising_wfTheory;
*)

val ERR = Feedback.mk_HOL_ERR "strongPostCondLib"
val WARN = HOL_WARNING "strongPostCondLib";

val is_fun_ty = can Type.dom_rng

(* destructs 'a -> 'b -> 'c to list ['a,'b,'c] *)
fun dest_fun_ty ty =
if not $ is_fun_ty ty then [ty] else
let val (dom,rng) = Type.dom_rng ty
in
  dom::dest_fun_ty rng
end

fun is_eq_tm x y = Term.compare(x,y) = EQUAL

fun list_mk_conj' ls = if null ls then ``T`` else boolSyntax.list_mk_conj ls

(* lookup value val for given key from list of pairs (key,val) *)
fun lookup cmp ls = Option.map snd $ List.find (cmp o fst) ls

(*
open binary_ieeeTheory
val tm = TypeBase.mk_record (``:('a, 'b) float``,[("Sign",``0w:word1``)])
val typ = type_of tm
type_of tm
val acc = "Sign"
type_of $ acc_fn "Sign" $ type_of tm
EVAL $ mk_icomb (acc_fn "Sign" $ type_of tm, tm)
*)
val acc_fn =
  fn acc =>
    #accessor o Option.valOf o lookup (curry op = acc) o TypeBase.fields_of
(*
map fst $ TypeBase.fields_of ``:bir_state_t``
*)

fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ [y] end
  handle HOL_ERR _ => [tm];

(*
any property is maintained by jumps
bir_exec_stmt_jmp_bst_eq
bir_exec_stmt_cjmp_mc_invar
*)

(*
Theorem bgcs_cjmp:
  !p s s' v lbl1 lbl2 cond_e.
  bir_get_current_statement p s.bst_pc =
    SOME $ BSGen $ BStmtE $ BStmt_CJmp cond_e (BLE_Label lbl1) (BLE_Label lbl2)
  /\ bir_exec_stmt_cjmp p cond_e (BLE_Label lbl1) (BLE_Label lbl2) s = s'
  /\ bir_state_set_typeerror s <> s'
  /\ (!l. s'.bst_status <> BST_JumpOutside l)
  ==>
  ?v. bir_eval_exp cond_e s.bst_environ = SOME v
  /\ IS_SOME $ bir_dest_bool_val v
  /\ (bir_dest_bool_val v = SOME T ==> s'.bst_pc = bir_block_pc lbl1)
  /\ (bir_dest_bool_val v = SOME F ==> s'.bst_pc = bir_block_pc lbl2)
Proof
  rw[bir_state_set_typeerror_def,bir_exec_stmt_cjmp_def,AllCaseEqs()]
  >> fs[bir_exec_stmt_jmp_def,AllCaseEqs(),bir_eval_label_exp_def]
  >> fs[bir_exec_stmt_jmp_to_label_def,COND_RAND,COND_RATOR,bir_state_t_component_equality]
  >> cheat
QED
*)

(*
raise ERR "method" "message"
*)

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

(*

Definition dequeue_def:
  dequeue hd_addr tl_addr reg dequeue_entry jump_after = MAP BBlock_Stmts [
    <|bb_label := BL_Address $ Imm64 dequeue_entry;
      bb_statements := [
        BMCStmt_Load (BVar "R1" $ BType_Imm Bit64)
          tl_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 4w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 4w;
      bb_statements := [
        BMCStmt_Load (BVar "R2" $ BType_Imm Bit64)
          hd_addr
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 8w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 8w;
      bb_statements := [];
      bb_last_statement :=
        BStmt_CJmp
          (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "R1" (BType_Imm Bit64)))
              (BExp_Den (BVar "R2" (BType_Imm Bit64))))
          (BLE_Label $ BL_Address $ Imm64 dequeue_entry)
          (BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 12w)
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 12w;
      bb_statements := [
        BMCStmt_Load (BVar reg $ BType_Imm Bit64)
          (BExp_Den (BVar "R1" (BType_Imm Bit64)))
          (* TODO cast? *)
          (SOME (BIExp_SignedCast,Bit64)) F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 16w
    |>;
    <|bb_label := BL_Address $ Imm64 $ dequeue_entry + 16w;
      bb_statements := [
        BMCStmt_Store
          (BVar "success" $ BType_Imm Bit64)
          tl_addr
          (BExp_BinExp BIExp_Plus
            (BExp_Den $ BVar "R1" $ BType_Imm Bit64)
            (* TODO correct assumption on memory layout? *)
            (BExp_Const $ Imm64 64w))
          F F F
      ];
      bb_last_statement := BStmt_Jmp $ BLE_Label $ BL_Address $ Imm64 $ dequeue_entry + 20w
    |>
  ]
End

*)

(*
strip_union_insert ``{a; b} ∪ ({c; d} ∪ {} ∪ {e})``;
*)
fun strip_union_insert tm =
  if can pred_setSyntax.dest_insert tm
  then let
      val (h, t) = pred_setSyntax.dest_insert tm
    in
       [h] @ (strip_union_insert t)
    end
  else if can pred_setSyntax.dest_union tm
  then let
      val (h, t) = pred_setSyntax.dest_union tm
    in
      (strip_union_insert h) @ (strip_union_insert t)
    end
  else if same_const tm pred_setSyntax.empty_tm
    then []
  else raise ERR "strip_union_insert" "not an enumerated union set"

fun bir_stmts_prog_thm prog =
  EVAL $ mk_icomb(``bir_stmts_of_prog``,prog)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [listTheory.MAP_APPEND,bir_typing_progTheory.bir_stmts_of_block_def]
  |> strip_union_insert

fun bir_stmts_progs_thm prog =
  EVAL $ mk_icomb(``bir_stmts_of_progs``,prog)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [listTheory.MAP_APPEND,bir_typing_progTheory.bir_stmts_of_block_def]

(*

arguments: jump_head

- for given program obtain list of each label and index and the statement at (label,index)
- for each block label construct the fold over the block's indices and the
  effect of the statement

*)

(*
 * first step collection of constraints
 *)

(*
  data structure to hold the constraints
*)
datatype kind = Mem of Term.term | Reg of Term.term;
fun kind_cmp (a,b) =
  case (a,b) of
    (Mem a,Mem b) => Term.compare (a,b)
  | (Reg a,Reg b) => Term.compare (a,b)
  | (Reg _,Mem _) => LESS
  | (Mem _,Reg _) => GREATER
fun unregmem a = case a of Mem a => a | Reg a => a

type constr = { dependents : term list, constraint : term };
(* check if el is among the dependents of constr *)
fun dep_lookup (constr : constr) el =
  List.exists (is_eq_tm el) (#dependents constr)

(* match str against termarg and return list of arguments *)
(*
unpack "BMCStmt_Load" stmt
unpack "BMCStmt_Store" stmt
 *)
fun unpack str termarg =
let
  val stmt_args = list_dest dest_comb termarg
  val stmt_term = hd stmt_args
  val {Name = stmt_str,...} = Term.dest_thy_const stmt_term
in
  if str = stmt_str then tl stmt_args else []
end

fun is_term_true tm = is_eq_tm ``T`` tm
fun is_term_false tm = is_eq_tm ``F`` tm

(* returns conjunct of lbl_var equals addr and index_var equals index:num *)
fun addr_label_cj_index addr index =
let
  val index_term = numSyntax.mk_numeral (Arbnum.fromInt index)
  val index_var = mk_var("index", ``:num``)
  val lbl_var = mk_var("lbl", hd $ dest_fun_ty $ type_of ``Imm64`` )
in
  mk_conj(mk_eq(``BL_Address $ Imm64 $ ^lbl_var``,addr),mk_eq(index_var,index_term))
end

(* transform the constraints into a term *)
fun constrs_to_term (addr,index) constr cjmp_constr =
let
  val term =
    Redblackmap.foldl (fn (_,v,x) => mk_conj(x, #constraint (v :constr))) ``T`` constr
in
  mk_imp(addr_label_cj_index addr index,
    if null cjmp_constr then term else mk_conj(term,list_mk_conj $ map #constraint (cjmp_constr :constr list))
  )
end

(* filter path conditions if dependency has changed *)
fun filter_cjmp_constr cjmp_constr addrs =
  List.filter
    (fn x =>
      List.all
        (fn addr =>
          not (List.exists (is_eq_tm addr) (#dependents (x : constr ))))
        addrs)
    cjmp_constr

(*
term_to_string_args ``SOME c``
 *)
fun term_to_string_args tm =
let
  val args = list_dest dest_comb tm
  val hd_term = hd args
  val {Name = hd_str,...} = Term.dest_thy_const hd_term
in
  (hd_str,tl args)
end

(* updates tuple (mem,reg) according to stmt at pc where
 *   stmt is a statement
 *   pc is the current program counter
 *)
(* TODO whenever statement modifies any of the
 * dependents of earlier constraints, drop the earlier constraints *)
(*
val cjmp_constr = [{constraints = ``T``, dependents = [``BExp_Const a``]}]
val var = hd o #dependents $ hd cjmp_constr
BMCStmt_Load:
val var::exp::opt::acq::rel::_ = snd $ term_to_string_args stmt
BMCStmt_Store:
val succ_reg::address::value::xcl::acq::rel::_ = snd $ term_to_string_args stmt
*)
fun update_constr stmt constr cjmp_constr =
(* match against statement type and respective arguments *)
case term_to_string_args stmt of
  ("BMCStmt_Load",   var::exp::opt::acq::rel::_) =>
  (*
    val var::exp::opt::acq::rel::_ = tl stmt_args
  *)
    (* not exhaustive *)
    (case term_to_string_args exp of
      ("BExp_Const", cexp_val::_) =>
        (Redblackmap.insert(constr, Reg var,
            (* TODO set dependencies to parts of cexp_val for non-constants *)
            { dependents = [],
            constraint =
              ``bir_eval_exp (BExp_Den ^var) s.bst_environ = SOME $ BVal_Imm $ ^cexp_val``
              (* keep path constraints for unchanged locations *)
            }
          ),
          filter_cjmp_constr cjmp_constr [var])
(*
val ("BExp_Den",var'::_) = term_to_string_args exp
 *)
    | ("BExp_Den",var'::_) =>
      (constr,
          { dependents = [var, var'],
            constraint =
              ``bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den ^var') (BExp_Den ^var)) s.bst_environ = SOME $ BVal_Imm $ Imm1 1w``
          }::cjmp_constr)
    )
| ("BMCStmt_Store",  succ_reg::address::value::xcl::acq::rel::_)
  =>
    let
      val address' = ``BVal_Imm ^(hd $ unpack "BExp_Const" address)``
    in
      (Redblackmap.insert(constr, Mem address',
      {
        constraint =
          (* semantics: may fail if xcl *)
          if is_term_true xcl then
          ``
            bir_eval_exp (BExp_Den ^succ_reg) s.bst_environ = SOME $ BVal_Imm v_succ
            ==>
              ?val. mem_read M ^address' (s.bst_coh ^address') = SOME $ val
              /\ bir_eval_exp ^value s.bst_environ = SOME val
          ``
          else
          ``
            ?val. mem_read M ^address' (s.bst_coh ^address') = SOME $ val
            /\ bir_eval_exp ^value s.bst_environ = SOME val
          ``,
        (* check if  *)
        dependents = [address',succ_reg]
      }), filter_cjmp_constr cjmp_constr [address',succ_reg])
    end
(*
| ("BMCStmt_Amo",    succ_reg::address::value::acq::rel::_) => constr
| ("BMCStmt_Assign", var::exp::_) => constr
| ("BMCStmt_Fence",  _) => constr
| ("BMCStmt_Assert", exp) => constr
| ("BMCStmt_Assume", exp) => constr
*)
| _ => (constr,cjmp_constr)
(*
  handle _ => ERR "blah" ("unkown statement: " ^ stmt_str)
*)

(* global fixed terms *)
val M = mk_var("M", ``:mem_msg_t list``)
val s = mk_var("s", ``:bir_state_t``)
val s_prime = mk_var("s'", ``:bir_state_t``)
val M_prime = mk_var("M'", ``:mem_msg_t list``)
(* pc = (lbl,index) ==> x *)
  val state_rec_fn =
    fn arg_term => fn fieldn =>
      mk_icomb (acc_fn fieldn ``:bir_state_t``, arg_term)
  val s_bst_pc = state_rec_fn s "bst_pc"
  val s_prime_bst_pc = state_rec_fn s_prime "bst_pc"
val index_var = mk_var("index", ``:num``)
val lbl_var = mk_var("lbl", hd $ dest_fun_ty $ type_of ``Imm64`` )
val last_imp_pre_tm = ``bst_pc_tuple ^s_bst_pc = (BL_Address $ Imm64 ^lbl_var, ^index_var)``
val last_imp = fn x => list_mk_forall ([lbl_var,index_var], mk_imp(last_imp_pre_tm,x))

(*
 * second step pretty-printing the invariant
 *)

(*
val index = 0
 *)

(* amends the contraints if jump constraint is not among the visited
 *  addr          address of the jump instruction
 *  index         index of the pc at the jump instruction
 *  constr        the collection of constraints on locations
 *  cjmp_constr   : constr list  of constraints with their dependents
 *  visited_pcs   : term list  of bir_label_t
 *)
(*
val cjmp_constr = [] : constr list
val visited_pcs = [] : term list
val jmp_stmt = jmp
assemble_cjmp_constr (constr,cjmp_constr,visited_pcs) jmp_stmt
*)

fun assemble_cjmp_constr (constr,cjmp_constr,visited_pcs) jmp_stmt =
let
  (* compare with bir_exec_stmt_cjmp_def *)
  (* assumes conditional jump statement *)
  val cond::target_t::target_f::_ = unpack "BStmt_CJmp" jmp_stmt
  (* assume both are BLE_Label's *)
  val target_t = hd $ unpack "BLE_Label" target_t
  val target_f = hd $ unpack "BLE_Label" target_f
  (*
  val visited_pcs = target_t::[]
  *)
  val assigned_locs =
    map (unregmem o fst) $ Redblackmap.listItems constr
  fun has_subterm subt t = (find_term (is_eq_tm subt) t; true) handle HOL_ERR _ => false
  (* determine the assigned_locs are subterms of cond *)
  val cond_locs = List.filter (fn x => has_subterm x cond) assigned_locs
  fun has_visited addr = List.exists (is_eq_tm addr) visited_pcs
  val (target,cjmp_constr') =
    (* keep the constraint for the unvisited target *)
    (case (has_visited target_t, has_visited target_f) of
      (true,false) =>
          (target_f,{ constraint =
              ``bir_eval_exp ^cond (^s).bst_environ = SOME $ BVal_Imm $ Imm1 1w``
          ,  dependents = cond_locs})
    | (false,true) =>
          (target_t,{ constraint =
            ``bir_eval_exp ^cond (^s).bst_environ = SOME $ BVal_Imm $ Imm1 0w``
          ,  dependents = cond_locs})
    )
    handle _ =>
      raise
        ERR "assemble_cjmp_constr" "we assume exactly one of the jump targets was visited before"
in
  (target,cjmp_constr'::cjmp_constr)
end
handle _ =>
  raise ERR "assemble_cjmp_constr" "jump statement or label format error"

fun get_jmp_target jmp_stmt =
  hd $ unpack "BLE_Label" $ hd $ unpack "BStmt_Jmp" jmp_stmt
  handle _ =>
    raise ERR "get_jmp_target" "unhandled jump target"

(* calculate block constraint including jump *)
fun block_constr constr cjmp_constr addr stmts jmp_stmt visited_pcs =
let
  (* constr and post condition *)
  val (constr,cjmp_constr,block_term) =
    List.foldl
      (fn ((index,stmt), (constr,cjmp_constr,term)) =>
        let
(*
val stmt = hd stmts
*)
          val (constr,cjmp_constr) = update_constr stmt constr cjmp_constr
          val term' = constrs_to_term (addr,index) constr cjmp_constr
        in
          (constr,cjmp_constr,mk_conj(term,term'))
        end
      )
      (constr,cjmp_constr,``T``)
      (mapi pair stmts)
  (* case split on the jump kind *)
  (* TODO should branch if neither addr has been visited before *)
  val (target,cjmp_constr) =
    case fst $ term_to_string_args jmp_stmt of
      "BStmt_CJmp" => assemble_cjmp_constr (constr,cjmp_constr,visited_pcs) jmp_stmt
    | "BStmt_Jmp" => (get_jmp_target jmp_stmt,cjmp_constr)
    | _ => (addr,cjmp_constr)
  val visited_pcs = addr::visited_pcs
  val jmp_term = constrs_to_term (target,length stmts) constr cjmp_constr
  val block_post_cond = mk_conj(block_term, jmp_term)
in
  (target, visited_pcs, block_post_cond, constr, cjmp_constr)
end

(*

open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_promisingTheory
     bir_programLib bir_promising_wfTheory;

open example_spinlockTheory

val prog = ``spinlock_concrete``
val prog = ``spinlock_concrete2 [] jump_after unlock_entry``

*)

val prog = ``BirProgram $ dequeue hd_addr tl_addr reg dequeue_entry jump_after ``
val prog = ``BirProgram $ dequeue (BExp_Const $ Imm64 42w) (BExp_Const $ Imm64 43w) reg dequeue_entry jump_after ``
val label_stmts_thm = bir_stmts_progs_thm prog
(* (bir_label_t # option) list *)

val labels_stmts_list =
  SPEC_ALL label_stmts_thm |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map pairSyntax.dest_pair
  handle HOL_ERR _ => raise ERR "function" "cannot destruct hol list of labels and stmts"

(* get block statements at address *)
(* label # stmt term list # jmp *)
val addresses_stmts =
(*
  val (addr,stmts) = hd $
  filter (optionSyntax.is_some o snd) labels_stmts_list
 *)
  filter (optionSyntax.is_some o snd) labels_stmts_list
  |> map (fn (addr,stmts) =>
    let val _::stmts::jmp::_ = pairSyntax.strip_pair $ optionSyntax.dest_some stmts
    in (addr, fst $ listSyntax.dest_list stmts, jmp) end)
(* address of external statements *)
val addresses_exts =
  map fst $ filter (optionSyntax.is_none o snd) labels_stmts_list
(* assume BL_Address *)
val addresses = map (rand o #1) addresses_stmts
(*
val stmt = List.nth (stmts, 0)
val len = length stmts
*)

(* assumption that the control flow is linear for this code *)

(* init *)

(*
val term = ``T``
val stmt = hd stmts
*)

(* init *)
val constr = Redblackmap.mkDict kind_cmp : (kind, constr) Redblackmap.dict
val cjmp_constr = [] : constr list
val visited_pcs = [] : term list
val post_conds = ``T``

(*
addresses_stmts
val (addr,stmts,jmp_stmt) = List.nth (addresses_stmts,4);
*)

val (constr,cjmp_constr,post_conds,visited_pcs) =
  List.foldl (fn ((addr,stmts,jmp_stmt),(constr,cjmp_constr,post_conds,visited_pcs)) =>
    let
      (* assume that next addr == target *)
      val (target, visited_pcs, block_post_cond, constr, cjmp_constr) =
        block_constr constr cjmp_constr addr stmts jmp_stmt visited_pcs
      val post_conds = mk_conj(post_conds,block_post_cond)
    in
      (constr,cjmp_constr,post_conds,visited_pcs)
    end
  )
  (constr,cjmp_constr,post_conds,visited_pcs)
  addresses_stmts

(*
$HOLDIR/src/portableML/Redblackmap.sig
wordsSyntax.mk_wordii (255, 8) (* 8w:word4 *)
*)

end
