(*
  automate post condition generation for given program
*)

structure strongPostCondLib :> strongPostCondLib =
struct

open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_promisingTheory
     bir_programLib bir_promising_wfTheory
     promising_thmsTheory ;
open example_spinlockTheory ;

Definition bst_pc_tuple_def:
  bst_pc_tuple x = (x.bpc_label,x.bpc_index)
End

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

fun bir_eval_exp_den_imm variable value =
``bir_eval_exp (BExp_Den ^variable) s.bst_environ = SOME $ BVal_Imm ^value``

fun bir_eval_exp_val tm value =
``bir_eval_exp (^tm) s.bst_environ = SOME $ BVal_Imm ^value``


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

(* rewrite term with some simpset equalities and resort/deduplicate conjuncts *)
fun simplify_term x =
  REFL x
  (* ++ boolSimps.DNF_ss *)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss()) [AC CONJ_ASSOC CONJ_COMM,AND_CLAUSES,GSYM lock_addr_def,GSYM lock_addr_val_def,GSYM bir_read_reg_def,bir_eval_exp_BExp_Const]
  |> rand o concl


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

(*
fun bir_stmts_prog_thm prog =
  EVAL $ mk_icomb(``bir_stmts_of_prog``,prog)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [listTheory.MAP_APPEND,bir_typing_progTheory.bir_stmts_of_block_def]
  |> strip_union_insert
*)

fun bir_stmts_progs_thm prog =
  EVAL $ mk_icomb(``bir_stmts_of_progs``,prog)
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [listTheory.MAP_APPEND,bir_typing_progTheory.bir_stmts_of_block_def]

fun bir_stmts_term prog =
  bir_stmts_progs_thm prog
  |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map pairSyntax.dest_pair
  handle HOL_ERR _ => raise ERR "function" "cannot destruct hol list of labels and stmts"

(*
list of collected constraints on registers
find the known registers from
map fst $ Redblackmap.listItems constr
that are part of the jump constraint cjmp_constr
*)

(* jump stmt to constraints
arguments
  stmt          current statement
  regs          list of register names (that may occur as dependents in jmp constraint)
  cjmp_constr   map: address to constr
                where the dependents are from regs list
*)
(*

val cjmp_constr = Redblackmap.mkDict Term.compare : (term, constr) Redblackmap.dict
val jmp_stmt =
   ``BStmt_CJmp
       (BExp_UnaryExp BIExp_Not
          (BExp_BinPred BIExp_Equal (BExp_Den (BVar "x5" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0w))))
       (BLE_Label (BL_Address (Imm64 lock_entry)))
       (BLE_Label (BL_Address (Imm64 (lock_entry + 8w))))``
val regs = [``BVar "x5" (BType_Imm Bit64)``];
Redblackmap.listItems $ #2 $ jmp_stmt_to_constr jmp_stmt regs cjmp_constr

*)

fun jmp_stmt_to_constr jmp_stmt regs cjmp_constr =
  case term_to_string_args jmp_stmt of
    ("BStmt_CJmp", cond::lbl1::lbl2::[]) =>
      let
        (* TODO extract dependencies of regs from cond expression, e.g. by
           evaluation, extracting all the variables *)
        val deps = []
        val cjmp_constr1 =
          Redblackmap.insert(cjmp_constr, lbl2, { dependents = deps, constraint = cond })
        val cond_neg = mk_icomb(``BExp_UnaryExp BIExp_Not``, cond)
        val cjmp_constr2 =
          Redblackmap.insert(cjmp_constr1, lbl1, { dependents = deps, constraint =  cond_neg})
      in ([lbl1,lbl2],cjmp_constr2,true) end
  | ("BStmt_Jmp", lbl::[]) => ([lbl],cjmp_constr,false)
  | _ => ([],cjmp_constr,false) (* ignore other final stmts *)


(* transforms a path and jump constraints into a conjunct
   cjmp_path     list of jump target addresses that were jumped on this path
   cjmp_constr   map of jump addresses to constraints
 *)
(*

val cjmp_path = [``BLE_Label (BL_Address (Imm64 (lock_entry + 8w)))``,``BLE_Label (BL_Address (Imm64 lock_entry))``]
val cjmp_constr = Redblackmap.mkDict Term.compare : (term, constr) Redblackmap.dict
val jmp_stmt =
   ``BStmt_CJmp
       (BExp_UnaryExp BIExp_Not
          (BExp_BinPred BIExp_Equal (BExp_Den (BVar "x5" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0w))))
       (BLE_Label (BL_Address (Imm64 lock_entry)))
       (BLE_Label (BL_Address (Imm64 (lock_entry + 8w))))``
val regs = [``BVar "x5" (BType_Imm Bit64)``];
val cjmp_constr = #2 $ jmp_stmt_to_constr jmp_stmt regs cjmp_constr

Redblackmap.listItems cjmp_constr
jmp_constr_to_term cjmp_constr path

*)

fun jmp_constr_to_term (cjmp_constr : (term, constr) Redblackmap.dict) (cjmp_path : term list) =
    simplify_term $ foldl (fn (x,e) =>
      let val v_opt = Redblackmap.peek(cjmp_constr,x)
          val v_opt = Option.map #constraint v_opt
          val v_opt = Option.map (fn v => bir_eval_exp_val v ``Imm1 1w``) v_opt
      in if isSome v_opt then mk_conj(e, (valOf v_opt)) else e end
    ) ``T`` cjmp_path

(*

arguments: jump_head

- for given program obtain list of each label and index and the statement at (label,index)
- for each block label construct the fold over the block's indices and the
  effect of the statement

*)

(*
 * first step collection of constraints
 *)

(* returns conjunct of lbl_var equals addr and index_var equals index:num *)
fun addr_label_cj_index addr index =
let
  val index_term = numSyntax.mk_numeral (Arbnum.fromInt index)
  val index_var = mk_var("index", ``:num``)
  val lbl_var = mk_var("lbl", hd $ dest_fun_ty $ type_of ``Imm64`` )
in
  simplify_term $ mk_conj(mk_eq(``BL_Address $ Imm64 $ ^lbl_var``,addr),mk_eq(index_var,index_term))
end

(* transform the constraints into a term *)
fun constrs_to_term (addr,index) constr cjmp_constr =
let
  val term =
    Redblackmap.foldl (fn (_,v,x) => mk_conj(x, #constraint (v :constr))) ``T`` constr
in
  simplify_term $
  mk_imp(addr_label_cj_index addr index,
    if null cjmp_constr then term else mk_conj(term,list_mk_conj $ map #constraint (cjmp_constr :constr list))
  )
end

(* print contstraints
Redblackmap.listItems constr
*)

(* filter path conditions if dependency has changed *)
fun filter_cjmp_constr cjmp_constr addrs =
  List.filter
    (fn x =>
      List.all
        (fn addr =>
          not (List.exists (is_eq_tm addr) (#dependents (x : constr ))))
        addrs)
    cjmp_constr

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
Redblackmap.listItems $ #1 $ update_constr stmt constr cjmp_constr
*)

fun update_constr stmt constr cjmp_constr =
case term_to_string_args stmt of
  ("BMCStmt_Load",   var::exp::opt::acq::rel::_) =>
  (*
    val var::exp::_ = #2 $ term_to_string_args stmt
  *)
    (* not exhaustive *)
    (case term_to_string_args exp of
      ("BExp_Const", cexp_val::_) =>
(*
val ("BExp_Const",cexp_val::_) = term_to_string_args exp
 *)
        (Redblackmap.insert(constr, Reg var,
            (* TODO set dependencies to parts of cexp_val for non-constants *)
            { dependents = [],
              constraint =
              ``?v t. bir_read_reg (bir_var_name ^var) s.bst_environ v
              /\ mem_read M (BVal_Imm ^cexp_val) t = SOME $ BVal_Imm $ Imm64 v``
              (* read from address cexp_val into register var *)
            }
          ),
          filter_cjmp_constr cjmp_constr [var])
(*
val ("BExp_Den",var'::_) = term_to_string_args exp
 *)
    | _ => (constr,cjmp_constr)
    (*
    ("BExp_Den",var'::_) =>
      (constr,
          { dependents = [var, var'],
            constraint =
              ``bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den ^var') (BExp_Den ^var)) s.bst_environ = SOME $ BVal_Imm $ Imm1 1w``
          }::cjmp_constr)
    *))
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
            (?v. bir_eval_exp (BExp_Den ^succ_reg) s.bst_environ = SOME $ BVal_Imm $ Imm64 v)
            /\ (bir_eval_exp (BExp_Den ^succ_reg) s.bst_environ = SOME $ BVal_Imm v_succ
            ==>
              ?val. mem_read M ^address' (s.bst_coh ^address') = SOME $ val
              /\ bir_eval_exp ^value s.bst_environ = SOME val)
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
| ("BMCStmt_Assign", var::exp::_) =>
    (case term_to_string_args exp of
      (* TODO non-exhaustive *)
      ("BExp_Const", cexp_val::_) =>
(*
val ("BExp_Const",cexp_val::_) = term_to_string_args exp
*)
        (Redblackmap.insert(constr, Reg var,
            (* TODO set dependencies to parts of cexp_val for non-constants *)
            { dependents = [],
              constraint = bir_eval_exp_den_imm var cexp_val
              (* keep path constraints for unchanged locations *)
            }
          ),
          filter_cjmp_constr cjmp_constr [var])
    )
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
              ``bir_eval_exp ^cond (^s).bst_environ = SOME $ BVal_Imm $ Imm1 0w``
          ,  dependents = cond_locs})
    | (false,true) =>
          (target_t,{ constraint =
            ``bir_eval_exp ^cond (^s).bst_environ = SOME $ BVal_Imm $ Imm1 1w``
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

fun get_cjmp_targets jmp_stmt =
  map (hd o unpack "BLE_Label") (tl $ unpack "BStmt_CJmp" jmp_stmt)
  handle _ =>
    raise ERR "get_jmp_target" "unhandled jump target"

(* linearisation points *)

(* Is stmt a store to the linearisation address?
   For exclusive stores this returns the success register *)
fun is_store_to_lin_addr lin_addr stmt =
case term_to_string_args stmt of
  ("BMCStmt_Load",   var::exp::opt::acq::rel::_) => (false, NONE)
| ("BMCStmt_Store",  succ_reg::address::value::xcl::acq::rel::_) =>
  let val to_lin_addr = is_eq_tm address lin_addr
  in
    if is_term_true xcl
    then (to_lin_addr, SOME succ_reg)
    else (to_lin_addr, NONE)
  end
| _ => (false, NONE)


(* linearisation constraints *)

type lc = {current: term list,
     last_point: (term * int * term) option,
     lin_addr: term, old: term list list, store_fail: term list}

(* updates the set of linearisation points according to the current statement *)
fun lin_constr (lc : lc) (addr,index,stmt) =
let
  val (store_to_lin,xcl_opt) = is_store_to_lin_addr (#lin_addr lc) stmt
in
  if isSome xcl_opt andalso store_to_lin
  then
    (* on store failure we assume a jump backwards to earlier covered states *)
    (* branching happens only on exclusive store *)
    {old=(#old lc), current=[], lin_addr=(#lin_addr lc),last_point=SOME (addr,index,valOf xcl_opt), store_fail=(#current lc)@[addr_label_cj_index addr index]}
  else if store_to_lin
  then
    (* here an non-exclusive store resets all earlier branching of linearisation points *)
    {old=(#old lc)@[#store_fail lc]@[#current lc@[addr_label_cj_index addr index]], current=[], lin_addr=(#lin_addr lc),last_point=NONE, store_fail=[]}
  else if isSome (#last_point lc)
  then
    (* the current pc is part of both equivalence classes of linearisation points (as the branching condition has not yet been checked in a cjmp) *)
    {old=(#old lc),current=(#current lc)@[
      mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_succ``)
    ],lin_addr=(#lin_addr lc),last_point=(#last_point lc),store_fail=(#store_fail lc)@[
      mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_fail``)
    ]}
  else
    {old=(#old lc),current=(#current lc)@[addr_label_cj_index addr index],lin_addr=(#lin_addr lc),last_point=(#last_point lc),store_fail=(#store_fail lc)}
end

(* updates lc given a jump stmt *)
fun update_lc_jmp (addr,index,jmp_stmt) (lc : lc) =
case fst $ term_to_string_args jmp_stmt of
  "BStmt_CJmp" =>
    if isSome (#last_point lc)
    then
      (* TODO fix to only override if jump constraint equals #3 (#last_point lc) *)
      {old=(#old lc)@[
        (#store_fail lc)@[mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_fail``)]
      ], current=(#current lc)@[
        mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_succ``)
      ], lin_addr=(#lin_addr lc),last_point=NONE,store_fail=[]}
    else
      {old=(#old lc),current=(#current lc)@[addr_label_cj_index addr index],lin_addr=(#lin_addr lc),last_point=(#last_point lc),store_fail=(#store_fail lc)}
| "BStmt_Jmp" =>
    if isSome (#last_point lc)
    then
      {old=(#old lc),current=(#current lc)@[
        mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_succ``)
      ],lin_addr=(#lin_addr lc),last_point=(#last_point lc),store_fail=(#store_fail lc)@[
        mk_conj(addr_label_cj_index addr index, bir_eval_exp_den_imm (#3 (valOf (#last_point lc))) ``v_fail``)
      ]}
    else
      {old=(#old lc),current=(#current lc)@[addr_label_cj_index addr index],lin_addr=(#lin_addr lc),last_point=(#last_point lc),store_fail=(#store_fail lc)}
| _ => lc (* ignore other final stmts *)

(* calculate block constraint including jump *)
(*
val constr = #constr s
val cjmp_constr = #cjmp_constr s
val visited_pcs = #visited_pcs s
Redblackmap.listItems constr
 *)
fun block_constr constr cjmp_constr addr stmts jmp_stmt visited_pcs cjmp_path (lc : lc) =
let
  (* constr and post condition *)
  val (constr,cjmp_constr,block_term,lc) =
    List.foldl
      (fn ((index,stmt), (constr,cjmp_constr,term,lc)) =>
        let
(*
val (index,stmt) =  (fn n => (n,List.nth(stmts,n))) 0
val cjmp_constr = []
val term = ``T``
*)
          (* constraint at current pc is collection of previous constraints *)
          val term' =
            constrs_to_term (addr,index) constr cjmp_constr
          val (constr,cjmp_constr) = update_constr stmt constr cjmp_constr
          (* linearisation constraint only needs to remember index and label of
             change of  *)
          val lc = lin_constr lc (addr,index,stmt)
        in
(*
          val term = simplify_term $ mk_conj(term,term')
 *)
          (constr,cjmp_constr,simplify_term $ mk_conj(term,term'),lc)
        end
      )
      (constr,cjmp_constr,``T``,lc)
      (mapi pair stmts)
  val jmp_term = constrs_to_term (addr,length stmts) constr cjmp_constr
  val block_post_cond = simplify_term $ mk_conj(block_term, jmp_term)
  (* case split on the jump kind *)
  (* TODO should branch if neither addr has been visited before *)
(*
  val (targets,cjmp_constr,is_cjmp) = jmp_stmt_to_constr jmp_stmt regs cjmp_constr
*)
  val (target,cjmp_constr) =
    case fst $ term_to_string_args jmp_stmt of
      "BStmt_CJmp" => assemble_cjmp_constr (constr,cjmp_constr,visited_pcs) jmp_stmt
    | "BStmt_Jmp" => (get_jmp_target jmp_stmt,cjmp_constr)
    | _ => (addr,cjmp_constr) (* ignore other final stmts *)
  (* TODO extract addresses from cjmp_constr and add to constr *)
  val lc = update_lc_jmp (addr,length stmts,jmp_stmt) lc
(* TODO choose proper address (branch!) *)
(*
   val target =
    if is_cjmp
      then hd $ List.filter (fn x => not (List.member x visited_pcs)) targets
      else target
   val cjmp_path = if is_cjmp cjmp_path then target::cjmp_path else cjmp_path
*)
  val visited_pcs = visited_pcs@[addr]
in
  (target, visited_pcs, block_post_cond, constr, cjmp_constr, cjmp_path, lc)
end

(*

open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_promisingTheory
     bir_programLib bir_promising_wfTheory;

open example_spinlockTheory

val prog = ``spinlock_concrete``
val prog = ``spinlock_concrete2 [] jump_after unlock_entry``

val prog = ``BirProgram $ dequeue hd_addr tl_addr reg dequeue_entry jump_after ``
val prog = ``BirProgram $ dequeue (BExp_Const $ Imm64 42w) (BExp_Const $ Imm64 43w) reg dequeue_entry jump_after ``

*)

val prog = ``BirProgram (unlock lock_addr unlock_entry : (bmc_stmt_basic_t, mem_msg_t list # num list) bir_generic_block_t list)``
val prog = ``BirProgram (lock lock_addr lock_entry jump_after : (bmc_stmt_basic_t, mem_msg_t list # num list) bir_generic_block_t list)``

(* (bir_label_t # option) list *)
val labels_stmts_list = bir_stmts_term prog
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

(*
val term = ``T``
val stmt = hd stmts
*)

(* init *)
val init_state = {
    constr = Redblackmap.mkDict kind_cmp : (kind, constr) Redblackmap.dict,
    cjmp_constr = [] : constr list,
    post_conds = ``T``,
    visited_pcs = [] : term list,
    cjmp_path = [] : term list (* path of jumped-to jump targets *)
};
val s = init_state;
(* matching the type lc *)
val lc = {
  old = [] : term list list,
  current = [] : term list,
  last_point = NONE : (term * int * term) option, (* SOME (addr,index,success reg) *)
  lin_addr = Term $ `BExp_Const (Imm64 42w)`, (* address to guess linearisation points *)
  (* following a store, this keeps the failure pcs until to the conditional jump
     non-empty means: the jump has not yet occurred *)
  store_fail = [] : term list
};

(* guesses of linearisation points for generation of the refinement relation
   the current equivalence class of linearisation points gets swapped after completing the block that contains a successful store to lin_addr
*)

val ({constr,cjmp_constr,post_conds,visited_pcs,cjmp_path},lc) =
  List.foldl (fn ((addr,stmts,jmp_stmt),(s,lc)) =>
    let
      (* assume that next addr == target *)
(*
      val (addr,stmts,jmp_stmt) = List.nth (addresses_stmts,3);
      val (target, visited_pcs, block_post_cond, constr, cjmp_constr, lc) =
        block_constr (#constr s) (#cjmp_constr s) addr stmts jmp_stmt (#visited_pcs s) lc
      val s =
      {constr=constr,cjmp_constr=cjmp_constr,post_conds=simplify_term $ mk_conj(#post_conds s,block_post_cond),visited_pcs=visited_pcs}
*)
      val (target, visited_pcs, block_post_cond, constr, cjmp_constr, cjmp_path, lc) =
        block_constr (#constr s) (#cjmp_constr s) addr stmts jmp_stmt (#visited_pcs s) (#cjmp_path s) lc
    in
      ({constr=constr,cjmp_constr=cjmp_constr,post_conds=simplify_term $ mk_conj(#post_conds s,block_post_cond),visited_pcs=visited_pcs,cjmp_path=cjmp_path},lc)
    end
  )
  (init_state,lc)
  addresses_stmts

(* print linearisation points for the refinement relation *)

val lin_term =
  list_mk_conj $
    map (fn (index, addrs) =>
      mk_imp(list_mk_disj addrs, mk_var("control_point" ^ Int.toString index , bool))
    )
    (mapi pair (filter (not o List.null) ((#old lc)@[#current lc])))

(*

^lin_term

post_conds

*)

(*
$HOLDIR/src/portableML/Redblackmap.sig
wordsSyntax.mk_wordii (255, 8) (* 8w:word4 *)
*)



(* constraints particular for this program *)


(* bir_get_current_statement equalities *)
val prog_bgcs = save_thm("prog_bgcs", bgcs_bmc_prog_thms prog);

(* trivial: no external statements *)
val prog_wf_ext = store_thm("prog_wf_ext",
  ``wf_ext ^prog cid c M``,
  fs[prog_bgcs,wf_ext_def,wf_ext_p_def]);

val prog_blop = save_thm("prog_blop", blop_prog_labels_thm prog)

(* for parameterised labels we assume disjointness *)
val prog_blop_ALL_DISTINCT_tm =
  ``ALL_DISTINCT $ bir_labels_of_program ^prog``
 (*``ALL_DISTINCT ^(prog_blop |> concl |> rator |> rand)``*)

val prog_blop_ALL_DISTINCT = EVAL prog_blop_ALL_DISTINCT_tm
  |> CONV_RULE $ RHS_CONV $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) [AC CONJ_ASSOC CONJ_COMM,wordsTheory.dimword_64]

val fv = Term.free_vars prog
val fv_tm = pairSyntax.list_mk_pair fv

val post_cond_def = Define `
  post_cond M s ^fv_tm =
    !lbl index. bst_pc_tuple s.bst_pc = (BL_Address $ Imm64 lbl, index)
      ==> ^post_conds
  `


(* dummy definitions for unlock_def *)
Definition prog_individual_constraints_def:
  prog_individual_constraints a = T
End

Theorem prog_individual_constraints_eq = prog_individual_constraints_def


(* has to quantify all arguments to lock_def *)
Definition prog_individual_constraints_def:
  prog_individual_constraints (^fv_tm)
  = ?x. jump_after = BL_Address (Imm64 x)
  /\ ~(MEM jump_after $ bir_labels_of_program ^prog)
End

Theorem prog_individual_constraints_eq =
  REWRITE_RULE[prog_blop] prog_individual_constraints_def
  |> CONV_RULE $ SIMP_CONV (srw_ss() ++ boolSimps.DNF_ss) []



(* assumption:
- distinct addresses is necessary due to parametrised addresses:
  ALL_DISTINCT $ bir_labels_of_program prog
- memory only holds values of certain fixed type: wf_mem_vals
- wellformed labels for jump outside (disjointness)
  jump outside of the program labels which are disjoint 
  prog_individual_constraints


TODO prove invariant wf_mem_vals
can we generally prove the invariant for
  certifying trace P ==> wf_mem_val P /\ wf_mem_loc P

*)

(* generic tactis for 12 theorems, see clstep_bgcs_cases *)

val clstep_post_cond_inv_tac =
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_get_current_statement_SOME_MEM
  >> drule_at (Pat `clstep`) clstep_preserves_wf
  >> disch_then $ drule_at_then Any assume_tac
  >> fs[prog_wf_ext]
  >> imp_res_tac clstep_bgcs_cases
  >> gvs[]
  >> gs[post_cond_def,clstep_cases,bst_pc_tuple_def,bir_pc_next_def,bmc_exec_general_stmt_exists,bir_state_read_view_updates_def]

Theorem clstep_post_cond_inv_BMCStmt_Load:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Load var a_e opt_cast xcl acq rel
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Load specific *)
  >> gvs[prog_bgcs,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM,prog_blop_ALL_DISTINCT]
  (* use distinctness of labels to solve all other issues *)
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[bir_read_reg_prime,lock_addr_def,lock_addr_val_def]
  >> fs[bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def]
  >> drule_all_then strip_assume_tac wf_mem_vals_mem_read
  >> fs[bir_eval_exp_view_def,cj 1 bir_expTheory.bir_eval_exp_def]
  >> goal_assum $ drule_at $ Pat `mem_read`
  >> drule $ GSYM bir_read_reg_env_update_cast64
  >> fs[]
QED

Theorem clstep_post_cond_inv_BMCStmt_Store_fail:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel
  /\ prom = [] /\ xcl
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Store *)
  >> fs[prog_blop_ALL_DISTINCT]
  >> gvs[prog_bgcs]
  >> fs[AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[wordsTheory.dimword_64,bir_read_reg_def]
  >> gs[xclfail_update_env_SOME,bir_eval_exp_BExp_Den_update_eq']
  >> fs[bir_eval_exp_BExp_Den_update_eq,v_fail_def,v_succ_def]
QED

Theorem clstep_post_cond_inv_BMCStmt_Store:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Store var_succ a_e v_e xcl acq rel
  /\ ~(NULL prom)
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Store *)
  >> fs[prog_blop_ALL_DISTINCT]
  >> gvs[prog_bgcs]
  >> fs[AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[wordsTheory.dimword_64,bir_state_fulful_view_updates_def,bir_read_reg_def]
  >> gs[fulfil_update_viewenv_def,fulfil_update_env_BVar_eq,fulfil_update_env_BVar_eq',bir_eval_exp_BExp_Den_update_eq']
  >> fs[bir_eval_exp_BExp_Den_update_eq,v_succ_def]
  >> fs[bir_eval_exp_view_def,cj 1 bir_expTheory.bir_eval_exp_def,lock_addr_val_def,combinTheory.APPLY_UPDATE_THM,mem_read_def]
QED

Theorem clstep_post_cond_inv_BMCStmt_Amo:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Amo var a_e v_e acq rel
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Amo *)
  (* TODO generalise with same reasoning as BMCStmt_Store *)
  >> gvs[prog_bgcs]
QED

Theorem clstep_post_cond_inv_BMCStmt_Fence:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Fence K1 K2
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Fence *)
  (* TODO implement for program *)
  >> fs[prog_blop_ALL_DISTINCT]
  >> gvs[prog_bgcs]
  >> fs[AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[wordsTheory.dimword_64,fence_updates_def,bir_pc_next_def]
QED

Theorem clstep_post_cond_inv_BMCStmt_CJmp:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtE $ BStmt_CJmp cond_e lbl1 lbl2
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BStmt_CJmp *)
  >> fs[prog_blop_ALL_DISTINCT]
  (* possible branching here due to several jumps *)
  >> gvs[prog_bgcs]
  >> fs[AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[wordsTheory.dimword_64,bir_exec_stmt_cjmp_mc_invar]
  >> fs[bir_exec_stmt_cjmp_def,bir_eval_exp_view_def,Once bir_eval_exp_SOME']
  >> gvs[v_succ_def,GSYM bir_read_reg_def,bir_read_reg_bir_env_read,bir_envTheory.bir_var_name_def]
  >> drule_then (gvs o single) bir_eval_exp_BExp_UnaryExp'
  >> fs[bir_valuesTheory.bir_dest_bool_val_def]
  >> qmatch_goalsub_abbrev_tac `COND cond _ _`
  >> Cases_on `cond`
  >> fs[bir_exec_stmt_jmp_def,bir_eval_label_exp_def,bir_exec_stmt_jmp_to_label_mc_invar]
  >> fs[bir_exec_stmt_jmp_to_label_def,prog_blop,bir_block_pc_def]
  >> fs[wordsTheory.dimword_64,prog_individual_constraints_eq]
  >> fs[COND_RAND,COND_RATOR]
  >> drule_then (fs o single) bir_eval_exp_BExp_UnaryExp
  >> goal_assum drule_all
  >> fs[]
QED

Theorem clstep_post_cond_inv_BMCStmt_Assign:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assign var e
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Assign *)
  >> gvs[prog_bgcs,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM,prog_blop_ALL_DISTINCT]
  (* use distinctness of labels to solve all other issues *)
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def,bir_eval_exp_view_def,cj 1 bir_expTheory.bir_eval_exp_def,wordsTheory.dimword_64,bir_read_reg_bir_env_read,GSYM bir_read_reg_def]
  >> drule $ GSYM bir_read_reg_env_update_cast64
  >> fs[]
QED

Theorem clstep_post_cond_inv_BMCStmt_Assert:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assert e
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Assert *)
  >> gvs[prog_bgcs,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM,prog_blop_ALL_DISTINCT]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[]
QED

Theorem clstep_post_cond_inv_BMCStmt_Assume:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtB $ BMCStmt_Assume e
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BMCStmt_Assume *)
  >> gvs[prog_bgcs,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM,prog_blop_ALL_DISTINCT]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[]
QED

Theorem clstep_post_cond_inv_BStmt_Halt:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtE $ BStmt_Halt e
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BStmt_Halt *)
  >> gvs[prog_bgcs,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM,prog_blop_ALL_DISTINCT]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[]
QED

Theorem clstep_post_cond_inv_BStmt_Jmp:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSGen $ BStmtE $ BStmt_Jmp e
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* BStmt_Jmp *)
  >> fs[prog_blop_ALL_DISTINCT]
  >> gvs[prog_bgcs]
  >> fs[AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
  >> qpat_assum `_ = c_bst_pc.bpc_label` $ assume_tac o GSYM
  >> fs[bir_envTheory.bir_var_name_def,bir_envTheory.bir_var_type_def,bir_read_reg_def,v_succ_def,v_fail_def]
  >> rpt strip_tac
  >> gs[bir_exec_stmt_jmp_eq,prog_blop,bir_block_pc_def,wordsTheory.dimword_64,bir_exec_stmt_jmp_bst_eq]
  >> rpt $ goal_assum drule_all
QED

Theorem clstep_post_cond_inv_BSExt:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  /\ bir_get_current_statement ^prog c.bst_pc = SOME $ BSExt R
  ==> post_cond M c' ^fv_tm
Proof
  clstep_post_cond_inv_tac
  (* We don't expect BSExt in programs *)
  >> gvs[prog_bgcs]
QED

(* combination of previous theorems *)
Theorem clstep_post_cond_inv:
  clstep (^prog) cid c M prom c'
  /\ post_cond M c ^fv_tm
  /\ well_formed cid M c
  /\ wf_mem_vals M
  /\ prog_individual_constraints ^fv_tm
  /\ ^prog_blop_ALL_DISTINCT_tm
  ==> post_cond M c' ^fv_tm
Proof
  rpt strip_tac
  >> imp_res_tac clstep_bgcs_imp
  >> drule_then assume_tac bir_get_current_statement_SOME_MEM
  >> drule_at (Pat `clstep`) clstep_preserves_wf
  >> disch_then $ drule_at_then Any assume_tac
  >> fs[prog_wf_ext]
  >> imp_res_tac clstep_bgcs_cases
  >> gvs[]
  (* 12 subgoals *)
  >~ [`BMCStmt_Load`]
  >- (
    drule_all clstep_post_cond_inv_BMCStmt_Load
    >> fs[]
  )
  >~ [`BMCStmt_Store _ _ _ T _ _`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Store_fail
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Store`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Store
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Amo`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Amo
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Fence`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Fence
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BStmt_CJmp`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_CJmp
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Assign`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Assign
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Assert`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Assert
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BMCStmt_Assume`]
  >- (
    drule clstep_post_cond_inv_BMCStmt_Assume
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BStmt_Halt`]
  >- (
    drule clstep_post_cond_inv_BStmt_Halt
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BStmt_Jmp`]
  >- (
    drule clstep_post_cond_inv_BStmt_Jmp
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
  >~ [`BSExt`]
  >- (
    drule clstep_post_cond_inv_BSExt
    >> rpt $ disch_then $ drule_at Any
    >> fs[]
  )
QED

end
