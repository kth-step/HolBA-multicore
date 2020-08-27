structure bir_conc_execLib : bir_conc_execLib =
struct

  open HolKernel pairLib listSyntax stringSyntax wordsSyntax optionSyntax;
  open bir_symb_execLib;
  open bir_symb_masterLib;
  open bir_symb_init_envLib;     
  open bir_embexp_driverLib;



  fun update_env name value env = 
      let
        val hname = fromMLstring name
        val wordval = mk_wordi (value, 64);
      in
	  (rhs o concl o EVAL) `` bir_symb_env_update 
			  ^hname (BExp_Const (Imm64 ^wordval)) (BType_Imm Bit64) ^env
			  ``
      end;

  fun gen_symb_updates s env =
    foldr (fn ((n,v),e) => update_env n v e) (env) s;

  fun conc_exec_program depth prog envfo =
    let 
      val precond = ``BExp_Const (Imm1 1w)``;

      val states = symb_exec_process_to_leafs_pdecide (fn x => true) envfo depth precond prog;

      (* filter for the concrete path *)
      fun eq_true t = identical t ``SOME (BVal_Imm (Imm1 1w))``;
      fun pathcond_val s = (snd o dest_eq o concl o EVAL)
			   ``bir_eval_exp ((^s).bsst_pred) (BEnv (K NONE))``;
      val filteredStates = List.filter (eq_true o pathcond_val) states;
      val final_state = case filteredStates of
			   [s] => s
			 | []  => raise ERR "conc_obs_compute" "no state has a true path condition?!?!?!"
                         | _   => raise ERR "conc_obs_compute" "more than one state has a true path condition?!?!?!";
    in
      final_state
    end;

  fun conc_exec_obs_extract symb_state =
    let
      fun eval_exp t = (rhs o concl o EVAL) t;
      fun eval_exp_to_val t =
        let
          val res = eval_exp ``bir_eval_exp ^t (BEnv (\x. NONE))``;
          val res_v = if is_some res then dest_some res else
                  raise ERR "conc_exec_obs_extract::eval_exp_to_val" "could not evaluate down to a value";
        in
          res_v
        end;
      fun eval_explist_to_vallist t =
        let
          val (tl, tt) = dest_list t
                         handle _ => raise ERR "conc_exec_obs_extract::eval_explist_to_vallist" "input is not a list";
          val _ = if tt = ``:bir_exp_t`` then ()
                  else raise ERR "conc_exec_obs_extract::eval_explist_to_vallist" "wrong list type";
        in
          mk_list (map eval_exp_to_val tl, ``:bir_val_t``)
        end;
      val state_ = symb_state;
      val _ = if symb_is_BST_Halted state_ then () else
              raise ERR "conc_exec_program" "the final state is not halted, something is off";
      val (_,_,_,_,observation) = dest_bir_symb_state state_;

      val nonemp_obs = filter (fn ob => (not o List.null o snd o strip_comb) ob) [observation];
      val obs_elem = map (fn ob => (fst o dest_list) ob)nonemp_obs;
      val obs_exp = map (fn ob => let val (c,t,f) = (dest_bir_symb_obs)  ob in (c,t,f) end) (flatten obs_elem);
      val res = List.concat
                    (map (fn (cond,ob,f) =>
                             if identical (eval_exp_to_val cond)
                                          ``BVal_Imm (Imm1 1w)``
                             then let val t = mk_comb (f, eval_explist_to_vallist ob)
                                  in [eval_exp t] end
                             else [])
                                 obs_exp);
    in res end;

  fun conc_exec_obs_compute prog s =
    let
      val envfo = SOME (gen_symb_updates s);
      val state_ = conc_exec_program 200 prog envfo;
      val obs = conc_exec_obs_extract state_;

      val _ = map print_term obs;
      val _ = print "\n";
    in
      obs
    end;

  fun conc_exec_obs_compare prog (s1, s2) =
    list_eq identical (conc_exec_obs_compute prog s1) (conc_exec_obs_compute prog s2);


(*

open bir_cfgVizLib;
open bir_obs_modelLib;
open bir_prog_genLib;
open bir_embexp_driverLib;

open optionSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open wordsSyntax;

(*
export HOLBA_EMBEXP_LOGS="/home/xmate/Projects/HolBA/logs/EmbExp-Logs";
*)

val obs_model_id = "cache_tag_index";

(*
val exp_ids = ["arm8/exps2/exp_cache_multiw/7d4fd31c0865567aae1ab23c57256c3e6dc6215d"];
*)

val listname = "hamperiments32_eqobs";
val exp_ids = bir_embexp_load_exp_ids listname;

(*
val exp_id = hd exp_ids;
val exp_ids = tl exp_ids;
val _ = print "\n\n\n\n";
val _ = print exp_id;
val _ = print "\n=============================\n";
*)

fun compare_obss_of_exp obs_model_id exp_id =
  let
    val (asm_lines, (s1,s2)) = bir_embexp_load_exp exp_id;

    val (_, lifted_prog) = prog_gen_store_fromlines asm_lines ();

    val add_obs = #add_obs (get_obs_model obs_model_id)
    val prog = add_obs lifted_prog;
    (*
    fun convobs_fun obs = (Arbnum.toHexString o (fn x => Arbnum.* (x, Arbnum.fromInt 64)) o dest_word_literal o dest_Imm64 o dest_BVal_Imm o dest_some) obs;
    val convobsl_fun = List.map convobs_fun;

    val obsl1 = conc_exec_obs_compute prog s1;
    val obsl2 = conc_exec_obs_compute prog s2;

    val obsl1_ = convobsl_fun obsl1;
    val obsl2_ = convobsl_fun obsl2;
    *)
  in
    conc_exec_obs_compare prog (s1,s2)
  end;

val results = List.map (fn x => (compare_obss_of_exp obs_model_id x, x)) exp_ids;


val _ = List.map (fn (b, s) => if b then print (s ^ "\n") else ()) results;


val exp_id = "arm8/exps2/exp_cache_multiw/113126365c7e68aa0b83ef9f42ff6ee6407b418b";
val (asm_lines, (s1,s2)) = bir_embexp_load_exp exp_id;
val (_, lifted_prog) = prog_gen_store_fromlines asm_lines ();
val add_obs = #add_obs (get_obs_model obs_model_id)
val prog = add_obs lifted_prog;

conc_exec_obs_compute prog s1;
conc_exec_obs_compute prog s2;
conc_exec_obs_compare prog (s1,s2);


val dot_path = "/home/xmate/Projects/HolBA/HolBA/src/tools/scamv/tempdir/cfg.dot";
bir_cfgVizLib.bir_export_graph_from_prog prog dot_path;
*)
end (* struct *)
