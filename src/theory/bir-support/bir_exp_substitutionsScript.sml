(*
  Substitution of variables in BIR expressions
*)

open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory;
open bir_immTheory bir_typing_expTheory;
open bir_exp_memTheory bir_expTheory;
open bir_exp_immTheory;
open finite_mapTheory pred_setTheory;
open HolBACoreSimps

val _ = new_theory "bir_exp_substitutions";


(* Basic parallel subsitution *)

val bir_exp_subst_var_def = Define `
  bir_exp_subst_var s v = case FLOOKUP s v of NONE => BExp_Den v | SOME e => e`;

val bir_exp_subst_var_REWRS = store_thm ("bir_exp_subst_var_REWRS",
  ``(!v. bir_exp_subst_var FEMPTY v = BExp_Den v) /\
    (!s v ve v'. bir_exp_subst_var (s |+ (v, ve)) v' = (if v = v' then ve else bir_exp_subst_var s v'))``,

SIMP_TAC std_ss [bir_exp_subst_var_def, FLOOKUP_EMPTY,
  FLOOKUP_UPDATE] >>
REPEAT STRIP_TAC >>
REPEAT CASE_TAC);

val bir_exp_subst_def = Define `
   (!s n. bir_exp_subst s (BExp_Const n) = (BExp_Const n)) /\
   (!s aty vty mmap. bir_exp_subst s (BExp_MemConst aty vty mmap) = (BExp_MemConst aty vty mmap)) /\
   (!s v. bir_exp_subst s (BExp_Den v) = bir_exp_subst_var s v) /\
   (!s ct e ty.
      bir_exp_subst s (BExp_Cast ct e ty) =
      BExp_Cast ct (bir_exp_subst s e) ty) /\
   (!s et e.
      bir_exp_subst s (BExp_UnaryExp et e) =
      BExp_UnaryExp et (bir_exp_subst s e)) /\
   (!s et e1 e2.
      bir_exp_subst s (BExp_BinExp et e1 e2) =
      BExp_BinExp et (bir_exp_subst s e1)
        (bir_exp_subst s e2)) /\
   (!s pt e1 e2.
      bir_exp_subst s (BExp_BinPred pt e1 e2) =
      BExp_BinPred pt (bir_exp_subst s e1)
        (bir_exp_subst s e2)) /\
   (!s me1 me2.
      bir_exp_subst s (BExp_MemEq me1 me2) =
      BExp_MemEq (bir_exp_subst s me1)
        (bir_exp_subst s me2)) /\
   (!s c et ef.
      bir_exp_subst s (BExp_IfThenElse c et ef) =
      BExp_IfThenElse (bir_exp_subst s c) (bir_exp_subst s et)
        (bir_exp_subst s ef)) /\
   (!s en ty.
      bir_exp_subst s (BExp_ExtGet en ty) = (BExp_ExtGet en ty)) /\
   (!s mem_e a_e en ty.
      bir_exp_subst s (BExp_Load mem_e a_e en ty) =
      BExp_Load (bir_exp_subst s mem_e) (bir_exp_subst s a_e) en
        ty) /\
   (!s mem_e a_e en v_e.
     bir_exp_subst s (BExp_Store mem_e a_e en v_e) =
     BExp_Store (bir_exp_subst s mem_e) (bir_exp_subst s a_e) en
       (bir_exp_subst s v_e))`;


(* An empty substitution is the identity operation *)
val bir_exp_subst_EMPTY = store_thm ("bir_exp_subst_EMPTY",
  ``!e. bir_exp_subst FEMPTY e = e``,
Induct >> (
  ASM_SIMP_TAC std_ss [bir_exp_subst_def, FLOOKUP_EMPTY, bir_exp_subst_var_def]
));

(* Substitution preserves typing if done properly *)
Theorem bir_exp_subst_TYPE_EQ_GEN:
  !ext_map s1 s2 e.
  (!v. type_of_bir_exp (bir_exp_subst_var s1 v) =
        type_of_bir_exp (bir_exp_subst_var s2 v)) ==>
  type_of_bir_exp (bir_exp_subst s1 e)
  = type_of_bir_exp (bir_exp_subst s2 e)
Proof
  REPEAT STRIP_TAC >>
  Induct_on `e` >>
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_exp_subst_def]
QED

Theorem bir_exp_subst_TYPE_EQ:
  !ext_map s e.
  FEVERY (\ (v, e). type_of_bir_exp e = SOME (bir_var_type v)) s ==>
    type_of_bir_exp (bir_exp_subst s e) = type_of_bir_exp e
Proof
  REPEAT STRIP_TAC >>
  MP_TAC (Q.SPECL [`ext_map`, `s`, `FEMPTY`, `e`] bir_exp_subst_TYPE_EQ_GEN) >>
  MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) >>
  FULL_SIMP_TAC std_ss [bir_exp_subst_EMPTY, bir_exp_subst_var_def, FLOOKUP_EMPTY,
    FEVERY_ALL_FLOOKUP] >>
  GEN_TAC >>
  Cases_on `FLOOKUP s v` >>
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def]
QED

(* Not well-typed sub-expressions always cause trouble *)
val bir_exp_subst_NO_TYPE = store_thm ("bir_exp_subst_NO_TYPE", ``
  !ext_map s e v ve. (
    (v IN bir_vars_of_exp e) /\
    (FLOOKUP s v = SOME ve) /\
    (type_of_bir_exp ve = NONE)) ==>
    (type_of_bir_exp (bir_exp_subst s e) = NONE)``,

REPEAT STRIP_TAC >>
Induct_on `e` >> (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [
    type_of_bir_exp_def, bir_exp_subst_def, bir_vars_of_exp_def,
    bir_exp_subst_var_def, pairTheory.pair_case_thm] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  REPEAT CASE_TAC
));


(* The evaluation is preserved if only substituting equivalent expressions. *)
val bir_exp_subst_EVAL_EQ_GEN = store_thm ("bir_exp_subst_EVAL_EQ_GEN", ``
  !env ext_st s1 s2 e.
  (!v. (bir_eval_exp (bir_exp_subst_var s1 v) env ext_st =
        bir_eval_exp (bir_exp_subst_var s2 v) env ext_st)) ==>
  (bir_eval_exp (bir_exp_subst s1 e) env ext_st = bir_eval_exp (bir_exp_subst s2 e) env ext_st)``,

REPEAT STRIP_TAC >>
Induct_on `e` >> (
  ASM_SIMP_TAC std_ss [bir_eval_exp_def, bir_exp_subst_def]
));


val bir_exp_subst_EVAL_EQ = store_thm ("bir_exp_subst_EVAL_EQ", ``
  !env ext_st s e.
  FEVERY (\ (v, e). (bir_eval_exp e env ext_st = bir_env_read v env)) s ==>
  (bir_eval_exp (bir_exp_subst s e) env ext_st = bir_eval_exp e env ext_st)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`env`, `ext_st`, `s`, `FEMPTY`, `e`] bir_exp_subst_EVAL_EQ_GEN) >>
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) >>
FULL_SIMP_TAC std_ss [bir_exp_subst_EMPTY, bir_exp_subst_var_def, FLOOKUP_EMPTY,
  FEVERY_ALL_FLOOKUP] >>
GEN_TAC >>
Cases_on `FLOOKUP s v` >> (
  ASM_SIMP_TAC std_ss [bir_eval_exp_def]
));


(* The set of used vars changes *)
val bir_exp_subst_USED_VARS = store_thm ("bir_exp_subst_USED_VARS",
``!s e. bir_vars_of_exp (bir_exp_subst s e) =
        ((bir_vars_of_exp e) DIFF (FDOM s)) UNION
        (BIGUNION (IMAGE bir_vars_of_exp
           {e' | ?v. ((v IN (bir_vars_of_exp e)) /\ (FLOOKUP s v = SOME e'))}))``,

GEN_TAC >>
SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [PULL_EXISTS] >>
Induct_on `e` >> (
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst_def, bir_vars_of_exp_def] >>
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [RIGHT_AND_OVER_OR,
    LEFT_AND_OVER_OR, EXISTS_OR_THM, bir_exp_subst_var_def]
) >>
REPEAT STRIP_TAC >>
CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++boolSimps.EQUIV_EXTRACT_ss) [
    bir_vars_of_exp_def, flookup_thm] >>
  METIS_TAC[]
));


(* The set of used exts changes *)
val bir_exp_subst_USED_EXTS = store_thm ("bir_exp_subst_USED_EXTS",
``!s e. bir_exts_of_exp (bir_exp_subst s e) =
        (bir_exts_of_exp e) UNION
        (BIGUNION (IMAGE bir_exts_of_exp
           {e' | ?v. ((v IN (bir_vars_of_exp e)) /\ (FLOOKUP s v = SOME e'))}))``,

GEN_TAC >>
SIMP_TAC std_ss [EXTENSION] >>
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [PULL_EXISTS] >>
Induct_on `e` >> (
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst_def, bir_vars_of_exp_def, bir_exts_of_exp_def] >>
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [RIGHT_AND_OVER_OR,
    LEFT_AND_OVER_OR, EXISTS_OR_THM, bir_exp_subst_var_def]
) >>
REPEAT STRIP_TAC >>
CASE_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exts_of_exp_def]
);



(* Variables not occurring in the expression are irrelevant *)
val bir_exp_subst_UNUSED_VARS_OVERAPPROX = store_thm ("bir_exp_subst_UNUSED_VARS_OVERAPPROX",
``!s vs e. bir_vars_of_exp e SUBSET vs ==>
           (bir_exp_subst (DRESTRICT s vs) e = bir_exp_subst s e)``,

REPEAT STRIP_TAC >>
Induct_on `e` >> (
  ASM_SIMP_TAC std_ss [bir_exp_subst_def, bir_vars_of_exp_def,
    INSERT_SUBSET, UNION_SUBSET, EMPTY_SUBSET, FLOOKUP_DRESTRICT, bir_exp_subst_var_def]
));


val bir_exp_subst_UNUSED_VARS = store_thm ("bir_exp_subst_UNUSED_VARS",
``!s e. (bir_exp_subst (DRESTRICT s (bir_vars_of_exp e)) e = bir_exp_subst s e)``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_exp_subst_UNUSED_VARS_OVERAPPROX >>
REWRITE_TAC[SUBSET_REFL]);



(* Often we are interested in just 1 var. This leads to the following specialised version. *)

val bir_exp_subst1_def = Define `
   bir_exp_subst1 v ve = (bir_exp_subst (FEMPTY |+ (v, ve)))`;


val bir_exp_subst1_REWRS = store_thm ("bir_exp_subst1_REWRS",
`` (!v ve n. bir_exp_subst1 v ve (BExp_Const n) = (BExp_Const n)) /\
   (!v ve aty vty mmap. bir_exp_subst1 v ve (BExp_MemConst aty vty mmap) = (BExp_MemConst aty vty mmap)) /\
   (!v ve v'. bir_exp_subst1 v ve (BExp_Den v') = (if v = v' then ve else (BExp_Den v'))) /\
   (!v ve ct e ty.
      bir_exp_subst1 v ve (BExp_Cast ct e ty) =
      BExp_Cast ct (bir_exp_subst1 v ve e) ty) /\
   (!v ve et e.
      bir_exp_subst1 v ve (BExp_UnaryExp et e) =
      BExp_UnaryExp et (bir_exp_subst1 v ve e)) /\
   (!v ve et e1 e2.
      bir_exp_subst1 v ve (BExp_BinExp et e1 e2) =
      BExp_BinExp et (bir_exp_subst1 v ve e1)
        (bir_exp_subst1 v ve e2)) /\
   (!v ve pt e1 e2.
      bir_exp_subst1 v ve (BExp_BinPred pt e1 e2) =
      BExp_BinPred pt (bir_exp_subst1 v ve e1)
        (bir_exp_subst1 v ve e2)) /\
   (!v ve me1 me2.
      bir_exp_subst1 v ve (BExp_MemEq me1 me2) =
      BExp_MemEq (bir_exp_subst1 v ve me1)
        (bir_exp_subst1 v ve me2)) /\
   (!v ve c et ef.
      bir_exp_subst1 v ve (BExp_IfThenElse c et ef) =
      BExp_IfThenElse (bir_exp_subst1 v ve c) (bir_exp_subst1 v ve et)
        (bir_exp_subst1 v ve ef)) /\
   (!v ve en ty.
      bir_exp_subst1 v ve (BExp_ExtGet en ty) = (BExp_ExtGet en ty)) /\
   (!v ve mem_e a_e en ty.
      bir_exp_subst1 v ve (BExp_Load mem_e a_e en ty) =
      BExp_Load (bir_exp_subst1 v ve mem_e) (bir_exp_subst1 v ve a_e) en
        ty) /\
   (!v ve mem_e a_e en v_e.
     bir_exp_subst1 v ve (BExp_Store mem_e a_e en v_e) =
     BExp_Store (bir_exp_subst1 v ve mem_e) (bir_exp_subst1 v ve a_e) en
       (bir_exp_subst1 v ve v_e))``,

SIMP_TAC std_ss [bir_exp_subst1_def, bir_exp_subst_def, FLOOKUP_UPDATE,
  FLOOKUP_EMPTY, bir_exp_subst_var_def] >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) []);


Theorem bir_exp_subst1_TYPE_EQ_GEN:
  !v ve ve' e. type_of_bir_exp ve = type_of_bir_exp ve'
  ==> type_of_bir_exp (bir_exp_subst1 v ve e)
    = type_of_bir_exp (bir_exp_subst1 v ve' e)
Proof
  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [bir_exp_subst1_def] >>
  MATCH_MP_TAC bir_exp_subst_TYPE_EQ_GEN >>
  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exp_subst_var_REWRS]
QED

val bir_exp_subst1_TYPE_EQ = store_thm ("bir_exp_subst1_TYPE_EQ",
  ``!v ve e. (type_of_bir_exp ve = SOME (bir_var_type v)) ==>
             (type_of_bir_exp (bir_exp_subst1 v ve e) = type_of_bir_exp e)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exp_subst1_def] >>
MATCH_MP_TAC bir_exp_subst_TYPE_EQ >>
ASM_SIMP_TAC std_ss [FEVERY_FUPDATE, DRESTRICT_FEMPTY, FEVERY_FEMPTY]);


val bir_exp_subst1_NO_TYPE = store_thm ("bir_exp_subst1_NO_TYPE", ``
  !e v ve. (
    (v IN bir_vars_of_exp e) /\
    (type_of_bir_exp ve = NONE)) ==>
    (type_of_bir_exp (bir_exp_subst1 v ve e) = NONE)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exp_subst1_def] >>
MATCH_MP_TAC bir_exp_subst_NO_TYPE >>
ASM_SIMP_TAC std_ss [FLOOKUP_EMPTY, FLOOKUP_UPDATE]);


Theorem bir_exp_subst1_NO_TYPE_SOME:
  !e v ve ty. (
    (v IN bir_vars_of_exp e) ==>
    (type_of_bir_exp (bir_exp_subst1 v ve e) = SOME ty) ==>
    (?ty. type_of_bir_exp ve = SOME ty))
Proof
  REPEAT STRIP_TAC >>
  Cases_on `type_of_bir_exp ve` >> ASM_SIMP_TAC std_ss [] >>
  METIS_TAC[bir_exp_subst1_NO_TYPE, optionTheory.option_CLAUSES]
QED

val bir_exp_subst1_EVAL_EQ_GEN = store_thm ("bir_exp_subst1_EVAL_EQ_GEN", ``
  !env ext_st v ve ve' e.
  (bir_eval_exp ve env ext_st = bir_eval_exp ve' env ext_st) ==>
  (bir_eval_exp (bir_exp_subst1 v ve e) env ext_st = bir_eval_exp (bir_exp_subst1 v ve' e) env ext_st)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exp_subst1_def] >>
MATCH_MP_TAC bir_exp_subst_EVAL_EQ_GEN >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exp_subst_var_REWRS]);


val bir_exp_subst1_EVAL_EQ = store_thm ("bir_exp_subst1_EVAL_EQ", ``
  !env ext_st v ve e.
  (bir_eval_exp ve env ext_st = bir_env_read v env) ==>
  (bir_eval_exp (bir_exp_subst1 v ve e) env ext_st = bir_eval_exp e env ext_st)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exp_subst1_def] >>
MATCH_MP_TAC bir_exp_subst_EVAL_EQ >>
ASM_SIMP_TAC std_ss [FEVERY_FUPDATE, DRESTRICT_FEMPTY, FEVERY_FEMPTY]);


val bir_exp_subst1_USED_VARS = store_thm ("bir_exp_subst1_USED_VARS",
``!v ve e. bir_vars_of_exp (bir_exp_subst1 v ve e) =
        ((bir_vars_of_exp e) DIFF {v}) UNION
        (if v IN bir_vars_of_exp e then bir_vars_of_exp ve else {})``,

SIMP_TAC std_ss [bir_exp_subst1_def, bir_exp_subst_USED_VARS,
  FDOM_FEMPTY, FDOM_FUPDATE, FLOOKUP_UPDATE, FLOOKUP_EMPTY, EXTENSION] >>
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++
          boolSimps.EQUIV_EXTRACT_ss) []);


val bir_exp_subst1_USED_EXTS = store_thm ("bir_exp_subst1_USED_EXTS",
``!v ve e. bir_exts_of_exp (bir_exp_subst1 v ve e) =
        (bir_exts_of_exp e) UNION
        (if v IN bir_vars_of_exp e then bir_exts_of_exp ve else {})``,

SIMP_TAC std_ss [bir_exp_subst1_def, bir_exp_subst_USED_EXTS,
  FDOM_FEMPTY, FDOM_FUPDATE, FLOOKUP_UPDATE, FLOOKUP_EMPTY, EXTENSION] >>
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++
          boolSimps.EQUIV_EXTRACT_ss) []
);


(* Variables not occurring in the expression are irrelevant *)
val bir_exp_subst1_UNUSED_VAR = store_thm ("bir_exp_subst1_UNUSED_VAR",
``!v ve e. ~(v IN bir_vars_of_exp e) ==>
           (bir_exp_subst1 v ve e = e)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exp_subst1_def] >>
ONCE_REWRITE_TAC [GSYM bir_exp_subst_UNUSED_VARS] >>
ASM_SIMP_TAC std_ss [DRESTRICT_FUPDATE, DRESTRICT_FEMPTY,
  bir_exp_subst_EMPTY]);


val bir_eval_exp_subst1_env = store_thm("bir_eval_exp_subst1_env",
``!ex env ext_st varn ty e1 e1_va.
    (bir_env_lookup_type varn (BEnv env) = SOME ty) ==>
    (bir_eval_exp e1 (BEnv env) ext_st = SOME e1_va) ==>
    (type_of_bir_val e1_va = ty) ==>
    (bir_eval_exp ex
      (BEnv ((varn =+ SOME e1_va) env)) ext_st =
        bir_eval_exp (bir_exp_subst1 (BVar varn ty) e1 ex)
                     (BEnv env) ext_st
    )``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Induct_on `ex` >> (
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_exp_subst1_REWRS]
) >>
(* Case not handled: BExp_Den *)
Cases_on `b = BVar varn ty` >- (
  FULL_SIMP_TAC std_ss [bir_exp_subst1_REWRS, bir_env_read_def, bir_var_name_def,
                 bir_env_lookup_def, bir_env_check_type_def, bir_env_lookup_type_def] >>
  FULL_SIMP_TAC std_ss [bir_var_type_def] >>
  FULL_SIMP_TAC std_ss [combinTheory.UPDATE_def]
) >>
Cases_on `b` >>
Cases_on `varn = s` >> (
  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_var_type_def, bir_var_name_def, bir_env_lookup_def, combinTheory.UPDATE_APPLY, bir_var_eq_EXPAND] >>
  REV_FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_var_type_def, bir_var_name_def, bir_env_lookup_def, combinTheory.UPDATE_APPLY, bir_var_eq_EXPAND]
));


val _ = export_theory();
