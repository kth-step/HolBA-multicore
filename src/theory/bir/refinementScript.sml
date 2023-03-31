(*
  A general framework for refinement proofs, with applications to refinements of
  BIR program code
*)

open HolKernel boolLib bossLib Parse;

val _ = new_theory "refinement";

Theorem RC_RTC_EQ:
  !R. RC (RTC R) = RTC R
Proof
  rw[relationTheory.RC_DEF,FUN_EQ_THM,EQ_IMP_THM]
  >> fs[relationTheory.RTC_REFL]
QED

(*
 * refinement theorem to show:
 * s -> s' ==> ref P R s s'
 * where P is the refinement relation and R is the abstract transition relation
 *)
Definition ref_def:
  ref P R s s' =
    !as. P s as ==> ?as'. R as as' /\ P s' as'
End

(* RC R' refines R under refinement relation P *)
Definition refinement_RC_def:
  refinement_RC R R' P = !s s'. R s s' ==> ref P (RC R') s s'
End

(* R' refines R under refinement relation P *)
Definition refinement_def:
  refinement R R' P = !s s'. R s s' ==> ref P R' s s'
End

Theorem refinement_RTC:
  !R R' P. refinement R R' P ==> refinement (RTC R) (RTC R') P
Proof
  rpt strip_tac
  >> simp[refinement_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT_RIGHT1
  >> conj_tac
  >- (
    rw[refinement_def,ref_def,RC_RTC_EQ]
    >> irule_at Any relationTheory.RTC_REFL
    >> asm_rewrite_tac[]
  )
  >> fs[refinement_def,ref_def,RC_RTC_EQ]
  >> rw[]
  >> rpt $ first_x_assum $ drule_then strip_assume_tac
  >> simp[Once relationTheory.RTC_CASES_RTC_TWICE,PULL_EXISTS,AC CONJ_ASSOC CONJ_COMM]
  >> rpt $ goal_assum drule
  >> fs[relationTheory.RC_RTC]
QED

Theorem refinement_RC_RTC:
  !R R' P. refinement_RC R R' P ==> refinement_RC (RTC R) (RTC R') P
Proof
  rpt strip_tac
  >> simp[refinement_RC_def]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT_RIGHT1
  >> conj_tac
  >- (
    fs[refinement_RC_def]
    >> rw[ref_def,RC_RTC_EQ]
    >> irule_at Any relationTheory.RTC_REFL
    >> asm_rewrite_tac[]
  )
  >> fs[refinement_RC_def,ref_def,RC_RTC_EQ]
  >> rw[]
  >> rpt $ first_x_assum $ drule_then strip_assume_tac
  >> simp[Once relationTheory.RTC_CASES_RTC_TWICE,PULL_EXISTS,AC CONJ_ASSOC CONJ_COMM]
  >> rpt $ goal_assum drule
  >> fs[relationTheory.RC_RTC]
QED

Theorem refinement_RC_composition:
  !R R' P' R'' P''.
    refinement_RC R R' P' /\ refinement_RC R' R'' P''
    ==> refinement_RC R R'' (λs as. ?bs.  P' s bs /\ P'' bs as)
Proof
  rw[refinement_RC_def]
  >> first_x_assum $ drule_then assume_tac
  >> fs[ref_def]
  >> rw[]
  >> first_x_assum $ drule_then strip_assume_tac
  >> dxrule_then strip_assume_tac $ iffLR relationTheory.RC_DEF
  >> gvs[PULL_EXISTS]
  >- (
    irule_at Any relationTheory.RC_REFL
    >> goal_assum drule_all
  )
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> rpt $ goal_assum $ drule_at Any
QED

val _ = export_theory ();

