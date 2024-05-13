(*
  Refinement theorems for the promising semantics
 *)

open HolKernel Parse boolLib bossLib;
open rich_listTheory arithmeticTheory listTheory pairTheory optionTheory
     finite_mapTheory relationTheory;
open bir_programTheory bir_promisingTheory
     bir_promising_wfTheory bir_programLib
     promising_thmsTheory refinementTheory;

val _ = new_theory "promisingrefinement";

(* invariants *)

Definition invariant_def:
  invariant P R = !s s'. P s /\ R s s' ==> P s'
End

Theorem clstep_preserves_wf_fwdb':
  !p cid M prom.
    invariant
      (λs. (!l. well_formed_fwdb l M (s.bst_coh l) (s.bst_fwdb l)))
      (λs s'. clstep p cid s M prom s' /\ wf_ext_fwdb p cid s M)
Proof
  fs[invariant_def]
  >> rpt strip_tac
  >> drule_all clstep_preserves_wf_fwdb
  >> fs[]
QED

Theorem parstep_preserves_wf':
  invariant
    (λ(cores,M). well_formed_cores cores M /\ well_formed_ext_cores cores)
    (λ(cores,M) (cores',M'). ?cid. parstep cid cores M cores' M')
Proof
  rw[invariant_def,ELIM_UNCURRY]
  >> drule_all_then assume_tac parstep_preserves_wf
  >> fs[]
  >> fs[well_formed_ext_cores_def,parstep_cases]
  >> rw[wf_ext_p_def,FLOOKUP_UPDATE]
  >> fs[wf_ext_p_def]
QED

(* refinement theorems *)

(* inclusion abstract and concrete *)
Definition state_prog_def:
  state_prog cores p cores' p' =
    !cid. IS_SOME $ FLOOKUP cores cid ==>
            (?s. FLOOKUP cores cid = SOME $ Core cid (BirProgram p) s)
            /\ ?s'. FLOOKUP cores' cid = SOME $ Core cid (BirProgram p') s'
End

(* required properties on the refinement relation *)
Definition rel_prop_def:
  rel_prop R =
  !s M s' M' msg.
    R (s,M) (s',M') ==> s.bst_prom = s'.bst_prom
      /\ M = M'
      /\ R
        (s  with bst_prom updated_by (λx. x ++ [LENGTH M  + 1]), M ++[msg])
        (s' with bst_prom updated_by (λx. x ++ [LENGTH M' + 1]), M'++[msg])
End

Theorem rel_prop_imp:
  rel_prop R ==>
    !s M s' M'.
      R (s,M) (s',M') ==> s.bst_prom = s'.bst_prom /\ M = M'
Proof
  rw[rel_prop_def]
  >> first_x_assum drule
  >> fs[]
QED

Theorem refinement_RC_clstep_imp_cstep:
  rel_prop R
  /\ refinement_RC
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M')
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p') cid s M prom s' /\ M = M')
    R
  ==> refinement_RC
    (λ(s,M) (s',M'). ?prom. cstep (BirProgram p ) cid s M prom s' M')
    (λ(s,M) (s',M'). ?prom. cstep (BirProgram p' ) cid s M prom s' M')
    R
Proof
  rpt strip_tac >> rw[refinement_RC_thm,ELIM_UNCURRY]
  >> dxrule_then strip_assume_tac $ iffLR cstep_cases
  >~ [`clstep`]
  >- (
    gvs[refinement_RC_thm,PULL_EXISTS,ELIM_UNCURRY]
    >> first_x_assum drule >> fs[]
    >> disch_then $ dxrule_then assume_tac >> fs[]
    >> goal_assum $ dxrule_at Any
    >> dxrule $ SIMP_RULE (srw_ss()) [ELIM_UNCURRY] clstep_imp_cstep_RC
    >> ho_match_mp_tac RC_MONOTONE
    >> rw[PULL_EXISTS]
    >> gvs[]
    >> goal_assum drule
  )
  >> irule_at Any RC_SUBSET
  >> dsimp[cstep_cases,PULL_EXISTS,ELIM_UNCURRY]
  >> disj2_tac
  >> qmatch_asmsub_rename_tac `R cs as`
  >> PairCases_on `cs` >> PairCases_on `as`
  >> rename1 `R cs'` >> PairCases_on `cs'`
  >> gvs[rel_prop_def]
  >> first_x_assum $ drule_then strip_assume_tac
  >> gs[FORALL_AND_THM,ELIM_UNCURRY,PULL_EXISTS,EXISTS_PROD]
  >> irule_at Any EQ_REFL
  >> fs[]
QED

Theorem refinement_RTC_clstep_imp_cstep:
  rel_prop R
  /\ refinement_RTC
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M')
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p') cid s M prom s' /\ M = M')
    R
  ==> refinement_RTC
    (λ(s,M) (s',M'). ?prom. cstep (BirProgram p ) cid s M prom s' M')
    (λ(s,M) (s',M'). ?prom. cstep (BirProgram p' ) cid s M prom s' M')
    R
Proof
  rpt strip_tac >> rw[refinement_RTC_thm,ELIM_UNCURRY]
  >> dxrule_then strip_assume_tac $ iffLR cstep_cases
  >~ [`clstep`]
  >- (
    gvs[refinement_RTC_thm,PULL_EXISTS,ELIM_UNCURRY]
    >> first_x_assum drule >> fs[]
    >> disch_then $ dxrule_then assume_tac >> fs[]
    >> goal_assum $ dxrule_at Any
    >> dxrule $ SIMP_RULE (srw_ss()) [ELIM_UNCURRY] clstep_imp_cstep_RTC
    >> ho_match_mp_tac RTC_MONOTONE
    >> rw[PULL_EXISTS]
    >> gvs[]
    >> goal_assum drule
  )
  >> irule_at Any RTC_SINGLE
  >> dsimp[cstep_cases,PULL_EXISTS,ELIM_UNCURRY]
  >> disj2_tac
  >> qmatch_asmsub_rename_tac `R cs as`
  >> PairCases_on `cs` >> PairCases_on `as`
  >> rename1 `R cs'` >> PairCases_on `cs'`
  >> gvs[rel_prop_def]
  >> first_x_assum $ drule_then strip_assume_tac
  >> gs[FORALL_AND_THM,ELIM_UNCURRY,PULL_EXISTS,EXISTS_PROD]
  >> irule_at Any EQ_REFL
  >> fs[]
QED

Theorem refinement_RC_clstep_imp_cstep_seq:
  rel_prop R
  /\ refinement_RC
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M')
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p') cid s M prom s' /\ M = M')
    R
  ==> refinement_RC
    (cstep_seq (BirProgram p ) cid)
    (cstep_seq (BirProgram p') cid)
    R
Proof
  rpt strip_tac >> rw[refinement_RC_thm]
  >> dxrule_then assume_tac $ iffLR cstep_seq_cases
  >> gvs[ELIM_UNCURRY,PULL_EXISTS,FORALL_PROD]
  >> rename1`R (s,M) as` >> PairCases_on `as`
  (* clstep case *)
  >- (
    fs[refinement_RC_thm,PULL_EXISTS,FORALL_PROD]
    >> first_x_assum $ dxrule_all_then strip_assume_tac
    >> irule_at Any clstep_imp_cstep_seq_RC
    >> goal_assum $ dxrule_at Any
    >> fs[ELIM_UNCURRY]
  )
  >~ [`cstep`]
  >> gvs[cstep_cases]
  >> qmatch_asmsub_abbrev_tac `clstep _ cid s' M' t s''`
  >> rename1 `R (s,M) as` >> PairCases_on `as`
  >> `R (s',M') (as0 with bst_prom updated_by (λx. x ++ t),as1 ++ [msg])` by (
    dxrule_all_then assume_tac $ iffLR rel_prop_def
    >> unabbrev_all_tac
    >> gvs[IMP_CONJ_THM,FORALL_AND_THM]
  )
  >> gs[refinement_RC_thm,PULL_EXISTS,LAMBDA_PROD,FORALL_PROD,EXISTS_PROD]
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> gvs[ELIM_UNCURRY,RC_DEF]
  >- (
    (* contradiction: promise is removed *)
    unabbrev_all_tac
    >> imp_res_tac clstep_imp_bst_prom
    >> dxrule_then imp_res_tac $ rel_prop_imp
    >> fs[remove_prom_contra,remove_prom_ID]
  )
  >> dsimp[cstep_seq_cases,cstep_cases]
  >> ntac 2 disj2_tac
  >> unabbrev_all_tac
  >> goal_assum $ drule_at Any
  >> imp_res_tac rel_prop_imp
  >> imp_res_tac clstep_imp_bst_prom
  >> gvs[EVERY_MEM,IMP_CONJ_THM,remove_prom_ID]
  >> `~NULL prom` by (
    spose_not_then assume_tac
    >> fs[NULL_EQ,remove_prom_ID,remove_prom_contra]
  )
  >> qmatch_asmsub_abbrev_tac `remove_prom [t]`
  >> `!x. MEM x prom ==> x = t` by (
    spose_not_then assume_tac
    >> fs[]
    >> first_x_assum $ drule_then strip_assume_tac
    >> fs[]
    >> `MEM x $ remove_prom [t] as0.bst_prom` by
      simp[remove_prom_def,MEM_FILTER]
    >> pop_assum mp_tac
    >> qpat_x_assum `remove_prom _ _ ++ remove_prom _ _ = _` $ rewrite_tac o single o GSYM
    >> simp[MEM_FILTER,remove_prom_def,COND_RAND,COND_RATOR]
  )
  >> `nub prom = [LENGTH M + 1]` by (
    cheat (* MEM_nub all_distinct_nub *)
  )
  >> cheat
  (* need to add nub function to BSExt for the fulfiled promises prom *)
  (* need to prove that
    clstep p cid s M prom s' = clstep p cid s M (nub prom) s'
  *)
QED

Theorem refinement_RC_is_certified:
  rel_prop R
  /\ refinement_RC
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M')
    (λ(s,M) (s',M'). ?prom. clstep (BirProgram p') cid s M prom s' /\ M = M')
    R
  /\ is_certified (BirProgram p) cid cs cM
  /\ R (cs,cM) (as,aM)
  ==> is_certified (BirProgram p') cid as aM
Proof
  rpt strip_tac >> fs[is_certified_def,cstep_seq_rtc_def]
  >> drule_all_then assume_tac refinement_RC_clstep_imp_cstep_seq
  >> dxrule refinement_RC_RTC
  >> fs[refinement_thm,rel_prop_def]
  >> disch_then $ dxrule_all_then strip_assume_tac
  >> qmatch_asmsub_rename_tac `R _ as'` >> PairCases_on `as'`
  >> goal_assum dxrule
  >> first_x_assum $ drule_then assume_tac
  >> fs[]
QED

Theorem refinement_RC_clstep_imp_parstep:
  rel_prop R
  /\ refinement_RC
      (λ(s,M) (s',M'). ?prom. clstep (BirProgram p) cid s M prom s' /\ M = M')
      (λ(s,M) (s',M'). ?prom. clstep (BirProgram p') cid s M prom s' /\ M = M')
      R
  ==> refinement_RC
      (λ(cores,M) (cores',M'). parstep cid cores M cores' M')
      (λ(cores,M) (cores',M'). parstep cid cores M cores' M')
      (λ(cores,M) (cores',M').
          state_prog cores p cores' p'
          /\ !s s'.
            FLOOKUP cores cid = SOME $ Core cid (BirProgram p) s
            /\ FLOOKUP cores' cid = SOME $ Core cid (BirProgram p') s'
            ==> R (s,M) (s',M'))
Proof
  rpt strip_tac
  >> rw[refinement_RC_thm,ELIM_UNCURRY]
  >> dxrule_then strip_assume_tac $ iffLR parstep_cases
  >> rename1`SOME $ Core cid p'' s`
  >> `p'' = BirProgram p` by (
    fs[state_prog_def,IS_SOME_EXISTS,PULL_EXISTS]
    >> first_x_assum $ drule_then strip_assume_tac
    >> gvs[]
  )
  >> gvs[]
  >> drule $ SIMP_RULE(std_ss) [ELIM_UNCURRY] refinement_RC_is_certified
  >> gvs[PULL_EXISTS,ELIM_UNCURRY]
  >> disch_then $ drule_then $ drule_then assume_tac
  (* establish R for post cstep *)
  >> drule refinement_RC_clstep_imp_cstep
  >> fs[ELIM_UNCURRY]
  >> disch_then drule
  >> simp[refinement_RC_thm,FORALL_PROD,PULL_EXISTS]
  >> disch_then drule
  >> `?s. FLOOKUP (FST as) cid = SOME $ Core cid (BirProgram p') s` by
    fs[state_prog_def]
  >> first_x_assum $ drule_then assume_tac
  >> disch_then $ drule_then strip_assume_tac (* abstract step *)
  >> rename1`R (s', _) as'` >> PairCases_on `as'`
  >> first_x_assum $ drule_then assume_tac (* is_certified *)
  (* abstract step cases *)
  >> dxrule_then assume_tac $ iffLR RC_DEF >> gvs[]
  (* abstract unchanged *)
  >- (
    dsimp[RC_DEF] >> disj1_tac
    >> conj_tac
    (* state_prog *)
    >- (
      fs[state_prog_def,FLOOKUP_UPDATE] >> rw[] >> fs[]
    )
    >> fs[FLOOKUP_UPDATE]
  )
  (* change also on abstract level *)
  >> dsimp[RC_DEF,parstep_cases] >> disj2_tac
  >> fs[EXISTS_PROD]
  >> goal_assum drule >> fs[]
  >> conj_tac
  (* state_prog *)
  >- (
    fs[state_prog_def,FLOOKUP_UPDATE] >> rw[] >> fs[]
  )
  >> fs[FLOOKUP_UPDATE]
QED

val _ = export_theory ();
