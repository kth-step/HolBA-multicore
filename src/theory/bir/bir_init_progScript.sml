(*
  defines an initial state of a program
*)

open HolKernel Parse boolLib bossLib;
open bir_typing_progTheory bir_programTheory;

val _ = new_theory "bir_init_prog";

Definition bir_state_init_def:
  bir_state_init p = <|
    bst_pc       := bir_pc_first p
  ; bst_environ  := bir_env_default $ bir_envty_of_vs $ bir_vars_of_program p
  ; bst_status := BST_Running
  ; bst_viewenv := FEMPTY
  ; bst_coh := \x.0
  ; bst_v_rOld := 0
  ; bst_v_CAP := 0
  ; bst_v_rNew := 0
  ; bst_v_wNew := 0
  ; bst_v_wOld := 0
  ; bst_v_Rel := 0
  ; bst_prom := []
  ; bst_inflight := []
  ; bst_counter := 0
  ; bst_fwdb := (\l. <| fwdb_time:= 0; fwdb_view:=0; fwdb_xcl:=F |>)
  ; bst_xclb := NONE
  |>
End

Definition bmc_state_init_def:
  bmc_state_init p = <|
      bst_pc       := bir_pc_first p
    ; bst_environ  := bir_env_default $ bir_envty_of_vs $ bmc_vars_of_program p
    ; bst_status := BST_Running
    ; bst_viewenv := FEMPTY
    ; bst_coh := \x.0
    ; bst_v_rOld := 0
    ; bst_v_CAP := 0
    ; bst_v_rNew := 0
    ; bst_v_wNew := 0
    ; bst_v_wOld := 0
    ; bst_v_Rel := 0
    ; bst_prom := []
    ; bst_inflight := []
    ; bst_counter := 0
    ; bst_fwdb := (\l. <| fwdb_time:= 0; fwdb_view:=0; fwdb_xcl:=F |>)
    ; bst_xclb := NONE
  |>
End

val _ = export_theory();
