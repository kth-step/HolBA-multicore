open HolKernel Parse boolLib bossLib;

open bir_program_valid_stateTheory;

val _ = new_theory "bir_ext";


(* This definition captures what an extern block must obey to play
 * nice with the existing theorems in bir-support.
 * Note this notion is stated with respect to a specific program *)
(* TODO: Rename *)
Definition well_formed_ext_def:
  well_formed_ext p ext =
    (bir_is_well_typed_ext ext /\
    !st st'.
    bir_exec_block_ext ext.beb_relation st = st' ==>
    bir_is_valid_pc p st.bst_pc ==>
    bir_is_valid_pc p st'.bst_pc)
End

(* The entire program is well-formed with respect to extern blocks *)
Definition well_formed_prog_ext_def:
  well_formed_prog_ext p =
    !st ext.
    bir_get_current_block p st.bst_pc = SOME (BBlock_Ext ext) ==>
    well_formed_ext p ext
End

val _ = export_theory();
