signature bir_programLib =
sig
  include Abbrev

  val bgcs_bmc_prog_thms     : term -> thm
  val blop_prog_labels_thm   : term -> thm

end
