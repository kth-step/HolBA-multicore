signature strongPostCondLib  =
sig
  include Abbrev

  val strong_post_define_consts :  term -> unit
  val strong_post_proof : term -> unit

end
