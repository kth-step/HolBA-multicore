structure herdLitmusValuesLib =
struct

    open HolKernel bossLib boolLib Parse;
    open computeLib;
    open numSyntax bir_immSyntax wordsSyntax wordsLib;

fun word_of_string s sz =
    case Int.fromString s
     of SOME n => mk_wordii(n, sz)
      | NONE => mk_const("lc_" ^ s, mk_int_word_type sz)

end		     
