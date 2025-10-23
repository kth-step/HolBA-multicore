open litmusInterfaceLib
open bir_fileLib;


datatype status = OK | ERROR of string;


fun lift_test_and_save inputfile outputfile =
    (save_litmus (outputfile, lift_herd_litmus inputfile); 
     OK)
    handle e => ERROR (exnMessage e);

						       
fun main () =
    let
	val arguments  = CommandLine.arguments ();
	val length     = List.length arguments;
	val inputfile  = List.nth (arguments, length-2);
	val outputfile = List.nth (arguments, length-1)
    in
	case lift_test_and_save inputfile outputfile
	 of OK      => Unix.exit (Word8.fromInt 0)
	  | ERROR s => (print s; Unix.exit (Word8.fromInt 1))
    end

val () = PolyML.export ("lifter.o", main);
