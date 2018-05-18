
(*****************************************************************************
 *
 * graf.mli  Funciones para la visualización gráfica e impresión de los
 *           autómatas.
 *
 *****************************************************************************)

val dot_of_af : Auto.af -> string;;
val dibuja_af : Auto.af -> unit;;

val dot_of_ap : Auto.ap -> string;;
val dibuja_ap : Auto.ap -> unit;;

val dot_of_mt : Auto.mt -> string;;
val dibuja_mt : Auto.mt -> unit;;

(*****************************************************************************)

