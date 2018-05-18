
(*****************************************************************************
 *
 * conj.ml   Una implementación basada en listas para realizar operaciones   
 *           básicas sobre conjuntos de elementos de cualquier tipo.         
 *
 *****************************************************************************)

type 'a conjunto = Conjunto of 'a list;;

(*****************************************************************************)

let conjunto_vacio = Conjunto [];;

(*****************************************************************************)

let es_vacio = function
     Conjunto [] -> true
   | _           -> false;;

(*****************************************************************************)

let rec pertenece a = function
     Conjunto []     -> false
   | Conjunto (x::l) -> (x = a) || (pertenece a (Conjunto l));;

(*****************************************************************************)

let agregar a (Conjunto l) = 
   if pertenece a (Conjunto l) then
      Conjunto l
   else
      Conjunto (a::l)
   ;;

(*****************************************************************************)

let rec conjunto_of_list = function
     []     -> conjunto_vacio
   | (x::l) -> agregar x (conjunto_of_list l);;

(*****************************************************************************)

let rec suprimir a = function
     Conjunto []     -> conjunto_vacio
   | Conjunto (x::l) -> if (x = a) then 
                           Conjunto l
			else 
                           agregar x (suprimir a (Conjunto l))
                        ;;

(*****************************************************************************)

let cardinal (Conjunto l) = List.length l;;

(*****************************************************************************)

let union (Conjunto a) (Conjunto b) = conjunto_of_list (a @ b) ;;

(*****************************************************************************)

let rec interseccion (Conjunto a) = function
     Conjunto []     -> conjunto_vacio
   | Conjunto (x::l) -> if pertenece x (Conjunto a) then 
			   agregar x (interseccion (Conjunto a) (Conjunto l))
			else 
			   interseccion (Conjunto a) (Conjunto l)
                        ;;

(*****************************************************************************)

let rec diferencia (Conjunto a) = function
     Conjunto []     -> Conjunto a
   | Conjunto (x::l) -> diferencia (suprimir x (Conjunto a)) (Conjunto l);;

(*****************************************************************************)

let rec incluido = function
     Conjunto []     -> (function _ -> true)
   | Conjunto (x::l) -> (function b -> (pertenece x b) && (incluido (Conjunto l) b));;

(*****************************************************************************)

let igual a b = (incluido a b) && (incluido b a);;

(*****************************************************************************)

let list_of_conjunto (Conjunto l) = l;;

(*****************************************************************************)

let cartesiano a b =
   match (a,b) with
        (Conjunto [], _) -> conjunto_vacio
      | (_, Conjunto []) -> conjunto_vacio
      | (Conjunto la, Conjunto lb) ->
           let rec aux1 acum1 = function
                []     -> Conjunto acum1
              | h1::t1 -> (let rec aux2 acum2 = function
                                []     -> aux1 acum2 t1
                              | h2::t2 -> aux2 ((h1,h2)::acum2) t2
                           in
                              aux2 acum1 lb)
           in
              aux1 [] la
           ;;

let cartesiano2 a b =
   match (a,b) with
        (Conjunto [], _) -> conjunto_vacio
      | (_, Conjunto []) -> conjunto_vacio
      | (a, b) ->
           let rec aux = function
                Conjunto []       -> (function _ -> conjunto_vacio)
              | Conjunto (h1::t1) -> (function
                     Conjunto []       -> aux (Conjunto t1) b
                   | Conjunto (h2::t2) -> agregar (h1,h2) (aux (Conjunto (h1::t1)) (Conjunto t2)))
           in
              aux a b
           ;;


(*****************************************************************************)

