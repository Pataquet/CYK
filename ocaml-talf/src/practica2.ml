#load "talf.cma";;
open Conj;; (*operaciones con conjuntos*)
open Auto;; (*estructuras algebraicas*)
open Ergo;; (*manejo de la sintaxis*)
open Graf;;

let a1 = gic_of_string "S A B; a b c; S; S -> a A; A -> a b c A | b B; B -> b c B | epsilon;";;
let a2 = gic_of_string "S A B; a b c; S; S -> A A; A -> a | B B; B -> b | c;";;


(* Ejercicio 1 *)
let rec comprobarRegla regla terminales noTerminales = 
	match regla with
		| Regla_gic(_,[]) -> false
		| Regla_gic(_,(h::[])) ->
				if pertenece h terminales then true
				else false
		| Regla_gic(_,(h1::h2::[])) ->
				if (pertenece h1 noTerminales &&
					pertenece h2 noTerminales) then true
				else false
		| Regla_gic(_,_) -> false;;
			
			
let es_fnc = function 
	Gic(noTerminales, terminales, Conjunto p, _) -> 
		let rec aux reglas =
		match reglas with
		| [] -> true
		| h::t -> 
			if comprobarRegla h terminales noTerminales then aux t 
			else false
	in aux p;;


es_fnc a1 ;;
es_fnc a2 ;;

(* Ejercicio 2 *)

let rec conjunto_of_list l =
	let rec aux l conjunto =
		match l with
			| [] -> conjunto
			| h::t ->aux t (agregar h conjunto)
	in aux l (Conjunto([]));;

let rec getTerminales simbolo reglas lNoTerms = 
	match reglas with
		| [] ->  lNoTerms
		| (Regla_gic(s,l))::t -> 
			if List.mem simbolo l then 
				getTerminales simbolo t (s::lNoTerms)
			else 
				getTerminales simbolo t lNoTerms;;

let rec buscarNoTerminales lSimbolos reglas l= 
	match lSimbolos with
	| [] ->List.rev l
	| h::t ->
		buscarNoTerminales t reglas
			(conjunto_of_list(getTerminales h reglas [])::l);;

(*se le pasa por parametro una lista de conjuntos y
hace el producto cartesiano por pares*)
let rec getProdCarListConj lConjuntos lConjuntoCartesianos = 
	match lConjuntos with
		| [] -> lConjuntoCartesianos
		| h::[] -> lConjuntoCartesianos
		| h1::h2::t ->getProdCarListConj (h2::t)
					((cartesiano h1 h2)::lConjuntoCartesianos);;

let rec compararTerminales a b reglas lTerminales =
	match reglas with
		| [] -> lTerminales
		| (Regla_gic(_,(h::[])))::t ->
			compararTerminales a b t lTerminales
		| (Regla_gic(s,(h1::h2::[])))::t ->
			if (h1 =a && h2 =b )then
				compararTerminales a b t (s::lTerminales)
			else compararTerminales a b t lTerminales
		| (Regla_gic(_,_)::t) ->compararTerminales a b t lTerminales;;

let rec recorreConjunto conjunto reglas listaResultados =
	match conjunto with
	| Conjunto [] ->conjunto_of_list listaResultados
	| Conjunto ((a,b)::t) ->
		recorreConjunto (Conjunto t) reglas (compararTerminales a b reglas listaResultados);;
			
let rec segundaFila lConjuntosCartesianos reglas lpadres = 
	match lConjuntosCartesianos with
		| [] ->List.rev lpadres
		| (Conjunto ((a,b)::t))::t2 ->
			segundaFila t2 reglas ((recorreConjunto (Conjunto ((a,b)::t)) reglas [])::lpadres)
		| (Conjunto []::t2) -> segundaFila t2 reglas lpadres;;

let rec getPosition l cont = 
	match l with
		| [] -> []
		| h::t ->
			if cont = 0 then h
			else getPosition t (cont-1);;

let diagonal l cont contCol = 
	let lista = getPosition l cont in
	let rec aux lista contCol= 
		match lista with
			| [] -> Conjunto []
			| h::t ->
				if contCol = 0 then h
				else aux t (contCol-1)
	in aux lista (cont+contCol+1) ;;

let vertical l cont contCol = 
	let lista = getPosition l cont in
	let rec aux lista contCol= 
		match lista with
			| [] -> Conjunto []
			| h::t ->
				if contCol = 0 then h
				else aux t (contCol-1)
	in aux lista contCol;;

let rec diagonalVertical listOfList reglas contBajar contSubir contCol =
	let conjVertical = vertical listOfList contBajar contCol in 
	let conjDiagonal = diagonal listOfList contSubir contCol in [conjVertical; conjDiagonal];;

 let rec subirYBajar listOfList reglas numCol vertical diagonal lista= 
	if(diagonal = -1) then lista
	else
		subirYBajar listOfList reglas numCol (vertical+1) (diagonal-1)
			((diagonalVertical listOfList reglas vertical diagonal numCol)::lista)

let rec casilla l lres= 
	match l with
		| [] -> lres
		| h::t -> casilla t ((getProdCarListConj h lres));;

let rec simplificar l reglas lres = 
	match l with
		| [] -> lres
		| h::t ->simplificar t reglas ((segundaFila h reglas [])::lres) 

let rec limpieza l lres= 
	match l with
		| [] -> lres
		| h::t -> limpieza t ((casilla h [])::lres);;
		
let rec recorrerFila listOfList reglas =
	match listOfList with
	| [] -> []
	| h::t ->
		let rec aux lista numCol diagonal lres = 
			match lista with
			| [] -> limpieza lres []
			| h2::[] -> limpieza lres []
			| h2::t2 -> aux t2 (numCol+1) diagonal 
				((subirYBajar listOfList reglas numCol 0 diagonal [])::lres)
		in aux h 0 ((List.length listOfList)-1) [];;

let rec unir l lres=
	match l with
	| [] -> lres
	| h::t -> let rec aux listConjuntos csol =
		match listConjuntos with
		| [] -> csol
		| h1::t1 -> aux t1 ((union h1 csol))
	in unir t ((aux h (Conjunto []))::lres);;

let rec comprobarAxioma lista axioma= 
	match lista with
	| [] -> false
	| h::t ->
	let rec aux l =
		match l with
			| [] -> false
			| h::t -> 
				if pertenece axioma h then true
				else false 
	in aux h ;;

let cyk lSimbolos gic = 
	if es_fnc gic then (
		match  gic with
		| Gic(noTerminales, terminales, Conjunto p, axioma) -> 
			let fila1 = buscarNoTerminales lSimbolos p [] in 
			let lista = [fila1] in 
			let rec aux lista = 
				if (List.length lista) >= (List.length lSimbolos) then
					comprobarAxioma lista axioma
				else 
					let fila = recorrerFila lista p in
					let simp = simplificar fila p [] in 
					let lista = (unir simp [])::lista in
					aux lista 
			in aux lista
	)else false;;


let a3 = gic_of_string "S A B C; a b c; S; S -> A B | B C ; A -> B A | a; B -> C C | b; C -> A B | a;";;
let w1 = [Terminal "a"; Terminal "b"; Terminal "a";Terminal "a";Terminal "b"];;
let w2 = [Terminal "a"; Terminal "b"; Terminal "a";Terminal "b"];;
Printf.printf "\n\n\n";;

cyk w1 a3;;

Printf.printf "\n\n\n";;

cyk w2 a3;;
(* let a4 = gic_of_string 
	"S NP VP PP NP V P N D;
	she eats with fish fork a;
	S;
	S -> NP VP;
	VP -> VP PP | V NP | eats; 
	PP -> P NP;
	NP -> D N | she;
	V -> eats;
	P -> with;
	N -> fish | fork;
	D -> a;";;

let w2 = [Terminal "she"; Terminal "eats"; Terminal "a";
		Terminal "fish";Terminal "with"; Terminal "a"; Terminal "fork"];;

cyk w2 a4;;
 *)