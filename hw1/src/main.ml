open Tree;;
open Buffer;;
open Printf;;
open Parser;;

let (>>) x f = f x;;

let string_of_tree tree =
    let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in

    let buf = create 1000 in
    let rec s_t t = match t with
        | Var v -> add_string buf v
        | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
        | Binop (op,l,r) -> bprintf buf "(%s," (s_op op); s_t l; add_char buf ','; s_t r; add_char buf ')'
        in s_t tree;
    contents buf;;

let tree_of_string s = s >> Lexing.from_string >> Parser.main Lexer.main;;
let correct s = s >> tree_of_string >> string_of_tree;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let s = ic >> input_line;;

let string_guesses_with_result = Array.of_list (Str.split (Str.regexp ",\||-") s);;
let guesses_with_result = Array.map tree_of_string string_guesses_with_result;;
let guesses_size = (Array.length guesses_with_result) - 1;;

let result = Array.get guesses_with_result guesses_size;;
let guesses = Array.sub guesses_with_result 0 guesses_size;;

let hypothesis = Hashtbl.create 1;;

for i = 0 to guesses_size - 1 do
    Hashtbl.add hypothesis (Array.get guesses i) i
done;;

let assumption tree =
    try Hashtbl.find hypothesis tree
    with Not_found -> -1
;;

let axiom tree = match tree with
    | Binop (Impl, a1, Binop (Impl, b, a2)) when a1 = a2 -> 1
    | Binop (Impl, Binop (Impl, a1, b1), Binop (Impl, Binop(Impl, a2, Binop (Impl, b2, c1)), Binop (Impl, a3, c2))) when
        a1 = a2 && a2 = a3 && b1 = b2 && c1 = c2 -> 2
    | Binop (Impl, a1, Binop (Impl, b1, Binop (Conj, a2, b2))) when a1 = a2 && b1 = b2 -> 3
    | Binop (Impl, Binop (Conj, a1, b), a2) when a1 = a2 -> 4
    | Binop (Impl, Binop (Conj, a, b1), b2) when b1 = b2 -> 5
    | Binop (Impl, a1, Binop (Disj, a2, b)) when a1 = a2 -> 6
    | Binop (Impl, b1, Binop (Disj, a, b2)) when b1 = b2 -> 7
    | Binop (Impl, Binop (Impl, a1, c1), Binop (Impl, Binop (Impl, b1, c2), Binop (Impl, Binop (Disj, a2, b2), c3))) when
        a1 = a2 && b1 = b2 && c1 = c2 && c2 = c3 -> 8
    | Binop (Impl, Binop (Impl, a1, b1), Binop (Impl, Binop (Impl, a2, Neg b2), Neg a3)) when
        a1 = a2 && a2 = a3 && b1 = b2 -> 9
    | Binop(Impl, Neg (Neg a1), a2) when a1 = a2 -> 10
    | _ -> 0
;;

let ready_modus_ponens = ref (Hashtbl.create 1);; (*store expressions, which could be reached with MP*)
let alpha_modus_ponens = ref (Hashtbl.create 1);; (*store A parts of expressions A , (A -> B)*)
let zero x = ref [];;
let waiting_modus_ponens = ref (Array.init 55000 zero);; (*array of arrays, each of them representing parts B for visited expressions A->B, which are waiting A*)
let waiting_index = ref (Hashtbl.create 1);; (*stores indexes of expression in waiting_modus_ponens*)
let waiting_size = ref 0;;

let print_int x = print_endline (string_of_int x);;

let get_waiting_pos a =
    try Hashtbl.find !waiting_index a
    with Not_found -> Hashtbl.add !waiting_index a !waiting_size; waiting_size := !waiting_size + 1; !waiting_size - 1
;;

let update_impl a b number =
    let index = try Hashtbl.find !alpha_modus_ponens a with Not_found -> -1 in
    if index >= 0 then Hashtbl.add !ready_modus_ponens b (number, index) else
    let waiting_pos = get_waiting_pos a in

    let updated_array = Array.get !waiting_modus_ponens waiting_pos in

    let _ = updated_array := ((b, number)::!updated_array) in ()
;;

let update_simple tree number =
    Hashtbl.add !alpha_modus_ponens tree number;
    let waiting_pos = try Hashtbl.find !waiting_index tree with Not_found -> -1 in
    if waiting_pos <> -1 then
    let current_array = Array.get !waiting_modus_ponens waiting_pos in
    let f (tree, id) = (Hashtbl.add !ready_modus_ponens tree (id, number)) in
    let _ = (List.map f !current_array) in (); ()
;;

let update tree number =
    let _ = (update_simple tree number) in ();
    match tree with
    | Binop (Impl, a, b) -> update_impl a b number
    | _ -> ()
;;

let modus_ponens tree =
    try Hashtbl.find !ready_modus_ponens tree
    with Not_found -> (-1, -1)
;;

let annotate tree =
    let index_assumption = assumption tree in
    let index_axiom = axiom tree in
    let (a, b) = modus_ponens tree in
    if (index_assumption >= 0) then " (Предп. " ^ (string_of_int (index_assumption + 1)) ^ ")\n" else
    if (index_axiom > 0) then " (Сх. акс. " ^ (string_of_int (index_axiom)) ^ ")\n" else
    if a <> -1 then " (M.P. " ^ (string_of_int a) ^ ", " ^ (string_of_int b) ^ ")\n"
    else " (Не доказано)\n"
;;

let numeration number = "(" ^ (string_of_int number) ^ ") ";;

let rec solve number =
    let input = try ic >> input_line with End_of_file -> "" in
    if input = "" then () else
    let tree = tree_of_string input in
    fprintf oc "%s" ((numeration number) ^ input ^ (annotate tree));
    update tree number;
    solve (number + 1)
;;

solve 1;;

close_out oc;;
close_in ic;;
