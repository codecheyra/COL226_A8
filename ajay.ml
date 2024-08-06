(* Define types for variables, constants, symbols, and terms *)
type variable = string
type constant = string
type symbol = string

(* Define the type for terms *)
type term =
  | Variable of variable
  | Constant of constant
  | Function of symbol * term list

(* Define atomic formulas as predicates with a symbol and a list of terms *)
type atomic_formula = Predicate of symbol * term list

(* Define clauses as either facts or rules *)
type clause =
  | Fact of atomic_formula
  | Rule of atomic_formula * atomic_formula list

(* Define a program as a list of clauses and a goal as a list of atomic formulas *)
type program = clause list
type goal = atomic_formula list

(* Define the substitution type for unification *)
type substitution = (variable * term) list

exception NOT_UNIFIABLE

(* Function to unify two terms with an initial substitution *)
let rec unify t1 t2 subst = match (t1, t2) with
  | Constant c1, Constant c2 when c1 = c2 -> subst
  | Variable v1, Variable v2 when v1 = v2 -> subst
  | Variable v, t | t, Variable v ->
      (match List.assoc_opt v subst with
      | Some t' when t' = t -> subst
      | None -> (v, t) :: subst
      | _ -> raise NOT_UNIFIABLE)
  | Function (f1, args1), Function (f2, args2) when f1 = f2 && List.length args1 = List.length args2 ->
      List.fold_left2 (fun s a1 a2 -> unify a1 a2 s) subst args1 args2
  | _, _ -> raise NOT_UNIFIABLE

(* Function to unify atomic formulas *)
let unify_atomic_formula af1 af2 subst =
  match (af1, af2) with
  | Predicate (s1, terms1), Predicate (s2, terms2) when s1 = s2 ->
      (try
         List.fold_left2 (fun acc t1 t2 -> unify t1 t2 acc) subst terms1 terms2
       with
       | Invalid_argument _ -> raise NOT_UNIFIABLE)
  | _ -> raise NOT_UNIFIABLE

(* Recursive function to solve a Prolog goal against a program *)
let rec solve goal program subst =
  match goal with
  | [] -> Some subst
  | g :: gs ->
      program |> List.fold_left (fun acc clause ->
        match acc with
        | Some _ -> acc
        | None -> match clause with
          | Fact head ->
              (try
                let new_subst = unify_atomic_formula g head subst in
                solve gs program new_subst
              with NOT_UNIFIABLE -> None)
          | Rule (head, body) ->
              (try
                let new_subst = unify_atomic_formula g head subst in
                solve (body @ gs) program new_subst
              with NOT_UNIFIABLE -> None)
      ) None

(* Entry point for the Prolog interpreter *)
let prolog_interpreter goal program =
  match solve goal program [] with
  | Some subst -> Printf.printf "Success with substitutions: %s\n" (String.concat "; " (List.map (fun (v, t) -> v ^ " = " ^ (match t with | Variable var -> var | Constant con -> con | Function (f, _) -> f)) subst))
  | None -> Printf.printf "No solution found.\n"

(* Define and run test programs and goals *)
let () =
  let program_1 = [Fact (Predicate ("parent", [Constant "alice"; Constant "bob"]))] in  (* alice is the parent of bob *)
  let goal_1 = [Predicate ("parent", [Variable "parent"; Constant "bob"])] in (* The goal is to find a parent of bob *)
  Printf.printf "Test Case 1: \n";
  prolog_interpreter goal_1 program_1;

(* Test Case 2 *)
let program_2 = [
  Fact (Predicate ("parent", [Constant "alice"; Constant "bob"]));
  Fact (Predicate ("parent", [Constant "bob"; Constant "charlie"]));
  Rule (Predicate ("ancestor", [Variable "x"; Variable "z"]),
        [Predicate ("parent", [Variable "x"; Variable "y"])]);
  Rule (Predicate ("ancestor", [Variable "x"; Variable "z"]),
        [Predicate ("parent", [Variable "y"; Variable "z"]); Predicate ("ancestor", [Variable "x"; Variable "z"])]);
] in
let goal_2 = [Predicate ("ancestor", [Variable "ancestor"; Constant "charlie"])] in
Printf.printf "Test Case 2: \n";
prolog_interpreter goal_2 program_2;

(* Test Case 3 *)
let program_3 = [
  Fact (Predicate ("parent", [Constant "alice"; Constant "bob"]));
  Fact (Predicate ("parent", [Constant "alice"; Constant "carol"]));
] in
let goal_3 = [Predicate ("parent", [Constant "alice"; Variable "child"])] in
Printf.printf "Test Case 3: \n";
prolog_interpreter goal_3 program_3;


(* Test Case 5 *)
(* let program_4 = [
  Fact (Predicate ("parent", [Constant "alice"; Constant "bob"]));
  Fact (Predicate ("parent", [Constant "alice"; Constant "carol"]));
  Rule (Predicate ("sibling", [Variable "x"; Variable "y"]),  
      [Predicate ("parent", [Variable "p"; Variable "x"]); 
       Predicate ("parent", [Variable "p"; Variable "y"]);
       Predicate ("not_equal", [Variable "x"; Variable "y"])]);
] in
let goal_4 = [Predicate ("sibling", [Variable "sibling"; Constant "bob"])] in
Printf.printf "Test Case 4: \n";
prolog_interpreter goal_4 program_4; *)

(* Test Case 6 *)
let program_5 = [
  Fact (Predicate ("manager", [Constant "alice"; Constant "bob"]));
  Fact (Predicate ("manager", [Constant "alice"; Constant "carol"]));
  Fact (Predicate ("manager", [Constant "bob"; Constant "dave"]));
  Rule (Predicate ("subordinate", [Variable "m"; Variable "s"]),
        [Predicate ("manager", [Variable "m"; Variable "s"])]);
] in
let goal_5 = [Predicate ("subordinate", [Constant "alice"; Variable "sub"])] in
Printf.printf "Test Case 5: \n";
prolog_interpreter goal_5 program_5;

(* Test Case 6 *)
let program_6 = [
  Fact (Predicate ("parent", [Constant "alice"; Constant "bob"]));
  Fact (Predicate ("parent", [Constant "bob"; Constant "carol"]));
  Rule (Predicate ("grandparent", [Variable "gp"; Variable "gc"]),
        [Predicate ("parent", [Variable "gp"; Variable "p"]); Predicate ("parent", [Variable "p"; Variable "gc"])]);
] in
let goal_6 = [Predicate ("grandparent", [Variable "grandparent"; Constant "carol"])] in
Printf.printf "Test Case 6: \n";
prolog_interpreter goal_6 program_6;
