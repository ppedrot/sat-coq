open Printf

let () = Random.self_init ()

let rec gen n =
  let case = Random.int 4 in
  let case = if Random.float 1. <= 0.8 then case else 0 in
  match case with
  | 0 ->
    let i = Random.int n in
    printf "x%i" i
  | 1 ->
    printf "negb("; gen n; printf ")"
  | 2 ->
    printf "orb("; gen n; printf ")("; gen n; printf ")"
  | _ ->
    printf "andb("; gen n; printf ")("; gen n; printf ")"

let gen n =
  printf "Goal forall ";
  for i = 0 to (pred n) do
    printf "x%i " i
  done;
  printf " : bool, ";
  gen n;
  printf "= true.\nProof.\nintros; bool_ring.\nAdmitted.\n"

let () =
  printf "Require Import Bool BoolTactic.\n\n";
  for i = 0 to 100 do
  gen (int_of_string Sys.argv.(1))
  done