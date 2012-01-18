let contrib_name = "btauto"

let init_constant dir s =
  let find_constant contrib dir s =
    Libnames.constr_of_global (Coqlib.find_reference contrib dir s)
  in
  find_constant contrib_name dir s

let get_constant dir s = lazy (init_constant dir s)

let get_inductive dir s =
  let glob_ref () = Coqlib.find_reference contrib_name dir s in
  Lazy.lazy_from_fun (fun () -> Libnames.destIndRef (glob_ref ()))

let decomp_term (c : Term.constr) =
  Term.kind_of_term (Term.strip_outer_cast c)

let lapp c v  = Term.mkApp (Lazy.force c, v)

let (===) = Term.eq_constr

module CoqList = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = get_constant path "list"
  let _nil = get_constant path "nil"
  let _cons = get_constant path "cons"

  let cons ty h t = lapp _cons [|ty; h ; t|]
  let nil ty = lapp _nil [|ty|]
  let rec of_list ty = function
    | [] -> nil ty
    | t::q -> cons ty t (of_list ty q)
  let type_of_list ty = lapp typ [|ty|]

end

module CoqNat = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = get_constant path "nat"
  let _S = get_constant path "S"
  let _O = get_constant path "O"

  (* A coq nat from an int *)
  let rec of_int n =
    if n <= 0 then Lazy.force _O
    else
      let ans = of_int (pred n) in
      lapp _S [|ans|]

end

module Env = struct

  module ConstrHashed = struct
    type t = Term.constr
    let equal = Term.eq_constr
    let hash = Term.hash_constr
  end

  module ConstrHashtbl = Hashtbl.Make (ConstrHashed)

  type t = (int ConstrHashtbl.t * int ref)

  let add (tbl, off) (t : Term.constr) =
    try ConstrHashtbl.find tbl t 
    with
    | Not_found -> 
      let i = !off in 
      let () = ConstrHashtbl.add tbl t i in
      let () = incr off in
      i

  let empty () = (ConstrHashtbl.create 16, ref 0)

  let to_list (env, _) =
    (* we need to get an ordered list *)
    let fold constr key accu = (key, constr) :: accu in
    let l = ConstrHashtbl.fold fold env [] in
    let sorted_l = List.sort (fun p1 p2 -> compare (fst p1) (fst p2)) l in
    List.map snd sorted_l

end

module Bool = struct

  let typ = get_constant ["Coq"; "Init"; "Datatypes"] "bool"
  let ind = get_inductive ["Coq"; "Init"; "Datatypes"] "bool"
  let trueb = get_constant ["Coq"; "Init"; "Datatypes"] "true"
  let falseb = get_constant ["Coq"; "Init"; "Datatypes"] "false"
  let andb = get_constant ["Coq"; "Init"; "Datatypes"] "andb"
  let orb = get_constant ["Coq"; "Init"; "Datatypes"] "orb"
  let xorb = get_constant ["Coq"; "Init"; "Datatypes"] "xorb"
  let negb = get_constant ["Coq"; "Init"; "Datatypes"] "negb"

  type t =
  | Var of int
  | Const of bool
  | Andb of t * t
  | Orb of t * t
  | Xorb of t * t
  | Negb of t
  | Ifb of t * t * t

  let quote (env : Env.t) (c : Term.constr) : t =
    let trueb = Lazy.force trueb in
    let falseb = Lazy.force falseb in
    let andb = Lazy.force andb in
    let orb = Lazy.force orb in
    let xorb = Lazy.force xorb in
    let negb = Lazy.force negb in

    let rec aux c = match decomp_term c with
    | Term.App (head, args) ->
      if head === andb && Array.length args = 2 then
        Andb (aux args.(0), aux args.(1))
      else if head === orb && Array.length args = 2 then
        Orb (aux args.(0), aux args.(1))
      else if head === xorb && Array.length args = 2 then
        Xorb (aux args.(0), aux args.(1))
      else if head === negb && Array.length args = 1 then
        Negb (aux args.(0))
      else Var (Env.add env c)
    | Term.Case (info, r, arg, pats) ->
      let is_bool =
        let i = info.Term.ci_ind in
        Names.eq_ind i (Lazy.force ind)
      in
      if is_bool then
        Ifb ((aux arg), (aux pats.(0)), (aux pats.(1)))
      else
        Var (Env.add env c)
    | _ ->
      if c === falseb then Const false
      else if c === trueb then Const true
      else Var (Env.add env c)
    in
    aux c

end

module Btauto = struct

  open Pp

  let eq = get_constant ["Coq"; "Init"; "Logic"]  "eq"

  let f_var = get_constant ["Btauto"; "Reflect"] "formula_var"
  let f_btm = get_constant ["Btauto"; "Reflect"] "formula_btm"
  let f_top = get_constant ["Btauto"; "Reflect"] "formula_top"
  let f_cnj = get_constant ["Btauto"; "Reflect"] "formula_cnj"
  let f_dsj = get_constant ["Btauto"; "Reflect"] "formula_dsj"
  let f_neg = get_constant ["Btauto"; "Reflect"] "formula_neg"
  let f_xor = get_constant ["Btauto"; "Reflect"] "formula_xor"
  let f_ifb = get_constant ["Btauto"; "Reflect"] "formula_ifb"

  let eval = get_constant ["Btauto"; "Reflect"] "formula_eval"
  let witness = get_constant ["Btauto"; "Reflect"] "boolean_witness"

  let soundness = get_constant ["Btauto"; "Reflect"] "reduce_poly_of_formula_sound_alt"
  let simpl_goal = get_constant ["Btauto"; "Reflect"] "reduce_poly_of_formula_simpl_goal"

  let rec convert = function
  | Bool.Var n -> lapp f_var [|CoqNat.of_int n|]
  | Bool.Const true -> Lazy.force f_top
  | Bool.Const false -> Lazy.force f_btm
  | Bool.Andb (b1, b2) -> lapp f_cnj [|convert b1; convert b2|]
  | Bool.Orb (b1, b2) -> lapp f_dsj [|convert b1; convert b2|]
  | Bool.Negb b -> lapp f_neg [|convert b|]
  | Bool.Xorb (b1, b2) -> lapp f_xor [|convert b1; convert b2|]
  | Bool.Ifb (b1, b2, b3) -> lapp f_ifb [|convert b1; convert b2; convert b3|]

  let convert_env env : Term.constr = 
    CoqList.of_list (Lazy.force Bool.typ) env

  let reify env t = lapp eval [|convert_env env; convert t|]

  let print_counterexample p env gl =
    let var = lapp witness [|p|] in
    (* Compute an assignment that dissatisfies the goal *)
    let var = Tacmach.pf_reduction_of_red_expr gl Glob_term.CbvVm var in
    let rec to_list l = match decomp_term l with
    | Term.App (c, _)
      when c === (Lazy.force CoqList._nil) -> []
    | Term.App (c, [|_; h; t|])
      when c === (Lazy.force CoqList._cons) ->
      if h === (Lazy.force Bool.trueb) then (true :: to_list t)
      else if h === (Lazy.force Bool.falseb) then (false :: to_list t)
      else invalid_arg "to_list"
    | _ -> invalid_arg "to_list"
    in
    let concat sep = function
    | [] -> mt ()
    | h :: t ->
      let rec aux = function
      | [] -> mt ()
      | x :: t -> (sep ++ x ++ aux t)
      in
      h ++ aux t
    in
    let msg =
      try
        let var = to_list var in
        let assign = List.combine env var in
        let map_msg (key, v) =
          let b = if v then str "true" else str "false" in
          let term = Printer.pr_constr key in
          term ++ spc () ++ str ":=" ++ spc () ++ b
        in
        let assign = List.map map_msg assign in
        let l = str "[" ++ (concat (str ";" ++ spc ()) assign) ++ str "]" in
        str "Not a tautology:" ++ spc () ++ l
      with _ -> (str "Not a tautology")
    in
    Tacticals.tclFAIL 0 msg gl

  let try_unification env gl =
    let eq = Lazy.force eq in
    let concl = Tacmach.pf_concl gl in
    let t = decomp_term concl in
    match t with
    | Term.App (c, [|typ; p; _|]) when c === eq ->
      (* should be an equality [@eq poly ?p (Cst false)] *)
      let tac = Tacticals.tclORELSE0 Tactics.reflexivity (print_counterexample p env) in
      tac gl
    | _ ->
      let msg = str "Btauto: Internal error" in
      Tacticals.tclFAIL 0 msg gl

  let tac gl =
    let eq = Lazy.force eq in
    let bool = Lazy.force Bool.typ in
    let concl = Tacmach.pf_concl gl in
    let t = decomp_term concl in
    match t with
    | Term.App (c, [|typ; tl; tr|])
        when typ === bool && c === eq ->
      let env = Env.empty () in
      let fl = Bool.quote env tl in
      let fr = Bool.quote env tr in
      let env = Env.to_list env in
      let fl = reify env fl in
      let fr = reify env fr in
      let changed_gl = Term.mkApp (c, [|typ; fl; fr|]) in
      Tacticals.tclTHENLIST [
        Tactics.change_in_concl None changed_gl;
        Tactics.apply (Lazy.force soundness);
        Tactics.normalise_vm_in_concl;
        try_unification env
      ] gl
    | _ ->
      let msg = str "Cannot recognize a boolean equality" in
      Tacticals.tclFAIL 0 msg gl

  let tac_reify gl =
    let eq = Lazy.force eq in
    let bool = Lazy.force Bool.typ in
    let concl = Tacmach.pf_concl gl in
    let t = decomp_term concl in
    match t with
    | Term.App (c, [|typ; tl; tr|])
        when typ === bool && c === eq ->
      let env = Env.empty () in
      let fl = Bool.quote env tl in
      let fr = Bool.quote env tr in
      let env = Env.to_list env in
      let fl = reify env fl in
      let fr = reify env fr in
      let changed_gl = Term.mkApp (c, [|typ; fl; fr|]) in
      Tactics.change_in_concl None changed_gl gl
    | _ ->
      let msg = str "Cannot recognize a boolean equality" in
      Tacticals.tclFAIL 0 msg gl

  let tac_simpl_goal gl =
    let eq = Lazy.force eq in
    let bool = Lazy.force Bool.typ in
    let concl = Tacmach.pf_concl gl in
    let t = decomp_term concl in
    match t with
    | Term.App (c, [|typ; tl; tr|])
        when typ === bool && c === eq ->
      let env = Env.empty () in
      let fl = Bool.quote env tl in
      let fr = Bool.quote env tr in
      let env = Env.to_list env in
      let fl = reify env fl in
      let fr = reify env fr in
      let changed_gl = Term.mkApp (c, [|typ; fl; fr|]) in
      Tacticals.tclTHENLIST [
        Tactics.change_in_concl None changed_gl;
        Tactics.apply (Lazy.force simpl_goal)
      ] gl
    | _ ->
      let msg = str "Cannot recognize a boolean equality" in
      Tacticals.tclFAIL 0 msg gl

end

TACTIC EXTEND _btauto_
(* | [ "btauto" ] -> [ Btauto.tac ] *)
| [ "btauto_zabong" ] -> [ Btauto.tac_reify ]
(* | [ "btauto_simplify" ] -> [ Btauto.tac_simpl_goal ] *)
END
