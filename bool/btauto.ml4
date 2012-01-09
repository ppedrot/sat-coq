let contrib_name = "btauto"

let init_constant dir s =
  let find_constant contrib dir s =
    Libnames.constr_of_global (Coqlib.find_reference contrib dir s)
  in
  find_constant contrib_name dir s

let get_constant dir s = lazy (init_constant dir s)

let decomp_term (c : Term.constr)  = 
  Term.kind_of_term (Term.strip_outer_cast c)
    
let lapp c v  = Term.mkApp (Lazy.force c, v)

let (===) = Term.eq_constr

module CoqList = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = get_constant path "list"
  let nil = get_constant path "nil"
  let cons = get_constant path "cons"

  let cons ty h t = lapp cons [|ty; h ; t|]
  let nil ty = lapp nil [|ty|]
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
    ConstrHashtbl.fold (fun constr key acc -> constr :: acc) env []
      
end

module Bool = struct

  let typ = get_constant ["Coq"; "Init"; "Datatypes"] "bool"
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
    | _ ->
      if c === falseb then Const false
      else if c === trueb then Const true
      else Var (Env.add env c)
    in
    aux c

end

module Btauto = struct

  let f_var = get_constant ["Btauto"; "Reflect"] "formula_var"
  let f_btm = get_constant ["Btauto"; "Reflect"] "formula_btm"
  let f_top = get_constant ["Btauto"; "Reflect"] "formula_top"
  let f_cnj = get_constant ["Btauto"; "Reflect"] "formula_cnj"
  let f_dsj = get_constant ["Btauto"; "Reflect"] "formula_dsj"
  let f_neg = get_constant ["Btauto"; "Reflect"] "formula_neg"
  let f_xor = get_constant ["Btauto"; "Reflect"] "formula_xor"
  let f_ifb = get_constant ["Btauto"; "Reflect"] "formula_ifb"

  let eval = get_constant ["Btauto"; "Reflect"] "formula_eval"

  let rec convert = function
  | Bool.Var n -> lapp f_var [|CoqNat.of_int n|]
  | Bool.Const true -> Lazy.force f_top
  | Bool.Const false -> Lazy.force f_btm
  | Bool.Andb (b1, b2) -> lapp f_cnj [|convert b1; convert b2|]
  | Bool.Orb (b1, b2) -> lapp f_dsj [|convert b1; convert b2|]
  | Bool.Negb b -> lapp f_neg [|convert b|]
  | _ -> assert false

  let convert_env env : Term.constr = 
    let l = Env.to_list env in 
    CoqList.of_list (Lazy.force Bool.typ) l

  let reify env t = lapp eval [|convert_env env; convert t|]

  let tac gl =
    Tactics.change_in_concl None (Lazy.force Bool.trueb) gl

  let tac gl =
    let concl = Tacmach.pf_concl gl in
    let t = decomp_term concl in
    match t with
    | Term.App (c, args) when Array.length args >= 2 ->
      let len = Array.length args in
      let tl = args.(len - 2) in
      let tr = args.(len - 1) in
      let ts = Array.sub args 0 (len - 2) in
      let rel = Term.mkApp (c, ts) in
      let env = Env.empty () in
      let fl = Bool.quote env tl in
      let fr = Bool.quote env tr in
      let changed_gl = Term.mkApp (rel, [|reify env fl; reify env fr|]) in
      Tactics.change_in_concl None changed_gl gl
    | _ ->
      let msg = Pp.str "Cannot recognize a boolean equality" in
      Tacticals.tclFAIL 1 msg gl

end

TACTIC EXTEND _btauto_
| [ "btauto" ] -> [ Btauto.tac ]
END
