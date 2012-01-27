TACTIC EXTEND context
| [ "vm_at" lconstr_pattern(pat) ] -> [

  let ocs = false, [] in
  let redfun env map c =
    let (_, pat) = Pattern.pattern_of_constr map pat in
    let vmfun _ env map c =
      let tpe = Retyping.get_type_of env map c in
      Vnorm.cbv_vm env c tpe
    in
    Tacred.contextually false (ocs, pat) vmfun env map c
  in
  Tactics.reduct_in_concl (redfun, Term.VMcast)
  ]
END
