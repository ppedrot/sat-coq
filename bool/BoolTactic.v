Require Import Definitions Algebra NPeano.

Section Bool.

(* Boolean formulas and their evaluations *)

Inductive formula :=
| formula_var : nat -> formula
| formula_btm : formula
| formula_top : formula
| formula_cnj : formula -> formula -> formula
| formula_dsj : formula -> formula -> formula
| formula_neg : formula -> formula.

Fixpoint formula_eval var f := match f with
| formula_var x => List.nth x var false 
| formula_btm => false
| formula_top => true
| formula_cnj fl fr => (formula_eval var fl) && (formula_eval var fr)
| formula_dsj fl fr => (formula_eval var fl) || (formula_eval var fr)
| formula_neg f => negb (formula_eval var f)
end.

(* Translation between lists and functions nat -> Z. For efficiency. *)

Definition var_of_list (l : list bool) i := List.nth i l false.

End Bool.

(* Translation of formulas into polynomials *)

Section Translation.

(* This is straightforward. *)

Fixpoint poly_of_formula f := match f with
| formula_var x => Poly (Cst false) x (Cst true) 
| formula_btm => Cst false
| formula_top => Cst true
| formula_cnj fl fr => poly_mul (poly_of_formula fl) (poly_of_formula fr)
| formula_dsj fl fr =>
  let pl := poly_of_formula fl in
  let pr := poly_of_formula fr in
  poly_add (poly_add pl pr) (poly_mul pl pr)
| formula_neg f => poly_add (Cst true) (poly_of_formula f)
end.

Opaque poly_add.

(* Compatibility of translation wrt evaluation *)

Lemma poly_of_formula_eval_compat : forall var f,
  eval (var_of_list var) (poly_of_formula f) = formula_eval var f.
Proof.
intros var f; induction f; simpl poly_of_formula; simpl formula_eval; auto.
  now simpl; unfold var_of_list; match goal with [ |- ?t = ?u ] => destruct u; reflexivity end.
  rewrite poly_mul_compat, IHf1, IHf2; ring.
  repeat rewrite poly_add_compat.
  rewrite poly_mul_compat; try_rewrite.
  now match goal with [ |- ?t = ?x || ?y ] => destruct x; destruct y; reflexivity end.
  rewrite poly_add_compat; try_rewrite.
  now match goal with [ |- ?t = negb ?x ] => destruct x; reflexivity end.
Qed.

Hint Extern 5 => change 0 with (min 0 0).
Local Hint Resolve poly_add_valid_compat poly_mul_valid_compat.
Local Hint Constructors valid.

(* Compatibility with validity *)

Lemma poly_of_formula_valid_compat : forall f, exists n, valid n (poly_of_formula f).
Proof.
intros f; induction f; simpl.
  now exists (S n); constructor; intuition; inversion H.
  now exists 0; auto.
  now exists 0; auto.
  now destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; exists (max n1 n2); auto.
  now destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; exists (max (max n1 n2) (max n1 n2)); auto.
  now destruct IHf as [n Hn]; exists (max 0 n); auto.
Qed.

(* The soundness lemma ; alas not complete! *)

Lemma poly_of_formula_sound : forall fl fr var,
  poly_of_formula fl = poly_of_formula fr -> formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
repeat rewrite <- poly_of_formula_eval_compat.
rewrite Heq; reflexivity.
Qed.

End Translation.

Section Completeness.

Existing Instance Decidable_null.

(* Remove the multiple occurences of monomials x_k *)
Fixpoint reduce_aux k p :=
match p with
| Cst c => Cst c
| Poly p i q =>
  if decide (i = k) then poly_add (reduce_aux k p) (reduce_aux k q)
  else
    let qs := reduce_aux i q in
    (* Ensure validity *)
    if decide (null qs) then (reduce_aux k p)
    else Poly (reduce_aux k p) i qs
end.

(* Rewrite any x_k ^ {n + 1} to x_k *)
Fixpoint reduce p :=
match p with
| Cst c => Cst c
| Poly p i q =>
  let qs := reduce_aux i q in
  if decide (null qs) then reduce p
  else Poly (reduce p) i qs
end.

Lemma reduce_aux_eval_compat : forall k p var, valid (S k) p ->
  (var k && eval var (reduce_aux k p) = var k && eval var p).
Proof.
intros k p var; revert k; induction p; intros k Hv; simpl; auto.
inversion Hv; case_decide; subst.
  rewrite poly_add_compat; ring_simplify.
  specialize (IHp1 k); specialize (IHp2 k).
  destruct (var k); ring_simplify; [|now auto].
  rewrite <- (andb_true_l (eval var p1)), <- (andb_true_l (eval var p2)).
  rewrite <- IHp2; auto; rewrite <- IHp1; [ring|].
  apply (valid_le_compat k); now auto.
  remember (var k) as b; destruct b; ring_simplify; [|now auto].
  case_decide; simpl.
    rewrite <- (IHp2 n); [inversion H|now auto]; simpl.
    replace (eval var p1) with (var k && eval var p1)%Z by (rewrite <- Heqb; ring); rewrite <- (IHp1 k).
      rewrite <- Heqb; ring.
      now apply (valid_le_compat n); [auto|omega].
    rewrite (IHp2 n); [|now auto].
    replace (eval var p1) with (var k && eval var p1)%Z by (rewrite <- Heqb; ring).
    rewrite <- (IHp1 k); [rewrite <- Heqb; ring|].
    apply (valid_le_compat n); [auto|omega].
Qed.

(* Reduction preserves evaluation by boolean assignations *)

Lemma reduce_eval_compat : forall k p var, valid k p ->
  eval var (reduce p) = eval var p.
Proof.
intros k p var H; induction H; simpl; auto.
case_decide; try_rewrite; simpl.
  rewrite <- reduce_aux_eval_compat; auto; inversion H3; simpl; ring.
  repeat rewrite reduce_aux_eval_compat; try_rewrite; now auto.
Qed.

Lemma reduce_aux_le_compat : forall k l p, valid k p -> k <= l ->
  reduce_aux l p = reduce_aux k p.
Proof.
intros k l p; revert k l; induction p; intros k l H Hle; simpl; auto.
  inversion H; subst; repeat case_decide; subst; try (exfalso; omega).
    now apply IHp1; [|now auto]; eapply valid_le_compat; [eauto|omega].
    f_equal; apply IHp1; auto.
    now eapply valid_le_compat; [eauto|omega].
Qed.

(* Lemma reduce_poly_of_formula_simpl : forall fl fr var,
  simpl_eval (var_of_list var) (reduce (poly_of_formula fl)) = simpl_eval (var_of_list var) (reduce (poly_of_formula fr)) ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Hrw.
do 2 rewrite <- poly_of_formula_eval_compat.
destruct (poly_of_formula_valid_compat fl) as [nl Hl].
destruct (poly_of_formula_valid_compat fr) as [nr Hr].
rewrite <- (reduce_eval_compat nl (poly_of_formula fl)); [|assumption].
rewrite <- (reduce_eval_compat nr (poly_of_formula fr)); [|assumption].
do 2 rewrite <- eval_simpl_eval_compat; assumption.
Qed. *)

(* Soundness of the method ; immediate *)

Lemma reduce_poly_of_formula_sound : forall fl fr var,
  reduce (poly_of_formula fl) = reduce (poly_of_formula fr) ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
repeat rewrite <- poly_of_formula_eval_compat.
destruct (poly_of_formula_valid_compat fl) as [nl Hl].
destruct (poly_of_formula_valid_compat fr) as [nr Hr].
rewrite <- (reduce_eval_compat nl (poly_of_formula fl)); auto.
rewrite <- (reduce_eval_compat nr (poly_of_formula fr)); auto.
rewrite Heq; reflexivity.
Qed.

(* Auxilliary stuff. We define it with [Let] not to pollute again the
   namespace. *)

Let make_last {A} :=
fix make_last n (x def : A) :=
match n with
| 0 => cons x nil
| S n => cons def (make_last n x def)
end.

Let make_last_nth_1 : forall A n i x def, i <> n ->
  List.nth i (make_last A n x def) def = def.
Proof.
intros A n; induction n; intros i x def Hd; simpl.
  destruct i; [exfalso; omega|now destruct i; auto].
  destruct i; intuition.
Qed.

Let make_last_nth_2 : forall A n x def, List.nth n (make_last A n x def) def = x.
Proof.
intros A n; induction n; intros x def; simpl; auto.
Qed.

(* Counterpart to [replace] with lists *)

Fixpoint list_replace l n b :=
match l with
| nil => make_last _ n b false
| cons a l =>
  match n with
  | 0 => cons b l
  | S n => cons a (list_replace l n b)
  end
end.

(* Compatibility between both. *)

Lemma list_replace_replace_compat : forall l n b i,
  var_of_list (list_replace l n b) i = replace (var_of_list l) n b i.
Proof.
unfold var_of_list, replace.
intros l; induction l; intros n b; simpl; intros i.
  case_decide; subst.
    now rewrite make_last_nth_2; auto.
    rewrite make_last_nth_1; destruct i; auto.
    destruct n; destruct i; case_decide; simpl; try (exfalso; omega); auto.
      rewrite IHl; case_decide; [reflexivity|exfalso; omega].
      rewrite IHl; case_decide; [exfalso; omega|reflexivity].
Qed.

(* Extract a non-zero boolean assignation from a polynomial *)

Fixpoint boolean_witness p :=
match p with
| Cst c => nil
| Poly p i q =>
  if decide (null p) then
    let var := boolean_witness q in
    list_replace var i true
  else
    let var := boolean_witness p in
    list_replace var i false
end.

Hint Constructors linear.

Lemma linear_valid_incl : forall k p, linear k p -> valid k p.
Proof.
intros k p H; induction H; constructor; auto.
eapply valid_le_compat; eauto.
Qed.

(* The witness is correct only if the polynomial is linear *)

Lemma boolean_witness_nonzero : forall k p, linear k p -> ~ null p ->
  eval (var_of_list (boolean_witness p)) p <> false.
Proof.
intros k p H Hp; induction H; simpl.
    intros Hrw; apply Hp; rewrite Hrw; now constructor.
  repeat case_decide; try congruence.
  match goal with [ H : null ?p |- _ ] => inversion H end; subst.
  simpl eval; intros Hc.
    let T := type of Hc in match T with (xorb false (?z && ?e) = false) => replace z with true in Hc; [ring_simplify in Hc|] end.
    erewrite (eval_extensional_eq_compat _ _ (replace _ _ _)) in Hc; [|now apply list_replace_replace_compat].
    rewrite (eval_replace_compat i) in Hc; intuition.
    apply linear_valid_incl; now auto.
    rewrite list_replace_replace_compat; unfold replace; case_decide; [now auto|exfalso; omega].
  intros Hc.
    let T := type of Hc in match T with (xorb ?p (?z && ?e) = false)%Z => replace z with false in Hc; [ring_simplify in Hc|] end.
    erewrite (eval_extensional_eq_compat _ _ (replace _ _ _)) in Hc; [|now apply list_replace_replace_compat].
    rewrite (eval_replace_compat i) in Hc; intuition.
    apply linear_valid_incl; now auto.
    rewrite list_replace_replace_compat; unfold replace; case_decide; [now auto|exfalso; omega].
Qed.

Lemma linear_le_compat : forall k l p, linear k p -> k <= l -> linear l p.
Proof.
intros k l p H; revert l; induction H; intuition.
Qed.

Transparent poly_add.

Hint Extern 5 => change 0 with (min 0 0).
Hint Extern 5 =>
match goal with
| [ |- max ?x ?y <= ?z ] =>
  apply Nat.max_case_strong; intros; omega
| [ |- ?z <= max ?x ?y ] =>
  apply Nat.max_case_strong; intros; omega
end.
Hint Resolve Nat.le_max_r Nat.le_max_l.

(* Compatibility of linearity wrt to linear operations *)

Lemma poly_add_linear_compat : forall kl kr pl pr, linear kl pl -> linear kr pr ->
  linear (max kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl; revert kr pr; induction Hl; intros kr pr Hr; simpl.
  apply (linear_le_compat kr); [|apply Nat.max_case_strong; omega].
  now induction Hr; constructor; auto.
  apply (linear_le_compat (max kr (S i))); [|repeat apply Nat.max_case_strong; omega].
  induction Hr; simpl.
    constructor; auto.
    replace i with (max i i) by (apply Nat.max_id); apply IHHl1; now constructor.
    destruct (nat_compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
      now apply (linear_le_compat (max i0 i0)); [now auto|]; rewrite Nat.max_id; auto.
      now apply (linear_le_compat (max i0 i0)); [now auto|]; rewrite Nat.max_id; auto.
      now apply (linear_le_compat (max i0 i0)); [now auto|]; rewrite Nat.max_id; auto.
      now apply (linear_le_compat (max i0 (S i))); intuition.
      now apply (linear_le_compat (max i (S i0))); intuition.
Qed.

(* Reduce projects valid polynomials into linear ones *)

Lemma linear_reduce_aux : forall i p, valid (S i) p -> linear i (reduce_aux i p).
Proof.
intros i p; revert i; induction p; intros i Hp; simpl.
  constructor.
  inversion Hp; subst; case_decide; subst.
    rewrite <- (Nat.max_id i) at 1; apply poly_add_linear_compat.
      apply IHp1; eapply valid_le_compat; eauto.
      now intuition.
  case_decide.
    apply IHp1; eapply valid_le_compat; [eauto|omega].
    constructor; try omega; auto.
    erewrite (reduce_aux_le_compat n); [|assumption|omega].
    now apply IHp1; eapply valid_le_compat; eauto.
Qed.

Lemma linear_reduce : forall k p, valid k p -> linear k (reduce p).
Proof.
intros k p H; induction H; simpl.
  now constructor.
  case_decide.
    eapply linear_le_compat; [eauto|omega].
    constructor; auto.
    apply linear_reduce_aux; auto.
Qed.

(* The completeness lemma *)

(* Lemma reduce_poly_of_formula_complete : forall fl fr,
  reduce (poly_of_formula fl) <> reduce (poly_of_formula fr) ->
  {var | formula_eval var fl <> formula_eval var fr}.
Proof.
intros fl fr H.
pose (p := poly_add (reduce (poly_of_formula fl)) (poly_opp (reduce (poly_of_formula fr)))).
pose (var := boolean_witness p).
exists var.
  intros Hc; apply (f_equal Z_of_bool) in Hc.
  assert (Hfl : linear 0 (reduce (poly_of_formula fl))).
    now destruct (poly_of_formula_valid_compat fl) as [n Hn]; apply (linear_le_compat n); [|now auto]; apply linear_reduce; auto.
  assert (Hfr : linear 0 (reduce (poly_of_formula fr))).
    now destruct (poly_of_formula_valid_compat fr) as [n Hn]; apply (linear_le_compat n); [|now auto]; apply linear_reduce; auto.
  repeat rewrite <- poly_of_formula_eval_compat in Hc.
  define (decide (null p)) b Hb; destruct b; tac_decide.
    now elim H; apply (null_sub_implies_eq 0 0); fold p; auto;
    apply linear_valid_incl; auto.
  elim (boolean_witness_nonzero 0 p); auto.
    unfold p; rewrite <- (min_id 0); apply poly_add_linear_compat; try apply poly_opp_linear_compat; now auto.
    unfold p at 2; rewrite poly_add_compat, poly_opp_compat.
    destruct (poly_of_formula_valid_compat fl) as [nl Hnl].
    destruct (poly_of_formula_valid_compat fr) as [nr Hnr].
    repeat erewrite reduce_eval_compat; eauto.
    fold var; rewrite Hc; ring.
Defined. *)

End Completeness.

(* Reification tactics *)

(* For reflexivity purposes, that woud better be transparent *)

Global Transparent decide poly_add.

Ltac append_var x l k :=
match l with
| nil => constr: (k, cons x l)
| cons x _ => constr: (k, l)
| cons ?y ?l =>
  let ans := append_var x l (S k) in
  match ans with (?k, ?l) => constr: (k, cons y l) end
end.

Ltac build_formula t l :=
match t with
| true => constr: (formula_top, l)
| false => constr: (formula_btm, l)
| ?fl && ?fr =>
  match build_formula fl l with (?tl, ?l) =>
    match build_formula fr l with (?tr, ?l) =>
      constr: (formula_cnj tl tr, l)
    end
  end
| ?fl || ?fr =>
  match build_formula fl l with (?tl, ?l) =>
    match build_formula fr l with (?tr, ?l) =>
      constr: (formula_dsj tl tr, l)
    end
  end
| negb ?f =>
  match build_formula f l with (?t, ?l) =>
    constr: (formula_neg t, l)
  end
| _ =>
  let ans := append_var t l 0 in
  match ans with (?k, ?l) => constr: (formula_var k, l) end
end.

(* Extract a counterexample from to formulas and display it *)

Ltac counterexample fl fr l :=
  let p := constr: (poly_add (reduce (poly_of_formula fl)) (reduce (poly_of_formula fr))) in
  let var := constr: (boolean_witness p) in
  let var := eval vm_compute in var in
  let rec print l vl :=
    match l with
    | nil => idtac
    | cons ?x ?l =>
      match vl with
      | nil =>
        idtac x ":=" "false"; print l (@nil bool)
      | cons ?v ?vl =>
        idtac x ":=" v; print l vl
      end
    end
  in
  idtac "CRITICAL PHAIL:"; print l var.

(* Simplification tactic *)

Ltac bool_simpl :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  match build_formula t (@nil bool) with
  | (?fl, ?l) =>
    match build_formula u l with
    | (?fr, ?l) =>
      change (formula_eval l fl = formula_eval l fr);
      (* apply reduce_poly_of_formula_simpl *) idtac
    end
  end
| _ => idtac "Cannot recognize a boolean equality"
end.

Ltac bool_reify :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  match build_formula t (@nil bool) with
  | (?fl, ?l) =>
    match build_formula u l with
    | (?fr, ?l) =>
      change (formula_eval l fl = formula_eval l fr)
    end
  end
| _ => idtac "Cannot recognize a boolean equality"
end.

(* The long-awaited tactic *)

Ltac bool_ring :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  match build_formula t (@nil bool) with
  | (?fl, ?l) =>
    match build_formula u l with
    | (?fr, ?l) =>
      (change (formula_eval l fl = formula_eval l fr);
      apply reduce_poly_of_formula_sound;
      vm_compute; reflexivity) || counterexample fl fr l
    end
  end
| _ => idtac "Cannot recognize a boolean equality"
end.
