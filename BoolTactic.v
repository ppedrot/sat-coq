Require Import Definitions Validity Algebra MinMax.

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

Definition Z_of_bool (b : bool) := if b then 1%Z else 0%Z.

(* Translation between lists and functions nat -> Z. For efficiency. *)

Definition var_of_list (l : list bool) i := Z_of_bool (List.nth i l false).

End Bool.

(* Reification tactics *)

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

(* Translation of formulas into polynomials *)

Section Translation.

(* This is straightforward. *)

Fixpoint poly_of_formula f := match f with
| formula_var x => Poly (Cst 0) x (Cst 1) 
| formula_btm => Cst 0
| formula_top => Cst 1
| formula_cnj fl fr => poly_mul (poly_of_formula fl) (poly_of_formula fr)
| formula_dsj fl fr =>
  let pl := poly_of_formula fl in
  let pr := poly_of_formula fr in
  poly_add (poly_add pl pr) (poly_opp (poly_mul pl pr))
| formula_neg f => poly_add (Cst 1) (poly_opp (poly_of_formula f))
end.

Lemma Z_of_bool_andb_compat : forall x y,
  Z_of_bool (x && y) = Zmult (Z_of_bool x) (Z_of_bool y).
Proof.
intros [] []; simpl; ring.
Qed.

Lemma Z_of_bool_orb_compat : forall x y,
  Z_of_bool (x || y) = ((Z_of_bool x) + (Z_of_bool y) - (Z_of_bool x) * (Z_of_bool y))%Z.
Proof.
intros [] []; simpl; reflexivity.
Qed.

Lemma Z_of_bool_negb_compat : forall x, Z_of_bool (negb x) = (1 - Z_of_bool x)%Z.
Proof.
intros []; simpl; auto.
Qed.

Lemma Z_of_bool_inj : forall x y, Z_of_bool x = Z_of_bool y -> x = y.
Proof.
intros [] []; simpl; congruence.
Qed.

Opaque poly_add.

(* Compatibility of translation wrt evaluation *)

Lemma poly_of_formula_eval_compat : forall var f,
  eval (var_of_list var) (poly_of_formula f) = Z_of_bool (formula_eval var f).
Proof.
intros var f; induction f; simpl poly_of_formula; simpl formula_eval; auto.
  simpl; unfold var_of_list, Z_of_bool; ring.
  rewrite Z_of_bool_andb_compat, poly_mul_Zmult_compat, IHf1, IHf2; ring.
  rewrite Z_of_bool_orb_compat; repeat rewrite poly_add_Zplus_compat.
  rewrite poly_opp_Zopp_compat, poly_mul_Zmult_compat; try_rewrite; ring.
  rewrite Z_of_bool_negb_compat, poly_add_Zplus_compat, poly_opp_Zopp_compat; try_rewrite.
  simpl eval; ring.
Qed.

Hint Extern 5 => change 0 with (min 0 0).
Hint Resolve poly_add_valid_aux_compat poly_mul_valid_aux_compat poly_opp_valid_aux_compat.

(* Compatibility with validity *)

Lemma poly_of_formula_valid_compat : forall f, valid (poly_of_formula f).
Proof.
intros f; exists 0; induction f; simpl; auto 6.
  apply (valid_aux_le_compat n); [repeat constructor|]; try omega.
  now intros Hc; inversion Hc.
Qed.

(* The soundness lemma ; alas not complete! *)

Lemma poly_of_formula_sound : forall fl fr var,
  poly_of_formula fl = poly_of_formula fr -> formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
apply Z_of_bool_inj.
repeat rewrite <- poly_of_formula_eval_compat.
rewrite Heq; reflexivity.
Qed.

End Translation.

Section Completeness.

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

Definition boolean (var : nat -> Z) := forall n, var n = 0%Z \/ var n = 1%Z.

Lemma boolean_var_of_list : forall l, boolean (var_of_list l).
Proof.
intros l n; unfold var_of_list.
destruct (List.nth n l false); auto.
Qed.

Hint Immediate boolean_var_of_list.

Lemma reduce_aux_eval_compat : forall k p var, boolean var -> valid_aux k p ->
  (var k * eval var (reduce_aux k p) = var k * eval var p)%Z.
Proof.
intros k p var Hvar; revert k; induction p; intros k Hv; simpl; auto.
inversion Hv; case_decide; subst.
  rewrite poly_add_Zplus_compat; ring_simplify.
  specialize (IHp1 k); specialize (IHp2 k).
  destruct (Hvar k) as [Hrw|Hrw]; rewrite Hrw in *; ring_simplify; [now auto|].
  replace (eval var p2 + eval var p1)%Z with (1 * eval var p2 + 1 * eval var p1)%Z by ring.
  rewrite <- IHp2; auto; rewrite <- IHp1; [ring|].
  apply (valid_aux_le_compat (S k)); now auto.
  destruct (Hvar k) as [Hrw|Hrw]; rewrite Hrw in *; ring_simplify; [now auto|].
  case_decide; simpl.
    rewrite <- (IHp2 n); [inversion H|now auto]; simpl.
    replace (eval var p1) with (var k * eval var p1)%Z by (rewrite Hrw; ring); rewrite <- (IHp1 k).
      rewrite Hrw; ring.
      now apply (valid_aux_le_compat (S n)); auto.
    rewrite (IHp2 n); [|now auto].
    replace (eval var p1) with (var k * eval var p1)%Z by (rewrite Hrw; ring).
    rewrite <- (IHp1 k); [rewrite Hrw; ring|].
    apply (valid_aux_le_compat (S n)); auto.
Qed.

(* Reduction preserves evaluation by boolean assignations *)

Lemma reduce_eval_compat : forall k p var, boolean var -> valid_aux k p ->
  eval var (reduce p) = eval var p.
Proof.
intros k p var Hb H; induction H; simpl; auto.
case_decide; try_rewrite; simpl.
  rewrite <- reduce_aux_eval_compat; auto; inversion H3; simpl; ring.
  repeat rewrite reduce_aux_eval_compat; try_rewrite; now auto.
Qed.

Lemma reduce_aux_le_compat : forall k l p, valid_aux (S k) p -> l <= k ->
  reduce_aux l p = reduce_aux k p.
Proof.
intros k l p; revert k l; induction p; intros k l H Hle; simpl; auto.
  inversion H; subst; repeat case_decide; subst; try (exfalso; omega).
    now apply IHp1; [|now auto]; eapply valid_aux_le_compat; eauto.
    f_equal; apply IHp1; auto.
    now eapply valid_aux_le_compat; eauto.
Qed.

(* Soundness of the method ; immediate *)

Lemma reduce_poly_of_formula_sound : forall fl fr var,
  reduce (poly_of_formula fl) = reduce (poly_of_formula fr) ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
apply Z_of_bool_inj.
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
  var_of_list (list_replace l n b) i = replace (var_of_list l) n (Z_of_bool b) i.
Proof.
unfold var_of_list, replace.
intros l; induction l; intros n b; simpl; intros i.
  case_decide; subst.
    now rewrite make_last_nth_2; auto.
    rewrite make_last_nth_1; destruct i; auto.
    destruct n; destruct i; case_decide; simpl; try (exfalso; omega); auto.
      rewrite IHl; case_decide; omega.
      rewrite IHl; case_decide; omega.
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

Inductive linear : nat -> poly -> Prop :=
| linear_cst : forall k c, linear k (Cst c)
| linear_poly : forall k p i q, k <= i -> ~ null q ->
  linear (S i) p -> linear (S i) q -> linear k (Poly p i q).

Hint Constructors linear.

Lemma linear_valid_aux_incl : forall k p, linear k p -> valid_aux k p.
Proof.
intros k p H; induction H; constructor; auto.
eapply valid_aux_le_compat; eauto.
Qed.

(* The witness is correct only if the polynomial is linear *)

Lemma boolean_witness_nonzero : forall k p, linear k p -> ~ null p ->
  eval (var_of_list (boolean_witness p)) p <> 0%Z.
Proof.
intros k p H Hp; induction H; simpl.
  intros Hrw; apply Hp; rewrite Hrw; now constructor.
  repeat case_decide; try congruence.
  match goal with [ H : null ?p |- _ ] => inversion H end; subst.
  simpl eval; intros Hc.
    let T := type of Hc in match T with (0 + ?z * ?e = 0)%Z => replace z with 1%Z in Hc; [ring_simplify in Hc|] end.
    erewrite (eval_extensional_eq_compat _ _ (replace _ _ _)) in Hc; [|now apply list_replace_replace_compat].
    rewrite (eval_replace_compat (S i)) in Hc; intuition.
    apply linear_valid_aux_incl; now auto.
    rewrite list_replace_replace_compat; unfold replace; case_decide; [now auto|omega].
  intros Hc.
    let T := type of Hc in match T with (?p + ?z * ?e = 0)%Z => replace z with 0%Z in Hc; [ring_simplify in Hc|] end.
    erewrite (eval_extensional_eq_compat _ _ (replace _ _ _)) in Hc; [|now apply list_replace_replace_compat].
    rewrite (eval_replace_compat (S i)) in Hc; intuition.
    apply linear_valid_aux_incl; now auto.
    rewrite list_replace_replace_compat; unfold replace; case_decide; [now auto|omega].
Qed.

Lemma linear_le_compat : forall k l p, linear k p -> l <= k -> linear l p.
Proof.
intros k l p H; revert l; induction H; intuition.
Qed.

Transparent poly_add.

Hint Extern 5 => change 0 with (min 0 0).
Hint Extern 5 =>
match goal with
| [ |- min ?x ?y <= ?z ] =>
  apply min_case_strong; intros; omega
| [ |- ?z <= min ?x ?y ] =>
  apply min_case_strong; intros; omega
end.
Hint Resolve le_min_r le_min_l.

(* Compatibility of linearity wrt to linear operations *)

Lemma poly_add_linear_compat : forall kl kr pl pr, linear kl pl -> linear kr pr ->
  linear (min kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl; revert kr pr; induction Hl; intros kr pr Hr; simpl.
  apply (linear_le_compat kr); [|apply min_case_strong; omega].
  induction Hr; constructor; auto.
  apply (linear_le_compat (min i kr)); [|repeat apply min_case_strong; omega].
  induction Hr; simpl.
    constructor; auto.
    replace (S i) with (min (S i) (S i)) by (apply min_id); apply IHHl1; now constructor.
    destruct (nat_compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
        eapply linear_le_compat; eauto; instantiate; rewrite min_id; now auto.
        now eapply linear_le_compat; eauto; instantiate; rewrite min_id; auto.
        now eapply linear_le_compat; eauto; instantiate; rewrite min_id; auto.
        now apply (linear_le_compat (min (S i) i0)); intuition.
        now apply (linear_le_compat (min i (S i0))); intuition.
Qed.

Lemma poly_opp_linear_compat : forall k p, linear k p -> linear k (poly_opp p).
Proof.
intros k p H; induction H; simpl; constructor; auto.
now intros Hc; apply poly_opp_null_compat in Hc; intuition.
Qed.

(* Reduce projects valid polynomials into linear ones *)

Lemma linear_reduce_aux : forall i p, valid_aux i p -> linear (S i) (reduce_aux i p).
Proof.
intros i p; revert i; induction p; intros i Hp; simpl.
  constructor.
  inversion Hp; subst; case_decide; subst.
    rewrite <- (min_id (S i)); apply poly_add_linear_compat.
      apply IHp1; eapply valid_aux_le_compat; eauto.
      now intuition.
  case_decide.
    apply IHp1; eapply valid_aux_le_compat; eauto.
    constructor; try omega; auto.
    erewrite (reduce_aux_le_compat n); auto.
    now apply IHp1; eapply valid_aux_le_compat; eauto.
Qed.

Lemma linear_reduce : forall k p, valid_aux k p -> linear k (reduce p).
Proof.
intros k p H; induction H; simpl.
  now constructor.
  case_decide.
    eapply linear_le_compat; eauto.
    constructor; auto.
    apply linear_reduce_aux; auto.
Qed.

(* The completeness lemma *)

Lemma reduce_poly_of_formula_complete : forall fl fr,
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
    apply linear_valid_aux_incl; auto.
  elim (boolean_witness_nonzero 0 p); auto.
    unfold p; rewrite <- (min_id 0); apply poly_add_linear_compat; try apply poly_opp_linear_compat; now auto.
    unfold p at 2; rewrite poly_add_Zplus_compat, poly_opp_Zopp_compat.
    destruct (poly_of_formula_valid_compat fl) as [nl Hnl].
    destruct (poly_of_formula_valid_compat fr) as [nr Hnr].
    repeat erewrite reduce_eval_compat; eauto.
    fold var; rewrite Hc; ring.
Defined.

End Completeness.

(* For reflexivity purposes, that woud better be transparent *)

Global Transparent decide poly_add.

(* Extract a counterexample from to formulas and display it *)

Ltac counterexample fl fr l :=
  let p := constr: (poly_add (reduce (poly_of_formula fl)) (poly_opp (reduce (poly_of_formula fr)))) in
  let var := constr: (boolean_witness p) in
  let var := eval compute in var in
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

(* The long-awaited tactic *)

Ltac bool_ring :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  match build_formula t (@nil bool) with
  | (?fl, ?l) =>
    match build_formula u l with
    | (?fr, ?l) =>
      first [
      now change (formula_eval l fl = formula_eval l fr);
      apply reduce_poly_of_formula_sound; reflexivity|counterexample fl fr l]
    end
  end
| _ => idtac "Cannot recognize a boolean equality"
end.
