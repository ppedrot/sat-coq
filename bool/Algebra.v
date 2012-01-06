Require Import Definitions.

Section Definitions.

(** * Global, inductive definitions. *)

(** A Horner polynomial is either a constant, or a product P × (i + Q), where i 
  is a variable. *)

Inductive poly :=
| Cst : bool -> poly
| Poly : poly -> nat -> poly -> poly.

(* TODO: We should use [positive] instead of [nat] to encode variables, for 
 efficiency purpose. *)

Inductive null : poly -> Prop :=
| null_intro : null (Cst false).

(** Polynomials satisfy a uniqueness condition whenever they are valid. A 
  polynomial [p] satisfies [valid n p] whenever it is well-formed and each of 
  its variable indices are < [n]. *)

Inductive valid : nat -> poly -> Prop :=
| valid_cst : forall k c, valid k (Cst c)
| valid_poly : forall k p i q,
  i < k -> ~ null q -> valid i p -> valid (S i) q -> valid k (Poly p i q).

(** Linear polynomials are valid polynomials in which every variable appears at 
  most once. *)

Inductive linear : nat -> poly -> Prop :=
| linear_cst : forall k c, linear k (Cst c)
| linear_poly : forall k p i q, i < k -> ~ null q ->
  linear i p -> linear i q -> linear k (Poly p i q).

End Definitions.

Section Computational.

(** * The core reflexive part. *)

Hint Constructors valid.

Fixpoint beq_poly pl pr :=
match pl with
| Cst cl =>
  match pr with
  | Cst cr => decide (cl = cr)
  | Poly _ _ _ => false
  end
| Poly pl il ql =>
  match pr with
  | Cst _ => false
  | Poly pr ir qr =>
    decide (il = ir) && beq_poly pl pr && beq_poly ql qr
  end
end.

(* We could do that with [decide equality] but dependency in proofs is heavy *)
Instance Decidable_eq_poly : forall (p q : poly), Decidable (eq p q) := {
  Decidable_witness := beq_poly p q
}.
Proof.
abstract(revert q; induction p; intros [] ?; simpl in *; bool; try_decide;
  f_equal; first [intuition congruence|auto]).
abstract(revert q; induction p; intros [] Heq; simpl in *; bool; try_decide; intuition;
  try injection Heq; first[congruence|intuition]).
Defined.

Instance Decidable_null : forall p, Decidable (null p) := {
  Decidable_witness := match p with Cst false => true | _ => false end
}.
abstract(destruct p as [[]|]; first [discriminate|constructor]).
abstract(inversion 1; trivial).
Defined.

Fixpoint eval (var : nat -> _) (p : poly) :=
match p with
| Cst c => c
| Poly p i q => xorb (eval var p) (andb (var i) (eval var q))
end.

Fixpoint valid_dec k p :=
match p with
| Cst c => true
| Poly p i q =>
  negb (decide (null q)) && decide (i < k) &&
    valid_dec i p && valid_dec (S i) q
end.

Instance Decidable_valid : forall n p, Decidable (valid n p) := {
  Decidable_witness := valid_dec n p
}.
Proof.
abstract(revert n; induction p; simpl in *; intuition; bool; try_decide; auto).
abstract(intros H; induction H; simpl in *; bool; try_decide; auto).
Defined.

(* Addition of polynomials *)

Fixpoint poly_add pl {struct pl} :=
match pl with
| Cst cl =>
  fix F pr := match pr with
  | Cst cr => Cst (xorb cl cr)
  | Poly pr ir qr => Poly (F pr) ir qr
  end
| Poly pl il ql =>
  fix F pr {struct pr} := match pr with
  | Cst cr => Poly (poly_add pl pr) il ql
  | Poly pr ir qr =>
    match nat_compare il ir with
    | Eq =>
      let qs := poly_add ql qr in
      (* Ensure validity *)
      if decide (null qs) then poly_add pl pr
      else Poly (poly_add pl pr) il qs
    | Gt => Poly (poly_add pl (Poly pr ir qr)) il ql
    | Lt => Poly (F pr) ir qr
    end
  end
end.

(* Multiply a polynomial by a constant *)

Fixpoint poly_mul_cst v p :=
match p with
| Cst c => Cst (andb c v)
| Poly p i q =>
  let r := poly_mul_cst v q in
  (* Ensure validity *)
  if decide (null r) then poly_mul_cst v p
  else Poly (poly_mul_cst v p) i r
end.

(* Multiply a polynomial by a monomial *)

Fixpoint poly_mul_mon k p :=
match p with
| Cst c =>
  if decide (null p) then p
  else Poly (Cst false) k p
| Poly p i q =>
  if decide (i <= k) then Poly (Cst false) k (Poly p i q)
  else Poly (poly_mul_mon k p) i (poly_mul_mon k q)
end.

(* Multiplication of polynomials *)

Fixpoint poly_mul pl {struct pl} :=
match pl with
| Cst cl => poly_mul_cst cl
| Poly pl il ql =>
  fun pr =>
    (* Multiply by a factor *)
    let qs := poly_mul ql pr in
    (* Ensure validity *)
    if decide (null qs) then poly_mul pl pr
    else poly_add (poly_mul pl pr) (poly_mul_mon il qs)
end.

End Computational.

Local Hint Constructors valid.

Section Validity.

(* Decision procedure of validity *)

Hint Constructors valid.

Lemma valid_le_compat : forall k l p, valid k p -> k <= l -> valid l p.
Proof.
intros k l p H Hl; induction H; constructor; eauto with arith.
Qed.

End Validity.

Section Evaluation.

(* Useful simple properties *)

Lemma eval_null_zero : forall p var, null p -> eval var p = false.
Proof.
intros p var []; reflexivity.
Qed.

Lemma eval_extensional_eq_compat : forall p var1 var2,
  (forall x, var1 x = var2 x) -> eval var1 p = eval var2 p.
Proof.
intros p var1 var2 H; induction p; simpl; try_rewrite; auto.
Qed.

Lemma eval_suffix_compat : forall k p var1 var2,
  (forall i, i < k -> var1 i = var2 i) -> valid k p ->
  eval var1 p = eval var2 p.
Proof.
intros k p var1 var2 Hvar Hv; revert var1 var2 Hvar.
induction Hv; intros var1 var2 Hvar; simpl; [now auto|].
rewrite Hvar; [|now auto]; erewrite (IHHv1 var1 var2); [|now intuition].
erewrite (IHHv2 var1 var2); [ring|now intuition].
Qed.

End Evaluation.

Section Algebra.

Require Import NPeano.

(* Compatibility with evaluation *)

Lemma poly_add_compat : forall pl pr var, eval var (poly_add pl pr) = xorb (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
  induction pr; simpl; auto; solve [try_rewrite; ring].
  induction pr; simpl; auto; try solve [try_rewrite; simpl; ring].
  destruct (nat_compare_spec n n0); repeat case_decide; simpl; first [try_rewrite; ring|idtac].
    try_rewrite; ring_simplify; repeat rewrite xorb_assoc.
    match goal with [ |- context [xorb (andb ?b1 ?b2) (andb ?b1 ?b3)] ] =>
      replace (xorb (andb b1 b2) (andb b1 b3)) with (andb b1 (xorb b2 b3)) by ring
    end.
    rewrite <- IHpl2.
    match goal with [ H : null ?p |- _ ] => rewrite (eval_null_zero _ _ H) end; ring.
    simpl; rewrite IHpl1; simpl; ring.
Qed.

Lemma poly_mul_cst_compat : forall v p var,
  eval var (poly_mul_cst v p) = (andb v (eval var p))%Z.
Proof.
intros v p; induction p; intros var; simpl; [ring|].
case_decide; simpl; try_rewrite; [ring_simplify|ring].
replace (v && var n && eval var p2)%Z with (var n && (v && eval var p2))%Z by ring.
rewrite <- IHp2; inversion H; simpl; ring.
Qed.

Lemma poly_mul_mon_compat : forall i p var,
  eval var (poly_mul_mon i p) = (var i && eval var p)%Z.
Proof.
intros i p var; induction p; simpl; case_decide; simpl; try_rewrite; try ring.
inversion H; ring.
match goal with [ |- ?u = ?t ] => set (x := t); destruct x; reflexivity end.
match goal with [ |- ?u = ?t ] => set (x := t); destruct x; reflexivity end.
Qed.

Lemma poly_mul_compat : forall pl pr var, eval var (poly_mul pl pr) = andb (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
  apply poly_mul_cst_compat.
  case_decide; simpl.
    rewrite IHpl1; ring_simplify.
    replace (eval var pr && var n && eval var pl2)%Z
    with (var n && (eval var pl2 && eval var pr))%Z by ring.
    now rewrite <- IHpl2; inversion H; simpl; ring.
    rewrite poly_add_compat, poly_mul_mon_compat, IHpl1, IHpl2; ring.
Qed.

(* Compatibility with validity *)

Hint Extern 5 =>
match goal with
| [ |- max ?x ?y <= ?z ] =>
  apply Nat.max_case_strong; intros; omega
| [ |- ?z <= max ?x ?y ] =>
  apply Nat.max_case_strong; intros; omega
end.
Hint Resolve Nat.le_max_r Nat.le_max_l.

Lemma poly_add_valid_compat : forall kl kr pl pr, valid kl pl -> valid kr pr ->
  valid (max kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr; induction Hl; intros kr pr Hr; simpl.
  eapply valid_le_compat; [clear k|apply Nat.le_max_r].
  now induction Hr; auto.
  assert (Hle : max (S i) kr <= max k kr).
    apply Nat.max_case_strong; intros; apply Nat.max_case_strong; intros; auto; omega.
  apply (valid_le_compat (max (S i) kr)); [|assumption].
  clear - IHHl1 IHHl2 Hl2 Hr H0; induction Hr.
    constructor; auto.
      now rewrite <- (Nat.max_id i); intuition.
    destruct (nat_compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
      now apply (valid_le_compat (max i0 i0)); [now auto|]; rewrite Nat.max_id; auto.
      now apply (valid_le_compat (max i0 i0)); [now auto|]; rewrite Nat.max_id; auto.
      now apply (valid_le_compat (max (S i0) (S i0))); [now auto|]; rewrite Nat.max_id; auto.
      now apply (valid_le_compat (max (S i) i0)); intuition.
      now apply (valid_le_compat (max i (S i0))); intuition.
Qed.

Lemma poly_mul_cst_valid_compat : forall k v p, valid k p -> valid k (poly_mul_cst v p).
Proof.
intros k v p H; induction H; simpl; [now auto|].
case_decide; [|now auto].
eapply (valid_le_compat i); [now auto|omega].
Qed.

Lemma poly_mul_mon_null_compat : forall i p, null (poly_mul_mon i p) -> null p.
Proof.
intros i p; induction p; simpl; case_decide; simpl; inversion 1; intuition.
Qed.

Lemma poly_mul_mon_valid_compat : forall k i p, valid k p -> valid (max (S i) k) (poly_mul_mon i p).
Proof.
intros k i p H; induction H; simpl poly_mul_mon; case_decide; intuition.
apply (valid_le_compat (S i)); auto; constructor; intuition.
match goal with [ H : null ?p |- _ ] => solve[inversion H] end.
apply (valid_le_compat k); auto; constructor; intuition.
  assert (X := poly_mul_mon_null_compat); intuition eauto.
  now cutrewrite <- (max (S i) i0 = i0); intuition.
  now cutrewrite <- (max (S i) (S i0) = S i0); intuition.
Qed.

Lemma poly_mul_valid_compat : forall kl kr pl pr, valid kl pl -> valid kr pr ->
  valid (max kl kr) (poly_mul pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr.
induction Hl; intros kr pr Hr; simpl.
  apply poly_mul_cst_valid_compat; auto.
  apply (valid_le_compat kr); now auto.
  apply (valid_le_compat (max (max i kr) (max (S i) (max (S i) kr)))).
    case_decide.
      now apply (valid_le_compat (max i kr)); auto.
      apply poly_add_valid_compat; auto.
      now apply poly_mul_mon_valid_compat; intuition.
    repeat apply Nat.max_case_strong; omega.
Qed.

End Algebra.

Section Eval.

(* Some stuff about replacing a variable in an assignation *)

Definition replace (var : nat -> bool) n z :=
  fun m => if decide (n = m) then z else var m.

Lemma eval_replace_compat : forall k p var n z, valid k p -> k <= n ->
  eval (replace var n z) p = eval var p.
Proof.
intros k p var n z H Hlt; unfold replace.
rewrite <- (eval_suffix_compat k _ var); auto.
intros; case_decide; [exfalso; omega|reflexivity].
Qed.

Lemma replace_idem : forall var n z1 z2 m,
  replace (replace var n z2) n z1 m = replace var n z1 m.
Proof.
intros; unfold replace; case_decide; auto.
Qed.

Lemma eval_replace_idem : forall p var n z1 z2,
  eval (replace (replace var n z2) n z1) p = eval (replace var n z1) p.
Proof.
intros p var n z1 z2; induction p; simpl; try_rewrite; auto.
repeat rewrite replace_idem; auto.
Qed.

End Eval.
