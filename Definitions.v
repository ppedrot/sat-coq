Require Export ZArith Bool Omega.

Inductive poly :=
| Cst : Z -> poly
| Poly : poly -> nat -> poly -> poly.

Inductive null : poly -> Prop :=
| null_intro : null (Cst 0).

Inductive valid_aux : nat -> poly -> Prop :=
| valid_cst : forall k c, valid_aux k (Cst c)
| valid_poly : forall k p i q,
  k <= i -> ~ null q -> valid_aux (S i) p -> valid_aux i q -> valid_aux k (Poly p i q).

Hint Constructors valid_aux.

Definition valid p := exists k, valid_aux k p.

Ltac bool :=
repeat match goal with
| [ H : ?P && ?Q = true |- _ ] =>
  apply andb_true_iff in H; destruct H
| |- ?P && ?Q = true =>
  apply <- andb_true_iff; split
end.

Hint Extern 5 => progress bool.

Ltac define t x H :=
set (x := t) in *; assert (H : t = x) by reflexivity; clearbody x.

Ltac try_rewrite :=
repeat match goal with
| [ H : ?P |- _ ] => rewrite H
end.

Class Decidable {A} (P : A -> Prop) := {
  Decidable_fun : A -> bool;
  Decidable_sound : forall x, Decidable_fun x = true -> P x;
  Decidable_complete : forall x, P x -> Decidable_fun x = true
}.

Lemma Decidable_sound_alt : forall A P (H : Decidable P) (x : A),
   ~ P x -> Decidable_fun x = false.
Proof.
intros A P H x Hd.
define (Decidable_fun x) b Hb; destruct b; auto.
elim Hd; apply Decidable_sound; auto.
Qed.

Lemma Decidable_complete_alt : forall A P (H : Decidable P) (x : A),
  Decidable_fun x = false -> ~ P x.
Proof.
intros A P H x Hd Hc.
apply Decidable_complete in Hc; congruence.
Qed.

Definition decide {A} P {H : Decidable P} := @Decidable_fun A P H.

(* We opacify here decide for proofs, and will make it transparent for
   reflexive tactics later on. *)

Global Opaque decide.

Ltac tac_decide :=
match goal with
| [ H : @decide ?A ?P ?D ?x = true |- _ ] => apply (@Decidable_sound A P D) in H
| [ H : @decide ?A ?P ?D ?x = false |- _ ] => apply (@Decidable_complete_alt A P D) in H
| [ |- @decide ?A ?P ?D ?x = true ] => apply (@Decidable_complete A P D)
| [ |- @decide ?A ?P ?D ?x = false ] => apply (@Decidable_sound_alt A P D)
| [ |- negb ?b = true ] => apply negb_true_iff
| [ |- negb ?b = false ] => apply negb_false_iff
| [ H : negb ?b = true |- _ ] => apply negb_true_iff in H
| [ H : negb ?b = false |- _ ] => apply negb_false_iff in H
end.

Ltac try_decide := repeat tac_decide.

Ltac make_decide P := match goal with
| [ |- context [@decide ?A P ?D ?x] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide A P D x) b H; destruct b; try_decide
| [ X : context [@decide ?A P ?D ?x] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide A P D x) b H; destruct b; try_decide
end.

Ltac case_decide := match goal with
| [ |- context [@decide ?A ?P ?D ?x] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide A P D x) b H; destruct b; try_decide
| [ X : context [@decide ?A ?P ?D ?x] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide A P D x) b H; destruct b; try_decide
| [ |- context [nat_compare ?x ?y] ] =>
  destruct (nat_compare_spec x y); try (exfalso; omega)
| [ X : context [nat_compare ?x ?y] |- _ ] =>
  destruct (nat_compare_spec x y); try (exfalso; omega)
end.

Instance Decidable_le : forall x, Decidable (le x) := {
  Decidable_fun := leb x
}.
Proof.
apply leb_complete.
apply leb_correct.
Defined.

Instance Decidable_lt : forall x, Decidable (lt x) := {
  Decidable_fun := leb (S x)
}.
Proof.
apply leb_complete.
apply leb_correct.
Defined.

Instance Decidable_eq_nat : forall (x : nat), Decidable (eq x) := {
  Decidable_fun := beq_nat x
}.
Proof.
abstract(intros y H; symmetry in H; apply beq_nat_eq in H; auto).
abstract(destruct 1; symmetry; apply beq_nat_refl).
Defined.

Instance Decidable_eq_Z : forall (x : Z), Decidable (eq x) := {
  Decidable_fun := Zeq_bool x
}.
Proof.
abstract(apply Zeq_is_eq_bool).
abstract(apply Zeq_is_eq_bool).
Defined.

Fixpoint beq_poly pl pr :=
match pl with
| Cst cl =>
  match pr with
  | Cst cr => decide (eq cl) cr
  | Poly _ _ _ => false
  end
| Poly pl il ql =>
  match pr with
  | Cst _ => false
  | Poly pr ir qr =>
    decide (eq il) ir && beq_poly pl pr && beq_poly ql qr
  end
end.

(* We could do that with [decide equality] but dependency in proofs is heavy *)
Instance Decidable_eq_poly : forall (p : poly), Decidable (eq p) := {
  Decidable_fun := beq_poly p
}.
Proof.
abstract(induction p; intros [] ?; simpl in *; bool; try_decide;
  f_equal; first [intuition congruence|auto]).
abstract(induction p; intros [] Heq; simpl in *; bool; try_decide; intuition;
  try injection Heq; first[congruence|intuition]).
Defined.

Instance Decidable_null : Decidable null := {
  Decidable_fun := fun p => match p with Cst 0 => true | _ => false end
}.
abstract(intros p; destruct p as [[]|]; first [discriminate|constructor]).
abstract(inversion 1; trivial).
Defined.
