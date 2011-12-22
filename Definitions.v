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

Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_sound : Decidable_witness = true -> P;
  Decidable_complete : P -> Decidable_witness = true
}.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
   ~ P -> Decidable_witness = false.
Proof.
intros P H Hd.
define (Decidable_witness) b Hb; destruct b; auto.
elim Hd; apply Decidable_sound; auto.
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  Decidable_witness = false -> ~ P.
Proof.
intros P H Hd Hc; apply Decidable_complete in Hc.
now congruence.
Qed.

Definition decide P {H : Decidable P} := @Decidable_witness P H.

(* We opacify here decide for proofs, and will make it transparent for
   reflexive tactics later on. *)

Global Opaque decide.

Ltac tac_decide :=
match goal with
| [ H : @decide ?P ?D = true |- _ ] => apply (@Decidable_sound P D) in H
| [ H : @decide ?P ?D = false |- _ ] => apply (@Decidable_complete_alt P D) in H
| [ |- @decide ?P ?D = true ] => apply (@Decidable_complete P D)
| [ |- @decide ?P ?D = false ] => apply (@Decidable_sound_alt P D)
| [ |- negb ?b = true ] => apply negb_true_iff
| [ |- negb ?b = false ] => apply negb_false_iff
| [ H : negb ?b = true |- _ ] => apply negb_true_iff in H
| [ H : negb ?b = false |- _ ] => apply negb_false_iff in H
end.

Ltac try_decide := repeat tac_decide.

Ltac make_decide P := match goal with
| [ |- context [@decide P ?D] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ X : context [@decide P ?D] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
end.

Ltac case_decide := match goal with
| [ |- context [@decide ?P ?D] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ X : context [@decide ?P ?D] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ |- context [nat_compare ?x ?y] ] =>
  destruct (nat_compare_spec x y); try (exfalso; omega)
| [ X : context [nat_compare ?x ?y] |- _ ] =>
  destruct (nat_compare_spec x y); try (exfalso; omega)
end.

Instance Decidable_le : forall x y, Decidable (le x y) := {
  Decidable_witness := leb x y
}.
Proof.
apply leb_complete.
apply leb_correct.
Defined.

Instance Decidable_lt : forall x y, Decidable (lt x y) := {
  Decidable_witness := leb (S x) y
}.
Proof.
apply leb_complete.
apply leb_correct.
Defined.

Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
  Decidable_witness := beq_nat x y
}.
Proof.
abstract(intros H; symmetry in H; apply beq_nat_eq in H; auto).
abstract(destruct 1; symmetry; apply beq_nat_refl).
Defined.

Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
  Decidable_witness := Zeq_bool x y
}.
Proof.
abstract(apply Zeq_is_eq_bool).
abstract(apply Zeq_is_eq_bool).
Defined.

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
  Decidable_witness := match p with Cst 0 => true | _ => false end
}.
abstract(destruct p as [[]|]; first [discriminate|constructor]).
abstract(inversion 1; trivial).
Defined.
