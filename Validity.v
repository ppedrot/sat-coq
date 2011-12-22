Require Import Definitions.

(* Decision procedure of validity *)

Section Validity.

Hint Constructors valid_aux.

Fixpoint valid_aux_dec k p :=
match p with
| Cst c => true
| Poly p i q =>
  negb (decide null q) && decide (le k) i &&
    valid_aux_dec (S i) p && valid_aux_dec i q
end.

Instance Decidable_valid_aux : forall n, Decidable (valid_aux n) := {
  Decidable_fun := valid_aux_dec n
}.
Proof.
abstract(intros p; revert n; induction p; simpl in *; intuition; bool; try_decide; auto).
abstract(intros p H; induction H; simpl in *; bool; try_decide; auto).
Defined.

Lemma valid_aux_le_compat : forall k l p, valid_aux k p -> l <= k -> valid_aux l p.
Proof.
intros k l p H Hl; induction H; constructor; eauto with arith.
Qed.

Instance Decidable_valid : Decidable valid := {
  Decidable_fun := valid_aux_dec 0
}.
Proof.
abstract(intros p H; exists 0; apply Decidable_sound; assumption).
abstract(intros p [n H]; apply (@Decidable_complete _ (valid_aux 0) (Decidable_valid_aux _));
apply (valid_aux_le_compat n); [auto|omega]).
Defined.

End Validity.

(* Useless, we do not use that at all *)

Section Polynomial.

Existing Instance Decidable_valid.

Record polynomial := {
  p_poly : poly;
  p_valid : decide valid p_poly = true
}.

Require Eqdep_dec.

Lemma polynomial_eq : forall p q : polynomial, p_poly p = p_poly q -> p = q.
Proof.
intros [p Hp] [q Hq]; simpl; destruct 1; f_equal.
apply Eqdep_dec.eq_proofs_unicity.
  intros [] []; intuition.
Qed.

(* Because writing dependent terms is fun: *)

(*

Definition foobar : forall (x y : bool) (p q : x = y), p = q := fun x =>
match x return forall y (p q : x = y), p = q with
| true => fun y p =>
  match p return forall q, p = q with
  | eq_refl => fun q =>
    match q in _ = b return
      match b return true = b -> Type with
      | true => fun q => (eq_refl true) = q
      | false => fun _ => True
      end q with
    | eq_refl => (eq_refl (eq_refl true))
    end
  end
| false => fun y p =>
  match p return forall q, p = q with
  | eq_refl => fun q =>
    match q in _ = b return
      match b return false = b -> Type with
      | false => fun q => (eq_refl false) = q
      | true => fun _ => True
      end q with
    | eq_refl => (eq_refl (eq_refl false))
    end
  end
end.

*)

End Polynomial.
