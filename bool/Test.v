Add Rec LoadPath "." as Btauto.

Require Import Bool Btauto.


Goal forall a b, a && (negb b) = a.
Proof.
Admitted.
(* intros a b.
btauto_reify.
apply Reflect.reduce_poly_of_formula_simpl_goal.
match goal with
| [ |- Algebra.simpl_eval ?var ?p = _ ] =>
  let t := eval vm_compute in p in
  change p with t
end.
unfold Algebra.simpl_eval.
simpl.*)

Unset Virtual Machine.

Goal forall a b c d e f g,
  (negb a && b && c && d && e && f && g) ||
  (a && negb b && c && d && e && f && g) ||
  (a && b && negb c && d && e && f && g) ||
  (a && b && c && negb d && e && f && g) ||
  (a && b && c && d && negb e && f && g) ||
  (a && b && c && d && e && negb f && g) ||
  (a && b && c && d && e && f && negb g)
  = true.
Proof.
intros.
btauto.
btauto_reify.
apply Reflect.reduce_poly_of_formula_sound.
compute.
apply Reflect.reduce_poly_of_formula_simpl_goal.
match goal with
| [ |- Algebra.simpl_eval ?var ?p = _ ] =>
  remember p as t
end;
vm_compute in Heqt; rewrite Heqt; unfold Algebra.simpl_eval; simpl Algebra.simpl_eval_aux.
admit.
Qed.

Print Unnamed_thm0.

btauto_simplify.
compute.
admit.
Qed.

Goal forall a b c : bool, c || b ||  a = b || negb ((negb a) && (negb c)).
Proof.
intros; btauto.
Qed.

Goal forall a b c, c || b && a = a || negb c && c.
Proof.
intros.
btauto_simplify.
vm_compute.

Goal forall a b c : bool, c || a || (negb a && b) || (negb a && negb b) = a || (negb a).
Proof.
intros.
btauto.
Qed.

Goal forall a, a = true.
Proof.
intros.
btauto.


Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; btauto.
Admitted.

Goal forall a b, (a || b || negb (a && b)) = true.
Proof.
intros; bool_ring.