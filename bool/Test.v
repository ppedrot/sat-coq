Require Import Definitions Bool BoolTactic.

Goal forall a b c : bool, c || a = negb (b && negb b && (a || negb a)).
Proof.
intros; bool_simpl; unfold var_of_list; simpl.
Print BoolTactic.
Qed.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.
