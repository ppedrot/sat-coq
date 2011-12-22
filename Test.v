Require Import Definitions Bool BoolTactic.

Goal forall a b c : bool, c || a || negb a = negb (b && negb b && (a || negb a)).
Proof.
intros; bool_ring.
Qed.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.
