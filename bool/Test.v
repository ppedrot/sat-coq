Require Import Definitions Bool BoolTactic.

Goal forall a b c d e f g,
  (negb a && b && c && d && e && f && g) ||
  (a && negb b && c && d && e && f && g) ||
  (a && b && negb c && d && e && f && g) ||
  (a && b && c && negb d && e && f && g) ||
  (a && b && c && d && negb e && f && g) ||
  (a && b && c && d && e && negb f && g) ||
  (a && b && c && d && e && f && negb g) = true.


Goal forall a b c : bool, c || a = negb (b && negb b && (a || negb a)).
Proof.
intros; bool_simpl; unfold var_of_list; simpl.
Print BoolTactic.
Qed.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.
