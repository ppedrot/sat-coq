Require Import Definitions Bool BoolTactic.

Goal forall a b c d e f g,
  (negb a && b && c && d && e && f && g) ||
  (a && negb b && c && d && e && f && g) ||
  (a && b && negb c && d && e && f && g) ||
  (a && b && c && negb d && e && f && g) ||
  (a && b && c && d && negb e && f && g) ||
  (a && b && c && d && e && negb f && g) ||
  (a && b && c && d && e && f && negb g) ||
  (a && b && c && d && e && f && g)
  = true.
Proof.
Print BoolTactic.
intros; bool_reify.
 apply reduce_poly_of_formula_sound; vm_compute; reflexivity.
Admitted.

Goal forall a b c : bool, c || a = negb (b && negb b && (a || negb a)).
Proof.
intros; bool_ring.
Admitted.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.

Goal forall a b, (a || b || negb (a && b)) = true.
Proof.
intros; bool_ring.