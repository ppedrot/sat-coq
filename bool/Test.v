Add Rec LoadPath "." as CoqSat.

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
intros; bool_ring.
 bool_reify.
vm_compute.
Abort.

Goal forall a b c : bool, c || a || negb a = a || (negb a).
Proof.
intros; bool_ring.
Qed.

Print Unnamed_thm.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.

Goal forall a b, (a || b || negb (a && b)) = true.
Proof.
intros; bool_ring.