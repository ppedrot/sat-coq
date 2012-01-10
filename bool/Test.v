Add Rec LoadPath "." as Btauto.

Require Import Bool Reflect.

Declare ML Module "btauto".

Goal forall a b c d e f g,
  (negb a && b && c && d && e && f && g) ||
  (a && negb b && c && d && e && f && g) ||
  (a && b && negb c && d && e && f && g) ||
  (a && b && c && negb d && e && f && g) ||
  (a && b && c && d && negb e && f && g) ||
  (a && b && c && d && e && negb f && g) ||
  (a && b && c && d && e && f && negb g)
  = false.
Proof.
intros.
Abort.

Goal forall a b c : bool, c || a = negb ((negb a) && (negb c)).
Proof.
intros; btauto.
Qed.

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