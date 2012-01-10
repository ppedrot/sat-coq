Goal True.

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
btauto.
 apply reduce_poly_of_formula_sound_alt; vm_compute.
admit.
Qed.

Goal forall a b c : bool, c || a = a || (negb a).
Proof.
intros; btauto.
Abort.

Goal forall a b c : bool, c || a || (negb a && b) || (negb a && negb b) = a || (negb a).
Proof.
intros.
btauto.
Qed.

Print Unnamed_thm.

Goal forall a b, (a || negb b) && (negb a || b) = true.
intros; bool_ring.
Admitted.

Goal forall a b, (a || b || negb (a && b)) = true.
Proof.
intros; bool_ring.