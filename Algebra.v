Require Import Definitions Validity.

Section Evaluation.

Existing Instance Decidable_null.

Fixpoint eval (var : nat -> Z) (p : poly) :=
match p with
| Cst c => c
| Poly p i q => Zplus (eval var p) (Zmult (var i) (eval var q))
end.

Definition same_eval (p q : poly) := forall var, eval var p = eval var q.

(* Useful simple properties *)

Lemma eval_null_zero : forall p var, null p -> eval var p = 0%Z.
Proof.
intros p var []; reflexivity.
Qed.

Lemma eval_extensional_eq_compat : forall p var1 var2,
  (forall x, var1 x = var2 x) -> eval var1 p = eval var2 p.
Proof.
intros p var1 var2 H; induction p; simpl; try_rewrite; auto.
Qed.

Lemma eval_suffix_compat : forall k p var1 var2,
  (forall i, k <= i -> var1 i = var2 i) -> valid_aux k p ->
  eval var1 p = eval var2 p.
Proof.
intros k p var1 var2 Hvar Hv; revert var1 var2 Hvar.
induction Hv; intros var1 var2 Hvar; simpl; [now auto|].
rewrite Hvar; [|now auto]; erewrite (IHHv1 var1 var2); [|now intuition].
erewrite (IHHv2 var1 var2); [ring|now intuition].
Qed.

End Evaluation.

Section Algebra.

Require Import MinMax.

(* Addition of polynomials *)

Fixpoint poly_add pl {struct pl} :=
match pl with
| Cst cl =>
  fix F pr := match pr with
  | Cst cr => Cst (cl + cr)
  | Poly pr ir qr => Poly (F pr) ir qr
  end
| Poly pl il ql =>
  fix F pr {struct pr} := match pr with
  | Cst cr => Poly (poly_add pl pr) il ql
  | Poly pr ir qr =>
    match nat_compare il ir with
    | Eq =>
      let qs := poly_add ql qr in
      (* Ensure validity *)
      if decide (null qs) then poly_add pl pr
      else Poly (poly_add pl pr) il qs
    | Lt => Poly (poly_add pl (Poly pr ir qr)) il ql
    | Gt => Poly (F pr) ir qr
    end
  end
end.

(* More efficient implementation of opposite over polynomials.
   Instead of computing (-1) × p we just swap coefficients. *)

Fixpoint poly_opp p :=
match p with
| Cst c => Cst (Zopp c)
| Poly p i q => Poly (poly_opp p) i (poly_opp q)
end.

(* Multiply by a constant *)

Fixpoint poly_mul_cst v p :=
match p with
| Cst c => Cst (c * v)
| Poly p i q =>
  let r := poly_mul_cst v q in
  (* Ensure validity *)
  if decide (null r) then poly_mul_cst v p
  else Poly (poly_mul_cst v p) i r
end.

(* Multiply by a monomial *)

Fixpoint poly_mul_mon k p :=
match p with
| Cst c =>
  if decide (null p) then p
  else Poly (Cst 0) k p
| Poly p i q =>
  if decide (k <= i) then Poly (Cst 0) k (Poly p i q)
  else Poly (poly_mul_mon k p) i (poly_mul_mon k q)
end.

(* Multiplication of polynomials *)

Fixpoint poly_mul pl {struct pl} :=
match pl with
| Cst cl => poly_mul_cst cl
| Poly pl il ql =>
  fun pr =>
    (* Multiply by a factor *)
    let qs := poly_mul ql pr in
    (* Ensure validity *)
    if decide (null qs) then poly_mul pl pr
    else poly_add (poly_mul pl pr) (poly_mul_mon il qs)
end.

(* Compatibility with evaluation *)

Lemma poly_add_Zplus_compat : forall pl pr var, eval var (poly_add pl pr) = Zplus (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
  induction pr; simpl; auto; solve [try_rewrite; ring].
  induction pr; simpl; auto; try solve [try_rewrite; simpl; ring].
  destruct (nat_compare_spec n n0); repeat case_decide; simpl; first [try_rewrite; ring|idtac].
    try_rewrite; ring_simplify; repeat rewrite <- Zplus_assoc.
    rewrite <- Zmult_plus_distr_r, <- IHpl2.
    match goal with [ H : null ?p |- _ ] => rewrite (eval_null_zero _ _ H) end; ring.
    simpl; rewrite IHpl1; simpl; ring.
Qed.

Lemma poly_opp_Zopp_compat : forall p var, eval var (poly_opp p) = Zopp (eval var p).
Proof.
intros p var; induction p; simpl; try_rewrite; ring.
Qed.

Lemma poly_mul_cst_Zmult_compat : forall v p var,
  eval var (poly_mul_cst v p) = (v * eval var p)%Z.
Proof.
intros v p; induction p; intros var; simpl; [ring|].
case_decide; simpl; try_rewrite; [ring_simplify|ring].
replace (v * var n * eval var p2)%Z with (var n * (v * eval var p2))%Z by ring.
rewrite <- IHp2; inversion H; simpl; ring.
Qed.

Lemma poly_mul_mon_Zmult_compat : forall i p var,
  eval var (poly_mul_mon i p) = (var i * eval var p)%Z.
Proof.
intros i p var; induction p; simpl; case_decide; simpl; try_rewrite; try ring.
inversion H; ring.
Qed.

Lemma poly_mul_Zmult_compat : forall pl pr var, eval var (poly_mul pl pr) = Zmult (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
  apply poly_mul_cst_Zmult_compat.
  case_decide; simpl.
    rewrite IHpl1; ring_simplify.
    replace (eval var pr * var n * eval var pl2)%Z
    with (var n * (eval var pl2 * eval var pr))%Z by ring.
    now rewrite <- IHpl2; inversion H; simpl; ring.
    rewrite poly_add_Zplus_compat, poly_mul_mon_Zmult_compat, IHpl1, IHpl2; ring.
Qed.

(* Compatibility with validity *)

Hint Extern 5 =>
match goal with
| [ |- min ?x ?y <= ?z ] =>
  apply min_case_strong; intros; omega
| [ |- ?z <= min ?x ?y ] =>
  apply min_case_strong; intros; omega
end.
Hint Resolve le_min_r le_min_l.

Lemma poly_add_valid_aux_compat : forall kl kr pl pr, valid_aux kl pl -> valid_aux kr pr ->
  valid_aux (min kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr; induction Hl; intros kr pr Hr; simpl.
  eapply valid_aux_le_compat; [clear k|apply le_min_r].
  now induction Hr; auto.
  assert (Hle : min k kr <= min i kr).
    apply min_case_strong; intros; apply min_case_strong; intros; auto; omega.
  apply (valid_aux_le_compat (min i kr)); auto.
  clear - IHHl1 IHHl2 Hl2 Hr H0; induction Hr.
    constructor; auto.
      now rewrite <- (min_id (S i)); intuition.
    destruct (nat_compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
        eapply valid_aux_le_compat; eauto; instantiate; rewrite min_id; auto.
        now eapply valid_aux_le_compat; eauto; instantiate; rewrite min_id; auto.
        now eapply valid_aux_le_compat; eauto; instantiate; rewrite min_id; auto.
        apply (valid_aux_le_compat (min (S i) i0)); intuition.
        apply (valid_aux_le_compat (min i (S i0))); intuition.
Qed.

Lemma poly_opp_null_compat : forall p, null (poly_opp p) -> null p.
Proof.
intros p; induction p; simpl; inversion 1 as [Hn].
replace z with (- - z)%Z by ring; destruct Hn; constructor.
Qed.

Lemma poly_opp_valid_aux_compat : forall k p, valid_aux k p -> valid_aux k (poly_opp p).
Proof.
intros k p H; induction H; simpl; constructor; auto.
intros Hc; apply poly_opp_null_compat in Hc; auto.
Qed.

Lemma poly_mul_cst_valid_aux_compat : forall k v p, valid_aux k p -> valid_aux k (poly_mul_cst v p).
Proof.
intros k v p H; induction H; simpl; [now auto|].
case_decide; [|now auto].
eapply (valid_aux_le_compat (S i)); now auto.
Qed.

Lemma poly_mul_mon_null_compat : forall i p, null (poly_mul_mon i p) -> null p.
Proof.
intros i p; induction p; simpl; case_decide; simpl; inversion 1; intuition.
Qed.

Lemma poly_mul_mon_valid_aux_compat : forall k i p, valid_aux k p -> valid_aux (min i k) (poly_mul_mon i p).
Proof.
intros k i p H; induction H; simpl; case_decide; intuition.
apply (valid_aux_le_compat i); auto; constructor; intuition.
match goal with [ H : null ?p |- _ ] => solve[inversion H] end.
apply (valid_aux_le_compat k); auto; constructor; intuition.
  assert (X := poly_mul_mon_null_compat); intuition eauto.
  cutrewrite <- (min i (S i0) = S i0); intuition.
  cutrewrite <- (min i i0 = i0); intuition.
Qed.

Lemma poly_mul_valid_aux_compat : forall kl kr pl pr, valid_aux kl pl -> valid_aux kr pr ->
  valid_aux (min kl kr) (poly_mul pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr.
induction Hl; intros kr pr Hr; simpl.
  apply poly_mul_cst_valid_aux_compat; auto.
  apply (valid_aux_le_compat kr); now auto.
  apply (valid_aux_le_compat (min (min (S i) kr) (min i (min i kr)))).
    case_decide.
      apply (valid_aux_le_compat (min (S i) kr)); now auto.
      apply poly_add_valid_aux_compat; auto.
      apply poly_mul_mon_valid_aux_compat; intuition.
    repeat apply min_case_strong; omega.
Qed.

Section Eval.

(* Here begins the proof that two polynoms are equal iff they have the same 
   evaluations. *)

(* Some stuff about replacing a variable in an assignation *)

Definition replace (var : nat -> Z) n z :=
  fun m => if decide (n = m) then z else var m.

Lemma eval_replace_compat : forall k p var n z, valid_aux k p -> n < k ->
  eval (replace var n z) p = eval var p.
Proof.
intros k p var n z H Hlt; unfold replace.
rewrite <- (eval_suffix_compat k _ var); auto.
intros; case_decide; omega.
Qed.

Lemma replace_idem : forall var n z1 z2 m,
  replace (replace var n z2) n z1 m = replace var n z1 m.
Proof.
intros; unfold replace; case_decide; auto.
Qed.

Lemma eval_replace_idem : forall p var n z1 z2,
  eval (replace (replace var n z2) n z1) p = eval (replace var n z1) p.
Proof.
intros p var n z1 z2; induction p; simpl; try_rewrite; auto.
repeat rewrite replace_idem; auto.
Qed.

(* Diverge builds up a non-zero assignation from a non-null polynom *)

Fixpoint diverge p :=
match p with
| Cst c => pair (fun _ : nat => 1%Z) (fun m : Z => m)
| Poly p i q =>
  let (var, bnd) := diverge q in
  let k := Zabs (eval var p) in
  let s := bnd (k + 1)%Z in
  (replace var i (Zmax 1 s), Zmax s)
end.

Let nonzero_var p := fst (diverge p).
Let lower_bound p := snd (diverge p).

(* The HARD theorem *)

Lemma not_null_diverge : forall k p M r, valid_aux k p -> ~ null p ->
  (0 <= M)%Z -> (lower_bound p M <= r)%Z ->
  (M <= Zabs (r * eval (replace (nonzero_var p) k r) p))%Z.
Proof.
intros k p; revert k; induction p as [c|p _ i q IH]; intros k M r H Hp HM Hr;
unfold lower_bound, nonzero_var in *; simpl in *; inversion H; subst.
  intros; rewrite Zabs_Zmult.
  assert (Hd : c <> 0%Z) by (intros Hc; elim Hp; rewrite Hc; constructor).
  assert (Hle : (1 <= Zabs c)%Z) by (apply Zabs_ind; omega).
  assert (Hrle : (M <= Zabs r)%Z) by (apply Zabs_ind; omega).
  replace M with (M * 1)%Z by ring.
  apply Zmult_le_compat; omega.
  define (diverge q) ans Hans; destruct ans as [var bnd]; simpl in *; clear Hans.
  rewrite Zabs_Zmult; replace M with (M * 1)%Z by ring; apply Zmult_le_compat; try omega.
    now eapply Zle_trans; [eapply Zle_max_r|]; eapply Zle_trans; [apply Hr|]; apply Zabs_ind; omega.
    repeat rewrite (eval_replace_compat (S i) p); first [now eauto|omega|idtac].
    apply (Zplus_le_reg_l _ _ (Zabs (- eval var p))).
    eapply Zle_trans; [|eapply Zabs_triangle].
    match goal with [ |- Zle _ (Zabs ?t) ] =>
      define t c Hc; ring_simplify in Hc; rewrite <- Hc, Zabs_Zopp; clear c Hc
    end.
    destruct (eq_nat_dec k i) as [Heq|Hdf]; subst.
      repeat rewrite replace_idem; repeat rewrite eval_replace_idem.
      unfold replace at 1; case_decide; try omega.
      now eapply IH; eauto; [apply Zabs_ind; omega|eapply Zle_trans; [apply Zle_max_l|apply Hr]].
      rewrite (eval_replace_compat i q); first [now eauto|omega|idtac].
    unfold replace at 1 2; repeat case_decide; try omega.
      eapply IH; eauto; [apply Zabs_ind; omega|apply Zle_max_r].
Qed.

(* Immediate consequence: non-null polynomials have non-zero evaluations. *)

Lemma not_null_nonzero : forall p,
  {var | forall k, valid_aux k p -> ~ null p -> eval var p <> 0%Z}.
Proof.
intros p.
pose (var := nonzero_var p); pose (bnd := lower_bound p 1).
exists (replace var 0 bnd).
abstract (
intros k H Hp Hc;
assert (Hv : valid_aux 0 p) by (eapply valid_aux_le_compat; [eauto|omega]);
assert (Hle : (0 <= 1)%Z) by omega;
assert (Hd := not_null_diverge 0 p 1 bnd Hv Hp Hle (Zle_refl _));
unfold var in Hc; rewrite Hc in Hd; rewrite Zmult_0_r in Hd; simpl in Hd; omega).
Defined.

(* Ancilliary purely syntactical lemma *)

Lemma null_sub_implies_eq : forall kl kr pl pr, valid_aux kl pl ->
  valid_aux kr pr -> null (poly_add pl (poly_opp pr)) -> pl = pr.
Proof.
intros kl kr pl pr Hl; revert kr pr; induction Hl; intros kr pr Hr Heq; simpl in *.
induction Hr; simpl in *; auto; inversion Heq.
  f_equal; match goal with [ H : 0%Z = ?t |- _ ] =>
    apply (f_equal (fun z => Zplus z c0)) in H; ring_simplify in H; now auto
  end.
induction Hr; simpl in *; auto; inversion Heq.
  destruct (nat_compare_spec i i0); subst; try discriminate.
  case_decide; try discriminate; f_equal.
    eapply IHHl1; now eauto.
    inversion H3; eapply IHHl2; now eauto.
Qed.

(* The main result *)

Lemma same_eval_eq : forall pl pr, valid pl -> valid pr ->
  same_eval pl pr -> pl = pr.
Proof.
intros pl pr [kl Hl] [kr Hr] H.
define (poly_add pl (poly_opp pr)) d Hd.
define (decide (null d)) b Hb; destruct b; try_decide.
  inversion Hb; subst d.
  eapply null_sub_implies_eq; eauto.
  exfalso; destruct (not_null_nonzero d) as [var Hvar]; auto.
  eelim Hvar; subst; eauto.
    subst; eapply valid_aux_le_compat; [apply poly_add_valid_aux_compat; eauto|apply le_0_n].
    apply poly_opp_valid_aux_compat; eauto.
  rewrite poly_add_Zplus_compat, poly_opp_Zopp_compat.
  specialize (H var); rewrite H; ring.
Qed.

End Eval.

End Algebra.
