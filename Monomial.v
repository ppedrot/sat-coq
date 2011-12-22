Require Import Definitions Validity.

Section Monomial.

Inductive monomial : Type :=
| mon_null : monomial
| mon_next : monomial -> monomial
| mon_incr : monomial -> monomial.

Fixpoint get_tail (p : poly) :=
match p with
| Cst c => c
| Poly p _ _ => get_tail p
end.

Fixpoint get_coeff n (m : monomial) :=
match m with
| mon_null => get_tail
| mon_next m =>
  get_coeff (S n) m
| mon_incr m =>
  fix F p := match p with
  | Cst _ => 0%Z
  | Poly p i q =>
    match nat_compare n i with
    | Eq => get_coeff n m q
    | Lt => 0%Z
    | Gt => F p
    end
  end
end.

Fixpoint shift (m : monomial) n :=
match n with
| 0 => m
| S n => mon_next (shift m n)
end.

Lemma get_coeff_shift : forall k n m p,
  get_coeff (k + n) m p = get_coeff n (shift m k) p.
Proof.
induction k; intros n m p; simpl; trivial.
  rewrite <- IHk; simpl; f_equal; apply plus_n_Sm.
Qed.

Lemma get_coeff_shift_0 : forall k m p,
  get_coeff k m p = get_coeff 0 (shift m k) p.
Proof.
intros k m p; rewrite <- get_coeff_shift, plus_0_r; trivial.
Qed.

Definition same_coeff p q :=
  forall m, get_coeff 0 m p = get_coeff 0 m q.

Lemma same_coeff_sym : forall p q, same_coeff p q -> same_coeff q p.
Proof.
red; intuition.
Qed.

Fixpoint head_coeff k p :=
match p with
| Cst _ => mon_null
| Poly _ i q =>
  let coeff := mon_incr (head_coeff i q) in
  shift coeff (i - k)
end.

Fixpoint unshift m :=
match m with
| mon_null => mon_null
| mon_next m => unshift m
| mon_incr m => mon_incr m
end.

Fixpoint prefix m :=
match m with
| mon_null => 0
| mon_next m => S (prefix m)
| mon_incr _ => 0
end.

Lemma head_coeff_nonzero : forall k p,
  valid_aux k p -> get_coeff k (head_coeff k p) p = 0%Z -> null p.
Proof.
intros k p Hv Hc.
induction Hv; simpl in *; [subst; constructor|exfalso].
absurd (null q); auto.
rewrite <- get_coeff_shift in Hc; replace (i - k + k) with i in Hc by omega.
simpl in Hc; case_decide; auto.
Qed.

Hint Resolve head_coeff_nonzero.

Lemma unshift_shift_rev : forall m,
  shift (unshift m) (prefix m) = m.
Proof.
intros m; induction m; simpl; congruence.
Qed.

Lemma unshift_max : forall m m', ~ unshift m = mon_next m'.
Proof.
induction m; simpl; congruence.
Qed.

Lemma shift_zero : forall k m p s, valid_aux k p -> s < k ->
  get_coeff 0 (shift (mon_incr m) s) p = 0%Z.
Proof.
intros k m p s Hv Hs; rewrite <- get_coeff_shift_0.
simpl; induction Hv; trivial; case_decide; now auto.
Qed.

Fixpoint diff_coeff pl pr :=
match pl with
| Cst cl =>
  match pr with
  | Cst cr => mon_null
  | Poly pr ir qr => head_coeff 0 (Poly pr ir qr)
  end
| Poly pl il ql =>
  match pr with
  | Cst cr => head_coeff 0 (Poly pl il ql)
  | Poly pr ir qr =>
    match nat_compare il ir with
    | Eq =>
      if decide (eq pl) pr then
      if decide (eq ql) qr then mon_null
      else
        let d := diff_coeff ql qr in
        let m := unshift d in
        let k := prefix d in
        shift (mon_incr (shift m (k - il))) il
      else
        let d := diff_coeff pl pr in
        let m := unshift d in
        let k := prefix d in
        shift (mon_incr (shift m (k - il - 1))) (il + 1)
    | Lt => shift (mon_incr (head_coeff il ql)) il
    | Gt => shift (mon_incr (head_coeff ir qr)) ir
    end
  end
end.

Hint Extern 5 => match goal with [ H : ~ null ?p |- _ ] => absurd (null p) end.

(* Lemma toto : forall kl kr pl pr, valid_aux kl pl -> valid_aux kr pr -> pl <> pr ->
  get_coeff 0 (diff_coeff pl pr) pl <> get_coeff 0 (diff_coeff pl pr) pr.
Proof.
intros kl kr pl pr Hl; revert kr pr; induction Hl; intros kr pr Hr Hd;
inversion Hr; subst; simpl.
    now congruence.
    repeat rewrite <- get_coeff_shift_0; simpl; replace (i - 0) with i in * by omega;
    case_decide; now intuition eauto.
    repeat rewrite <- get_coeff_shift_0; simpl; replace (i - 0) with i in * by omega;
    case_decide; now intuition eauto.
    repeat rewrite <- get_coeff_shift_0; simpl; destruct (nat_compare_spec i i0).
      make_decide (eq p); subst.
        make_decide (eq q); subst; [congruence|].
        repeat rewrite <- get_coeff_shift_0; simpl; case_decide.
        repeat rewrite <- get_coeff_shift.
        match goal with [ |- ?f (?k - ?i + ?i) ?m ?p <> ?t ] => replace (k - i + i) with (k + 0) end.
        do 2 (rewrite get_coeff_shift; rewrite unshift_shift_rev); now intuition eauto.
        assert (i0 <= prefix (diff_coeff q q0)); [apply not_gt; intros Hc|omega].
        eelim IHHl2 with (pr := q0); eauto.
        set (m := diff_coeff q q0) in *; rewrite <- (unshift_shift_rev m);
        define (unshift m) s Hs; destruct s.
          repeat rewrite <- get_coeff_shift_0; simpl.
      admit.
      repeat rewrite <- get_coeff_shift_0; simpl; case_decide.
      replace (i0 + 1) with (S i0).
      rewrite unshift_shift_rev.
      admit.
      do 2 rewrite <- get_coeff_shift_0; simpl; repeat case_decide; intuition eauto.
      do 2 rewrite <- get_coeff_shift_0; simpl; repeat case_decide; intuition eauto.
Qed. *)

Lemma same_coeff_Poly_not_lt : forall kl kr il ir pl ql pr qr,
  valid_aux kl (Poly pl il ql) -> valid_aux kr (Poly pr ir qr) ->
  same_coeff (Poly pl il ql) (Poly pr ir qr) -> ~ il < ir.
Proof.
intros kl kr i j pl ql pr qr Hl Hr H Hc.
pose (m := mon_incr (head_coeff i ql)).
specialize (H (shift m i)); repeat rewrite <- get_coeff_shift_0 in H; simpl in H.
repeat case_decide.
apply head_coeff_nonzero in H; inversion Hl; subst; auto.
Qed.

Lemma same_coeff_Poly_inj_var : forall kl kr il ir pl ql pr qr,
  valid_aux kl (Poly pl il ql) -> valid_aux kr (Poly pr ir qr) ->
  same_coeff (Poly pl il ql) (Poly pr ir qr) -> il = ir.
Proof.
intros kl kr; intros; destruct (lt_eq_lt_dec il ir) as [[Hd|Hd]|Hd]; trivial; exfalso.
eapply (same_coeff_Poly_not_lt kl kr); eauto.
eapply (same_coeff_Poly_not_lt kr kl); eauto; apply same_coeff_sym; auto.
Qed.

Lemma same_coeff_Poly_inj_r : forall kl kr il ir pl ql pr qr,
  valid_aux kl (Poly pl il ql) -> valid_aux kr (Poly pr ir qr) ->
  same_coeff (Poly pl il ql) (Poly pr ir qr) -> same_coeff ql qr.
Proof.
intros kl kr il ir pl ql pr qr Hl Hr H.
assert (Hrw : il = ir) by (eapply same_coeff_Poly_inj_var; eauto); destruct Hrw; rename il into i.
intros m; rewrite <- (unshift_shift_rev m).
remember (unshift m) as m'; destruct m'.
  repeat rewrite <- get_coeff_shift_0; simpl.
  specialize (H (shift (mon_incr mon_null) i));
  repeat rewrite <- get_coeff_shift_0 in H; simpl in H.
  now case_decide; auto.
  symmetry in Heqm'; apply unshift_max in Heqm'; intuition.
  remember (prefix m) as k; destruct (le_lt_dec i k).
    repeat rewrite <- get_coeff_shift_0.
    specialize (H (shift (mon_incr (shift (mon_incr m') (k - i))) i)).
    repeat rewrite <- get_coeff_shift_0 in H; simpl in H.
    case_decide; repeat rewrite <- get_coeff_shift in H.
    replace (k - i + i) with k in H by omega; now auto.
    repeat erewrite shift_zero; eauto; inversion Hl; inversion Hr; subst; now auto.
Qed.

Lemma same_coeff_Poly_inj_l : forall kl kr il ir pl ql pr qr,
  valid_aux kl (Poly pl il ql) -> valid_aux kr (Poly pr ir qr) ->
  same_coeff (Poly pl il ql) (Poly pr ir qr) -> same_coeff pl pr.
Proof.
intros kl kr il ir pl ql pr qr Hl Hr H.
assert (Hrw : il = ir) by (eapply same_coeff_Poly_inj_var; eauto); destruct Hrw; rename il into i.
intros m; rewrite <- (unshift_shift_rev m).
remember (unshift m) as m'; destruct m'.
  repeat rewrite <- get_coeff_shift_0; simpl.
  specialize (H mon_null); simpl in H; now auto.
  now symmetry in Heqm'; apply unshift_max in Heqm'; intuition.
  remember (prefix m) as k; destruct (le_lt_dec (S i) k).
    specialize (H (shift (mon_incr m') k)).
    repeat rewrite <- get_coeff_shift_0 in H; simpl in H.
    case_decide; now repeat rewrite <- get_coeff_shift_0; simpl; auto.
    now repeat erewrite shift_zero; trivial; inversion Hl; inversion Hr; subst; eauto.
Qed.

Lemma not_same_coeff_Cst_Poly : forall c k i p q, valid_aux k (Poly p i q) -> ~ same_coeff (Cst c) (Poly p i q).
Proof.
intros c k i p q H Hc.
pose (coeff := shift (head_coeff k (Poly p i q)) k); specialize (Hc coeff); unfold coeff in Hc; clear coeff.
repeat rewrite <- get_coeff_shift_0 in Hc.
inversion H; subst; absurd (null q); auto.
eapply head_coeff_nonzero; eauto.
simpl in Hc; repeat rewrite  <- get_coeff_shift in Hc; replace (i - k + k) with i in Hc by omega; simpl in Hc.
now case_decide; auto.
Qed.

Lemma same_coeff_aux_eq : forall p q kp kq, valid_aux kp p -> valid_aux kq q ->
  same_coeff p q -> p = q.
Proof.
intros p q kp kq Hp Hq; revert q kq Hq; induction Hp; intros.
  destruct q.
    specialize (H mon_null); simpl in H; congruence.
    eapply not_same_coeff_Cst_Poly in H; now intuition eauto.
  inversion Hq; subst.
    now eelim not_same_coeff_Cst_Poly; [econstructor; eauto|apply same_coeff_sym; eauto].
    f_equal.
      eapply IHHp1; eauto; eapply same_coeff_Poly_inj_l; eauto; now constructor; eauto.
      eapply same_coeff_Poly_inj_var; eauto; now constructor; eauto.
      eapply IHHp2; eauto; eapply same_coeff_Poly_inj_r; eauto; now constructor; eauto.
Qed.

Lemma same_coeff_eq :
  forall p q : poly, valid p -> valid q -> same_coeff p q -> p = q.
Proof.
intros p q [np Hp] [nq Hq] H.
eapply same_coeff_aux_eq; eauto.
Qed.

End Monomial.
