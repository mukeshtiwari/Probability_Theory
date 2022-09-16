From Coq Require Import 
  Utf8 Pnat BinNatDef
  BinPos List Lia.

Import ListNotations.

Section Prob.

 (* We formalise the probability as a rational 
    number where denominator is positive. 
    By construction, we can only construct 
    zero or positive values. 
  *)
  Record prob := 
    mk_prob {num : nat; denum : positive}.

  Declare Scope Prob_scope.
  Delimit Scope Prob_scope with P.
  Local Open Scope Prob_scope.

  Definition prob_eq (p q : prob) : bool := 
    match p, q with 
    | mk_prob pa pb, mk_prob qa qb => 
      Nat.eqb (pa * Pos.to_nat qb) (qa * Pos.to_nat pb)
    end.

  (* Print Grammar constr. *)
  Local Infix "=p=" := prob_eq
    (at level 70, no associativity) : Prob_scope.


  
  (* prob_eq is an equivalence relation *)
  Lemma prob_eq_refl : forall p, p =p= p = true.
  Proof.
    intros [pa pb]; simpl; f_equal.
    apply PeanoNat.Nat.eqb_eq; 
    reflexivity.
  Qed.


  Lemma prob_eq_sym : forall p q,
    p =p= q = true -> q =p= p = true.
  Proof.
    intros [pa pb] [qa qb]; simpl; intro Heq.
    apply PeanoNat.Nat.eqb_eq in Heq.
    apply PeanoNat.Nat.eqb_eq.
    lia.
  Qed.

  Lemma prob_eq_trans : forall p q r, 
    p =p= q = true -> q =p= r = true -> 
    p =p= r = true.
  Proof.
    intros [pa pb] [qa qb] [ra rb]; simpl;
    intros Ha Hb.
    apply PeanoNat.Nat.eqb_eq in Ha, Hb.
    apply PeanoNat.Nat.eqb_eq.
    nia. (* facinating! lia can't solve this goal *) 
  Qed.
  (* end of equivalence relation *)


  Definition zero : prob := mk_prob 0 1.

  Definition one : prob := mk_prob 1 1.


  Definition add_prob (p q : prob) : prob :=
    match p, q with
    | mk_prob a b, mk_prob c d => 
        mk_prob 
        (a * Pos.to_nat d + c * Pos.to_nat b) 
        (b * d) 
    end.

  
  Local Infix "+p" := (add_prob) 
    (at level 50, left associativity) : Prob_scope.

  
  
  Lemma add_prob_assoc : forall p q r : prob, 
    p +p q +p r = p +p (q +p r).
  Proof.
    intros [px dpx] [qx dqx] [rx drx]; simpl; 
     f_equal; try lia.
  Qed.

  Lemma add_prob_comm : forall p q, p +p q = q +p p.
  Proof.
    intros [px Hpx] [qx Hqx]; simpl; 
    f_equal; try lia.
  Qed.


  Definition mul_prob (p q : prob) : prob :=
    match p, q with
    | mk_prob a b , mk_prob c d => 
        mk_prob (a * c) (b * d)
    end.

  Local Infix "*p" := (mul_prob) 
    (at level 40, left associativity) : Prob_scope.

  Lemma mul_prob_assoc : forall px pxx pt,  
    px *p pxx *p pt =  px *p (pxx *p pt).
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd];
    simpl; f_equal; lia.
  Qed.

  Lemma mul_prob_comm: forall p q,  
    p *p q = q *p p.
  Proof.
    intros [px Hpx] [qx Hqx]; simpl; 
    f_equal; try lia.
  Qed.



  Definition leq (p q : prob) : bool :=
    match p, q with
    | mk_prob pa pb, mk_prob qa qb => 
      Nat.leb (pa * Pos.to_nat qb) (qa * Pos.to_nat pb)
    end.

    
  Local Infix "<p=" := (leq) (at level 70). (* associativity? *)
  (* Print Grammar constr. *)

  Lemma prob_leq_refl : forall p, 
    p <p= p = true.
  Proof.
    intros [pa pb]; simpl. 
    apply PeanoNat.Nat.leb_le.
    nia.
  Qed.
  
  Lemma prob_leq_trans : forall p q r, 
    p <p= q = true -> q <p= r = true -> p <p= r = true.
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd]; 
      simpl; intros Hpq Hqr.
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hpq, Hqr.
    nia.
  Qed.

  Lemma prob_leq_add_r : forall p q r, 
    p <p= q = true -> p +p r <p= q +p r = true.
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd]; 
      simpl; intros Hpq.
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hpq.
    nia.
  Qed.

  Lemma prob_leq_add_l : forall p q r, 
    p <p= q = true -> r +p p <p= r +p q = true.
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd]; 
      simpl; intros Hpq.
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hpq.
    nia.
  Qed.

  Lemma prob_leq_mul_r : forall p q r, 
    p <p= q = true -> p *p r <p= q *p r = true.
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd]; 
      simpl; intros Hpq.
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hpq.
    repeat rewrite Pos2Nat.inj_mul, 
      PeanoNat.Nat.mul_assoc.
    apply PeanoNat.Nat.mul_le_mono_r. 
    nia.
  Qed.
    

  Lemma prob_leq_mul_l : forall p q r, 
    p <p= q = true ->  r *p p <p= r *p q = true.
  Proof.
    intros [pxn pxd] [ppxn ppxd] [ptn ptd]; 
      simpl; intros Hpq.
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hpq.
    repeat rewrite Pos2Nat.inj_mul, 
      PeanoNat.Nat.mul_assoc.
    assert (Ht: ptn * pxn * Pos.to_nat ptd * Pos.to_nat ppxd = 
      ptn * (Pos.to_nat ptd * pxn * Pos.to_nat ppxd)). 
    nia.
    rewrite Ht; clear Ht.
    assert (Ht: ptn * ppxn * Pos.to_nat ptd * Pos.to_nat pxd = 
      ptn * (Pos.to_nat ptd * ppxn * Pos.to_nat pxd)). 
    nia.
    rewrite Ht; clear Ht.
    eapply PeanoNat.Nat.mul_le_mono_nonneg_l with (p := ptn); 
    try nia.
  Qed.

  Lemma leq_prob : forall p q, 
    p <p= q = true <-> 
    num p * (Pos.to_nat (denum q)) <= num q * (Pos.to_nat (denum p)).
  Proof.
    intros [px qx] [py qy]; simpl.
    split; intros H;
    [apply PeanoNat.Nat.leb_le in H |
      apply PeanoNat.Nat.leb_le];
    nia.
  Qed.

End Prob.











  