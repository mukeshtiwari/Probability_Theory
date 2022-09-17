Require Import 
  Utf8 Lia Vector
 Fin.

Section Mat.

  Context {R : Type}.

  Lemma vector_inv_0 (v : Vector.t R 0) :
    v = @Vector.nil R.
  Proof.
    refine (match v with
            | @Vector.nil _ => _
            end).
    reflexivity.
  Defined.

  Lemma vector_inv_S {n : nat} (v : Vector.t R (S n)) :
    {x & {v' | v = @Vector.cons _ x _ v'}}.
  Proof.
    refine (match v with
            | @Vector.cons _ x _ v' =>  _
            end);
    eauto.
  Defined.

  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  Lemma fin_inv_S {n : nat} (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 => _
            | Fin.FS _ => _
            end); eauto.
  Defined.


  Definition vector_to_finite_fun : 
    forall {n : nat}, 
    Vector.t R n -> (Fin.t n -> R).
  Proof.
    induction n.
    + intros v f.
      apply fin_inv_0 in f.
      refine (match f with end).
    + intros v f.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      destruct (fin_inv_S f) as [h | [t p]].
      exact vhd.
      exact (IHn vtl t).
  Defined.


  Definition finite_fun_to_vector : 
    forall {n : nat},  
    (Fin.t n -> R) -> Vector.t R n.
  Proof.
    induction n.
    + intros f.
      apply Vector.nil.
    + intros f.
      apply Vector.cons.
      apply f, Fin.F1.
      apply IHn;
      intro m.
      apply f, Fin.FS, m.
  Defined.


  Lemma finite_fun_to_vector_correctness 
    (m : nat) (f : Fin.t m -> R) (i : Fin.t m) :
    Vector.nth (finite_fun_to_vector f) i = f i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S i as [-> | (i' & ->)].
      + reflexivity.
      + cbn. 
        now rewrite IHm.
  Defined.


  Lemma vector_to_finite_fun_correctness 
    (m : nat) (v : Vector.t R m) (i : Fin.t m) :
    Vector.nth v i = (vector_to_finite_fun v) i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S i as [-> | (i' & ->)].
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp.
      reflexivity.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp;
      simpl; 
      now rewrite IHm.
  Defined.


  Lemma vector_finite_back_forth : 
    forall (n : nat) (v : Vector.t R n),
    v = finite_fun_to_vector (vector_to_finite_fun v).
  Proof.
    induction n.
    + intros v.
      pose proof (vector_inv_0 v) as Hv.
      subst; 
      reflexivity.
    + intros v.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      subst; simpl; f_equal.
      apply IHn.
  Defined.


  Lemma finite_vector_back_forth : 
    forall (n : nat) (f : Fin.t n -> R) (i : Fin.t n),
    vector_to_finite_fun (finite_fun_to_vector f) i = f i.
  Proof.
    intros ? ? ?.
    now rewrite <-vector_to_finite_fun_correctness,
    finite_fun_to_vector_correctness.
  Qed.
        
End Mat.


Section Mx.

  Context {R : Type}.

  Definition Matrix n m := Vector.t (Vector.t R m) n.

  Definition finite_fun_to_matrix {n m}  
    (f : Fin.t n -> Fin.t m -> R) : Matrix n m :=
    @finite_fun_to_vector _ n (fun (x : Fin.t n) => 
      @finite_fun_to_vector _ m (fun (y : Fin.t m) => f x y)).

  Definition matrix_to_finite_fun {n m} 
    (mx : Matrix n m) : Fin.t n -> Fin.t m -> R :=
    fun (x : Fin.t n) (y : Fin.t m) => 
      @vector_to_finite_fun _ m 
        ((@vector_to_finite_fun _ n mx) x) y.

  
  Lemma matrix_to_finite_back_forth : 
    forall n m (mx : Matrix n m),
    mx = finite_fun_to_matrix (matrix_to_finite_fun mx).
  Proof.
    induction n.
    + intros ? ?.
      unfold Matrix in mx.
      pose proof (vector_inv_0 mx) as Hn.
      subst; reflexivity.
    + intros ? ?.
      unfold Matrix in mx. 
      destruct (vector_inv_S mx) as (vhd & vtl & vp).
      subst.
      cbn.
      f_equal.
      apply vector_finite_back_forth.
      apply IHn.
  Defined.


  Lemma finite_to_matrix_back_and_forth : 
    forall n m (mx : Fin.t n -> Fin.t m -> R)
    (i : Fin.t n) (j : Fin.t m), 
    mx i j =  
    matrix_to_finite_fun (finite_fun_to_matrix mx) i j.
  Proof.
    unfold matrix_to_finite_fun, 
    finite_fun_to_matrix.
    intros until j.
    rewrite !finite_vector_back_forth.
    reflexivity.
  Qed.

End Mx.

(* Can I generalise the it to an arbitrary dimension

  Matrix n m p q r s .... :=
  Vector R (Vector R (Vector R ...)) n 

  It will be very nice and awesome dependent type programming

*)

Section VUtil.

  Context {R : Type} 
    {f : R -> R -> R}.

  Definition zip_with_f_vector_matrix_row_wise : 
    forall {m : nat},
    Vector.t R m -> 
    forall {n : nat}, @Matrix R m n -> Vector.t R (m * n).
  Proof.
    refine (fix Fn m vx {struct vx} := 
    match vx as vx' in Vector.t _ m' 
    return forall (pf : m = m'), 
      vx = eq_rect m' _ vx' m (eq_sym pf) -> _ 
    with 
    | Vector.nil _ => fun pf Hvx n vy => _
    | Vector.cons _ h m' t => fun pf Hvx n vy => _ 
    end eq_refl eq_refl).
    + cbn; exact (@Vector.nil R).
    + unfold Matrix in vy; cbn.
      destruct (vector_inv_S vy) as [vh [vt Hvy]].
      remember (Vector.map (λ x, f h x) vh) as vhret.
      remember (Fn _ t _ vt) as vyret.
      exact (Vector.append vhret vyret).
  Defined.

End VUtil.




    
    
