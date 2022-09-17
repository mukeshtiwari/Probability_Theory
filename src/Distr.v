From Coq Require Import 
  PeanoNat Lia Eqdep_dec Arith.
Require Import 
  ExtLib.Structures.Monad
  ExtLib.Structures.Functor
  ExtLib.Structures.Applicative
  ExtLib.Structures.MonadLaws
  ExtLib.Structures.FunctorLaws
  Coq.Unicode.Utf8 
  Coq.Logic.FunctionalExtensionality
  Coq.PArith.Pnat Coq.NArith.BinNatDef
  Coq.PArith.BinPos Lia Coq.Lists.List
  Coq.Classes.Morphisms 
  Coq.Classes.SetoidClass 
  Coq.Sorting.Permutation
  Coq.Relations.Relation_Definitions
  Coq.Logic.FunctionalExtensionality
  Discprob.Prob Discprob.Matrix
  Discprob.Fin_util.


Section Distr.


  (* A probability distribution is a function 
    from finite type to Prob. It's non-empty set.
  *)
  Definition Dist {n : nat} := Fin.t (S n) -> prob.

  
  (* Two distribution are equivalent if the every element 
  has same probablity *)
  Definition dist_equiv {n : nat} : relation (@Dist n) := 
    fun fd gd => forall (t : Fin.t (S n)), fd t = gd t.
  
  Local Infix "=r=" := dist_equiv 
    (at level 70, no associativity).


  (* dist_equiv is Equivalence relation *)  
  Global Instance dist_refl {n : nat} : 
    Reflexive (@dist_equiv n).
  Proof.
    unfold dist_equiv, Reflexive;
    intros ? ?.
    reflexivity.
  Qed.

  Global Instance dist_sym {n : nat} : 
    Symmetric (@dist_equiv n).
  Proof.
    unfold dist_equiv, Symmetric.
    intros ? ? f t.
    now apply eq_sym, f.
  Qed.

  Global Instance dist_trans {n : nat} : 
    Transitive (@dist_equiv n).
  Proof.
    unfold dist_equiv, Transitive.
    intros ? ? ? f g t.
    eapply eq_trans;
    [eapply f | eapply g].
  Qed.

  Global Instance dist_Equiv {n : nat} : 
    Equivalence (@dist_equiv n).
  Proof.
    constructor; 
    [apply dist_refl | 
     apply dist_sym | 
     apply dist_trans].
  Qed.

    


  (* Probability Monad *)
  (* if you give an element x of type Fin (S n),
    I construct a distribution where probability of 
    x is one and everything is zero *)
  Definition Ret {n : nat} (x : Fin.t (S n)) : @Dist n := 
    fun y => match fin_dec x y with 
      | left _ => one
      | right _ => zero
    end.

  (* 
    Proof Idea:
    xs : Fin (S m) → prob is ismorphic to Vector prob (S m), 
    and f : Fin (S m) → Fin (S n) → prob is 
    ismorphic to Vector (Vector (S n) prob) (S m).
    We take first element, say x, of xs and first element,
    say fv,  of f and multiply every every element of fv 
    by x and put it infront. 

  *)
  Definition Bind {m n : nat} 
    (xs : @Dist m) (f : Fin.t (S m) -> @Dist n) : 
    @Dist (m + n + m * n).
  Proof.
    unfold Dist in * |- *.
    pose proof (finite_fun_to_vector xs) as vx.
    pose proof (finite_fun_to_matrix f) as vy.
    remember (@zip_with_f_vector_matrix_row_wise prob
      mul_prob _ vx _ vy) as Hw.
    assert (Ht : S (m + n + m * n) = S m * S n) by nia. 
    rewrite Ht.
    refine(fun ind => Vector.nth Hw ind).
  Defined. 

  (* unfortunately, It can't be turned into monad. *)
End Distr.

  