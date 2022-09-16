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
  Discprob.Fin Discprob.Prob.


Section Distr.

  (* A probability distribution is a function 
    from finite type to Prob. It's non-empty set.
    
  *)
  Definition Dist {n : nat} := Fin (S n) -> prob.


  (* Two distribution are equivalent if the every element 
  has same probablity *)
  Definition dist_equiv {n : nat} : relation (@Dist n) := 
    fun fd gd => forall (t : Fin (S n)), fd t = gd t.
  
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
  Definition Ret {n : nat} (x : Fin n) : @Dist 1 := 
    fun x => one.

  Definition Bind {m n : nat} 
    (xs : @Dist m) (f : Fin (S m) -> @Dist n) : @Dist m.
  Proof.
  Admitted. 
  