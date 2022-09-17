From Coq Require Import Fin.

Lemma fin_inv_0 (f : Fin.t 0) : False.
Proof.
  refine (match f with end).
Defined.


Lemma fin_inv_S {n : nat} (f : Fin.t (S n)) :
  (f = Fin.F1) + {t | f = Fin.FS t}.
Proof.
  refine (match f with
    | Fin.F1 => _ 
    | Fin.FS s => _ 
    end);
    [left | right; exists s]; 
    exact eq_refl.
Defined.


Definition fin_dec : 
  forall {n : nat} (x y : Fin.t n), 
  {x = y} + {x <> y}.
Proof.
  refine(
    fix Fn n x {struct x} := 
      match x as x' in Fin.t n' 
      return forall (pf : n = n'),  
      x = eq_rect n' (fun u => Fin.t u) x' n (eq_sym pf) -> _ 
      with 
      | Fin.F1 => fun pf Hx y => _ 
      | Fin.FS xp => fun pf Hx y => _ 
      end eq_refl eq_refl).
  + 
    destruct (fin_inv_S y) as [Hl | [t Hr]];
    subst; [left | right].
    ++ reflexivity.
    ++ intro Hf; inversion Hf.
  + 
    destruct (fin_inv_S y) as [Hl | [t Hr]];
    subst.
    ++ 
      right; intros Hf; inversion Hf.
    ++ 
      destruct (Fn _ xp t) as [Hl | Hr];
      subst.
      +++
        left; auto.
      +++
        right; intro Hf.
        apply Hr.
        apply FS_inj.
        exact Hf.
Defined.

