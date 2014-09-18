Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Import ListNotations.

(** Recursive polymorphic definition of trees *)
Inductive tree (X:Type) : Type :=
  | nilt : tree X
  | node : X -> tree X -> tree X -> tree X.

Arguments nilt {X}.
Arguments node {X} _ _ _.

(** Functions over lists and trees. *)
(** Reflection *)
Fixpoint refl {X:Type} (t:tree X) : (tree X) :=
  match t with
    | nilt => nilt
    | (node a izq der) => node a (refl der) (refl izq)
  end.

(** Reverse *)
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
    | [] => []
    | x::xs => (rev xs) ++ [x]
  end.

(** Auxiliary lemmas *)
Lemma rev_unit : forall {X:Type} (l:list X) (a:X), 
  rev (l ++ [a]) = a :: rev l.
Proof.
  intros X l a.
  induction l as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs. reflexivity.
Qed.
    
Lemma rev_app_distr: forall {X:Type} (x y : list X), 
  rev (x ++ y) = rev y ++ rev x.
Proof.
  intros X x.
  induction x as [|x' xs].
    intros y. simpl. rewrite -> app_nil_r. reflexivity.
    intros y. simpl. rewrite -> IHxs. symmetry. apply app_assoc.
Qed.



(** Tree traversals *)
Fixpoint prer {X:Type} (t:tree X) : list X :=
  match t with
    | nilt => []
    | (node a izq der) => [a] ++ (prer izq) ++ (prer der)
  end.

Fixpoint inor {X:Type} (t:tree X) : list X :=
  match t with
    | nilt => []
    | (node a izq der) => (inor izq) ++ [a] ++ (inor der)
  end.

Fixpoint posr {X:Type} (t:tree X) : list X :=
  match t with
    | nilt => []
    | (node a izq der) => (posr izq) ++ (posr der) ++ [a]
  end.




(** Two theorems about tree traversals in reflected trees. *)
Theorem prerfl_invpos : forall {X:Type} (t:tree X),
  prer(refl t) = rev(posr t).
Proof.
  intros X t.
  induction t as [|x izq Hiz der Hdr].
  (* Case t = nilt *)
    reflexivity.
  (* Case t = (x izq der) *)
    simpl.
    rewrite -> rev_app_distr.
    rewrite -> rev_unit.
    rewrite -> Hiz.
    rewrite -> Hdr.
    reflexivity.
Qed.

Remark posrfl_invpre : forall {X:Type} (t:tree X),
  prer(refl t) = rev(posr t).
Proof.
  