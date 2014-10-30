Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical_Prop.

Lemma true_and_left : forall P, (True /\ P) <-> P.
Proof. intuition. 
Qed. 

Lemma false_and_right : forall P, (P /\ False) <-> False.
intuition.
Qed.

Lemma false_or_left : forall P, (P \/ False) <-> P.
intuition.
Qed.

Lemma not_false_and_left : forall P, (~(False /\ P) <-> True).
intuition.
Qed.

Goal (~False) <-> True. intuition.
Goal (~True) <-> False. intuition.

Hint Rewrite true_and_left : ex.
Hint Rewrite false_and_right : ex.
Hint Rewrite false_or_left : ex.
Hint Rewrite not_false_and_left: ex.

Lemma example1 : forall (P Q : Prop), P -> (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros. intuition.
Qed.

Print example1.

Inductive reify_prop :=
| ftrue | ffalse
| fand : reify_prop -> reify_prop -> reify_prop
| f_or :  reify_prop -> reify_prop -> reify_prop
| fnot : reify_prop -> reify_prop
| finj : Prop -> reify_prop.

Fixpoint reify_propD (e : reify_prop) := 
match e with
| ftrue => True
| ffalse => False
| fand l r => reify_propD l /\ reify_propD r
| f_or l r => reify_propD l \/ reify_propD r
| fnot p => ~ (reify_propD p)
| finj p => p
end.

Ltac reify_prop_tac G :=
match G with
| True => ftrue
| False => ffalse
| ?A /\ ?B  => let Ar := reify_prop_tac A in
                     let Br := reify_prop_tac B in
                     constr:(fand Ar Br)
| ?A \/ ?B  => let Ar := reify_prop_tac A in
                     let Br := reify_prop_tac B in
                     constr:(f_or Ar Br)
| ~ ?A => let Ar := reify_prop_tac A in
         constr:(fnot Ar)
| ?A => constr:(finj A)
end.

Ltac reify :=
match goal with
[ |- ?G ] => let reif := reify_prop_tac G in
             change ?G with (reify_propD reif)
end.

Fixpoint simplify_fprop e := 
match e with
| ftrue => ftrue
| ffalse => ffalse
| fand l r => match (simplify_fprop l), (simplify_fprop r) with
                | ftrue, p | p, ftrue => p
                | ffalse, _ | _, ffalse => ffalse
                | _, _ => e
              end
| f_or l r => match (simplify_fprop l), (simplify_fprop r) with
                | ftrue, p | p, ftrue => ftrue
                | ffalse, p | p, ffalse => p
                | _, _ => e
              end
| fnot (fand ffalse p) | fnot (fand p ffalse) => ftrue
| _ => e end.  

Lemma simplify_fprop_sound : forall e,
reify_propD (simplify_fprop e) -> reify_propD e.
Proof.
intros. induction e; auto.
  + simpl. 
    destruct (simplify_fprop e1) eqn :?; simpl in *; auto;
    destruct (simplify_fprop e2) eqn :?; simpl in *; auto;
    rewrite Heqr in *; simpl in *; intuition.

  + destruct (simplify_fprop e1) eqn :?; simpl in *; auto;
    destruct (simplify_fprop e2) eqn :?; simpl in *; auto;
    rewrite Heqr in *; simpl in *; intuition.

  + destruct e; auto.
    simpl in *.  destruct (e1) eqn :?; simpl in *; auto;
    destruct (e2) eqn :?; simpl in *; auto;
    try rewrite Heqr in *; simpl in *; intuition.
Qed.
 

Lemma example2 : forall (P Q : Prop), P -> (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros. reify. apply simplify_fprop_sound. vm_compute. exact H.
Qed.

Print example2.
