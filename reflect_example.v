(* Joey Dodds *)

(* begin hide*)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical_Prop.
(* end hide *)

(** This example builds on Adam Chlipala's CPDT chapter 
    on reflection:
    http://adam.chlipala.net/cpdt/html/Reflection.html *)

(** Our goal in this file is to simplify propositions
    with and, or, True, False, as well as other arbitrary
    propositions mixed in. We will do this by standard Ltac
    programming and also by computational reflection. A
    technique that is generally much faster, in part because
    it produces very compact proof terms 

    [example1] is easily solved by Coq*)

Lemma easy_solve : forall (P Q : Prop), P -> (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros. intuition.
Qed.

(** The following goal can't be solved by intuition. It only unfolds
    ~. It should be possible to make some progress on the goal
    automatically though.
*)

Goal forall (P Q : Prop), (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros. intuition.
Abort.

(** We define a few lemmas that we can use to do rewrites in a goal
    these aren't all we need for arbitrary goals, but they 
    work for our example  *)

Lemma true_and_left : forall P, (True /\ P) <-> P.
intuition. 
Qed. 

Lemma false_and_right : forall P, (P /\ False) <-> False.
intuition.
Qed.

Lemma false_or_left : forall P, (P \/ False) <-> P.
intuition.
Qed.

(** Coq uses an intuitionistic logic which means we can't distribute 
   negation (~) using De Morgan's laws like we can in classical logic.
   we can prove some special cases like the following though. *)

Lemma not_false_and_left : forall P, (~(False /\ P) <-> True).
intuition.
Qed.

Lemma not_false_true : (~False) <-> True. intuition. Qed.
Lemma not_true_false : (~True) <-> False. intuition. Qed.

(** We can add these lemmas to a hint database named [ex], so that 
    coq can automatically try them all for us. *)

Hint Rewrite true_and_left : ex.
Hint Rewrite false_and_right : ex.
Hint Rewrite false_or_left : ex.
Hint Rewrite not_false_and_left: ex.

(* We use our autorewrite datase to simplify the lemma down to [P], and admit it
   to see the proof term *)

Lemma simplify_it : forall (P Q : Prop), (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros.
autorewrite with ex. admit.
Qed.

(** The proof term for simplify it is pretty large (around 50 lines). It
    is easy to imagine that for larger goals and more complex reasoning
    things could get much bigger much faster *)

Print simplify_it.

(** To fix this problem, we use proof by reflection. Proof by reflection
    uses computation in Gallina, Coq's built-in programming languages to
    do the proof work. Because the execution of a program is the proof,
    the generated proof term will be smaller. *)

(** Gallina programs can't match on Prop because it is not an inductively
    defined datatype. This means we need to use Ltac, the tactic programming
    language of Coq, to transform our Prop into an expression that Gallina programs
    can run on the sytax of these expressions is given below. The process of 
    translation from Prop into a concrete syntax is called reification. *)

Inductive reified_prop :=
| ftrue | ffalse
| fand : reified_prop -> reified_prop -> reified_prop
| f_or :  reified_prop -> reified_prop -> reified_prop
| fnot : reified_prop -> reified_prop
| finj : Prop -> reified_prop.

(** Next we give the denotation of the syntax of [reified_prop]. This is the connection
    between the expressions of [reified_prop] and the Props that we wish to reason
    about in our proof. We give a constructor for each term we are interested in
    as well as finj, a constructor that allows us to put arbitrary Props into 
    expressions. The process of taking the denotation of a reified expression
    is called reflecting it. 
    The entire process of reifying a term, computing on it, and returning it
    to it's original form is known as proof by reflection.
     *)

Fixpoint reified_propD (e : reified_prop) := 
match e with
| ftrue => True
| ffalse => False
| fand l r => reified_propD l /\ reified_propD r
| f_or l r => reified_propD l \/ reified_propD r
| fnot p => ~ (reified_propD p)
| finj p => p
end.

(** We use Ltac to take a Prop and turn it into a [reified_prop] *)

Ltac reified_prop_tac G :=
match G with
| True => ftrue
| False => ffalse
| ?A /\ ?B  => let Ar := reified_prop_tac A in
                     let Br := reified_prop_tac B in
                     constr:(fand Ar Br)
| ?A \/ ?B  => let Ar := reified_prop_tac A in
                     let Br := reified_prop_tac B in
                     constr:(f_or Ar Br)
| ~ ?A => let Ar := reified_prop_tac A in
         constr:(fnot Ar)
| ?A => constr:(finj A)
end.

(** Our reification tactic runs [reified_prop_tac] and changes the goal
    out for the denotation function applied to the reification. 
    Ideally reified_propD and reified_prop_tac will be inverse of eachother.
    if they aren't this tactic might fail. *)

Ltac reify :=
match goal with
[ |- ?G ] => let reif := reified_prop_tac G in
             change ?G with (reified_propD reif)
end.

(** Now we write our function to simplify our reified Props. 
    the result of this function is a possibly-simplified reified Prop*)

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

(** Now we prove a soundness lemma that allows us to replace
    a reified goal with a simplified reified goal *)

Ltac prove_sdns e1 e2 :=
destruct (e1) eqn :Heqr; simpl in *; auto;
    destruct (e2) eqn : ? ; simpl in *; auto;
    try rewrite Heqr in *; simpl in *; intuition.

Lemma simplify_fprop_sound : forall e,
reified_propD (simplify_fprop e) -> reified_propD e.
Proof.
intros. induction e; auto;
  solve [prove_sdns (simplify_fprop e1) (simplify_fprop e2) | 
         destruct e; auto; simpl in *; prove_sdns e1 e2]. 
Qed.    


(** We can now use our reflective procedure to simplify the goal *)

Lemma example2 : forall (P Q : Prop), (True /\ ~(False /\ (~False \/ P)) /\ P) \/ Q /\ False.
intros. 
(** We use our tactic to reify the goal, replacing it with something
    we can run a program on *)
reify.
(** We apply our soundness lemma, letting us put the computation
    we wish to run into the goal *) 
apply simplify_fprop_sound. 
(** We simultaneously run the computation and evaluate the denotation
    function by calling vm_compute. vm_compute compiles code to very
    quickly perform computation *)
vm_compute. 
admit.
Qed.

(** The resulting proof term is much smaller (around 16 lines). Most of it is used
    to print the original term and the reified term to show that
    there is a conversion between the two, so the size is always approximately
    linear in the size of the goal being simplified *)

Print example2.
