From Stdlib Require Import RelationClasses.

Declare Scope fixit.
Delimit Scope fixit with fixit.
Open Scope fixit.

(** * Unary Inductive and Coinductive Predicates *)

Section Fix1.

Variable A : Prop.

(** ** Definitions *)

Definition le (X Y : A -> Prop) : Prop :=
  forall a, X a -> Y a.

Definition union (X Y : A -> Prop) (a : A) : Prop :=
  X a \/ Y a.

Definition inter (X Y : A -> Prop) (a : A) : Prop :=
  X a /\ Y a.

Definition mono (F : (A -> Prop) -> (A -> Prop)) : Prop :=
  forall (X Y : A -> Prop), le X Y -> le (F X) (F Y).

Definition lfp (F : (A -> Prop) -> (A -> Prop)) (a : A) :=
  forall X, le (F X) X -> X a.

Definition gfp (F : (A -> Prop) -> (A -> Prop)) (a : A) :=
  exists X, le X (F X) /\ X a.

(** ** Notations **)

Infix "<=" := le : fixit.
Infix "/\" := union : fixit.
Infix "\/" := inter : fixit.

(** ** Typeclasses *)

Instance le_trans:
  Transitive le.
Proof.
  intros X Y Z H1 H2 a Ha.
  now apply H2, H1.
Qed.

Instance le_refl:
  Reflexive le.
Proof.
  easy.
Qed.

Class Mono (F : (A -> Prop) -> (A -> Prop)) : Prop :=
  is_mono : mono F.

(** ** Facts *)

Theorem lfp_fold (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  F (lfp F) <= lfp F.
Proof.
  intros a Ha X HX.
  apply HX.
  eapply is_mono; cycle 1.
  apply Ha.
  intros b Hb.
  apply (Hb X), HX.
Qed.

Theorem lfp_unfold (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  lfp F <= F (lfp F).
Proof.
  intros a Ha.
  apply (Ha (F (lfp F))), is_mono.
  apply lfp_fold, is_mono.
Qed.

Theorem fixpoint_induction (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  forall (P : A -> Prop),
    F P <= P ->
    forall a, lfp F a -> P a.
Proof.
  intros P HP a Ha.
  apply (Ha P), HP.
Qed.

Theorem lfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    lfp F1 <= lfp F2.
Proof.
  intros F1 F2 H a Ha X HX.
  apply (Ha X).
  now transitivity (F2 X).
Qed.

Theorem gfp_unfold (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  gfp F <= F (gfp F).
Proof.
  intros a (X & Hle & Ha).
  eapply is_mono; cycle 1.
  apply Hle, Ha.
  transitivity (F X); auto.
  intros b Hb. exists (F X).
  split; auto.
Qed.

Theorem gfp_fold (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  F (gfp F) <= gfp F.
Proof.
  intros a Ha. exists (F (gfp F)).
  split; auto.
  apply is_mono.
  now apply gfp_unfold.
Qed.

Theorem fixpoint_coinduction (F : (A -> Prop) -> (A -> Prop)) `{Mono F}:
  forall (P : A -> Prop),
    P <= F P ->
    forall a, P a -> gfp F a.
Proof.
  intros P HP a Ha.
  now exists P.
Qed.

Theorem gfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    gfp F1 <= gfp F2.
Proof.
  intros F1 F2 H a (X & Hle & Ha).
  exists X. split; auto.
  now transitivity (F1 X).
Qed.

Theorem lfp_le_gfp F `{Mono F}:
  lfp F <= gfp F.
Proof.
  intros a Ha.
  exists (lfp F).
  split; auto.
  now apply lfp_unfold.
Qed.

End Fix1.