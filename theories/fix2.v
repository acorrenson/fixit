From Stdlib Require Import RelationClasses.

Declare Scope fixit.
Delimit Scope fixit with fixit.
Open Scope fixit.

(** * Binary Inductive and Coinductive Predicates *)

Section Fix2.

Variable A B : Prop.

(** ** Definitions *)

Definition le (X Y : A -> B -> Prop) : Prop :=
  forall a b, X a b -> Y a b.

Definition union (X Y : A -> B -> Prop) (a : A) (b : B) : Prop :=
  X a b \/ Y a b.

Definition inter (X Y : A -> B -> Prop) (a : A) (b : B) : Prop :=
  X a b /\ Y a b.

Definition mono (F : (A -> B -> Prop) -> (A -> B -> Prop)) : Prop :=
  forall (X Y : A -> B -> Prop), le X Y -> le (F X) (F Y).

Definition lfp (F : (A -> B -> Prop) -> (A -> B -> Prop)) (a : A) (b : B) :=
  forall X, le (F X) X -> X a b.

Definition gfp (F : (A -> B -> Prop) -> (A -> B -> Prop)) (a : A) (b : B) :=
  exists X, le X (F X) /\ X a b.

(** ** Notations **)

Infix "<=" := le : fixit.
Infix "/\" := union : fixit.
Infix "\/" := inter : fixit.

(** ** Typeclasses *)

Instance le_trans:
  Transitive le.
Proof.
  intros X Y Z H1 H2 a b Hab.
  now apply H2, H1.
Qed.

Instance le_refl:
  Reflexive le.
Proof.
  easy.
Qed.

Class Mono F : Prop :=
  is_mono : mono F.

(** ** Facts *)

Theorem lfp_fold F `{Mono F}:
  F (lfp F) <= lfp F.
Proof.
  intros a b Hab X HX.
  apply HX.
  eapply is_mono; cycle 1.
  apply Hab.
  intros c d Hcd.
  apply (Hcd X), HX.
Qed.

Theorem lfp_unfold F `{Mono F}:
  lfp F <= F (lfp F).
Proof.
  intros a b Hab.
  apply (Hab (F (lfp F))), is_mono.
  apply lfp_fold, is_mono.
Qed.

Theorem fixpoint_induction F `{Mono F}:
  forall (P : A -> B -> Prop),
    F P <= P ->
    forall a b, lfp F a b -> P a b.
Proof.
  intros P HP a b Hab.
  apply (Hab P), HP.
Qed.

Theorem lfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    lfp F1 <= lfp F2.
Proof.
  intros F1 F2 H a b Hab X HX.
  apply (Hab X).
  now transitivity (F2 X).
Qed.

Theorem gfp_unfold F `{Mono F}:
  gfp F <= F (gfp F).
Proof.
  intros a b (X & Hle & Hab).
  eapply is_mono; cycle 1.
  apply Hle, Hab.
  transitivity (F X); auto.
  intros c d Hcd. exists (F X).
  split; auto.
Qed.

Theorem gfp_fold F `{Mono F}:
  F (gfp F) <= gfp F.
Proof.
  intros a b Hab. exists (F (gfp F)).
  split; auto.
  apply is_mono.
  now apply gfp_unfold.
Qed.

Theorem fixpoint_coinduction F `{Mono F}:
  forall (P : A -> B -> Prop),
    P <= F P ->
    forall a b, P a b -> gfp F a b.
Proof.
  intros P HP a b Hab.
  now exists P.
Qed.

Theorem gfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    gfp F1 <= gfp F2.
Proof.
  intros F1 F2 H a b (X & Hle & Hab).
  exists X. split; auto.
  now transitivity (F1 X).
Qed.

Theorem lfp_le_gfp F `{Mono F}:
  lfp F <= gfp F.
Proof.
  intros a b Hab.
  exists (lfp F).
  split; auto.
  now apply lfp_unfold.
Qed.

End Fix2.