From Stdlib Require Import RelationClasses.

Declare Scope fixit.
Delimit Scope fixit with fixit.
Open Scope fixit.

(** * Ternary Inductive and Coinductive Predicates *)

Section Fix3.

Variable A B C : Prop.

(** ** Definitions *)

Definition le (X Y : A -> B -> C -> Prop) : Prop :=
  forall a b c, X a b c -> Y a b c.

Definition union (X Y : A -> B -> C -> Prop) (a : A) (b : B) (c : C) : Prop :=
  X a b c \/ Y a b c.

Definition inter (X Y : A -> B -> C -> Prop) (a : A) (b : B) (c : C) : Prop :=
  X a b c /\ Y a b c.

Definition opp (X : A -> B -> C -> Prop) (a : A) (b : B) (c : C) : Prop :=
  ~X a b c.

Definition mono (F : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop)) : Prop :=
  forall (X Y : A -> B -> C -> Prop), le X Y -> le (F X) (F Y).

Definition lfp (F : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop)) (a : A) (b : B) (c : C) :=
  forall X, le (F X) X -> X a b c.

Definition gfp (F : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop)) (a : A) (b : B) (c : C) :=
  exists X, le X (F X) /\ X a b c.

(** ** Notations **)

Infix "<=" := le : fixit.
Infix "/\" := union : fixit.
Infix "\/" := inter : fixit.

(** ** Typeclasses *)

Instance le_trans:
  Transitive le.
Proof.
  intros X Y Z H1 H2 a b c Habc.
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
  intros a b c Habc X HX.
  apply HX.
  eapply is_mono; cycle 1.
  apply Habc.
  intros d e f Hdef.
  apply (Hdef X), HX.
Qed.

Theorem lfp_unfold F `{Mono F}:
  lfp F <= F (lfp F).
Proof.
  intros a b c Habc.
  apply (Habc (F (lfp F))), is_mono.
  apply lfp_fold, is_mono.
Qed.

Theorem fixpoint_induction F `{Mono F}:
  forall (P : A -> B -> C -> Prop),
    F P <= P ->
    forall a b c, lfp F a b c -> P a b c.
Proof.
  intros P HP a b c Habc.
  apply (Habc P), HP.
Qed.

Theorem lfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    lfp F1 <= lfp F2.
Proof.
  intros F1 F2 H a b c Habc X HX.
  apply (Habc X).
  now transitivity (F2 X).
Qed.

Theorem gfp_unfold F `{Mono F}:
  gfp F <= F (gfp F).
Proof.
  intros a b c (X & Hle & Habc).
  eapply is_mono; cycle 1.
  apply Hle, Habc.
  transitivity (F X); auto.
  intros d e f Hdef. exists (F X).
  split; auto.
Qed.

Theorem gfp_fold F `{Mono F}:
  F (gfp F) <= gfp F.
Proof.
  intros a b c Habc. exists (F (gfp F)).
  split; auto.
  apply is_mono.
  now apply gfp_unfold.
Qed.

Theorem fixpoint_coinduction F `{Mono F}:
  forall (P : A -> B -> C -> Prop),
    P <= F P ->
    forall a b c, P a b c -> gfp F a b c.
Proof.
  intros P HP a b c Habc.
  now exists P.
Qed.

Theorem gfp_mono:
  forall F1 F2,
    (forall X, F1 X <= F2 X) ->
    gfp F1 <= gfp F2.
Proof.
  intros F1 F2 H a b c (X & Hle & Habc).
  exists X. split; auto.
  now transitivity (F1 X).
Qed.

Theorem lfp_le_gfp F `{Mono F}:
  lfp F <= gfp F.
Proof.
  intros a b c Habc.
  exists (lfp F).
  split; auto.
  now apply lfp_unfold.
Qed.

Theorem opp_lfp F `{Mono F}:
  gfp (fun X => opp (F (opp X))) <= opp (lfp F).
Proof.
  intros a b c (X & HX & Habc) Hcontr.
  apply (Hcontr (opp X)); auto.
  intros d e f Hdef Hcontr'.
  eapply HX; eauto.
Qed.

Theorem opp_gfp F `{Mono F}:
  lfp (fun X => opp (F (opp X))) <= opp (gfp F).
Proof.
  intros a b c Hcontr (X & HX & Habc).
  apply (Hcontr (opp X)); auto.
  intros d e f Hdef Hcontr'.
  specialize (HX d e f Hcontr').
  apply Hdef.
  apply (is_mono X); auto.
  intros g h i Hghi Hghi'.
  now apply Hghi'.
Qed.

End Fix3.