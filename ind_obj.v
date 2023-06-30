(*
 * Proofs about indistinguishable objectives in
 * multiplayer non zero-sum games
 *)

Require Import Sets.Ensembles.

Section PreliminariesOnEnsembles.

Variable U : Type.

Infix "∩" := (Intersection U)  (at level 40, left associativity).
Infix "∪" := (Union U)         (at level 50, left associativity).
Infix "⊆" := (Included U)      (at level 55, no associativity).
Notation "x ∈ S" := (In U S x) (at level 55, no associativity).
Notation "¬ x" := (Complement U x) (at level 35).

Lemma subset_of_each_is_subset_of_intersection :
  forall A B C,
  C ⊆ A /\ C ⊆ B <-> C ⊆ A ∩ B.
Proof.
  intros A B C.
  split.
  - (* -> *)
  unfold Included;
  intros [H1 H2] x Cx.
  specialize (H1 x Cx).
  specialize (H2 x Cx).
  now apply Intersection_intro.
  - (* <- *)
  unfold Included;
  intros H.
  split;
  intros x Cx;
  specialize (H x Cx);
  destruct H as [x H1 H2];
  assumption.
Qed.

(* We assume here that whether x ∈ A or not is decidable for every A and x. *)
Axiom In_dec :
  forall (A : Ensemble U) x, {x ∈ A} + {x ∈ ¬ A}.

End PreliminariesOnEnsembles.

Section IntersectionForall.

(* ∩_{x ∈ P} S(x) *)
Inductive IntersectionForall {X Y : Type}
  (P : Ensemble X) (S : X -> Ensemble Y) : Ensemble Y :=
| IntersectionForall_intro :
    forall y, (forall x, In _ P x -> In _ (S x) y) ->
      In _ (IntersectionForall P S) y.

Lemma IntersectionForall_split :
  forall X Y (P : Ensemble X) (S : X -> Ensemble Y) P1 P2,
  P = Union _ P1 P2 ->
  IntersectionForall P S
    = Intersection _ (IntersectionForall P1 S) (IntersectionForall P2 S).
Proof.
  intros X Y P S P1 P2 Hp.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros y Hy.
  - (* ⊆ *)
  rewrite Hp in Hy.
  destruct Hy as [y Hy].
  apply Intersection_intro.
  + (* to show y ∈ IntersectionForall P1 S *)
    apply IntersectionForall_intro.
    intros x Hx.
    apply Union_introl with (C:=P2) in Hx.
    apply (Hy x Hx).
  + (* to show y ∈ IntersectionForall P2 S *)
    apply IntersectionForall_intro.
    intros x Hx.
    apply Union_intror with (B:=P1) in Hx.
    apply (Hy x Hx).
  - (* ⊇ *)
  destruct Hy as [y Hy1 Hy2].
  destruct Hy1 as [y Hy1].
  destruct Hy2 as [y Hy2].
  apply IntersectionForall_intro.
  rewrite Hp.
  intros x Hx.
  destruct Hx as [x Hx | x Hx];
  [apply Hy1 | apply Hy2];
  assumption.
Qed.

End IntersectionForall.

Section IndistinguishableObjectives.

Variable Play : Type.
Let U := Play.

Infix "∩" := (Intersection U)  (at level 40, left associativity).
Infix "∪" := (Union U)         (at level 50, left associativity).
Infix "⊆" := (Included U)      (at level 55, no associativity).
Notation "x ∈ S" := (In U S x) (at level 55, no associativity).
Notation "¬ x" := (Complement U x) (at level 35).
Notation "∅" := (Empty_set U).

Definition Omega := Ensemble Play.
Variable winnablep : Ensemble Omega.

Infix ".∩" := (Intersection Omega)  (at level 40, left associativity).
Infix ".∪" := (Union Omega)         (at level 50, left associativity).
Infix ".⊆" := (Included Omega)      (at level 55, no associativity).
Notation "x .∈ S" := (In Omega S x) (at level 55, no associativity).
Notation ".¬ x" := (Complement Omega x) (at level 35).

(* Original definitions of the Obj's *)
Inductive ObjPW' (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPW'_intro : forall O,
  (rho ∈ O /\ rho ∈ Op) \/ (rho ∈ ¬ O /\ rho ∈ ¬ Op)
  -> O .∈ ObjPW' Op rho.

Inductive ObjGW' (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjGW'_intro : forall O,
  (rho ∈ Op /\ O <> ∅) \/ (rho ∈ ¬ Op /\ O .∈ .¬ winnablep)
  -> O .∈ ObjGW' Op rho.

Inductive ObjPG' (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPG'_intro : forall O,
  (rho ∈ O /\ O <> ∅) \/ (rho ∈ ¬ O /\ O .∈ .¬ winnablep)
  -> O .∈ ObjPG' Op rho.

Inductive ObjPGW' (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPGW'_intro : forall O,
  (rho ∈ O /\ rho ∈ Op /\ O <> ∅) \/
  (rho ∈ ¬ O /\ rho ∈ ¬ Op /\ O .∈ .¬ winnablep)
  -> O .∈ ObjPGW' Op rho.

(* Definitions of the Obj's *)
Inductive ObjPW (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPW_intro : forall O,
  rho ∈ (O ∩ Op) ∪ (¬ O ∩ ¬ Op) -> O .∈ ObjPW Op rho.

Inductive ObjGW (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjGW_intro : forall O,
  (O .∈ winnablep -> rho ∈ Op) /\
  (O = ∅ -> rho ∈ ¬ Op) -> O .∈ ObjGW Op rho.

Inductive ObjPG (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPG_intro : forall O,
  (O .∈ winnablep -> rho ∈ O) -> O .∈ ObjPG Op rho.

Inductive ObjPGW (Op : Omega) (rho : Play) : Ensemble Omega :=
| ObjPGW_intro : forall O,
  rho ∈ (O ∩ Op) ∪ (¬ O ∩ ¬ Op) /\
  (O .∈ winnablep -> rho ∈ O ∩ Op) -> O .∈ ObjPGW Op rho.

(*
 * Showing the original and the simplified
 * definitions are the same.
 *)
Theorem ObjPW_eq_ObjPW' :
  forall Op rho,
  ObjPW Op rho = ObjPW' Op rho.
Proof.
  intros Op rho.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In.
  split;
  intros O H.
  - (* ⊆ *)
  apply ObjPW'_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [rho H | rho H].
  + (* when rho ∈ O ∩ Op *)
  destruct H as [rho H1 H2].
  left; split; assumption.
  + (* when rho ∈ ¬ O ∩ ¬ Op *)
  destruct H as [rho H1 H2].
  right; split; assumption.
  - (* ⊇ *)
  apply ObjPW_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H | H].
  + (* when rho ∈ O /\ rho ∈ Op *)
  destruct H as [H1 H2].
  apply Union_introl.
  now apply Intersection_intro.
  + (* when rho ∈ ¬ O /\ rho ∈ ¬ Op *)
  destruct H as [H1 H2].
  apply Union_intror.
  now apply Intersection_intro.
Qed.

Theorem ObjGW_eq_ObjGW' :
  forall Op rho,
  ObjGW Op rho = ObjGW' Op rho.
Proof.
  intros Op rho.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In.
  split;
  intros O H.
  - (* ⊆ *)
  apply ObjGW'_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H1 H2].
  destruct (In_dec _ Op rho) as [Hop | Hop].
  + (* when rho ∈ Op *)
  left. split; [assumption |].
  intros Hemp.
  apply H2 in Hemp.
  now apply Hemp in Hop.
  + (* when rho ∈ ¬ Op *)
  right. split; [assumption |].
  intros Hwin.
  apply Hop.
  now apply H1.
  - (* ⊇ *)
  apply ObjGW_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H | H].
  + (* when rho ∈ Op /\ O <> ∅ *)
  destruct H as [H1 H2].
  split; intros Ho; [assumption |].
  now apply H2 in Ho.
  + (* when rho ∈ ¬ Op /\ O .∈ .¬ winnablep *)
  destruct H as [H1 H2].
  split; intros Ho; [| assumption].
  now apply H2 in Ho.
Qed.

Theorem ObjPG_eq_ObjPG' :
  forall Op rho,
  ObjPG Op rho = ObjPG' Op rho.
Proof.
  intros Op rho.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In.
  split;
  intros O H.
  - (* ⊆ *)
  apply ObjPG'_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct (In_dec _ O rho) as [Ho | Ho].
  + (* when rho ∈ O *)
  left. split; [assumption |].
  intros Hemp.
  rewrite Hemp in Ho.
  inversion Ho.
  + (* when rho ∈ ¬ O *)
  right. split; [assumption |].
  intros Hwin.
  apply H' in Hwin.
  now apply Ho in Hwin.
  - (* ⊇ *)
  apply ObjPG_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H | H].
  + (* when rho ∈ O /\ O <> ∅ *)
  destruct H as [H1 H2].
  now intros Hwin.
  + (* when rho ∈ ¬ O /\ O .∈ .¬ winnablep *)
  destruct H as [H1 H2].
  intros Hwin.
  now apply H2 in Hwin.
Qed.

Theorem ObjPGW_eq_ObjPGW' :
  forall Op rho,
  ObjPGW Op rho = ObjPGW' Op rho.
Proof.
  intros Op rho.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In.
  split;
  intros O H.
  - (* ⊆ *)
  apply ObjPGW'_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H1 H2].
  destruct H1 as [rho Hop | rho Hop].
  + (* when rho ∈ O ∩ Op *)
  destruct Hop as [rho Ho Hop].
  left. split; [| split]; try assumption.
  intros Hemp.
  rewrite Hemp in Ho.
  inversion Ho.
  + (* when rho ∈ ¬ O ∩ ¬ Op *)
  destruct Hop as [rho Ho Hop].
  right. split; [| split]; try assumption.
  intros Hwin.
  apply H2 in Hwin.
  destruct Hwin as [rho Hwin _].
  now apply Ho in Hwin.
  - (* ⊇ *)
  apply ObjPGW_intro.
  inversion H as [O' H' EQO'];
  clear O' EQO' H.
  destruct H' as [H | H].
  + (* when rho ∈ O /\ rho ∈ Op /\ O <> ∅ *)
  destruct H as [H1 [H2 H3]].
  split.
  * (* to show rho ∈ O ∩ Op ∪ ¬ O ∩ ¬ Op *)
  apply Union_introl.
  now apply Intersection_intro.
  * (* to show O .∈ winnablep -> rho ∈ O ∩ Op *)
  intros Hwin.
  now apply Intersection_intro.
  + (* when rho ∈ ¬ O /\ rho ∈ ¬ Op /\ O .∈ .¬ winnablep *)
  destruct H as [H1 [H2 H3]].
  split.
  * (* to show rho ∈ O ∩ Op ∪ ¬ O ∩ ¬ Op *)
  apply Union_intror.
  now apply Intersection_intro.
  * (* to show O .∈ winnablep -> rho ∈ O ∩ Op *)
  intros Hwin.
  now apply H3 in Hwin.
Qed.

(*
 * Showing ObjPGW Op rho =
 * (ObjPW Op rho) .∩ (ObjGW Op rho) .∩ (ObjPG Op rho).
 *)

Lemma included_ObjPGW_ObjPW :
  forall Op rho,
  ObjPGW Op rho .⊆ ObjPW Op rho.
Proof.
  intros Op rho.
  unfold Included, In.
  intros O H.
  destruct H as [O [H1 H2]].
  apply ObjPW_intro.
  apply H1.
Qed.

Lemma included_ObjPGW_ObjGW :
  forall Op rho,
  ObjPGW Op rho .⊆ ObjGW Op rho.
Proof.
  intros Op rho.
  unfold Included, In.
  intros O H.
  destruct H as [O [H1 H2]].
  apply ObjGW_intro.
  split.
  - intros Ho.
  specialize (H2 Ho).
  destruct H2 as [x H2 H2'].
  apply H2'.
  - intros Hemp.
  destruct H1 as [rho H1 | rho H1].
  + destruct H1 as [rho H1 _].
  rewrite Hemp in H1. inversion H1.
  + now destruct H1 as [rho _ H1].
Qed.

Lemma included_ObjPGW_ObjPG :
  forall Op rho,
  ObjPGW Op rho .⊆ ObjPG Op rho.
Proof.
  intros Op rho.
  unfold Included, In.
  intros O H.
  destruct H as [O [H1 H2]].
  apply ObjPG_intro.
  intros Ho.
  specialize (H2 Ho).
  destruct H2 as [x H2 H2'].
  apply H2.
Qed.

Lemma included_ObjPGW_others :
  forall Op rho,
  ObjPGW Op rho .⊆ (ObjPW Op rho) .∩ (ObjGW Op rho) .∩ (ObjPG Op rho).
Proof.
  intros Op rho.
  apply subset_of_each_is_subset_of_intersection; split;
  [apply subset_of_each_is_subset_of_intersection |]; [split |];
  [apply included_ObjPGW_ObjPW |
   apply included_ObjPGW_ObjGW |
   apply included_ObjPGW_ObjPG].
Qed.

Lemma included_others_ObjPGW :
  forall Op rho,
  (ObjPW Op rho) .∩ (ObjGW Op rho) .∩ (ObjPG Op rho)
  .⊆ ObjPGW Op rho.
Proof.
  intros Op rho.
  unfold Included.
  intros x Hx.
  destruct Hx as [y [x Hxpw Hxgw] Hxpg].
  destruct Hxpw as [O Hpw].
  destruct Hxgw as [O Hgw].
  destruct Hxpg as [O Hpg].
  apply ObjPGW_intro.
  split.
  - (* to show rho ∈ O ∩ Op ∪ ¬ O ∩ ¬ Op *)
  destruct Hpw as [rho Hpw | rho Hpw];
  [apply Union_introl | apply Union_intror]; assumption.
  - (* to show O .∈ winnablep -> rho ∈ O ∩ Op *)
  intros Hw.
  destruct Hgw as [Hgw _].
  specialize (Hgw Hw).
  specialize (Hpg Hw).
  now apply Intersection_intro.
Qed.

Theorem ObjPGW_equals_intersection_of_others :
  forall Op rho,
  ObjPGW Op rho =
  (ObjPW Op rho) .∩ (ObjGW Op rho) .∩ (ObjPG Op rho).
Proof.
  intros Op rho.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - apply included_ObjPGW_others.
  - apply included_others_ObjPGW.
Qed.


(* The intersections of Obj's for all plays in outp(sigmap) *)
Variable outp_sigmap : Ensemble Play.
Definition ObjPWa (Op : Omega) : Ensemble Omega :=
  IntersectionForall outp_sigmap (ObjPW Op).
Definition ObjGWa (Op : Omega) : Ensemble Omega :=
  IntersectionForall outp_sigmap (ObjGW Op).
Definition ObjPGa (Op : Omega) : Ensemble Omega :=
  IntersectionForall outp_sigmap (ObjPG Op).
Definition ObjPGWa (Op : Omega) : Ensemble Omega :=
  IntersectionForall outp_sigmap (ObjPGW Op).

(*
 * Showing the equivalence between calO-indistinguishability and
 * the existence of a winning strategy
 *)

Theorem characterization_of_indistinguishable_strategy_PW :
  forall Op calO,
  calO .⊆ ObjPWa Op <->
  outp_sigmap ⊆
    IntersectionForall calO (fun O => (O ∩ Op) ∪ (¬ O ∩ ¬ Op)).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros Hobj.
  unfold ObjPWa, Included in Hobj.
  unfold Included.
  intros rho Hrho.
  apply IntersectionForall_intro;
  intros O Ho.
  (* to show rho ∈ IntersectionForall calO
       (fun O : Omega => O ∩ Op ∪ ¬ O ∩ ¬ Op) *)
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O Hobj].
  apply Hobj.
  - (* <- *)
  unfold Included.
  intros Hout O Ho.
  unfold ObjPWa.
  apply IntersectionForall_intro.
  intros rho Hrho.
  specialize (Hout rho Hrho).
  apply ObjPW_intro.
  destruct Hout as [rho Ho1].
  apply (Ho1 O Ho).
Qed.

Theorem characterization_of_indistinguishable_strategy_GW :
  forall Op calO,
  calO .⊆ ObjGWa Op <->
  outp_sigmap ⊆
    IntersectionForall (calO .∩ (Singleton _ ∅))
                       (fun O => ¬ Op)
      ∩ IntersectionForall (calO .∩ winnablep) (fun O => Op).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros Hobj.
  unfold ObjGWa, Included in Hobj.
  unfold Included.
  intros rho Hrho.
  apply Intersection_intro.
  + (* to show outp_sigmap ⊆
       IntersectionForall (calO .∩ (Singleton _ ∅))
                          (fun O => ¬ Op) *)
  apply IntersectionForall_intro;
  intros O Ho.
  destruct Ho as [O Ho Ho1].
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O Hobj].
  destruct Hobj as [Hobj1 Hobj2].
  apply Hobj2.
  destruct Ho1.
  reflexivity.
  + (* to show outp_sigmap ⊆
       IntersectionForall (calO .∩ winnablep) (fun O => Op) *)
  apply IntersectionForall_intro;
  intros O Ho.
  destruct Ho as [O Ho Ho1].
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O Hobj].
  destruct Hobj as [Hobj _].
  apply (Hobj Ho1).
  - (* <- *)
  unfold Included.
  intros Hout O Ho.
  unfold ObjGWa.
  apply IntersectionForall_intro.
  intros rho Hrho.
  specialize (Hout rho Hrho).
  apply ObjGW_intro.
  destruct Hout as [rho Ho1 Ho2].
  split.
  + (* to show O .∈ winnablep -> rho ∈ Op *)
  intros Hw.
  destruct Ho2 as [rho Ho2].
  apply (Ho2 O (Intersection_intro _ _ _ _ Ho Hw)).
  + (* to show O = ∅ -> rho ∈ ¬ Op *)
  intros He.
  destruct Ho1 as [rho Ho1].
  apply (Ho1 O).
  apply Intersection_intro; [assumption |].
  rewrite He.
  apply In_singleton.
Qed.

Theorem characterization_of_indistinguishable_strategy_PG :
  forall Op calO,
  calO .⊆ ObjPGa Op <->
  outp_sigmap ⊆
    IntersectionForall (calO .∩ winnablep) (fun O => O).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros Hobj.
  unfold ObjPGa, Included in Hobj.
  unfold Included.
  intros rho Hrho.
  apply IntersectionForall_intro;
  intros O Ho.
  destruct Ho as [O Ho Ho1].
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O Hobj].
  apply (Hobj Ho1).
  - (* <- *)
  unfold Included.
  intros Hout O Ho.
  unfold ObjPGa.
  apply IntersectionForall_intro.
  intros rho Hrho.
  specialize (Hout rho Hrho).
  apply ObjPG_intro.
  intros Hw.
  destruct Hout as [rho Ho1].
  apply (Ho1 O (Intersection_intro _ _ _ _ Ho Hw)).
Qed.

Theorem characterization_of_indistinguishable_strategy_PGW :
  forall Op calO,
  calO .⊆ ObjPGWa Op <->
  outp_sigmap ⊆
    IntersectionForall calO (fun O => (O ∩ Op) ∪ (¬ O ∩ ¬ Op))
      ∩ IntersectionForall (calO .∩ winnablep) (fun O => O ∩ Op).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros Hobj.
  unfold ObjPGWa, Included in Hobj.
  unfold Included.
  intros rho Hrho.
  destruct (In_dec _ Op rho) as [Hop | Hop].
  + (* when rho ∈ Op *)
  apply Intersection_intro;
  apply IntersectionForall_intro;
  intros O Ho.
  * (* to show rho ∈ IntersectionForall calO
       (fun O : Omega => O ∩ Op ∪ ¬ O ∩ ¬ Op) *)
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O [Hobj _]].
  apply Hobj.
  * (* to show rho ∈ IntersectionForall (calO .∩ winnablep)
       (fun O : Omega => O ∩ Op) *)
  destruct Ho as [O Ho Ho1].
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O [_ Hobj]].
  apply (Hobj Ho1).
  + (* when rho ∈ ¬ Op *)
  apply Intersection_intro;
  apply IntersectionForall_intro;
  intros O Ho.
  * (* to show rho ∈ IntersectionForall calO
       (fun O : Omega => O ∩ Op ∪ ¬ O ∩ ¬ Op) *)
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O [Hobj _]].
  apply Hobj.
  * (* to show rho ∈ IntersectionForall (calO .∩ winnablep)
       (fun O : Omega => O ∩ Op) *)
  destruct Ho as [O Ho Ho1].
  specialize (Hobj O Ho).
  destruct Hobj as [O Hobj].
  specialize (Hobj rho Hrho).
  destruct Hobj as [O [_ Hobj]].
  apply (Hobj Ho1).
  - (* <- *)
  unfold Included.
  intros Hout O Ho.
  unfold ObjPGWa.
  apply IntersectionForall_intro.
  intros rho Hrho.
  specialize (Hout rho Hrho).
  apply ObjPGW_intro.
  destruct Hout as [rho Ho1 Ho2].
  destruct Ho1 as [rho Ho1].
  destruct Ho2 as [rho Ho2].
  specialize (Ho1 O Ho).
  split; [apply Ho1 |].
  intros Hw.
  apply Ho2.
  now apply Intersection_intro.
Qed.


Theorem characterization_of_winning_IS_PGW :
  forall Op calO,
  calO .⊆ ObjPGWa Op /\ outp_sigmap ⊆ Op <->
  outp_sigmap ⊆ Op ∩
    IntersectionForall calO (fun O => O).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros [His Hwin].
  apply characterization_of_indistinguishable_strategy_PGW in His.
  unfold Included.
  unfold Included in His.
  unfold Included in Hwin.
  intros x Hx.
  specialize (His x Hx).
  specialize (Hwin x Hx).
  apply Intersection_intro; [assumption |].
  apply IntersectionForall_intro.
  intros O Ho.
  destruct His as [x His _].
  destruct His as [x His].
  specialize (His O Ho).
  destruct His as [x His | x His].
  + (* when x ∈ O ∩ Op *)
  now destruct His as [x His _].
  + (* when x ∈ ¬ O ∩ ¬ Op *)
  destruct His as [x _ His].
  now apply His in Hwin.
  - (* <- *)
  intros Hinc.
  unfold Included in Hinc.
  split.
  + (* to show calO .⊆ ObjPGWa Op *)
  apply characterization_of_indistinguishable_strategy_PGW.
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  destruct Hinc as [x Hxop Hxo].
  destruct Hxo as [x Hxo].
  apply Intersection_intro;
  apply IntersectionForall_intro;
  intros O Ho;
  [apply Union_introl | destruct Ho as [O Ho _]];
  specialize (Hxo O Ho);
  now apply Intersection_intro.
  + (* to show outp_sigmap ⊆ Op *)
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  now destruct Hinc as [x Hxop _].
Qed.

Theorem characterization_of_winning_IS_PW :
  forall Op calO,
  calO .⊆ ObjPWa Op /\ outp_sigmap ⊆ Op <->
  outp_sigmap ⊆ Op ∩
    IntersectionForall calO (fun O => O).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros [His Hwin].
  apply characterization_of_indistinguishable_strategy_PW in His.
  unfold Included.
  unfold Included in His.
  unfold Included in Hwin.
  intros x Hx.
  specialize (His x Hx).
  specialize (Hwin x Hx).
  apply Intersection_intro; [assumption |].
  apply IntersectionForall_intro.
  intros O Ho.
  destruct His as [x His].
  specialize (His O Ho).
  destruct His as [x His | x His].
  + (* when x ∈ O ∩ Op *)
  now destruct His as [x His _].
  + (* when x ∈ ¬ O ∩ ¬ Op *)
  destruct His as [x _ His].
  now apply His in Hwin.
  - (* <- *)
  intros Hinc.
  unfold Included in Hinc.
  split.
  + (* to show calO .⊆ ObjPWa Op *)
  apply characterization_of_indistinguishable_strategy_PW.
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  destruct Hinc as [x Hxop Hxo].
  destruct Hxo as [x Hxo].
  apply IntersectionForall_intro.
  intros O Ho.
  apply Union_introl.
  specialize (Hxo O Ho).
  now apply Intersection_intro.
  + (* to show outp_sigmap ⊆ Op *)
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  now destruct Hinc as [x Hxop _].
Qed.

Theorem characterization_of_winning_IS_GW :
  forall Op calO,
  calO .⊆ ObjGWa Op /\ outp_sigmap ⊆ Op <->
  outp_sigmap ⊆ Op
    ∩ IntersectionForall (calO .∩ Singleton _ ∅)
                         (fun O => ¬ Op).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros [His Hwin].
  apply subset_of_each_is_subset_of_intersection.
  split; [assumption |].
  unfold Included.
  intros rho Hrho.
  apply IntersectionForall_intro.
  intros O Ho.
  destruct Ho as [O Ho1 Ho2].
  inversion Ho2 as [EQO];
  clear Ho2.
  unfold Included in His.
  specialize (His O Ho1).
  inversion His as [O' His' EQO'];
  clear O' EQO' His.
  specialize (His' rho Hrho).
  inversion His' as [O' His EQO'];
  clear O' EQO'.
  destruct His as [His1 His2].
  apply His2.
  rewrite EQO.
  reflexivity.
  - (* <- *)
  intros Hinc.
  apply subset_of_each_is_subset_of_intersection in Hinc.
  destruct Hinc as [Hinc1 Hinc2].
  split; [| assumption].
  apply characterization_of_indistinguishable_strategy_GW.
  apply subset_of_each_is_subset_of_intersection.
  unfold Included.
  unfold Included in Hinc1.
  unfold Included in Hinc2.
  split;
  intros rho Hrho;
  [specialize (Hinc2 rho Hrho) |
   specialize (Hinc1 rho Hrho)]; try assumption.
  apply IntersectionForall_intro.
  now intros O Ho.
Qed.

Theorem characterization_of_winning_IS_PG :
  forall Op calO,
  calO .⊆ ObjPGa Op /\ outp_sigmap ⊆ Op <->
  outp_sigmap ⊆ Op ∩
    IntersectionForall (calO .∩ winnablep) (fun O => O).
Proof.
  intros Op calO.
  split.
  - (* -> *)
  intros [His Hwin].
  apply characterization_of_indistinguishable_strategy_PG in His.
  unfold Included.
  unfold Included in His.
  unfold Included in Hwin.
  intros x Hx.
  specialize (His x Hx).
  specialize (Hwin x Hx).
  apply Intersection_intro; assumption.
  - (* <- *)
  intros Hinc.
  unfold Included in Hinc.
  split.
  + (* to show calO .⊆ ObjPGa Op *)
  apply characterization_of_indistinguishable_strategy_PG.
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  destruct Hinc as [x Hxop Hxo].
  apply Hxo.
  + (* to show outp_sigmap ⊆ Op *)
  unfold Included.
  intros x Hx.
  specialize (Hinc x Hx).
  now destruct Hinc as [x Hxop _].
Qed.

End IndistinguishableObjectives.

