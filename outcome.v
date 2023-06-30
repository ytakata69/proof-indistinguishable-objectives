(*
 * Proofs about indistinguishable objectives in
 * multiplayer non zero-sum games
 *)

Require Import Lists.List.
Require Import Sets.Ensembles.
Require Import Arith.
Require Import ind_obj.

Section Outcome.

(* To show the relationship between out and out^p *)

Definition P := nat. (* the set of players *)
Parameter V : Set. (* the set of vertices *)
Parameter v0 : V.
Parameter player : V -> P. (* the controller of a vertex *)

(* the set of all players *)
Inductive allP : Ensemble P :=
  allP_intro : forall p : P, In _ allP p.

(*
 * A strategy is a function from history to vertex.
 * In this proof script, a history given to a strategy is reversed;
 * the current vertex is the head of the history.
 *)
Definition SigmaP := list V -> V.
Definition Sigma := P -> SigmaP.

(* A play is a function from length to a list of V *)
Definition Play := nat -> list V.
Axiom extensionality_Play :
  forall rho rho' : Play,
  (forall i, rho i = rho' i) -> rho = rho'.

Fixpoint out (sigma : Sigma) (i : nat) : list V :=
  match i with
  | 0 => v0 :: nil
  | S i' => let l := out sigma i' in
            sigma (player (hd v0 l)) l :: l
  end.

Inductive outp : P -> SigmaP -> Ensemble Play :=
  | outp_intro : forall p sigmap rho,
    rho 0 = v0 :: nil ->
    (forall i h l, (h :: l) = rho i -> p = player h ->
       (sigmap (h :: l)) :: h :: l = rho (S i)) ->
    In _ (outp p sigmap) rho
  .

Lemma out_is_not_nil :
  forall sigma i, out sigma i <> nil.
Proof.
  intros sigma.
  destruct i as [| i]; simpl.
  - intros H; inversion H.
  - intros H; inversion H.
Qed.

Lemma destruct_out :
  forall sigma i, exists h l, h :: l = out sigma i.
Proof.
  intros sigma i.
  destruct (destruct_list (out sigma i)) as [Hrho | Hrho].
  - destruct Hrho as [h [l Hl]].
    exists h, l. now symmetry.
  - now apply out_is_not_nil in Hrho.
Qed.

Theorem out_equals_intersection_of_outp :
  forall sigma : Sigma,
  Singleton _ (out sigma) =
    IntersectionForall allP (fun p => outp p (sigma p)).
Proof.
  intros sigma.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
  - (* ⊆ *)
  intros x Hx.
  unfold In in Hx.
  inversion Hx as [Hx'];
  clear Hx x Hx'.
  apply IntersectionForall_intro.
  intros p Hallp.
  apply outp_intro;
  [reflexivity |].

  destruct i as [| i].
  + (* when i = 0 *)
  simpl.
  intros h l EQhl EQp.
  injection EQhl; intros EQl EQh.
  rewrite EQp, EQl, EQh.
  reflexivity.
  + (* when i > 0 *)
  intros h l EQhl EQp.
  simpl in EQhl.
  injection EQhl; intros EQl EQh.
  simpl.
  rewrite EQp, EQl, EQh.
  reflexivity.

  - (* ⊇ *)
  intros rho Hrho.
  inversion Hrho as [rho' Hrho' EQrho'];
  clear rho' EQrho' Hrho.
  assert (Hrho : rho = out sigma).
  + (* to show rho = out sigma *)
  apply extensionality_Play.
  induction i as [| i IH].
  * (* when i = 0 *)
  assert (Hp0 : In _ allP (player v0)).
  { apply allP_intro. }
  specialize (Hrho' (player v0) Hp0).
  inversion Hrho' as [p' sigmap rho' Hrho0 Hrho EQp' EQsigmap EQrho'];
  clear p' EQp' sigmap EQsigmap rho' EQrho'.
  now simpl.
  * (* when i > 0 *)
  destruct (destruct_out sigma i) as [h [l Hhl]].
  remember (player h) as p eqn:EQp.
  assert (Hp : In _ allP p).
  { apply allP_intro. }
  specialize (Hrho' p Hp).
  inversion Hrho' as [p' sigmap rho' Hrho0 Hrho EQp' EQsigmap EQrho'];
  clear p' EQp' sigmap EQsigmap rho' EQrho'.
  rewrite <- IH in Hhl.
  specialize (Hrho i h l Hhl EQp).
  rewrite <- Hrho.
  simpl.
  rewrite <- IH, <- Hhl.
  simpl.
  rewrite <- EQp.
  reflexivity.
  + (* to show the rest *)
  rewrite Hrho.
  apply In_singleton.
Qed.

Theorem outp_is_not_empty :
  forall p sigma, outp p (sigma p) <> Empty_set _.
Proof.
  intros p sigma He.
  assert (Ho := out_equals_intersection_of_outp sigma).
  assert (He' : IntersectionForall allP (fun p => outp p (sigma p)) = Empty_set _).
  - (* to show He' *)
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split;
  intros rho Hrho.
  + inversion Hrho as [rho' Hrho' EQrho'];
  clear rho' EQrho'.
  assert (Hp : In _ allP p).
  { apply allP_intro. }
  specialize (Hrho' p Hp).
  rewrite He in Hrho'.
  inversion Hrho'.
  + inversion Hrho.
  - (* to show the rest *)
  rewrite He' in Ho.
  assert (Hne := In_singleton _ (out sigma)).
  rewrite Ho in Hne.
  inversion Hne.
Qed.


(* the updated strategy profile *)
Definition update (sigma : Sigma) (p : P) (sigmap : SigmaP)
  (p' : P) : SigmaP :=
  if p =? p' then sigmap else sigma p'.

(* alternative definition of outp *)
Inductive outp_alt : P -> SigmaP -> Ensemble Play :=
  | outp_alt_intro : forall p sigmap sigma,
    In _ (outp_alt p sigmap) (out (update sigma p sigmap))
  .

(* every play rho has a strategy whose outcome equals rho *)
Axiom every_play_can_be_an_outcome :
  forall rho : Play, exists sigma : Sigma,
  rho = out sigma.

Theorem outp_equals_outp_alt :
  forall p sigmap,
  outp p sigmap = outp_alt p sigmap.
Proof.
  intros p sigmap.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split;
  intros rho Hrho.
  - (* ⊆ *)
  inversion Hrho as [p' sigmap' rho' Hrho0 Hrho' EQp' EQsigmap' EQrho'];
  clear p' EQp' sigmap' EQsigmap' rho' EQrho'.
  destruct (every_play_can_be_an_outcome rho)
    as [sigma Hrs].
  assert (Hrs' : rho = out (update sigma p sigmap)).
  + (* to show rho = out (update sigma p sigmap) *)
  apply extensionality_Play.
  induction i as [| i IH].
  * (* when i = 0 *)
  rewrite Hrho0.
  reflexivity.
  * (* when i > 0 *)
  destruct (destruct_out sigma i) as [h [l Hhl]].
  rewrite <- Hrs in Hhl.
  specialize (Hrho' i h l Hhl).
  simpl.
  rewrite <- IH, <- Hhl.
  simpl.
  unfold update.
  destruct (Nat.eq_dec p (player h)) as [Hp | Hp].
  -- (* when p = player h *)
  specialize (Hrho' Hp).
  rewrite <- Hrho'.
  apply Nat.eqb_eq in Hp.
  rewrite Hp.
  reflexivity.
  -- (* when p <> player h *)
  apply Nat.eqb_neq in Hp.
  rewrite Hp.
  rewrite Hrs.
  simpl.
  rewrite <- Hrs, <- Hhl.
  simpl.
  reflexivity.
  + (* to show the rest *)
  rewrite Hrs'.
  apply outp_alt_intro.

  - (* ⊇ *)
  inversion Hrho as [p' sigmap' sigma EQp' EQsigmap' EQrho];
  clear p' EQp' sigmap' EQsigmap' rho EQrho Hrho.
  apply outp_intro;
  [reflexivity |].
  intros i h l Hhl Hp.
  simpl.
  rewrite <- Hhl.
  simpl.
  unfold update.
  apply Nat.eqb_eq in Hp.
  rewrite Hp.
  reflexivity.
Qed.

End Outcome.
