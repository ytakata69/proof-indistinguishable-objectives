(*
 * Proofs about indistinguishable objectives in
 * multiplayer non zero-sum games
 *)

Require Import Lists.List.
Require Import Sets.Ensembles.
Require Import Arith.
Require Import ind_obj.

Section PreliminariesOnListsAndEnsembles.

(* prefix of length n *)
Fixpoint take {T : Type} (n : nat) (l : list T) : list T :=
  match n, l with
  | 0, _   => nil
  | _, nil => nil
  | S n', h :: t => h :: take n' t
  end.

Variable T : Type.
Variable A : Ensemble T.

Lemma empty_is_subset_of_any :
  Included _ (Empty_set T) A.
Proof.
  unfold Included.
  intros x Hx.
  inversion Hx.
Qed.

Lemma subset_of_empty_is_empty :
  Included _ A (Empty_set _) ->
  A = Empty_set T.
Proof.
  intros Ha.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; [assumption |].
  apply empty_is_subset_of_any.
Qed.

End PreliminariesOnListsAndEnsembles.

Section Outcome.

(* To show the relationship between out and out^p *)

Definition P := nat. (* the set of players *)
Parameter V : Set. (* the set of vertices *)
Parameter player : V -> P. (* the controller of a vertex *)

Definition allP := Full_set P. (* the set of all players *)

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

Variable v0 : V.
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

Lemma length_of_out :
  forall sigma i,
  length (out sigma i) = S i.
Proof.
  intros sigma.
  induction i as [| i IH].
  - (* when i = 0 *)
  reflexivity.
  - (* when i > 0 *)
  simpl.
  now rewrite IH.
Qed.

Lemma out_is_in_outp :
  forall (sigma : Sigma) (p : P),
  In _ (outp p (sigma p)) (out sigma).
Proof.
  intros sigma p.
  apply outp_intro.
  - (* to show out sigma 0 = v0 :: nil *)
  reflexivity.
  - (* to show the rest *)
  intros i h l EQhl EQp.
  destruct i as [| i];
  unfold out in EQhl;
  injection EQhl;
  intros EQl EQh;
  unfold out;
  rewrite <- EQh, EQl, EQp;
  reflexivity.
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
  apply out_is_in_outp.

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
  { apply Full_intro. }
  specialize (Hrho' (player v0) Hp0).
  inversion Hrho' as [p' sigmap rho' Hrho0 Hrho EQp' EQsigmap EQrho'];
  clear p' EQp' sigmap EQsigmap rho' EQrho'.
  now simpl.
  * (* when i > 0 *)
  destruct (destruct_out sigma i) as [h [l Hhl]].
  remember (player h) as p eqn:EQp.
  assert (Hp : In _ allP p).
  { apply Full_intro. }
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
  { apply Full_intro. }
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

Lemma out_update_sigma_is_in_outp :
  forall p sigma sigmap,
  In _ (outp p sigmap) (out (update sigma p sigmap)).
Proof.
  intros p sigma sigmap.
  rewrite outp_equals_outp_alt.
  apply outp_alt_intro.
Qed.

Definition Omega := Ensemble Play.

Inductive winnable (p : P) : Ensemble Omega :=
| winnable_intro : forall O,
  (exists (sigma : Sigma),
    Included _ (outp p (sigma p)) O)
  -> In _ (winnable p) O.

Lemma empty_is_not_winnable :
  forall p, ~ In _ (winnable p) (Empty_set _).
Proof.
  intros p Hw.
  inversion Hw as [O Hw' EQO];
  clear O EQO Hw.
  destruct Hw' as [sigma Hw].
  unfold Included in Hw.
  specialize (Hw (out sigma)).
  specialize (Hw (out_is_in_outp sigma p)).
  inversion Hw.
Qed.

Definition NashEq (sigma : Sigma) (alpha : P -> Omega) : Prop :=
  forall (p : P) (sigmap : SigmaP),
  In _ (alpha p) (out (update sigma p sigmap)) ->
  In _ (alpha p) (out sigma).

End Outcome.

Section DropPrefix.

Let U := Play.
Infix "∩" := (Intersection U)  (at level 40, left associativity).
Infix "∪" := (Union U)         (at level 50, left associativity).
Infix "⊆" := (Included U)      (at level 55, no associativity).
Notation "x ∈ S" := (In U S x) (at level 55, no associativity).
Notation "¬ x" := (Complement U x) (at level 35).
Notation "∅" := (Empty_set U).

Infix ".∩" := (Intersection Omega)  (at level 40, left associativity).
Infix ".∪" := (Union Omega)         (at level 50, left associativity).
Infix ".⊆" := (Included Omega)      (at level 55, no associativity).
Notation "x .∈ S" := (In Omega S x) (at level 55, no associativity).
Notation ".¬ x" := (Complement Omega x) (at level 35).

Definition dropPrefix (n : nat) (rho : Play) (i : nat) : list V
  := take (S i) (rho (n + i)).

Definition prefixIndependent (Op : Omega) : Prop :=
  forall (rho : Play) (n : nat),
  rho ∈ Op <-> (dropPrefix n rho) ∈ Op.

(* composition of two strategies *)
Definition composite (n : nat) (sigmap taup : SigmaP)
  (l : list V) : V :=
  if length l <=? n then sigmap l else taup (take (length l - n) l).

Lemma strategy_switching_before :
  forall v0 p sigma taup n,
  forall i, i <= n ->
  out v0 (update sigma p (composite n (sigma p) taup)) i
    = out v0 sigma i.
Proof.
  intros v0 p sigma taup n i Hi.
  induction i as [| i IH].
  - (* when i = 0 *)
  reflexivity.
  - (* when i > 0 *)
  apply le_Sn_le in Hi as Hi'.
  specialize (IH Hi'); clear Hi'.
  destruct (destruct_out v0 sigma i)
    as [h [l Hhl]].
  simpl.
  unfold update at 1.
  rewrite IH.
  rewrite <- Hhl.
  simpl.
  destruct (eq_nat_dec p (player h)) as [Hp | Hp].
  + (* when p = player h *)
  rewrite <- Hp.
  rewrite (Nat.eqb_refl p).
  unfold composite.
  assert (Hlen : length (h :: l) <= n).
  { rewrite Hhl. now rewrite length_of_out. }
  apply Nat.leb_le in Hlen.
  rewrite Hlen.
  reflexivity.
  + (* when p <> player h *)
  apply Nat.eqb_neq in Hp.
  rewrite Hp.
  reflexivity.
Qed.

Lemma strategy_switching_after :
  forall _v v0 p sigma taup n,
  dropPrefix n (out v0 (update sigma p (composite n (sigma p) taup)))
    ∈ outp (hd _v (out v0 sigma n)) p taup.
Proof.
  intros _v v0 p sigma taup n.
  apply outp_intro.
  - (* to show at the head *)
  unfold dropPrefix.
  rewrite Nat.add_0_r.
  rewrite strategy_switching_before;
  [| apply Nat.le_refl].
  destruct (destruct_out v0 sigma n)
    as [h [l Hhl]].
  rewrite <- Hhl.
  unfold take.
  reflexivity.

  - (* to show at the rest *)
  remember (update sigma p (composite n (sigma p) taup))
  as sigma' eqn:EQsigma'.
  unfold dropPrefix.

  intros i h l Hhl Hp.
  destruct (destruct_out v0 sigma' (n + i))
    as [h' [l' Hhl']].
  rewrite <- Hhl' in Hhl.
  unfold take in Hhl.
  injection Hhl;
  intros EQl EQh.
  rewrite <- EQh in Hhl'.
  clear h' Hhl EQh.

  rewrite Nat.add_succ_r.
  assert (Hhl'' := Hhl').
  unfold out in Hhl''.
  unfold out.
  rewrite <- Hhl''.
  clear Hhl''.
  simpl.

  rewrite EQsigma'.
  unfold update.
  apply Nat.eqb_eq in Hp as Hp'.
  rewrite Hp'.
  unfold composite.
  assert (Hlen : length (h :: l') > n).
  {
    rewrite Hhl'.
    rewrite length_of_out.
    apply le_gt_S.
    apply le_plus_l.
  }
  apply gt_not_le in Hlen.
  apply Nat.leb_nle in Hlen.
  rewrite Hlen; clear Hlen.
  pattern (h :: l') at 1;
  rewrite Hhl'.
  rewrite length_of_out.
  assert (Hi : S (n + i) - n = S i).
  {
    rewrite <- Nat.add_succ_r.
    apply minus_plus.
  }
  rewrite Hi.
  unfold take.
  rewrite EQl.
  reflexivity.
Qed.

Variable v0 : V.

Lemma characterization_of_NE_lr :
  forall alpha : P -> Omega,
    (forall p : P, prefixIndependent (alpha p)) ->
  forall rho : Play,
    (exists sigma : Sigma,
       rho = out v0 sigma /\ NashEq v0 sigma alpha) ->
  forall (p : P) (i : nat),
    p = player (hd v0 (rho i)) /\
    alpha p .∈ winnable (hd v0 (rho i)) p
    -> dropPrefix i rho ∈ alpha p.
Proof.
  intros alpha Hpre rho [sigma [EQrho Hne]].
  rewrite EQrho; clear rho EQrho.
  intros p i [Hp Hw].

  inversion Hw as [Op Hw' EQOp];
  clear Op EQOp Hw.
  destruct Hw' as [tau Htau].
  unfold Included in Htau.

  apply (Hpre _ (out v0 sigma) i).
  apply Hne with (sigmap:=composite i (sigma p) (tau p)).
  apply Hpre with (n:=i).
  apply Htau.
  apply strategy_switching_after.
Qed.

(*
Lemma characterization_of_NE_rl :
  forall alpha : P -> Omega,
    (forall p : P, prefixIndependent (alpha p)) ->
  forall rho : Play,
    (forall (p : P) (i : nat),
     p = player (hd v0 (rho i)) /\
     alpha p .∈ winnable (hd v0 (rho i)) p
     -> dropPrefix i rho ∈ alpha p) ->
  exists sigma : Sigma,
    rho = out v0 sigma /\ NashEq v0 sigma alpha.
Proof.
  intros alpha Hpre rho Hw.
  unfold prefixIndependent in Hpre.
  unfold NashEq.
Abort.
*)

End DropPrefix.
