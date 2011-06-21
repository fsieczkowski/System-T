(** This file contains the termination argument via logical relations *)

Require Import Semantics.
Open Scope t_scope.
Open Scope list_scope.

Section Definitions.

  (* Logical relation at type ω *)
  Inductive Rω : te -> Prop :=
  | Rω_z : forall M (HRed : M ↦* z), Rω M
  | Rω_s : forall M M' (HRed : M ↦* s M') (HR : Rω M'), Rω M.

  (* Logical relation at type stream, parameterised with the relation at element type *)
  CoInductive Rstream : (te -> Type) -> te -> Prop :=
  | Rs : forall M P (HHD : P (hd M)) (HTL : Rstream P (tl M)), Rstream P M.

  (* The reducibility relation: has to be defined as a fixpoint, since Coq doesn't allow
     for negative occurrences of a relation in the A₁ → A₂ case *)
  Fixpoint R A M : Prop :=
    match A with
      | ω => Rω M
      | A₁ → A₂ => forall N (HTN : nil ⊢ N ::: A₁) (HR : R A₁ N), R A₂ (M @ N)
      | stream A => Rstream (R A) M
    end.

  (* Reduciblity for the whole contexts *)
  Fixpoint rctx γ Γ :=
    match γ, Γ with
      | nil, nil => True
      | M :: γ, A :: Γ => R A M /\ rctx γ Γ
      | _, _ => False
    end.

End Definitions.

Section Termination_proof.

  Lemma head_expansion : forall A M N
    (HR : R A N)
    (HS : M ↦ N),
    R A M.
  Proof.
    induction A; intros; simpl in *.
    (* nat *)
    inversion HR.
      apply Rω_z; unfold steps; econstructor; eassumption.
    apply Rω_s with M'; [| assumption]; econstructor; eassumption.
    (* arr *)
    intros.
    eapply IHA2; [| apply red_appC; eassumption].
    apply HR; assumption.
    (* stream *)
    (* We need coinduction to prove the property here, and a stronger lemma. *)
    assert (HT : exists K : te, (M ↦ K) /\ Rstream (R A) K)
      by (exists N; tauto).
    clear HS HR; destruct HT as [K [HRed HR]]; generalize dependent K; revert M.
    cofix; intros.
    inversion HR; subst; apply Rs.
      eapply IHA; [eassumption | apply red_hdC; eassumption].
    eapply head_expansion; [| eassumption].
    apply red_tlC; assumption.
  Qed.

  (* lifting of head expansion to reflexive transitive closure *)
  Lemma head_exp_star : forall A M N
    (HR : R A N)
    (HS : M ↦* N),
    R A M.
  Proof.  
    intros; induction HS; [assumption |].
    eapply head_expansion; [| eassumption].
    tauto.
  Qed.

  Lemma types_red : forall Γ M A γ
    (HT : Γ ⊢ M ::: A)
    (HR : rctx γ Γ)
    (HΓ : tcmt γ Γ),
    R A [γ!0]M.
  Proof.
    intros; generalize dependent γ; induction HT; intros.
    (* var *)
    assert (HT := subst_var _ _ _ 0 _ HFind HΓ); rewrite plus_comm in HT; simpl in *.
    destruct HT as [HT _].
    revert HT; generalize ([γ ! 0](#n)) as M; intros M; generalize dependent Γ;
      revert n; induction γ; simpl; destruct Γ; intros; try contradiction; [|].
      destruct n; discriminate.
    destruct n; simpl in *.
      inversion HT; subst a.
      inversion HFind; subst t; tauto.
    destruct HR as [Ha HR]; destruct HΓ as [Ht HΓ]; eapply IHγ; eassumption.
    (* lam *)
    simpl; intros; rewrite sub_lam.
    eapply head_expansion; [| apply red_β].
    rewrite subcomp; apply IHHT; simpl; tauto.
    (* appl *)
    rewrite sub_app; simpl in IHHT1.
    apply IHHT1; intuition; [].
    eapply subst_types; simpl; eassumption.
    (* z *)
    apply Rω_z; rewrite sub_z; constructor.
    (* s *)
    simpl in *; rewrite sub_s; eapply Rω_s; [constructor | intuition].
    (* rec *)
    specialize (IHHT1 _ HR HΓ); specialize (IHHT2 _ HR HΓ); simpl in *.
    assert (HTR : nil ⊢ [γ ! 0]M ::: ω) by (eapply subst_types; simpl; eassumption).
    rewrite sub_rec; revert IHHT1 HTR; generalize ([γ ! 0]M); intros K HRK HTK;
      induction HRK.
      apply head_exp_star with (rec z [γ ! 0]M₀ [γ ! 2]M₁);
        [| apply rec_cong_star; assumption].
      eapply head_expansion; [| apply red_recz]; assumption.
    eapply head_exp_star with (rec (s M') [γ ! 0]M₀ [γ ! 2]M₁);
    [| apply rec_cong_star; assumption].
    eapply head_expansion; [| apply red_recs].
    assert (HST : nil ⊢ s M' ::: ω).
      induction HRed; [assumption |].
      eapply IHHRed, preservation; eassumption.
    inversion HST; subst.
    rewrite subcomp; apply IHHT3; simpl; intuition; [].
    apply tc_rec; [assumption | |]; eapply subst_types; simpl; eassumption.
    (* hd *)
    specialize (IHHT _ HR HΓ); inversion IHHT; subst.
    rewrite sub_hd; assumption.
    (* tl *)
    specialize (IHHT _ HR HΓ); inversion IHHT; subst.
    rewrite sub_tl; assumption.
    (* seed *)
    specialize (IHHT1 _ HR HΓ).
    assert (HTR : nil ⊢ [γ ! 0]M ::: A) by (eapply subst_types; simpl; eassumption).
    clear HT1; simpl; rewrite sub_seed.
    assert (exists K, (seed [γ ! 0]M [γ ! 1]M₀ [γ ! 1]M₁ ↦* seed K [γ ! 1]M₀ [γ ! 1]M₁)
      /\ (nil ⊢ K ::: A) /\ R A K).
    simpl; eexists; split; [constructor | split; assumption].
    simpl in H; destruct H as [K [HRed [HTK HRK]]]; generalize dependent K.
    generalize (seed [γ ! 0]M [γ ! 1]M₀ [γ ! 1]M₁) as N.
    cofix; intros; apply Rs.
      eapply head_exp_star; [| eapply hd_cong_star; eassumption].
      eapply head_expansion; [| apply red_hds].
      change (R A [K :: nil ! 0]([γ ! 1]M₀)); rewrite subcomp.
      apply IHHT2; simpl; tauto.
    apply types_red with [K ↑ 0]([γ ! 1]M₁); clear types_red.
        apply clos_rt_rt1n; eapply rt_trans;
          [apply clos_rt1n_rt, tl_cong_star; eassumption |].
        apply rt_step, red_tls.
      change (nil ⊢ [K :: nil ! 0]([γ ! 1]M₁) ::: A); rewrite subcomp.
      eapply subst_types; [| simpl; eassumption]; simpl; tauto.
    change (R A [K :: nil ! 0]([γ ! 1]M₁)); rewrite subcomp.
    apply IHHT3; simpl; tauto.
  Qed.

  Theorem termination : forall M (HT : nil ⊢ M ::: ω),
    exists V, value V /\ (M ↦* V).
  Proof.
    intros.
    apply types_red with (γ := nil) in HT; [| exact I | exact I].
    inversion HT; subst.
    (* z *)
    exists z; split; [apply val_z | assumption].
    (* s *)
    exists (s M'); split; [apply val_s | assumption].
  Qed.

End Termination_proof.
