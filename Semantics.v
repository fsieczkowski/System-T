(** This file contains the definition of static and dynamic semantics, and basic
    properties, including preservation and progress lemmas *)

Require Export Relations.
Require Export List.
Require Export Substitution.
Require Import Omega.

Open Scope t_scope.
Open Scope list_scope.

Global Reserved Notation " Γ '⊢' M ':::' A " (at level 70).
Global Reserved Notation " γ ':–:' Γ " (at level 70).

Section Statics.

  (* Typing relation for terms *)
  Inductive types : list ty -> te -> ty -> Prop :=
  | tc_var  : forall A Γ n
      (HFind : nth_error Γ n = Some A),
      Γ ⊢ #n ::: A
  | tc_lam : forall A B Γ M
      (HT : A :: Γ ⊢ M ::: B),
      Γ ⊢ λ A, M ::: A → B
  | tc_app : forall Γ A B M N
      (HTM : Γ ⊢ M ::: A → B)
      (HTN : Γ ⊢ N ::: A),
      Γ ⊢ M @ N ::: B
  | tc_z   : forall Γ,
      Γ ⊢ z ::: ω
  | tc_s   : forall Γ M
      (HT : Γ ⊢ M ::: ω),
      Γ ⊢ s M ::: ω
  | tc_rec : forall Γ A M M₀ M₁
      (HTM : Γ ⊢ M ::: ω)
      (HT0 : Γ ⊢ M₀ ::: A)
      (HTS : ω :: A :: Γ ⊢ M₁ ::: A),
      Γ ⊢ rec M M₀ M₁ ::: A
  | tc_hd  : forall Γ A M
      (HTM : Γ ⊢ M ::: stream A),
      Γ ⊢ hd M ::: A
  | tc_tl  : forall Γ A M
      (HTM : Γ ⊢ M ::: stream A),
      Γ ⊢ tl M ::: stream A
  | tc_seed: forall Γ A M M₀ M₁
      (HTM : Γ ⊢ M ::: A)
      (HTH : A :: Γ ⊢ M₀ ::: A)
      (HTT : A :: Γ ⊢ M₁ ::: A),
      Γ ⊢ seed M M₀ M₁ ::: stream A
  where " Γ ⊢ M ::: A " := (types Γ M A) : t_scope.

  (* Typing relation for substitutions (only for closed substitutions) *)
  Fixpoint tcmt γ Γ : Prop :=
    match γ, Γ with
      | nil, nil => True
      | M :: γ, A :: Γ => nil ⊢ M ::: A /\ γ :–: Γ
      | _, _ => False
    end where " γ ':–:' Γ " := (tcmt γ Γ) : t_scope.

End Statics.

Global Reserved Notation " M ↦ N " (at level 70).
Global Reserved Notation " M ↦* N " (at level 70).
Section Dynamics.

  Inductive value : te -> Prop :=
  | val_z   :
      value z
  | val_s   : forall M,
      value (s M)
  | val_lam : forall A M,
      value (λ A, M)
  | val_seed: forall M M₀ M₁,
      value (seed M M₀ M₁).

  Inductive step : te -> te -> Prop :=
  | red_β    : forall A M N,
      (λ A, M) @ N ↦ [N :: nil ! 0]M
  | red_recz : forall M₀ M₁,
      rec z M₀ M₁ ↦ M₀
  | red_recs : forall M M₀ M₁,
      rec (s M) M₀ M₁ ↦ [M :: rec M M₀ M₁ :: nil ! 0] M₁
  | red_hds  : forall M M₀ M₁,
      hd (seed M M₀ M₁) ↦ [M ↑ 0]M₀
  | red_tls  : forall M M₀ M₁,
      tl (seed M M₀ M₁) ↦ seed [M ↑ 0]M₁ M₀ M₁
  | red_appC : forall M M' N
      (HR : M ↦ M'),
      M @ N ↦ M' @ N
  | red_recC : forall M M' M₀ M₁
      (HR : M ↦ M'),
      rec M M₀ M₁ ↦ rec M' M₀ M₁
  | red_hdC  : forall M M'
      (HR : M ↦ M'),
      hd M ↦ hd M'
  | red_tlC  : forall M M'
      (HR : M ↦ M'),
      tl M ↦ tl M'
  where " M ↦ N " := (step M N) : t_scope.
  Definition steps := clos_refl_trans_1n _ step.

End Dynamics.

Notation " Γ ⊢ M ::: A " := (types Γ M A) : t_scope.
Notation " γ ':–:' Γ " := (tcmt γ Γ) : t_scope.
Notation " M ↦* N " := (steps M N) : t_scope.
Notation " M ↦ N " := (step M N) : t_scope.

Section Properties.

  Lemma weaken : forall Γ Δ K A (HT : Γ ⊢ K ::: A), (Γ ++ Δ ⊢ K ::: A).
  Proof.
    induction 1; eauto using types; [].
    apply tc_var.
    generalize dependent n; induction Γ; intros; simpl; destruct n; simpl in *;
      discriminate || intuition.
  Qed.

  Lemma ssubst_type : forall M K A B Δ
    (HTK : nil ⊢ K ::: A)
    (HTM : Δ ++ A :: nil ⊢ M ::: B),
    Δ ⊢ [K ↑ length Δ]M ::: B.
  Proof.
    intros; remember (Δ ++ A :: nil) as Γ; generalize dependent Δ;
      induction HTM; simpl in *; intros; subst; simpl in *; eauto using types; [| | |].
    destruct (eq_nat_dec (length Δ) n).
      subst; assert (HEq : A = A0); [| subst A0].
        induction Δ; simpl in *; [inversion HFind; subst; tauto |].
        apply IHΔ; assumption.
      replace Δ with (nil ++ Δ) by reflexivity; apply weaken; assumption.
    apply tc_var.
    generalize dependent n; induction Δ; simpl in *; intros.
    destruct n; [tauto | destruct n; discriminate].
      destruct n; simpl in *; [assumption |].
      apply IHΔ; [assumption |].
      intro HEq; apply n0; f_equal; assumption.
    simpl; eapply tc_lam, IHHTM; tauto.
    simpl; apply tc_rec; [apply IHHTM1 | apply IHHTM2 | apply IHHTM3]; tauto.
    simpl; apply tc_seed; [apply IHHTM1 | apply IHHTM2 | apply IHHTM3]; tauto.
  Qed.

  Lemma subst_types : forall γ Γ Δ M A
    (HTC : γ :–: Γ)
    (HT  : Δ ++ Γ ⊢ M ::: A),
    Δ ⊢ [γ!length Δ]M ::: A.
  Proof.
    induction γ; destruct Γ; simpl in *; intros; try contradiction; [|].
      rewrite <- app_nil_end in HT; assumption.
    destruct HTC as [HTa HTC].
    eapply ssubst_type; [eassumption |].
    replace (S (length Δ)) with (length (Δ ++ t :: nil))
      by (rewrite app_length, plus_comm; reflexivity).
    eapply IHγ; [eassumption |].
    rewrite <- app_assoc; simpl; assumption.
  Qed.

  Lemma closed_sub : forall M A K n Γ
    (HT : Γ ⊢ M ::: A),
    M = [K ↑ length Γ + n]M.
  Proof.
    induction 1; try (simpl in *; f_equal; reflexivity || assumption).
    simpl.
    assert (n0 < length Γ).
      generalize dependent n0; induction Γ; intros; [destruct n0; discriminate |].
      destruct n0; simpl; [auto with arith |].
      simpl in HFind; apply IHΓ in HFind; auto with arith.
    destruct (eq_nat_dec (length Γ + n) n0); [| reflexivity].
    contradict e; omega.
  Qed.

  Lemma subst_var : forall γ Γ n m A
    (HT  : nth_error Γ n = Some A)
    (HΓ  : tcmt γ Γ),
    Some [γ ! m](#(n+m)) = nth_error γ n /\ (nil ⊢ [γ ! m](#(n+m)) ::: A).
  Proof.
    induction γ; intros.
      destruct Γ; [destruct n |]; contradiction || discriminate.
    destruct Γ; [contradiction |].
    destruct n; simpl in *.
      rewrite <- subst_gt; [| auto with arith].
      unfold Specif.value; simpl; destruct (eq_nat_dec m m);
      inversion HT; subst; tauto.
    destruct HΓ as [Ht HΓ]; specialize (IHγ _ _ (S m) _ HT HΓ).
    rewrite plus_comm in IHγ; simpl in *; rewrite plus_comm in IHγ.
    destruct IHγ as [HEq HTy]; split.
      rewrite <- HEq; f_equal; symmetry.
      replace m with (length (@nil ty) + m) by reflexivity; eapply closed_sub;
        simpl; eassumption.
    replace m with (length (@nil ty) + m) by reflexivity.
    erewrite <- closed_sub; simpl in *; eassumption.
  Qed.

  (* Lemmas extending congruence to multistep reduction *)
  Lemma rec_cong_star : forall M M' M₀ M₁
    (HR : M ↦* M'),
    rec M M₀ M₁ ↦* rec M' M₀ M₁.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [apply red_recC; eassumption | apply IHHR].
  Qed.
  Lemma hd_cong_star : forall M M'
    (HRed : M ↦* M'),
    hd M ↦* hd M'.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [| apply IHHRed].
    apply red_hdC; assumption.
  Qed.
  Lemma tl_cong_star : forall M M'
    (HRed : M ↦* M'),
    tl M ↦* tl M'.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [| apply IHHRed].
    apply red_tlC; assumption.
  Qed.

  (* Progress lemma is not really needed to prove termination,
     but it's a good sanity check *)
  Lemma progress : forall M A
    (HT : nil ⊢ M ::: A),
    value M \/ exists N, M ↦ N.
  Proof.
    induction M; intros; simpl in *.
    (* var *)
    inversion HT; destruct n; discriminate.
    (* lam *)
    left; apply val_lam.
    (* app *)
    inversion HT; subst; right.
    specialize (IHM1 _ HTM); clear IHM2 HTN.
    destruct IHM1 as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail); [].
      eexists; apply red_β.
    exists (N @ M2); apply red_appC; assumption.
    (* z *)
    left; apply val_z.
    (* s *)
    left; apply val_s.
    (* rec *)
    right; clear IHM2 IHM3; inversion HT; subst.
    specialize (IHM1 _ HTM); destruct IHM1 as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
        eexists; apply red_recz.
      eexists; apply red_recs.
    eexists; apply red_recC; eassumption.
    (* hd *)
    right; inversion HT; subst.
    specialize (IHM _ HTM); destruct IHM as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
      eexists; apply red_hds.
    eexists; apply red_hdC; eassumption.
    (* tl *)
    right; inversion HT; subst.
    specialize (IHM _ HTM); destruct IHM as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
      eexists; apply red_tls.
    eexists; apply red_tlC; eassumption.
    (* seed *)
    left; apply val_seed.
  Qed.

  (* Type preservation is needed to use the head expansion lemma *)
  Lemma preservation : forall A M N
    (HT : nil ⊢ M ::: A)
    (HR : M ↦ N),
    nil ⊢ N ::: A.
  Proof.
    intros; remember (@nil ty) as Γ; generalize dependent N;
      induction HT; intros; inversion HR; subst.
    (* beta *)
    clear IHHT1 IHHT2 HR.
    inversion HT1; subst; clear HT1.
    eapply subst_types; simpl; [| eassumption]; simpl; tauto.
    (* cong app *)
    eapply tc_app; [apply IHHT1 |]; tauto.
    (* rec z *)
    assumption.
    (* rec s *)
    clear IHHT1 IHHT2 IHHT3 HR.
    inversion HT1; subst.
    eapply subst_types; [| simpl; eassumption]; simpl; intuition; [].
    apply tc_rec; assumption.
    (* cong rec *)
    apply tc_rec; [apply IHHT1 | |]; tauto.
    (* hd seed *)
    inversion HT; subst.
    eapply ssubst_type; simpl in *; eassumption.
    (* cong hd *)
    apply tc_hd; apply IHHT; tauto.
    (* tl seed *)
    inversion HT; subst.
    apply tc_seed; [eapply ssubst_type; simpl in *; eassumption | |]; assumption.
    (* cong tl *)
    apply tc_tl; apply IHHT; tauto.
  Qed.

End Properties.

Close Scope t_scope.
Close Scope list_scope.
