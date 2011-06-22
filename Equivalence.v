Require Import Termination.
Require Import Setoid.

Open Scope t_scope.
Open Scope list_scope.

Reserved Notation " M ≃ N " (at level 70).
Inductive Eq2 M N : Prop :=
| equivT : forall
    (HTM : nil ⊢ M ::: 2)
    (HTN : nil ⊢ N ::: 2)
    (HRedM : M ↦* TT)
    (HRedN : N ↦* TT),
    M ≃ N
| equivF : forall
    (HTM : nil ⊢ M ::: 2)
    (HTN : nil ⊢ N ::: 2)
    (HRedM : M ↦* FF)
    (HRedN : N ↦* FF),
    M ≃ N
where " M ≃ N " := (Eq2 M N).

Lemma step_det : forall M N₁ N₂
  (Hred₁ : M ↦ N₁)
  (Hred₂ : M ↦ N₂),
  N₁ = N₂.
Proof.
  intros; generalize dependent N₂; induction Hred₁; intros;
    try (inversion Hred₂; subst; [reflexivity | inversion HR]);
      inversion Hred₂; subst; (inversion Hred₁; fail) || f_equal; intuition.
Qed.

Lemma value_not_red : forall V M
  (Hval : value V)
  (Hred : V ↦* M),
  M = V.
Proof.
  induction 2; [reflexivity |].
  inversion H; subst; inversion Hval.
Qed.
  
Lemma steps_val_det : forall M V₁ V₂
  (Hval₁ : value V₁)
  (Hval₂ : value V₂)
  (Hred₁ : M ↦* V₁)
  (Hred₂ : M ↦* V₂),
  V₁ = V₂.
Proof.
  intros; generalize dependent V₂; induction Hred₁; intros.
    symmetry; apply value_not_red; assumption.
  inversion Hred₂; subst.
    inversion H; subst; inversion Hval₂.
  assert (y = y0) by (eauto using step_det); subst.
  apply IHHred₁; assumption.
Qed.

Instance Eq2_sym : Symmetric Eq2.
Proof.
  intros x.
  unfold Symmetric; intros.
  inversion H; auto using Eq2.
Qed.

Instance Eq2_trans : Transitive Eq2.
Proof.
  unfold Transitive; intros.
  inversion H0; subst; inversion H; subst; auto using Eq2;
    assert (TT = FF) by (eauto using steps_val_det, value); discriminate.
Qed.

Lemma Eq2_type_refl : forall M (HT : nil ⊢ M ::: 2), M ≃ M.
Proof.
  intros; assert (HR := types_red _ _ _ nil HT I I).
  simpl in *; inversion HR; subst; auto using Eq2.
Qed.

Inductive Eqω : te -> te -> Prop :=
| Eqωz : forall M N (HMz : M ↦* z) (HNz : N ↦* z), Eqω M N
| Eqωs : forall M N M' N' (HMs : M ↦* s M') (HNs : N ↦* s N') (HEq : Eqω M' N'), Eqω M N.

Instance Eqω_sym : Symmetric Eqω.
Proof.
  unfold Symmetric; intros; induction H; eauto using Eqω.
Qed.    

Instance Eqω_trans : Transitive Eqω.
Proof.
  unfold Transitive; intros.
  revert z H0; induction H; intros u Hu; inversion Hu; subst; eauto using Eqω.
  assert (z = s M') by (eauto using steps_val_det, value); discriminate.
  assert (z = s N') by (eauto using steps_val_det, value); discriminate.
  assert (HT : s N' = s M'0) by (eauto using steps_val_det, value); inversion HT; subst;
    eauto using Eqω.
Qed.

CoInductive Eqs (P : te -> te -> Prop) : te -> te -> Prop :=
| EqS : forall M N (HEqHD : P (hd M) (hd N)) (HEqTL : Eqs P (tl M) (tl N)), Eqs P M N.

Instance Eqs_sym P (HSym : Symmetric P) : Symmetric (Eqs P).
Proof.
  unfold Symmetric; cofix; intros x y H.
  inversion H; subst; constructor.
    symmetry; assumption.
  apply Eqs_sym; assumption.
Qed.

Instance Eqs_trans P (HTran : Transitive P) : Transitive (Eqs P).
Proof.
  cofix; unfold Transitive; intros u v w Huv Hvw.
  inversion Huv; subst; inversion Hvw; subst; constructor.
    eapply HTran; eassumption.
  eapply Eqs_trans; eassumption.
Qed.

Inductive ctx : Type :=
| hole   : ctx
| full   : te -> ctx
| ct_lam : ty -> ctx -> ctx
| ct_appL: te -> ctx -> ctx
| ct_appR: te -> ctx -> ctx
| ct_s   : ctx -> ctx
| ct_rec0: te -> te -> ctx -> ctx
| ct_rec1: te -> te -> ctx -> ctx
| ct_rec2: te -> te -> ctx -> ctx
| ct_hd  : ctx -> ctx
| ct_tl  : ctx -> ctx
| ct_sd0 : te -> te -> ctx -> ctx
| ct_sd1 : te -> te -> ctx -> ctx
| ct_sd2 : te -> te -> ctx -> ctx.

Fixpoint plug (E : ctx) (M : te) : te :=
  match E with
    | hole           => M
    | full N         => N
    | ct_lam A E     => λ A, plug E M
    | ct_appL N E    => N @ (plug E M)
    | ct_appR N E    => (plug E M) @ N
    | ct_s E         => s (plug E M)
    | ct_rec0 M₀ M₁ E => rec (plug E M) M₀ M₁
    | ct_rec1 M₀ M₁ E => rec M₀ (plug E M) M₁
    | ct_rec2 M₀ M₁ E => rec M₀ M₁ (plug E M)
    | ct_hd E        => hd (plug E M)
    | ct_tl E        => tl (plug E M)
    | ct_sd0 M₀ M₁ E  => seed (plug E M) M₀ M₁
    | ct_sd1 M₀ M₁ E  => seed M₀ (plug E M) M₁
    | ct_sd2 M₀ M₁ E  => seed M₀ M₁ (plug E M)
  end.

Reserved Notation " E · F " (at level 40).

Fixpoint compose (E E' : ctx) : ctx :=
  match E with
    | hole => E'
    | full M => E
    | ct_lam A E => ct_lam A (E · E')
    | ct_appL M E => ct_appL M (E · E')
    | ct_appR N E => ct_appR N (E · E')
    | ct_s E => ct_s (E · E')
    | ct_rec0 M N E => ct_rec0 M N (E · E')
    | ct_rec1 M N E => ct_rec1 M N (E · E')
    | ct_rec2 M N E => ct_rec2 M N (E · E')
    | ct_hd E => ct_hd (E · E')
    | ct_tl E => ct_tl (E · E')
    | ct_sd0 M N E => ct_sd0 M N (E · E')
    | ct_sd1 M N E => ct_sd1 M N (E · E')
    | ct_sd2 M N E => ct_sd2 M N (E · E')
  end where " E · E' " := (compose E E').

Lemma plug_compose : forall M E E',
  plug E (plug E' M) = plug (E · E') M.
Proof.
  induction E; intros; simpl; try rewrite IHE; reflexivity.
Qed.  

Definition type_context E Γ Δ A B :=
  forall M (HT : Γ ⊢ M ::: A), Δ ⊢ plug E M ::: B.
Notation " E ::: [ Γ , A ] → [ Δ , B ] " := (type_context E Γ Δ A B) (at level 70).

Definition obs_eq Γ A (M N : {K : te | Γ ⊢ K ::: A}) :=
  forall E (HTE : E ::: [ Γ, A ] → [ nil, 2 ]),
    plug E (proj1_sig M) ≃ plug E (proj1_sig N).
Notation " Γ ⊢ M == N ::: A " := (obs_eq Γ A M N) (at level 70).

Definition consistent (P : forall Γ A, relation {K : te | Γ ⊢ K ::: A}) :=
  forall M N, P nil 2 M N -> proj1_sig M ≃ proj1_sig N.

Definition closed (P : forall Γ A, relation {K : te | Γ ⊢ K ::: A}) :=
  forall E Γ Δ A B M N
    (HTE  : E ::: [Γ, A] → [Δ, B])
    (HPMN : P Γ A M N),
    (P Δ B (exist _ (plug E (proj1_sig M)) (HTE _ (proj2_sig M)))
      (exist _ (plug E (proj1_sig N)) (HTE _ (proj2_sig N)))).

Record ConsCong (P : forall Γ A, relation {K : te | Γ ⊢ K ::: A}) :=
  { Cong_Equiv  : forall Γ A, Equivalence (P Γ A);
    Cong_Cons   : consistent P;
    Cong_Closed : closed P}.

Lemma obs_eq_cong : ConsCong obs_eq.
Proof.
  split; intros.
  split; unfold Reflexive, Symmetric, Transitive; intros.
  (* refl *)
  unfold obs_eq; intros.
  apply Eq2_type_refl, HTE, (proj2_sig x).
  (* symm *)
  unfold obs_eq; intros; symmetry; apply H; assumption.
  (* tran *)
  unfold obs_eq; intros; etransitivity; eauto; fail.
  (* cons *)
  unfold consistent; intros.
  specialize (H hole); simpl in H; apply H.
  intros K HT; simpl; assumption.
  (* cong *)
  unfold closed, obs_eq; intros.
  simpl; rewrite !plug_compose; apply HPMN.
  intros K HT; rewrite <- plug_compose.
  apply HTE0, HTE; assumption.
Qed.

Lemma obs_eq_coarsest :
  forall (P : forall Γ A, relation {K : te | Γ ⊢ K ::: A})
    (HCC : ConsCong P)
    Γ A M N (HIn : P Γ A M N),
    Γ ⊢ M == N ::: A.
Proof.
  unfold obs_eq; intros.
  assert (HCons := Cong_Cons _ HCC (exist _ (plug E (proj1_sig M)) (HTE _ (proj2_sig M)))
    (exist _ (plug E (proj1_sig N)) (HTE _ (proj2_sig N)))); simpl in HCons.
  apply HCons; clear HCons.
  apply (Cong_Closed _ HCC); assumption.
Qed.

(* Logical Equivalence *)

Reserved Notation " M ≡ N ::: A " (at level 70).

Fixpoint log_equiv (A : ty) (M N : te) : Prop :=
  match A with
    | 2 => M ≃ N
    | ω => Eqω M N
    | A₁ → A₂ => forall M' N' (HEq : M' ≡ N' ::: A₁), M ≡ N ::: A₂
    | stream A => Eqs (log_equiv A) M N
  end where " M ≡ N ::: A " := (log_equiv A M N) : t_scope.

Instance log_equiv_symm A : Symmetric (log_equiv A).
Proof.
  induction A; eauto with typeclass_instances.
  (* arrow *)
  unfold Symmetric; simpl; intros.
  symmetry; eapply H; eassumption.
  (* stream *)
  unfold Symmetric; simpl; apply Eqs_sym; assumption.
Qed.

Instance log_equiv_trans A : Transitive (log_equiv A).
Proof.
  induction A; eauto with typeclass_instances.
  (* arrow *)
  unfold Transitive; simpl; intros.
  etransitivity; eauto.
  (* stream *)
  unfold Transitive; simpl; apply Eqs_trans; assumption.
Qed.

Reserved Notation " γ₁ ∼ γ₂ ::: Γ " (at level 70).
Fixpoint ctx_log_equiv Γ γ₁ γ₂ :=
  match Γ, γ₁, γ₂ with
    | nil, nil, nil => True
    | A :: Γ, M :: γ₁, N :: γ₂ => (M ≡ N ::: A) /\ (γ₁ ∼ γ₂ ::: Γ)
    | _, _, _ => False
  end where " γ₁ ∼ γ₂ ::: Γ " := (ctx_log_equiv Γ γ₁ γ₂) : t_scope.

Instance ctx_log_equiv_sym Γ : Symmetric (ctx_log_equiv Γ).
Proof.
  induction Γ; unfold Symmetric; intros; destruct x; destruct y;
    try contradiction; [tauto |].
  simpl in *; destruct H; split; symmetry; assumption.
Qed.

Instance ctx_log_equiv_trans Γ : Transitive (ctx_log_equiv Γ).
Proof.
  induction Γ; unfold Transitive; intros;
    destruct x; destruct y; destruct z; try contradiction; [tauto |].
  simpl in *; destruct H; destruct H0; split; etransitivity; eassumption.
Qed.

Definition open_simeq Γ A (M N : {K : te | Γ ⊢ K ::: A}) := forall γ₁ γ₂
  (HEΓ : γ₁ ∼ γ₂ ::: Γ),
  [γ₁ ! 0](proj1_sig M) ≡ [γ₂ ! 0](proj1_sig N) ::: A.
Notation " Γ ⊢ M ∼ N ::: A " := (open_simeq Γ A M N) (at level 70) : t_scope.

Instance open_simeq_symm  Γ A : Symmetric (open_simeq Γ A).
Proof.
  unfold Symmetric, open_simeq; intros.
  symmetry; apply H; try symmetry; assumption.
Qed.  

Lemma open_simeq_trans : forall Γ A, transitive _ (open_simeq Γ A).
Proof.
  unfold transitive, open_simeq; intros.
  etransitivity; [apply H | apply H0]; try eassumption.
  etransitivity; [symmetry |]; eassumption.
Qed.

Lemma open_simeq_cons : consistent open_simeq.
Proof.
  unfold consistent; intros.
  apply (H nil nil I).
Qed.

Scheme types_Ind := Induction for types Sort Prop.
