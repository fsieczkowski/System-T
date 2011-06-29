Require Import Termination.
Require Import Setoid.

Open Scope t_scope.
Open Scope list_scope.

Reserved Notation " M ≃ N " (at level 70).
Inductive Eq2 M N : Prop :=
| equivT : forall
    (HRedM : M ↦* TT)
    (HRedN : N ↦* TT),
    M ≃ N
| equivF : forall
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
    | ct_lam A E     => λ A, plug E M
    | ct_appR N E    => N @ (plug E M)
    | ct_appL N E    => (plug E M) @ N
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

(* TODO Define context typing inductively and prove the property below holds *)
Reserved Notation " E ::: [ Γ , A ] → [ Δ , B ] " (at level 70).

Inductive tyctx : ctx -> list ty -> ty -> list ty -> ty -> Prop :=
| cty_hole   : forall Γ A, hole ::: [Γ, A] → [Γ, A]
| cty_lam    : forall Γ Δ A B C E
    (HCT : E ::: [Γ, B] → [A :: Δ, C]),
    ct_lam A E ::: [Γ, B] → [Δ, A → C]
| cty_appL   : forall Γ Δ A B C E M
    (HCT : E ::: [Γ, A] → [Δ, B → C])
    (HTR : Δ ⊢ M ::: B),
    ct_appL M E ::: [Γ, A] → [Δ, C]
| cty_appR   : forall Γ Δ A B C E M
    (HCT : E ::: [Γ, A] → [Δ, B])
    (HTR : Δ ⊢ M ::: B → C),
    ct_appR M E ::: [Γ, A] → [Δ, C]
| cty_s      : forall Γ Δ A E
    (HCT : E ::: [Γ, A] → [Δ, ω]),
    ct_s E ::: [Γ, A] → [Δ, ω]
| cty_rec0   : forall Γ Δ A B M₀ M₁ E
    (HCT : E ::: [Γ, A] → [Δ, ω])
    (HT0 : Δ ⊢ M₀ ::: B)
    (HT1 : ω :: B :: Δ ⊢ M₁ ::: B),
    ct_rec0 M₀ M₁ E ::: [Γ, A] → [Δ, B]
| cty_rec1   : forall Γ Δ A B M M₁ E
    (HCT : E ::: [Γ, A] → [Δ, B])
    (HTM : Δ ⊢ M ::: ω)
    (HT1 : ω :: B :: Δ ⊢ M₁ ::: B),
    ct_rec1 M M₁ E ::: [Γ, A] → [Δ, B]
| cty_rec2   : forall Γ Δ A B M M₀ E
    (HCT : E ::: [Γ, A] → [ω :: B :: Δ, B])
    (HTM : Δ ⊢ M ::: ω)
    (HT1 : Δ ⊢ M₀ ::: B),
    ct_rec2 M M₀ E ::: [Γ, A] → [Δ, B]
| cty_hd     : forall Γ Δ A B E
    (HCT : E ::: [Γ, A] → [Δ, stream B]),
    ct_hd E ::: [Γ, A] → [Δ, B]
| cty_tl     : forall Γ Δ A B E
    (HCT : E ::: [Γ, A] → [Δ, stream B]),
    ct_tl E ::: [Γ, A] → [Δ, stream B]
| cty_seed0  : forall Γ Δ A B M₀ M₁ E
    (HCT : E ::: [Γ, A] → [Δ, B])
    (HT0 : B :: Δ ⊢ M₀ ::: B)
    (HT1 : B :: Δ ⊢ M₁ ::: B),
    ct_sd0 M₀ M₁ E ::: [Γ, A] → [Δ, stream B]
| cty_seed1  : forall Γ Δ A B M M₁ E
    (HCT : E ::: [Γ, A] → [B :: Δ, B])
    (HTM : Δ ⊢ M ::: B)
    (HT1 : B :: Δ ⊢ M₁ ::: B),
    ct_sd1 M M₁ E ::: [Γ, A] → [Δ, stream B]
| cty_seed2  : forall Γ Δ A B M M₀ E
    (HCT : E ::: [Γ, A] → [B :: Δ, B])
    (HTM : Δ ⊢ M ::: B)
    (HT1 : B :: Δ ⊢ M₀ ::: B),
    ct_sd2 M M₀ E ::: [Γ, A] → [Δ, stream B]

where " E ::: [ Γ , A ] → [ Δ , B ] " := (tyctx E Γ A Δ B).

Lemma context_type : forall {E Γ Δ A B M}
  (HCT : E ::: [Γ, A] → [Δ, B])
  (HMT : Γ ⊢ M ::: A),
  Δ ⊢ plug E M ::: B.
Proof.
  induction 1; intros; simpl in *; eauto using types.
Qed.

Lemma context_comp : forall {E F Γ Δ Σ A B C}
  (HC1 : F ::: [Δ, B] → [Σ, C])
  (HC2 : E ::: [Γ, A] → [Δ, B]),
  F · E ::: [Γ, A] → [Σ, C].
Proof.
  intros; generalize dependent Γ; revert A E; induction HC1;
    intros; simpl in *; eauto using tyctx.
Qed.

Definition obs_eq Γ A (M N : {K : te | Γ ⊢ K ::: A}) :=
  forall E (HTE : E ::: [ Γ, A ] → [ nil, 2 ]),
    plug E (proj1_sig M) ≃ plug E (proj1_sig N).
Notation " Γ ⊢ M == N ::: A " := (obs_eq Γ A M N) (at level 70).

Section Defs.
  Variable P : forall Γ A, relation {K : te | Γ ⊢ K ::: A}.

  Definition consistent :=
    forall M N, P nil 2 M N -> proj1_sig M ≃ proj1_sig N.

  Definition closed :=
    forall {E Γ Δ A B M N}
      (HTE  : E ::: [Γ, A] → [Δ, B])
      (HPMN : P Γ A M N),
      (P Δ B (exist _ (plug E (proj1_sig M)) (context_type HTE (proj2_sig M)))
        (exist _ (plug E (proj1_sig N)) (context_type HTE (proj2_sig N)))).

  Record ConsCong :=
    { Cong_Equiv  : forall Γ A, Equivalence (P Γ A);
      Cong_Cons   : consistent;
      Cong_Closed : closed}.

End Defs.

Lemma obs_eq_cong : ConsCong obs_eq.
Proof.
  split; intros.
  split; unfold Reflexive, Symmetric, Transitive; intros.
  (* refl *)
  unfold obs_eq; intros.
  destruct x.
  eauto using Eq2_type_refl, @context_type.
  (* symm *)
  unfold obs_eq; intros; symmetry; apply H; assumption.
  (* tran *)
  unfold obs_eq; intros; etransitivity; eauto; fail.
  (* cons *)
  unfold consistent; intros.
  specialize (H hole); simpl in H; apply H.
  constructor.
  (* cong *)
  unfold closed, obs_eq; intros; simpl in *.
  simpl; rewrite !plug_compose; apply HPMN.
  eapply context_comp; eauto.
Qed.

Lemma obs_eq_coarsest :
  forall (P : forall Γ A, relation {K : te | Γ ⊢ K ::: A})
    (HCC : ConsCong P)
    Γ A M N (HIn : P Γ A M N),
    Γ ⊢ M == N ::: A.
Proof.
  unfold obs_eq; intros.
  destruct HCC as [Equiv Cons Cong].
  unfold consistent in Cons.
  specialize (Cons (exist _ (plug E (proj1_sig M)) (context_type HTE (proj2_sig M))) (exist _ (plug E (proj1_sig N)) (context_type HTE (proj2_sig N)))); simpl in Cons; apply Cons; clear Cons.
  apply Cong; assumption.
Qed.

(* Logical Equivalence *)

Reserved Notation " M ≡ N ::: A " (at level 70).

Fixpoint log_equiv (A : ty) (M N : te) : Prop :=
  match A with
    | 2 => M ≃ N
    | ω => Eqω M N
    | A₁ → A₂ => forall M' N' (HEq : M' ≡ N' ::: A₁), M @ M' ≡ N @ N' ::: A₂
    | stream A => Eqs (log_equiv A) M N
  end where " M ≡ N ::: A " := (log_equiv A M N) : t_scope.

Instance log_equiv_symm A : Symmetric (log_equiv A).
Proof.
  induction A; eauto with typeclass_instances.
  (* arrow *)
  unfold Symmetric; simpl; intros.
  symmetry; eapply H; symmetry; eassumption.
  (* stream *)
  unfold Symmetric; simpl; apply Eqs_sym; assumption.
Qed.

Instance log_equiv_trans A : Transitive (log_equiv A).
Proof.
  induction A; eauto with typeclass_instances.
  (* arrow *)
  unfold Transitive; simpl; intros.
  assert (HEq' : N' ≡ N' ::: A1) by (etransitivity; [symmetry |]; eassumption).
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

Hint Rewrite sub_lam sub_app sub_z sub_s sub_rec sub_hd sub_tl sub_seed
  sub_TT sub_FF : sub.

Ltac msimp :=
  autorewrite with sub.

Lemma head_expansion : forall A M M' N
  (HR : M' ≡ N ::: A)
  (HS : M ↦ M'),
  M ≡ N ::: A.
Proof.
  induction A; intros; simpl in *.
  (* bool *)
  inversion HR; [ apply equivT | apply equivF ]; auto; econstructor; eauto.
  (* nat *)
  inversion HR; subst; clear HR.
    apply Eqωz; auto; econstructor; eassumption.
  eapply Eqωs; eauto; econstructor; eassumption.
  (* arr *)
  intros.
  eapply IHA2; [| apply red_appC; eassumption].
  apply HR; assumption.
  (* stream *)
  generalize dependent M'; revert N M.
  cofix; intros.
  inversion HR; subst; clear HR; apply EqS.
    eapply IHA; [eassumption | apply red_hdC; eassumption].
  eapply head_expansion; eauto using step.
Qed.

(* lifting of head expansion to reflexive transitive closure *)
Lemma head_exp_star : forall A M M' N
  (HR : M' ≡ N ::: A)
  (HS : M ↦* M'),
  M ≡ N ::: A.
Proof.  
  intros; induction HS; [assumption |].
  eapply head_expansion; [| eassumption].
  tauto.
Qed.

Lemma refl : forall Γ A, Reflexive (open_simeq Γ A).
Proof.
  unfold Reflexive; intros.
  destruct x as [M HMT].
  induction HMT using types_Ind;
    unfold open_simeq; simpl; intros; msimp;
      eauto using Eq2_type_refl, types.
  (* var *)
  replace n with (0 + n) by reflexivity; generalize 0; generalize dependent n;
    generalize dependent γ₂; revert γ₁; induction Γ; intros;
      destruct γ₁; destruct γ₂; try contradiction.
    destruct n; inversion HFind.
  destruct n; simpl in *; [inversion HFind; subst; clear HFind |].
    rewrite plus_comm; simpl; rewrite <- !subst_gt; simpl; auto with arith.
    destruct (eq_nat_dec n0 n0); tauto.
  admit (* add typings *).
  (* lam *)
  eapply head_expansion; eauto using step.
  symmetry; eapply head_expansion; eauto using step.
  symmetry.
  rewrite !subcomp; eapply IHHMT; simpl; auto.
  (* app *)
  specialize (IHHMT1 _ _ HEΓ); simpl in IHHMT1; apply IHHMT1.
  specialize (IHHMT2 _ _ HEΓ); simpl in IHHMT2; apply IHHMT2.
  (* z *)
  repeat constructor.
  (* s *)
  apply IHHMT in HEΓ; simpl in *.
  eapply Eqωs; eauto; constructor.
  (* rec *)
  specialize (IHHMT1 _ _ HEΓ); simpl in *.
  revert IHHMT1; generalize [γ₁ ! 0]M; generalize [γ₂ ! 0]M;
    intros K L HKL; induction HKL.
    eapply head_exp_star; eauto using rec_cong_star.
    eapply head_expansion; eauto using step; symmetry.
    eapply head_exp_star; eauto using rec_cong_star.
    eapply head_expansion; eauto using step; symmetry.
    eapply IHHMT2; eauto.
  eapply head_exp_star; eauto using rec_cong_star.
  eapply head_expansion; eauto using step; symmetry.
  eapply head_exp_star; eauto using rec_cong_star.
  eapply head_expansion; eauto using step; symmetry.
  rewrite !subcomp.
  eapply IHHMT3; simpl; eauto.
  (* hd *)
  apply IHHMT in HEΓ; simpl in *; inversion HEΓ; subst; clear HEΓ; auto.
  (* tl *)
  apply IHHMT in HEΓ; simpl in *; inversion HEΓ; subst; clear HEΓ; auto.
  (* seed *)
  specialize (IHHMT1 _ _ HEΓ); simpl in *.
  assert (exists K, exists L,
    (seed [γ₁ ! 0]M [γ₁ ! 1]M₀ [γ₁ ! 1]M₁ ↦* seed K [γ₁ ! 1] M₀ [γ₁ ! 1]M₁) /\
    (seed [γ₂ ! 0]M [γ₂ ! 1]M₀ [γ₂ ! 1]M₁ ↦* seed L [γ₂ ! 1] M₀ [γ₂ ! 1]M₁) /\
    K ≡ L ::: A).
    repeat eexists; repeat split; try constructor; assumption.
  destruct H as [K [L [HRedK [HRedL HEq]]]].
  generalize dependent L; generalize dependent K.
  generalize (seed [γ₁ ! 0]M [γ₁ ! 1]M₀ [γ₁ ! 1]M₁) as MM;
    generalize (seed [γ₂ ! 0]M [γ₂ ! 1]M₀ [γ₂ ! 1]M₁) as NN.
  cofix; intros; apply EqS.
    eapply head_exp_star; eauto using hd_cong_star.
    eapply head_expansion; eauto using step; symmetry.
    eapply head_exp_star; eauto using hd_cong_star.
    eapply head_expansion; eauto using step; symmetry.
    change ([K :: nil ! 0]([γ₁ ! 1]M₀) ≡ [L :: nil ! 0]([γ₂ ! 1]M₀) ::: A);
      rewrite !subcomp; eapply IHHMT2; simpl; tauto.
  eapply refl.
    apply clos_rt_rt1n; eapply rt_trans;
      [apply clos_rt1n_rt, tl_cong_star; eassumption |];
      eauto using rt_step, step.
    apply clos_rt_rt1n; eapply rt_trans;
      [apply clos_rt1n_rt, tl_cong_star; eassumption |];
      eauto using rt_step, step.
  replace ([K ↑ 0][γ₁ ! 1]M₁) with ([K :: nil ! 0][γ₁ ! 1]M₁) by reflexivity;
    replace ([L ↑ 0][γ₂ ! 1]M₁) with ([L :: nil ! 0][γ₂ ! 1]M₁) by reflexivity.
  rewrite !subcomp; eapply IHHMT3; simpl; eauto.
Qed.

Scheme tyctx_Ind := Induction for tyctx Sort Prop.

Lemma seed_cong : forall M M₀ M₁ N N₀ N₁ K L A
  (HMN  : M ≡ N ::: A)
  (HMN₀ : forall K L, K ≡ L ::: A -> [K ↑ 0]M₀ ≡ [L ↑ 0]N₀ ::: A)
  (HMN₁ : forall K L, K ≡ L ::: A -> [K ↑ 0]M₁ ≡ [L ↑ 0]N₁ ::: A)
  (HRK  : K ↦* seed M M₀ M₁)
  (HRL  : L ↦* seed N N₀ N₁),
  K ≡ L ::: stream A.
Proof.
  intros; simpl; generalize dependent M; generalize dependent N; revert K L.
  cofix; intros; simpl; apply EqS.
    do 2 (eapply head_exp_star; eauto using hd_cong_star;
      eapply head_expansion; eauto using step; symmetry); auto.
  eapply seed_cong.
    apply clos_rt_rt1n; eapply rt_trans;
      [apply clos_rt1n_rt, tl_cong_star; eassumption |];
      eauto using rt_step, step.
    eauto.
  apply clos_rt_rt1n; eapply rt_trans;
    [apply clos_rt1n_rt, tl_cong_star; eassumption |];
    eauto using rt_step, step.
Qed.

Lemma rec_cong : forall M M₀ M₁ N N₀ N₁ A
  (HMN  : M ≡ N ::: ω)
  (HMN₀ : M₀ ≡ N₀ ::: A)
  (HMN₁ : forall K L K₀ L₀, K ≡ L ::: ω -> K₀ ≡ L₀ ::: A ->
    [K :: K₀ :: nil ! 0]M₁ ≡ [L :: L₀ :: nil ! 0]N₁ ::: A),
  rec M M₀ M₁ ≡ rec N N₀ N₁ ::: A.
Proof.
  intros; induction HMN;
    do 2 (eapply head_exp_star; eauto using rec_cong_star;
      eapply head_expansion; eauto using step; symmetry); auto.
Qed.

Lemma cong_log_equiv : closed open_simeq.
Proof.
  unfold closed; intros.
  revert M N HPMN; induction HTE using tyctx_Ind; intros; simpl;
    unfold open_simeq; simpl; intros; msimp.
  (* hole *)
  apply HPMN; assumption.
  (* lam *)
  eapply head_expansion; eauto using step; symmetry.
  eapply head_expansion; eauto using step; symmetry.
  rewrite !subcomp.
  eapply IHHTE; simpl; eauto.
  (* appL *)
  eapply IHHTE; eauto.
  fold ([γ₁ ! 0]M ≡ [γ₂ ! 0]M ::: B).
  assert (HT := refl Δ B (exist _ M HTR)); eapply HT; eauto.
  (* appR *)
  assert (HT := refl _ _ (exist _ M HTR)); eapply HT; eauto.
  fold log_equiv.
  eapply IHHTE; eauto.
  (* s *)
  eapply Eqωs; [constructor | constructor |].
  eapply IHHTE; eauto.
  (* rec arg *)
  eapply rec_cong.
  apply IHHTE; auto.
  eapply (refl _ _ (exist _ M₀ HT0)); assumption.
  intros; rewrite !subcomp;
    eapply (refl _ _ (exist _ M₁ HT1)); simpl; auto.
  (* rec base *)
  eapply rec_cong.
  eapply (refl _ _ (exist _ M HTM)); simpl; auto.
  apply IHHTE; auto.
  intros; rewrite !subcomp;
    eapply (refl _ _ (exist _ M₁ HT1)); simpl; auto.
  (* rec step *)
  eapply rec_cong.
  eapply (refl _ _ (exist _ M HTM)); simpl; auto.
  eapply (refl _ _ (exist _ M₀ HT1)); auto.
  intros; rewrite !subcomp; apply IHHTE; simpl; auto.
  (* hd *)
  eapply IHHTE in HEΓ; eauto; simpl in *.
  inversion HEΓ; auto.
  (* tl *)
  eapply IHHTE in HEΓ; eauto; simpl in *.
  inversion HEΓ; auto.
  (* seed arg *)
  eapply seed_cong; try (constructor; fail).
  apply IHHTE; auto.
  intros; change ([K :: γ₁ ! 0]M₀ ≡ [L :: γ₂ ! 0]M₀ ::: B).
  apply (refl _ _ (exist _ M₀ HT0)); simpl; auto.
  intros; change ([K :: γ₁ ! 0]M₁ ≡ [L :: γ₂ ! 0]M₁ ::: B).
  apply (refl _ _ (exist _ M₁ HT1)); simpl; auto.
  (* seed hd *)
  eapply seed_cong; try (constructor; fail).
  apply (refl _ _ (exist _ M HTM)); simpl; auto.
  intros; change ([K :: γ₁ ! 0](plug E (proj1_sig M0)) ≡ [L :: γ₂ ! 0](plug E (proj1_sig N)) ::: B).
  apply IHHTE; simpl; auto.
  intros; change ([K :: γ₁ ! 0]M₁ ≡ [L :: γ₂ ! 0]M₁ ::: B).
  apply (refl _ _ (exist _ M₁ HT1)); simpl; auto.
  (* seed tl *)
  eapply seed_cong; try (constructor; fail).
  apply (refl _ _ (exist _ M HTM)); simpl; auto.
  intros; change ([K :: γ₁ ! 0]M₀ ≡ [L :: γ₂ ! 0]M₀ ::: B).
  apply (refl _ _ (exist _ M₀ HT1)); simpl; auto.
  intros; change ([K :: γ₁ ! 0](plug E (proj1_sig M0)) ≡ [L :: γ₂ ! 0](plug E (proj1_sig N)) ::: B).
  apply IHHTE; simpl; auto.
Qed.