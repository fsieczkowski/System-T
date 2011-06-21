(** This file defines the single and multiple substitutions. Since we only ever
    substitute closed terms, multiple substitution can be defined in terms of the
    single one. *)

Require Export Syntax.
Require Export Arith.
Open Scope t_scope.
Open Scope list_scope.

Reserved Notation " [ γ ! n ] M " (at level 5).
Reserved Notation " [ K ↑ n ] M " (at level 5).

(* Substitution of index n for term K in M *)
Fixpoint subt K n M :=
  match M with
    | #m => if (eq_nat_dec n m) then K else M
    | λ A, M => λ A, [K ↑ S n]M
    | M @ N => [K ↑ n]M @ [K ↑ n]N
    | z => z
    | s M => s [K ↑ n]M
    | rec M M₀ M₁ => rec [K ↑ n]M [K ↑ n]M₀ [K ↑ S (S n)]M₁
    | hd M => hd [K ↑ n]M
    | tl M => tl [K ↑ n]M
    | seed M M₀ M₁ => seed [K ↑ n]M [K ↑ S n]M₀ [K ↑ S n]M₁
  end where " [ K ↑ n ] M " := (subt K n M) : t_scope.

(* Substitution for the list γ, starting from index n in M *)
Fixpoint sub (γ : list te) (n : nat) (M : te) :=
  match γ with
    | nil => M
    | K :: γ => [K ↑ n][γ ! S n]M
  end where " [ γ ! n ] M " := (sub γ n M) : t_scope.

(* Substitutions are composable if they don't miss an index *)
Lemma subcomp : forall γ δ n M,
  ([γ ! n][δ ! n + length γ]M) = [γ ++ δ ! n]M.
Proof.
  induction γ; intros; simpl in *; rewrite plus_comm; simpl; [tauto |].
  rewrite plus_comm, IHγ; reflexivity.
Qed.

(* Boring lemmas about pushing substitutions through constructors *)

Lemma subst_gt : forall γ n m
  (Hlt : n < m),
  #n = [γ ! m](#n).
Proof.
  induction γ; simpl; intros; [reflexivity |].
  rewrite <- IHγ; [| auto with arith].
  simpl.
  destruct (eq_nat_dec m n); [| reflexivity].
  subst; contradict Hlt; auto with arith.
Qed.
Lemma sub_lam : forall γ n A M,
  ([γ ! n]λ A, M) = λ A, [γ ! S n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_app : forall γ n M N,
  ([γ ! n](M @ N)) = [γ ! n]M @ [γ ! n]N.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_z : forall γ n,
  ([γ ! n]z) = z.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_s : forall γ n M,
  ([γ ! n](s M)) = s [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_rec : forall γ n M M₀ M₁,
  ([γ ! n](rec M M₀ M₁)) = rec [γ ! n]M [γ ! n]M₀ [γ ! S (S n)]M₁.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_hd : forall γ n M,
  ([γ ! n](hd M)) = hd [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_tl : forall γ n M,
  ([γ ! n](tl M)) = tl [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_seed : forall γ n M M₀ M₁,
  ([γ ! n](seed M M₀ M₁)) = seed [γ ! n]M [γ ! S n]M₀ [γ ! S n]M₁.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.

Close Scope list_scope.
Close Scope t_scope.