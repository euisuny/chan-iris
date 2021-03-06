From iris.algebra Require Import gmap_view frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Class gen_networkGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_networkGpreS_inG :> inG Σ (gmap_viewR L (leibnizO V));
}.

Class gen_networkGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenNetworkGS {
  gen_network_inG :> gen_networkGpreS L V Σ;
  gen_network_name : gname;
}.
Global Arguments GenNetworkGS L V Σ {_ _ _} _: assert.
Global Arguments gen_network_name {L V Σ _ _} _ : assert.

Definition gen_networkΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (gmap_viewR L (leibnizO V))
].

Global Instance subG_gen_networkGpreS {Σ L V} `{Countable L} :
  subG (gen_networkΣ L V) Σ → gen_networkGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_networkGS L V Σ}.

  Definition gen_network_interp (σ : gmap L V) : iProp Σ :=
    own (gen_network_name hG) (gmap_view_auth 1 (σ : gmap L (leibnizO V))).

  Definition mapsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    own (gen_network_name hG) (gmap_view_frag l dq (v : leibnizO V)).
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_network.
  Context {L V} `{Countable L, !gen_networkGS L V Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap L V) (l : L) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite mapsto_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_frag_op_valid_L.
    auto.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (mapsto_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** Update lemmas *)
  Lemma gen_network_alloc σ l v :
    σ !! l = None →
    gen_network_interp σ ==∗ gen_network_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_network_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (gmap_view_alloc _ l (DfracOwn 1)); done. }
    iModIntro. iFrame.
  Qed.

  Lemma gen_network_valid σ l dq v : gen_network_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_network_interp mapsto_eq.
    by iDestruct (own_valid_2 with "Hσ Hl") as %[??]%gmap_view_both_valid_L.
  Qed.

  Lemma gen_network_update σ l v1 v2 :
    gen_network_interp σ -∗ l ↦ v1 ==∗ gen_network_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_network_interp mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %[_ Hl]%gmap_view_both_valid_L.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply gmap_view_update. }
    iModIntro. iFrame.
  Qed.
End gen_network.
