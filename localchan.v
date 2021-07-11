From iris.bi.lib Require Import fractional.
From iris.bi Require Import atomic derived_laws interface.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
Import uPred.


From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode.
Set Default Proof Using "Type".

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)
(* In [Iris 1.0 Paper] --
      See "Stack Item 2 : Local channel assertions" and
      "Stack Item 3 : Channels with blocking recv" in [Figure 1]. *)

Section atomic_invariants.

  Context `{!chanG Σ}.

  Notation iProp := (iProp Σ).

  Notation "'val'" := chan_lang.val.

  Lemma awp_send (c : loc) (M : gset val) (m : val) :
    ⊢ <<< c ↦ M >>> send(c, m) @ ⊤ <<< c ↦ (M ∪ {[m]}), RET #() >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as "[H↦ [_ Hclose]]".
    match goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
        reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ _ _ _ _ K))
    end.
    - iSolveTC.
    - iAssumptionCore.
    - pm_reduce; first [wp_finish].
      iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  (* To start off, let's try defining a blocking receive. *)
  Definition recv : chan_lang.val :=
    rec: "loop" "c" :=
      let: "v" := TryRecv "c" in
      match: "v" with
        NONE => "loop" "c"
      | SOME "m" => "m"
      end.

  Lemma tac_wp_tryrecv_fail Δ Δ' s E l K Φ M i:
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦ M)%I →
    M = ∅ -> envs_entails Δ' (WP fill K (Val $ NONEV) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (TryRecv (LitV $ LitLoc l)) @ s; E {{ Φ }}).
  Proof.
    intros H1 H2.
    rewrite envs_entails_eq=> Heq Hfail.
    rewrite -wp_bind. eapply wand_apply.
    { eapply wp_tryrecv_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r.
    apply wand_mono; auto.
    rewrite Heq. done.
  Qed.

  (* IY: Not sure how to define this.. Naive attempts failed. *)
  Lemma tac_wp_tryrecv_suc Δ Δ' s E l K Φ M i:
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    (* IY: How do we express that "the precondition [M]" is an existentially
      quantified state? *)
    M ≠ ∅ ->
    envs_lookup i Δ' = Some (false, l ↦ M)%I →
    (exists v,
        match envs_simple_replace i false (Esnoc Enil i (l ↦ (M∖{[v]}))) Δ' with
      | Some Δ'' =>
      envs_entails Δ' (WP fill K (Val $ SOMEV v) @ s; E [{ Φ }])
        | None => False
     end
    ) →
    envs_entails Δ (WP fill K (TryRecv (LitV $ LitLoc l)) @ s; E {{ Φ }}).
  Proof.
    (* intros Ne H1. *)
    (* rewrite envs_entails_eq=> Heq Hsuc. *)
    (* rewrite -wp_bind. eapply wand_apply. *)
    (* { eapply wp_tryrecv_suc; eauto. Unshelve. 2 : exact (M ∪ {[v]}). set_solver. } *)

    (* destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
    (* rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl. *)
    (* apply later_mono, sep_mono_r. *)
    (* apply forall_intro=> v'. *)
    (* apply wand_intro_r. *)
    (* rewrite sep_elim_l. *)
    (* rewrite right_id. *)
    (* rewrite Hsuc. *)
    (* Unshelve. 2 : exact v'. *)
  Admitted.

  Ltac wp_pures :=
    iStartProof;
    first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
            progress repeat (wp_pure _; [])
          | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
          ].

  Lemma awp_recv (c : loc) (m : val):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤ <<< c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET m >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind (tryrecv _)%E.
    iMod "AU" as (M) "[Hl [Hclose _]]".
    destruct (decide (M = ∅)) as [[= ->]|Hx].
    - (* Empty set : Returns none. *)
      match goal with
      | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
          reshape_expr e ltac:(fun K e' => eapply (tac_wp_tryrecv_fail _ _ _ _ _ K))
      end.
      + iSolveTC.
      + let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
        iAssumptionCore.
      + reflexivity.
      + pm_reduce. intros. wp_finish.
        iMod ("Hclose" with "Hl") as "HΦ".
        iModIntro. wp_pures. iApply "IH". done.

    - (* Non-empty : update the state. *)
      match goal with
      | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
          reshape_expr e ltac:(fun K e' => eapply (tac_wp_tryrecv_suc _ _ _ _ _ K))
      end.
      + iSolveTC.
      + eauto.
      + iAssumptionCore.
      + pm_reduce.
        assert (∃ x : val, x ∈ M).
        { unfold_leibniz. eapply set_choose in Hx. eauto. }

        destruct H as (v & IN).
        exists v.
        wp_pures.
        (* iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hl") as "HΦ". *)

        (* iMod ("Hclose" with "Hl") as "AU". *)
        (* iModIntro. *)

        (* iMod "AU" as (M') "[Hl [Hclose _]]". *)
        (* wp_pures. *)
  Admitted.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
