From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
From iris.bi Require Import atomic derived_laws interface.
Import uPred.

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode.
Set Default Proof Using "Type".

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)

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
    - let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
        iAssumptionCore.
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

  Lemma tac_wp_tryrecv Δ Δ' s E l K Φ M i:
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦ M)%I →
    (* This condition is very fishy. TODO *)
    (forall v, M ≠ ∅ -> v ∈ M -> envs_entails Δ' (WP fill K (Val $ SOMEV v) @ s; E {{ Φ }})) ->
    (M = ∅ -> envs_entails Δ' (WP fill K (Val $ NONEV) @ s; E {{ Φ }})) →
    envs_entails Δ (WP fill K (TryRecv (LitV $ LitLoc l)) @ s; E {{ Φ }}).
  Proof.
    intros H1 H2.
    rewrite envs_entails_eq=> Hsuc Hfail.
    destruct (decide (M = ∅)) as [Heq|Hne].
    - (* NONE *)
      specialize (Hfail Heq).
      rewrite -wp_bind. eapply wand_apply.
      { eapply wp_tryrecv_fail; eauto. }
      rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
      apply later_mono, sep_mono_r.
      apply wand_mono; auto.
      rewrite Heq. done.

    - (* SOME *)
      clear Hfail.
      (* destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
      rewrite -wp_bind. eapply wand_apply.
      { eapply wp_tryrecv_suc; eauto. }
      rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
      (* envs_simple_replace_sound //; simpl. *)
      (* rewrite right_id. *)
      apply later_mono, sep_mono_r; eauto.
      apply forall_intro=> v'.
      apply wand_intro_r.
      rewrite sep_elim_l.
      specialize (Hsuc v').
      (* destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
      (* specialize (Hsuc Hne). rewrite -Hsuc. *)
      (* rewrite envs_simple_replace_sound //; simpl. *)
      (* rewrite sep_elim_r. *)
      (* rewrite right_id. *)
      (* iIntros "HΦ". iApply "HΦ". *)
      (* + *)
      (* Contradiction here? ? *)
  Admitted.

  Ltac wp_pures :=
    iStartProof;
    first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
            progress repeat (wp_pure _; [])
          | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
          ].

  Lemma awp_recv (c : loc) (m : val):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤
      <<< c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_bind (tryrecv _)%E. iMod "AU" as (M) "[Hl [Hclose _]]".
    match goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
        reshape_expr e ltac:(fun K e' => eapply (tac_wp_tryrecv _ _ _ _ _ K))
    end.
    - iSolveTC.
    - let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
        iAssumptionCore.
    - (* Some *)
      pm_reduce. intros. wp_finish.
      iMod ("Hclose" with "Hl") as "HΦ".
      iModIntro. wp_pures.
      admit.
    - (* None *)
      pm_reduce. intros. wp_finish.
      iMod ("Hclose" with "Hl") as "HΦ".
      iModIntro. wp_pures. iApply "IH". done.
   Abort.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
