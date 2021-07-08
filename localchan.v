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

  Lemma tac_wp_tryrecv Δ Δ' s E l K Φ v M i:
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦ M)%I →
    match envs_simple_replace i false (Esnoc Enil i (l ↦ (M∖{[v]}))) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ v) @ s; E {{ Φ }})
    | None => False
    end ->
    envs_entails Δ (WP fill K (TryRecv (LitV $ LitLoc l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq=> ??.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    intros H.
    rewrite -wp_bind. eapply wand_apply.
      { eapply wp_tryrecv; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply forall_intro=>v'.
    apply wand_mono; auto;cycle 1.
    - iIntros. iApply H.
    - apply or_elim. iIntros "H".

        * iIntros "H". iDestruct "H" as (h h'). iDestruct "H"
        match goal with
        | |- context[bi_or ?P ?Q] => remember P; remember Q
        end. apply or_elim.
        subst.
  Admitted.

  Lemma awp_recv (c : loc) (m : val):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤
      <<< c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_bind (tryrecv _)%E. iMod "AU" as (M) "[Hl [Hclose _]]".
    (* iApply tac_wp_tryrecv. *)
    (* wp_recv. *)
   Abort.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
