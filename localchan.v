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

  Ltac wp_pures :=
    iStartProof;
    first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
            progress repeat (wp_pure _; [])
          | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
          ].

  Ltac wp_apply_core lem tac_suc tac_fail := first
    [iPoseProofCore lem as false (fun H =>
      lazymatch goal with
      | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
        reshape_expr e ltac:(fun K e' =>
          wp_bind_core K; tac_suc H)
      | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
        reshape_expr e ltac:(fun K e' =>
          twp_bind_core K; tac_suc H)
      | _ => fail 1 "wp_apply: not a 'wp'"
      end)
    |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
    |let P := type of lem in
    fail "wp_apply: cannot apply" lem ":" P ].

  Tactic Notation "wp_apply" open_constr(lem) :=
    wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                      ltac:(fun cont => fail).
  Tactic Notation "wp_smart_apply" open_constr(lem) :=
    wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                      ltac:(fun cont => wp_pure _; []; cont ()).


  Lemma awp_recv (c : loc) (m : val):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤ <<< c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET m >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam.
    wp_bind (tryrecv _)%E.
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
      iApply (wp_tryrecv_suc with "Hl"); auto.
      iNext. iIntros (v) "HΦ".
      (* IY: "Hclose" needs to be updated but wp_tryrecv_suc does not take a WP
        condition.. *)
  Admitted.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
