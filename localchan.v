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

  Lemma awp_send (c : loc) (m : val) :
    ⊢ <<< ∀ M, c ↦ M >>> send(c, m) @ ⊤ <<< c ↦ (M ∪ {[m]}), RET #() >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as (M) "[H↦ [_ Hclose]]".
    (* TODO: define [wp_send] *)
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

  Lemma awp_recv (c : loc):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤
      <<< ∃ m, c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET m >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam.
    wp_bind (tryrecv _)%E.
    iMod "AU" as (M) "[Hl Hclose]".
    destruct (decide (M = ∅)) as [[= ->]|Hx].
    - (* Empty set : Returns none. *)
      iDestruct "Hclose" as "[Hclose _]".
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
      iDestruct "Hclose" as "[_ Hclose]".
      iApply (wp_tryrecv_suc with "Hl"); auto.
      iNext. iIntros (v) "HΦ".
      iMod ("Hclose" with "HΦ") as "HΦ".
      iModIntro. wp_pures. done.
  Qed.

End atomic_invariants.
