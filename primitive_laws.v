From iris.program_logic Require Export ectx_lifting total_ectx_lifting weakestpre.
From iris.proofmode Require Import tactics.
From chanlang Require Import lang notation network_ra tactics.
From iris Require Import options.
From iris.base_logic.lib Require Import invariants.

(* Ghost state for reasoning about chan_lang threadpool. *)
Class chanG Σ :=
  ChanG {
      chan_invG : invG Σ;
      chan_gen_networkG :> gen_networkGS loc (option (gset val)) Σ;
    }.

Global Instance chan_irisG `{!chanG Σ} : irisG chan_lang Σ :=
  {
  iris_invG := chan_invG;
  state_interp σ _ κs _ := (gen_network_interp σ.(chan))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section proof.
  Context `{!chanG Σ}.

  Notation iProp := (iProp Σ).

  Definition true : iProp := ⌜ True ⌝.

  Definition wp_newch :
    {{{ true }}} newch {{{ l, RET LitV (LitLoc l); l ↦ Some ∅ }}}.
  Proof.
    iIntros (Φ) "Pre Post".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>"; iSplit; first by auto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_network_alloc σ1.(chan) c empty with "Hσ") as "[Hσ Hl]"; first done.
    iModIntro. iFrame. iApply "Post".
    iApply "Hl".
  Qed.

  Definition threadpool := gmap loc (option (gset val)).

  (* Definition recv_inv v (P : iProp) (Q : threadpool -> chan_lang.val -> iProp) : iProp := *)
  (*   (P ∗ ⌜v = NONE⌝ ∨ ∃ M m, Q M m ∗ ⌜v = SOMEV m⌝)%I. *)

  (* Definition is_recv P Q v := *)
  (*   inv N (recv_inv v P Q). *)

  (* (* Section 7.2 Proof of blocking receive (10) *) *)
  (* Lemma wp_tryrecv P (Q : threadpool -> chan_lang.val -> iProp) c : *)
  (*   {{{ P }}} tryrecv c {{{ v , RET v; is_recv P Q v }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "P Q". *)
  (*   iApply wp_lift_atomic_head_step; [done|]. *)
  (*   iIntros (σ1 ns κ κs nt) "Hσ !>". iSplit. *)
  (*   (* - first by euto with head_step. iMod "Q (tryrecv c)". *) *)
  (*   (*   unfold head_reducible. iExists _, _, _, _. iSimpl. *) *)
  (*   (*   iMod "Q".  as  "_". *) *)
  (* Admitted. *)

End proof.
