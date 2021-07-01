From iris.program_logic Require Export ectx_lifting total_ectx_lifting weakestpre.
From iris.proofmode Require Import tactics.
From chanlang Require Import lang notation network_ra tactics.
From iris Require Import options.
From iris.base_logic.lib Require Import invariants.

(* Ghost state for reasoning about chan_lang threadpool. *)
Class chanG Σ :=
  ChanG {
      chan_invG : invG Σ;
      chan_gen_networkG :> gen_networkGS loc (gset val) Σ;
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

  (* Figure 11. Derived rules for language primitives *)
  Definition wp_newch :
    {{{ true }}} newch {{{ l, RET LitV (LitLoc l); l ↦ ∅ }}}.
  Proof.
    iIntros (Φ) "Pre Post".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>"; iSplit; first by auto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_network_alloc σ1.(chan) c empty with "Hσ") as "[Hσ Hl]"; first done.
    iModIntro. iFrame. iApply "Post".
    iApply "Hl".
  Qed.

  (* Section 7.2 Proof of blocking receive (10) *)
  Lemma wp_tryrecv (l : loc) (v' : gset chan_lang.val) :
    {{{ l ↦ v' }}}
      tryrecv l
      {{{ (x : chan_lang.expr), RET x;
          (∃ v, ⌜x = SOMEV v⌝ ∧ l ↦ (v'∖{[v]}) ∧ ⌜ v ∈ v' ⌝) ∨
          (⌜x = NONEV⌝ ∧ l ↦ ∅)
      }}}.
  Proof.
    iIntros (Φ) "Pre Post".
    iApply wp_lift_atomic_head_step_no_fork; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>".
    iDestruct (gen_network_valid with "Hσ Pre") as %?. iSplit.
    - assert (Decision (v' = ∅)).
      { typeclasses eauto. }
        destruct H0.
      + iPureIntro. eexists _, _, _, _. cbn. econstructor.
        rewrite H. rewrite e. reflexivity.
      + iPureIntro.
        assert (exists M v, v' = M ∪ {[v]}).
        { unfold_leibniz. eapply set_choose in n. destruct n.
          exists (v' ∖ {[x]}). exists x.
          rewrite difference_union.
          set_solver. }
        destruct H0 as (? & ? & ?).
        eexists _, _, _, _. cbn. eapply TryRecvSomeS. rewrite H.
        rewrite H0. reflexivity.
    - iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
      + iModIntro; iSplit=> //. iFrame.
        iApply "Post". iRight. iSplit; done.
      + iMod (gen_network_update _ _ _ (M∖{[v]}) with "Hσ Pre") as "[Hσ Hl]".
        iModIntro; iSplit=> //. iFrame.
        iApply "Post". iLeft. iExists v.
        iSplit; first by done. iSplit; eauto with set_solver.
        assert (M ∪ {[v]} = {[v]} ∪ M) by set_solver.
        rewrite H0.
        assert (({[v]} ∪ M)∖{[v]} = M∖{[v]}) by set_solver.
        rewrite H1. iApply "Hl".
  Qed.

  Lemma wp_send (c : loc) (M : gset chan_lang.val) (m : chan_lang.val) :
    {{{ c ↦ M }}}
      send(c, m)
    {{{ RET #(); c ↦ (M ∪ {[m]}) }}}.
  Proof.
    Unset Printing Notations.
    iIntros (Φ) "Pre Post".
    iApply wp_lift_atomic_head_step_no_fork; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>".
    iDestruct (gen_network_valid with "Hσ Pre") as %?.
    iSplit; first by eauto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_network_update _ _ _ (M ∪ {[m]}) with "Hσ Pre") as "[Hσ Hl]".
    iModIntro; iSplit=> //. iFrame.
    iApply "Post". done.
  Qed.

End proof.
