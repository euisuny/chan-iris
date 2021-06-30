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

  Lemma tryrecv_None_chan (σ : state) (l: loc) :
    chan σ !! l = Some ∅ ->
    head_step (tryrecv l) σ [] None_ σ [].
  Proof.
    constructor. eauto.
  Qed.

  Lemma tryrecv_some_chan (σ : state) (c: loc) M v :
    chan σ !! c = Some (M ∪ {[v]})
    → head_step (chan_lang.TryRecv #c) σ []
        (Some_ v) (state_upd_chan <[c:=M]> σ) [].
  Proof.
    constructor. eauto.
  Qed.

  (* Section 7.2 Proof of blocking receive (10) *)
  Lemma wp_tryrecv (l : loc) (dq : dfrac) (v' : gset chan_lang.val) :
    {{{ l ↦{dq} v' }}}
      tryrecv l
      {{{ (x : chan_lang.expr), RET x;
          (∃ v, ⌜x = SOME (SOMEV v)⌝ ∧ l ↦{dq} (v'∖{[v]}) ∧ ⌜ v ∈ v' ⌝) ∨
          (⌜x = NONE⌝ ∧ l ↦{dq} ∅)
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
          exists (v' ∖ {[x]}). exists x. eapply difference_union.
          set_solver. }
        destruct H0 as (? & ? & ?).
        eexists _, _, _, _. cbn. eapply TryRecvSomeS. rewrite H.
        rewrite H0. reflexivity.
    - iNext. iIntros (v2 σ2 efs Hstep).
      repeat match goal with
              | _ => progress simplify_map_eq/= (* simplify memory stuff *)
              | H : to_val _ = Some _ |- _ => apply of_to_val in H
             end.
      inversion Hstep; subst; cycle 1.

  Admitted.


  Definition threadpool := gmap loc (option (gset val)).

  Definition recv_inv v (P : iProp) (Q : threadpool -> chan_lang.val -> iProp)
    : iProp :=
    (P ∗ ⌜v = NONE⌝ ∨ ∃ M m, Q M m ∗ ⌜v = SOMEV m⌝)%I.

End proof.
