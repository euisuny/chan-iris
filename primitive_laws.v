From iris.program_logic Require Export ectx_lifting total_ectx_lifting weakestpre.
From iris.proofmode Require Import tactics.
From chanlang Require Import lang notation network_ra tactics.
From iris Require Import options.
From iris.base_logic.lib Require Import invariants.

(* Ghost state for reasoning about chan_lang threadpool. *)
Class chanG Σ :=
  ChanG {
      chan_invG : invGS Σ;
      chan_gen_networkG :> gen_networkGS loc (gmultiset val) Σ;
    }.

Global Instance chan_irisG `{!chanG Σ} : irisGS chan_lang Σ :=
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
  Definition wp_newch s E:
    {{{ true }}} newch @ s; E {{{ l, RET LitV (LitLoc l); l ↦ ∅ }}}.
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
  Lemma twp_tryrecv (l : loc) (v' : gmultiset chan_lang.val) s E :
    [[{ l ↦ v' }]]
      tryrecv l @ s; E
    [[{ (x : val), RET x;
        ((∃ v, ⌜x = SOMEV v⌝ ∧ l ↦ (v'∖{[+ v +]}) ∧ ⌜ v ∈ v' ⌝) ∨
        (⌜x = NONEV⌝ ∧ l ↦ ∅))
    }]].
  Proof.
    iIntros (Φ) "Pre Post".
    iApply twp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 ns κs nt) "Hσ !>".
    iDestruct (gen_network_valid with "Hσ Pre") as %?. iSplit.
    - assert (Decision (v' = ∅)).
      { typeclasses eauto. }
        destruct H0.
      + iPureIntro. eexists _, _, _. cbn. econstructor.
        rewrite H. rewrite e. reflexivity.
      + iPureIntro.
        assert (exists M v, v' = M ⊎ {[+ v +]}).
        {
          eapply gmultiset_choose in n. destruct n.
          exists (v' ∖ {[+ x +]}). exists x.
          multiset_solver. }
        destruct H0 as (? & ? & ?).
        eexists _, _, _. cbn. rewrite H0 in H. eapply TryRecvSomeS; eauto.
        Unshelve. 2 : exact x0. set_solver.
    - iIntros (κ v2 σ2 efs Hstep); inv_head_step.
      + iModIntro; iSplit=> //. iFrame. iSplit.
        * iPureIntro; eauto.
        * iApply "Post". iRight. iSplit; done.
      + iMod (gen_network_update with "Hσ Pre") as "[Hσ Hl]".
        iModIntro; iSplit=> //. iFrame. iSplit.
        * iPureIntro; eauto.
        * iApply "Post". iLeft. iExists v.
          iSplit; first by done. iSplit; eauto with set_solver.
  Qed.

  Lemma wp_tryrecv (l : loc) (v' : gmultiset chan_lang.val) s E:
    {{{ ▷ l ↦ v' }}}
      tryrecv l @ s; E
    {{{ (x : val), RET x;
        ((∃ v, ⌜x = SOMEV v⌝ ∧ l ↦ (v'∖{[+ v +]}) ∧ ⌜ v ∈ v' ⌝) ∨
        (⌜x = NONEV⌝ ∧ l ↦ ∅))
    }}}.
  Proof.
    iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_tryrecv with "H") ; [by auto..|]. iIntros (x) "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_tryrecv_suc (l : loc) (v' : gmultiset chan_lang.val) s E :
    v' ≠ ∅ ->
    [[{ l ↦ v'  }]]
      tryrecv l @ s; E
    [[{ v, RET SOMEV v; l ↦ (v'∖{[+ v +]}) ∧ ⌜ v ∈ v' ⌝ }]].
  Proof.
    iIntros (neq Φ) "Pre Post". iApply twp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 ns κs nt) "Hσ !>". iDestruct (gen_network_valid with "Hσ Pre") as %?.
    iSplit.
    - iPureIntro.
      assert (exists M v, v' = M ⊎ {[+ v +]}).
      { eapply gmultiset_choose in neq. destruct neq.
        exists (v' ∖ {[+x+]}). exists x.
        multiset_solver. }
      destruct H0 as (? & ? & ?).
      rewrite H0 in H. eauto.
      eexists _, _, _. cbn.
      eapply TryRecvSomeS; eauto.
      Unshelve. 2 : exact x0. set_solver.
    - iIntros (κ v2 σ2 efs Hstep); inv_head_step.
      iMod (gen_network_update with "Hσ Pre") as "[Hσ Hl]".
      iModIntro; iSplit=> //. iSplit; first by done.
      iFrame; eauto. iApply "Post".
      iSplit; cycle 1.
      + iPureIntro. set_solver.
      + done.
  Qed.

  Lemma twp_tryrecv_fail (l : loc) (v' : gmultiset chan_lang.val) s E :
    v' = ∅ ->
    [[{ l ↦ v' }]] tryrecv l @ s; E [[{ RET NONEV; l ↦ ∅ }]].
  Proof.
    iIntros ( neq Φ) "Pre Post". iApply twp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 ns κs nt) "Hσ !>". iDestruct (gen_network_valid with "Hσ Pre") as %?.
    iSplit.
    - iPureIntro. rewrite neq in H. eexists _, _, _. cbn.
      eapply TryRecvNoneS; eauto.
    - rewrite neq. rewrite neq in H.
      iIntros (κ v2 σ2 efs Hstep); inv_head_step.
      + iModIntro; iSplit=> //. iSplit; first by done.
        iFrame; eauto. iApply "Post". done.
      + set_solver.
  Qed.

  Lemma wp_tryrecv_suc (l : loc) (v' : gmultiset chan_lang.val) s E :
    v' ≠ ∅ ->
    {{{ ▷ l ↦ v' }}}
      tryrecv l @ s; E
    {{{ v, RET SOMEV v; l ↦ (v'∖{[+v+]}) ∧ ⌜ v ∈ v' ⌝ }}}.
  Proof.
    iIntros (neq Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_tryrecv_suc with "H"); [by auto..|]; iIntros (v) "H HΦ". by iApply "HΦ".
  Qed.

  Lemma wp_tryrecv_fail (l : loc) (v' : gmultiset chan_lang.val) s E :
    v' = ∅ ->
    {{{ ▷ l ↦ v' }}} tryrecv l @ s; E {{{ RET NONEV; l ↦ ∅ }}}.
  Proof.
    iIntros (eq Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_tryrecv_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_send (c : loc) (M : gmultiset chan_lang.val) (m : chan_lang.val) s E:
    [[{ c ↦ M }]] send(c, m) @ s; E
    [[{ RET #(); c ↦ (M ⊎ {[+m+]}) }]].
  Proof.
    iIntros (Φ) "Pre Post".
    iApply twp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 ns κs nt) "Hσ !>". iDestruct (gen_network_valid with "Hσ Pre") as %?.
    iSplit; first by eauto with head_step.
    iIntros (κ v2 σ2 efs Hstep); inv_head_step.
    iMod (gen_network_update _ _ _ (M ⊎ {[+m+]}) with "Hσ Pre") as "[Hσ Hl]".
    iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "Post".
  Qed.

  Lemma wp_send (c : loc) (M : gmultiset chan_lang.val) (m : chan_lang.val) s E:
    {{{ ▷ c ↦ M }}}
      send(c, m) @ s; E
    {{{ RET #(); c ↦ (M ⊎ {[+m+]}) }}}.
  Proof.
    iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_send with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma wp_fork s E e Φ :
    ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
  Proof.
    iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>"; iSplit; first by eauto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep); inv_head_step. by iFrame.
  Qed.

End proof.
