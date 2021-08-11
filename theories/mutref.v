(* An atomic heap defined over the channel primitives in the language. *)
From iris.algebra Require Import excl.
From iris.proofmode Require Import
     tactics coq_tactics reduction spec_patterns environments.
From iris.base_logic Require Import lib.ghost_var lib.invariants.
From iris.program_logic Require Export atomic weakestpre.
From chanlang Require Import
     locations class_instances lang proofmode notation
     network_ra tactics primitive_laws localchan.
From iris.prelude Require Import options.

(* See [Stack Item 4 : Mutable references] *)
(* Section 8 : Putting logical atomicity to work *)

Notation val := chan_lang.val.
(* The {!chanG Σ} refers to the resource algebra available in the context. *)
(** A general logically atomic interface for mutable references. *)
Class mut_ref {Σ} `{!chanG Σ} := MutRef {
  (* -- operations -- *)
  ref : val;
  get : val;
  set : val;
  (* cas : val; *)
  (* -- predicates -- *)
  mapsto (l : loc) (v : val) : iProp Σ;
  (* -- mapsto properties -- *)
  mapsto_timeless l v :> Timeless (mapsto l v);
  (* -- operation specs -- *)
  ref_spec (v : val) :
    {{{ True }}} ref v {{{ l, RET #l; mapsto l v }}};
  get_spec (r : loc) :
    ⊢ <<< ∀ v, mapsto r v >>> get #r @ ⊤ <<< mapsto r v, RET v >>>;
  set_spec (r : loc) (v : val) :
    ⊢ <<< ∀ w, mapsto r w >>> set #r v @ ⊤ <<< mapsto r v, RET #() >>>;
  (* cas_spec (r : loc) (v1 v2 : val) : *)
  (*   ⊢ <<< ∀ v, mapsto r v >>> cas #r v1 v2 @ ⊤ *)
  (*     <<< if decide (v = v1) then mapsto r v2 else mapsto r v, *)
  (*         RET (v, #if decide (v = v1) then TRUE else FALSE) >>>; *)
}.
Global Arguments mut_ref _ {_}.

Definition expr := chan_lang.expr.

(* Figure 16 *)
Definition srv : val :=
  λ: "r",
    rec: "loop" "v" :=
      (* Receive on channel [r] (a "reference") *)
      let: "dm" := recv "r" in
      let: "replychan" := Fst "dm" in
      let: "m" := Snd "dm" in
      let: "reply" :=
        λ: "m'" "v'",
          Send "replychan" "m'";; "loop" "v'" in
      match: "m" with
        NONE => "reply" "v" "v" (* GET *)
      | SOME "w" => "reply" #() "w" (* SET *)
      end.
(* LATER : implement CAS (equality/binop) *)

(* Remote procedure call between a client and a server *)
Definition rpc : val :=
  λ: "r" "m",
    let: "d" := newch in
    Send "r" ("d", "m");; recv "d".

Definition GET := NONE.
Definition SET w:= SOME w.

Definition chan_get : val := λ: "e", rpc "e" GET.
Definition chan_set : val := λ: "e" "e'", rpc "e" (SET "e'").
(* Definition chan_cas : val := λ: "e" "e1" "e2", rpc "e" (CAS "e1" "e2"). *)

Definition chan_ref : val :=
  λ: "e",
    let: "r" := newch in
    Fork (srv "r" "e");; "r".

(* CMRA *)
Class refG Σ := RefG { ref_tokG :> ghost_varG Σ val }.
Definition refΣ : gFunctors := #[ghost_varΣ val].

Global Instance subG_refΣ {Σ} : subG refΣ Σ → refG Σ.
Proof. solve_inG. Qed.


Notation chan := loc.

Section inv.

  Context `{!chanG Σ, !refG Σ}.
  Notation iProp := (iProp Σ).

  Definition is_chan (s : chan) (R : val -> iProp) : iProp :=
    (∃ (Ms : gmultiset val), s ↦ Ms ∗ ([∗ mset] m ∈ Ms, R m)).

  Definition chan_inv N (s : chan) (R : val -> iProp): iProp :=
    inv N (is_chan s R).

  Lemma recv_chan_inv N (s : chan) (R : val -> iProp):
    chan_inv N s R -∗
    {{{ True }}} recv #s {{{ m, RET m; R m }}}.
  Proof.
    iIntros "#Hr !# %Φ _ HΦ".
    rewrite /recv.
    wp_rec.
    iLöb as "IH".
    wp_bind (chan_lang.TryRecv _).
    iInv "Hr" as (M) "[>Hs HM]" "Hclose".
    wp_apply (wp_tryrecv with "Hs").
    iIntros (new_v) "Hnew".
    iDestruct "Hnew" as "[[%v (%Hnew & Hs & %Hv)] | (%Hnew & Hs)]";
      subst.
    - rewrite big_sepMS_delete; eauto.
      iDestruct "HM" as "[HR HM]".
      iMod ("Hclose" with "[Hs HM]").
      { iNext. iExists _. iSplitL "Hs"; done. }
      iModIntro. wp_pures. iModIntro. iApply "HΦ"; done.
    - iMod ("Hclose" with "[Hs HM]").
      { iNext. iExists _. iSplitL "Hs"; first done.
        rewrite big_sepMS_empty; done. }
      iModIntro.
      wp_pures. iApply "IH"; done.
  Qed.

  Lemma send_chan_inv N (s : chan) (R : val -> iProp) (m : val):
    chan_inv N s R -∗
    {{{ R m }}} Send #s m {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hr !# %Φ Hm HΦ".
    iInv "Hr" as (M) "[>Hs HM]" "Hclose".
    wp_apply (wp_send with "Hs").
    iIntros "Hs".
    iMod ("Hclose" with "[Hs HM Hm]").
    { iNext. iExists _. iSplitL "Hs"; first done.
      rewrite comm. rewrite big_sepMS_insert. iFrame. }
    iModIntro. iApply "HΦ"; done.
  Qed.

  (* TODO: make [newch] a non-keyword notation *)
  Lemma new_chan_inv N (R : val -> iProp):
    {{{ True }}} NewCh {{{ (s : chan), RET #s; chan_inv N s R }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl".
    iMod (inv_alloc N _ (is_chan l R) with "[Hl]") as "#Hinv".
    { iNext. iExists _. iFrame. rewrite big_sepMS_empty. done. }
    iModIntro. iApply "HΦ". done.
  Qed.

End inv.

Section proof.

  Context `{!chanG Σ, !refG Σ}.
  Notation iProp := (iProp Σ).

  Let N := nroot .@ "mutref".
  (* We define a "mapsto" operator for the channels. In this case, the
   mapsto will correspond to a channel in the threadpool which stores a log of
   messages and that returns [v] from a [chan_get] operation. *)

  Local Definition option_to_val (v : option val) : val :=
    match v with
    | None => NONEV
    | Some v => SOMEV v
    end.

  (* For a reference that is a server, the invariant also keeps track
    of what is stored in reply channel *)
  (* TODO: refactor with [chan_inv] *)
  (* TODO: rename [w] to [req] *)
  Definition reply_payload (γ : gname) (old_v : val) (w : option val) (reply : val) : iProp :=
    (* There exists some reply channel that stores sent messages *)
    ∃ new_v, ghost_var γ (1/2) new_v ∗
      match w with
      | Some v => ⌜new_v = v ∧ reply = #()⌝
      | None => ⌜new_v = old_v ∧ reply = new_v⌝ end.

  (* All messsages sent to an rpc is a pair of [reply_channel] and whether
    or not it is a GET/SET message *)
  Definition request_payload (γ : gname) (m : val): iProp :=
    ∃ (w : option val) (r : chan) (old_v : val),
      (⌜m = (#r, option_to_val w)%V⌝ ∗
        chan_inv N r (reply_payload γ old_v w) ∗
        ghost_var γ (1/2) old_v).

  (* "Client state" *)
  Definition ref_mapsto (γ : gname) (v : val) : iProp :=
    ghost_var γ (1/2) v.

  Definition is_ref (γ : gname) (l : chan) : iProp :=
    chan_inv N l (request_payload γ).

  Global Instance is_ref_persistent γ l : Persistent (is_ref γ l).
  Proof. apply _. Qed.

  Global Instance ref_mapsto_timeless γ l: Timeless (ref_mapsto γ l).
  Proof. apply _. Qed.

  Lemma chan_get_spec (v : val) l γ:
    is_ref γ l -∗
    {{{ ref_mapsto γ v }}} chan_get #l @ ⊤ {{{ RET v ; ref_mapsto γ v }}}.
  Proof.
    iIntros "#Hr !# %Φ Hv HΦ".
    wp_lam.

    rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    iIntros (rc) "Hrc". (* reply channel *)
    wp_pures.
    wp_bind (chan_lang.Send _ _).
    iDestruct "Hv" as "Hv".

    iMod (inv_alloc N _ (reply_inv γ rc v None) with "[Hrc]") as "#Hinv".
    { iExists _. iFrame. rewrite big_sepMS_empty. done. }

    iInv "Hr" as (M) "[>Hl >Hm]".
    wp_apply (wp_send with "Hl").
    iIntros "Hl !>".
    iSplitL "Hv Hm Hl".
    { iNext. iExists _. iSplitL "Hl"; first done.
      rewrite comm. rewrite big_sepMS_insert.
      iFrame. iExists None, _, _. iSplit; auto.
    }
    wp_pures.

    wp_pures.
    unfold recv.
    wp_pures.
    iLöb as "IH".
    wp_bind (chan_lang.TryRecv _).
    clear M.
    iInv "Hinv" as (Mr) "[>Hrc >Hm]".

    wp_apply (wp_tryrecv with "Hrc").
    iIntros (new_val) "Hrc".
    iDestruct "Hrc" as "[Hrc | Hrc]".
    - iModIntro.
      iDestruct "Hrc" as (new_val_v) "(-> & Hrc & %HIn)".
      rewrite big_sepMS_delete; eauto.
      iDestruct "Hm" as "[Hnew Hdel]".
      iSplitL "Hrc Hdel".
      { iNext. iExists _. iFrame. }
      iDestruct "Hnew" as (new_v) "[Hgv %Eq]".
      destruct Eq as (-> & ->).
      wp_pures. iModIntro. iApply "HΦ". done.
    - iModIntro.
      iDestruct "Hrc" as "(-> & Hrc)".
      iSplitL "Hm Hrc".
      { iNext.
        iExists _. iFrame. rewrite big_sepMS_empty. done.
      }
      wp_pures. iApply ("IH" with "HΦ").
  Qed.

  Lemma chan_set_spec (v : val) γ l:
    is_rpc γ l -∗
    {{{ ∀ w, ref_mapsto γ w }}} chan_set #l v @ ⊤ {{{ RET #() ; ref_mapsto γ v }}}.
  Proof.
    iIntros "#Hr !# %Φ Hv HΦ".
    wp_lam.

    rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    iIntros (rc) "Hrc". (* reply channel *)
    wp_pures.
    wp_bind (chan_lang.Send _ _).
    iDestruct "Hv" as "Hv".

    iMod (inv_alloc N _ (reply_inv γ rc v (Some v)) with "[Hrc]") as "#Hinv".
    { iExists _. iFrame. rewrite big_sepMS_empty. done. }

    iInv "Hr" as (M) "[>Hl >Hm]".
    wp_apply (wp_send with "Hl").
    iIntros "Hl !>".
    iSplitL "Hv Hm Hl".
    { iNext. iExists _. iSplitL "Hl"; first done.
      rewrite comm. rewrite big_sepMS_insert.
      iFrame. iExists (Some v), _, _. iSplit; auto.
    }
    wp_pures.

    wp_pures.
    unfold recv.
    wp_pures.
    iLöb as "IH".
    wp_bind (chan_lang.TryRecv _).
    clear M.
    iInv "Hinv" as (Mr) "[>Hrc >Hm]".

    wp_apply (wp_tryrecv with "Hrc").
    iIntros (new_val) "Hrc".
    iDestruct "Hrc" as "[Hrc | Hrc]".
    - iModIntro.
      iDestruct "Hrc" as (new_val_v) "(-> & Hrc & %HIn)".
      rewrite big_sepMS_delete; eauto.
      iDestruct "Hm" as "[Hnew Hdel]".
      iSplitL "Hrc Hdel".
      { iNext. iExists _. iFrame. }
      iDestruct "Hnew" as (new_v) "[Hgv %Eq]".
      destruct Eq as (-> & ->).
      wp_pures. iModIntro. iApply "HΦ". done.
    - iModIntro.
      iDestruct "Hrc" as "(-> & Hrc)".
      iSplitL "Hm Hrc".
      { iNext.
        iExists _. iFrame. rewrite big_sepMS_empty. done.
      }
      wp_pures. iApply ("IH" with "HΦ").
    Unshelve. eauto.
  Qed.

  Local Lemma chan_srv_spec (l : loc) (v : val) γ:
    is_srv γ l -∗
    {{{ ghost_var γ (1/2) v }}} srv #l v @ ⊤ {{{ RET #(); False }}}.
  Proof.
    (* Note : % moves things to the Coq context *)
    iIntros "#Hr !# %Φ Hv● HΦ".
    wp_lam.
    wp_pures.
    iLöb as "IH" forall (v).

    awp_apply awp_recv.
    iInv "Hr" as (M) "[>Hl >HM]".
    iAaccIntro with "Hl".
    { iFrame. iIntros. iModIntro. iNext.
      rewrite /rpc_inv. iExists M. iFrame. }
    iIntros (w) "Hup".
    iModIntro.
    iDestruct "Hup" as "[Hlup %Hw]".
    rewrite (big_sepMS_delete _ M w Hw).

    iDestruct "HM" as "[HM HMset]".
    iSplitL "HMset Hlup".

    {(* Re-establish [ref_inv] for channel [l]. *)
      iNext. rewrite /rpc_inv.
      iExists (M ∖ {[+ w +]}). iFrame. }

    wp_pures.
    iDestruct "HM" as (w0 r old_v) "[%Hweq [Hv◯ Hrc]]".
    destruct Hweq as (-> & Hweq).
    subst.
    wp_pures.

    destruct w0 eqn: Hw0; wp_match.
    { wp_pures.

      wp_bind (Send _ _).

      iDestruct "Hrc" as (Mr) "[Hrc HM]".
      wp_apply (wp_send with "Hrc").

      iIntros "Hrm".
      wp_pures.
      subst.
      iDestruct (ghost_var_agree with "Hv● Hv◯") as %->. simpl in *.
      iApply ("IH" $! v0 with "Hv●"); try done.
    }
    { wp_pures. wp_bind (Send _ _).

      iDestruct "Hrc" as (Mr) "[Hrc HM]".
      wp_apply (wp_send with "Hrc").

      iIntros "Hrm".
      wp_pures.

      iDestruct (ghost_var_agree with "Hv● Hv◯") as %->. simpl in *.
      iApply ("IH" $! old_v with "Hv●"); try done.
    }
  Qed.

  Lemma chan_ref_spec (v : val):
    {{{ True }}} chan_ref v {{{ l γ, RET LitV (LitLoc l); is_ref γ l ∗ ref_mapsto γ v }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    wp_lam.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl". wp_pures.

    iMod (inv_alloc N _ (srv_inv γ l) with "[Hl]") as "#Hinv".
    { iNext. iExists _; iFrame. rewrite big_sepMS_empty. done. }
    wp_apply (wp_fork with "[Hv]"); cycle 1.
    {
      wp_seq. iModIntro. iApply "HΦ". iApply "Hinv".
    }
    iNext. wp_apply (chan_srv_spec with "[] [Hv]"); eauto.
  Qed.

End proof.
Typeclasses Opaque is_srv is_rpc ref_mapsto.
