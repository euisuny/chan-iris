(* An atomic heap defined over the channel primitives in the language. *)
From iris.algebra Require Import excl.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.ghost_var lib.invariants.
From iris.program_logic Require Export atomic weakestpre.
From chanlang Require Import proofmode localchan.
From iris.prelude Require Import options.

(* See [Stack Item 4 : Mutable references] *)
(* Section 8 : Putting logical atomicity to work *)

Notation val := chan_lang.val.
(* The {!chanGS Σ} refers to the resource algebra available in the context. *)
(** A general logically atomic interface for mutable references. *)
Class mut_ref {Σ} `{!chanGS Σ} := MutRef {
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
    let: "d" := NewCh in
    Send "r" ("d", "m");; recv "d".

Definition GET := NONE.
Definition SET w:= SOME w.

Definition chan_get : val := λ: "e", rpc "e" GET.
Definition chan_set : val := λ: "e" "e'", rpc "e" (SET "e'").
(* Definition chan_cas : val := λ: "e" "e1" "e2", rpc "e" (CAS "e1" "e2"). *)

Definition chan_ref : val :=
  λ: "e",
    let: "r" := NewCh in
    Fork (srv "r" "e");; "r".

(* CMRA *)
Class refG Σ := RefG { ref_tokG :> ghost_varG Σ val }.
Definition refΣ : gFunctors := #[ghost_varΣ val].

Global Instance subG_refΣ {Σ} : subG refΣ Σ → refG Σ.
Proof. solve_inG. Qed.


Notation chan := loc.

Section inv.

  Context `{!chanGS Σ}.
  Notation iProp := (iProp Σ).

  Local Definition chan_inv (s : chan) (R : val -> iProp) : iProp :=
    (∃ (Ms : gmultiset val), s ↦ Ms ∗ ([∗ mset] m ∈ Ms, R m)).

  Definition is_chan N (s : chan) (R : val -> iProp): iProp :=
    inv N (chan_inv s R).

  (* Enable [eauto] to prove [chan_inv]. *)
  Local Hint Extern 0 (environments.envs_entails _ (chan_inv _ _)) => unfold chan_inv : core.

  Lemma recv_spec N (srv : chan) (R : val -> iProp):
    is_chan N srv R -∗
    {{{ True }}} recv #srv {{{ m, RET m; ▷ R m }}}.
  Proof.
    iIntros "#Hr !# %Φ _ HΦ".
    iApply (wp_step_fupd _ _ ⊤ with "[HΦ]"); first done.
    { do 3 iModIntro. iAccu. }
    awp_apply awp_recv.
    iInv "Hr" as (M) "[>Hs HM]".
    iAaccIntro with "Hs".
    { eauto 10 with iFrame. }
    iIntros (new_v) "[Hs %Hnew_v]".
    iModIntro.
    rewrite (big_sepMS_delete _ _ new_v); last done.
    iDestruct "HM" as "[HR HM]".
    iSplitL "HM Hs".
    { eauto 10 with iFrame. }
    iIntros "HΦ". iApply "HΦ". done.
  Qed.

  Lemma send_spec N (s : chan) (R : val -> iProp) (m : val):
    is_chan N s R -∗
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

  Lemma newch_spec N (R : val -> iProp):
    {{{ True }}} NewCh {{{ (s : chan), RET #s; is_chan N s R }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl".
    iMod (inv_alloc N _ (chan_inv l R) with "[Hl]") as "#Hinv".
    { iNext. iExists _. iFrame. rewrite big_sepMS_empty. done. }
    iModIntro. iApply "HΦ". done.
  Qed.

End inv.

Section proof.

  Context `{!chanGS Σ, !refG Σ}.
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
  Definition reply_payload (γ : gname) (old_v : val) (req : option val) (reply : val) : iProp :=
    (* There exists some reply channel that stores sent messages *)
      match req with
      | Some v => ⌜reply = #()⌝ ∗ ghost_var γ (1/2) v
      | None => ⌜reply = old_v⌝ ∗ ghost_var γ (1/2) old_v end.

  (* All messsages sent to an rpc is a pair of [reply_channel] and whether
    or not it is a GET/SET message *)
  Definition request_payload (γ : gname) (m : val): iProp :=
    ∃ (req : option val) (r : chan) (old_v : val),
      (⌜m = (#r, option_to_val req)%V⌝ ∗
        is_chan N r (reply_payload γ old_v req) ∗
      (* match req with *)
      (* | Some v => ghost_var γ (1/2) v *)
      (* | None => *)
        ghost_var γ (1/2) old_v
       (* end *)
      ).

  (* "Client state" *)
  Definition ref_mapsto (γ : gname) (v : val) : iProp :=
    ghost_var γ (1/2) v.

  Definition is_ref (γ : gname) (l : chan) : iProp :=
    is_chan N l (request_payload γ).

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
    wp_pures.

    set (get_R := fun γ v x => reply_payload γ v None x).

    wp_apply (newch_spec N (get_R γ v)); first done.
    iIntros (s) "#Hs".
    wp_pures.
    wp_bind (Send _ _).
    wp_apply (send_spec with "[] [Hv]"); first done.
    { iExists None, s, v. iSplit.
      - iPureIntro; reflexivity.
      - iSplitL ""; done. }
    iIntros "_".
    wp_pures.

    (* Make sure we still have a fupd after applying [recv_spec]. *)
    iApply wp_fupd.

    wp_apply recv_spec ; try done.
    iIntros (m) "HR".
    unfold get_R. simpl.
    iDestruct "HR" as ">[-> Hgv]".
    iApply "HΦ". done.
  Qed.

  Lemma chan_set_spec (v w : val) γ l:
    is_ref γ l -∗
    {{{ ref_mapsto γ w }}} chan_set #l v @ ⊤ {{{ RET #() ; ref_mapsto γ v }}}.
  Proof.
    iIntros "#Hr !# %Φ Hv HΦ".
    wp_lam.

    rewrite /rpc.
    wp_pures.

    set (set_R := fun γ v x => reply_payload γ v (Some v) x).

    wp_apply (newch_spec N (set_R γ v)); first done.
    iIntros (s) "#Hs".
    wp_pures.
    wp_bind (Send _ _).
    wp_apply (send_spec with "[] [Hv]"); first done.
    { iExists (Some v), s, w. iSplit.
      - iPureIntro. simpl. reflexivity.
      - iSplitL ""; done. }
    iIntros "_".
    wp_pures.

    iApply wp_fupd.
    wp_apply recv_spec; try done.
    rewrite /set_R /=.
    iIntros (m) ">[%H HR]". subst.
    iApply "HΦ". done.
  Qed.

  Local Lemma chan_srv_spec (l : loc) (v : val) γ:
    is_ref γ l -∗
    {{{ ghost_var γ (1/2) v }}} srv #l v @ ⊤ {{{ RET #(); False }}}.
  Proof.
    iIntros "#Hr !# %Φ Hv● HΦ".
    wp_lam.
    wp_pures.
    iLöb as "IH" forall (v).

    wp_apply recv_spec; try done.
    iIntros (msg) "HR".
    iDestruct "HR" as (req rc old_v) "[>%Eq [#HR >Hv◯]]".

    iDestruct (ghost_var_agree with "Hv● Hv◯") as %<-.
    subst; wp_pures.
    destruct req eqn: Hreq; simpl; wp_pures.
    {
      iMod (ghost_var_update_halves v0 with "Hv● Hv◯") as "[Hv● Hv◯]".
      wp_apply (send_spec with "HR [Hv◯]"); try done.
      { iFrame. done. }

      iIntros "_".
      wp_pures.
      iApply ("IH" $! v0 with "Hv●"); try done. }
    {
      wp_apply (send_spec with "HR [Hv◯]"); try done.
      { iFrame. done. }

      iIntros "_".
      wp_pures.
      iApply ("IH" $! v with "Hv●"); try done.
    }
  Qed.

  Lemma chan_ref_spec (v : val):
    {{{ True }}} chan_ref v {{{ l γ, RET LitV (LitLoc l); is_ref γ l ∗ ref_mapsto γ v }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    wp_lam.

    set (ref_R := fun γ x => request_payload γ x).

    iMod (ghost_var_alloc v) as (γ) "[Hγ● Hγ◯]".

    wp_apply (newch_spec N (ref_R γ)); first done.

    iIntros (s) "#Hs". wp_pures.
    wp_bind (Fork _).
    iInv "Hs" as (M) "Hf".
    wp_apply (wp_fork with "[Hv Hs Hγ●]"); cycle 1.
    {
      iModIntro. iSplitL "Hf".
      { iNext. iExists _. done. }
      wp_seq. iApply "HΦ". iModIntro. iSplitL "".
      { iApply "Hs". }
      done.
    }
    iNext. wp_apply (chan_srv_spec with "[] [Hγ●]"); eauto.
  Qed.

End proof.
