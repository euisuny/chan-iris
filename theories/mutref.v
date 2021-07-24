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

  Notation chan := loc.

  (* "Shared state" *)
  Definition ref_inv (γ : gname) (s : chan) : iProp :=
    ∃ (Ms : gmultiset val),
      (* server *)
      s ↦ Ms ∗
          ([∗ mset] m ∈ Ms, ∃ (r : chan) (w : option val) (v : val),
            ⌜m = (#r, option_to_val w)%V⌝ ∗
            ghost_var γ (1/2) v) ∗
          (∃ (r : chan) (Mr : gmultiset val),
              r ↦ Mr ∗
              [∗ mset] v ∈ Mr, ghost_var γ (1/2) v).


  (* "Client state" *)
  Definition ref_mapsto (γ : gname) (l : chan) (v : val) : iProp :=
    ghost_var γ (1/2) v.

  Definition is_ref (γ : gname) (l : chan) : iProp :=
    inv N (ref_inv γ l).

  Global Instance is_ref_persistent γ l : Persistent (is_ref γ l).
  Proof. apply _. Qed.

  Lemma chan_get_spec (v : val) l γ:
    is_ref γ l -∗
    {{{ ref_mapsto γ l v }}} chan_get #l @ ⊤ {{{ RET v ; ref_mapsto γ l v }}}.
  Proof.
    iIntros "#Hr !#" (Φ) "Hl HΦ".
    wp_lam. rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    iIntros (rc) "Hrc". (* reply channel *)
    wp_pures.
    wp_bind (chan_lang.Send _ _).
    iInv "Hr" as (M) "[>Hl' HM]".
    iDestruct "HM" as "[HR HM]".
    wp_apply (wp_send with "Hl'").
    iIntros "Hl' !>". iSplitL "Hl' HM Hl HR".
    {
      iNext. iExists _. iFrame "Hl'".
      iSplitL "Hl HR".
      { rewrite comm. rewrite big_sepMS_insert.
        iFrame. iExists _, None, _. iSplit; auto. }
      iFrame.
    }

    wp_pures.
    awp_apply awp_recv.
    iAaccIntro with "Hrc".
    { eauto with iFrame. }
    iIntros (w) "[? %IN]". set_solver.
    (* A somewhat odd way to conclude the proof, but it works.. *)
  Qed.

  Local Lemma chan_srv_spec (l : loc) (v : val) γ:
    is_ref γ l -∗
    {{{ ghost_var γ (1/2) v }}} srv #l v @ ⊤ {{{ RET #(); False }}}.
  Proof.
    (* Note : % moves things to the Coq context *)
    iIntros "#Hr !# %Φ Hl HΦ".
    wp_lam. iLöb as "IH" forall (v).
    wp_pures.
    awp_apply awp_recv.
    iInv "Hr" as (M) "[>Hl' >[HM Hr']]".
    iAaccIntro with "Hl'".
    { iFrame. iIntros. iModIntro. iNext.
      rewrite /ref_inv. iExists M. iFrame. }
    iIntros (w) "Hup".
    iModIntro.
    iDestruct "Hup" as "[Hlup %Hw]".
    rewrite (big_sepMS_delete _ M w Hw).
    iDestruct "HM" as "[Hw HM]".
    iDestruct "Hw" as (r' w' v') "[Hweq Hgv]".

    iSplitL "HM Hlup Hr'".

    {(* Re-establish [ref_inv] for channel [l]. *)
      iNext. rewrite /ref_inv.
      iExists (M ∖ {[+ w +]}), _. iFrame. }

    wp_pures.
    iDestruct "Hweq" as "%Hweq". subst.
    wp_pures.

    destruct w'; wp_match.
    { wp_pures. wp_bind (Send _ _).
      iInv "Hr" as (M' Mr') "[>Hl' >[Hr' HM]]".
      wp_apply (wp_send with Hr').
      admit.
    }
    { wp_pures. wp_bind (Send _ _).

      (* Same problem in this branch. *)
      admit.
    }

  Abort.

  Lemma chan_set_spec (v : val) γ l:
    is_ref γ l -∗
    {{{ ∀ w, ref_mapsto γ l w }}} chan_set #l v @ ⊤ {{{ RET #() ; ref_mapsto γ l v }}}.
  Proof.
    iIntros "#Hr !#" (Φ) "Hl HΦ".
    wp_lam. rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    iIntros (rc) "Hrc". wp_pures.
    wp_bind (chan_lang.Send _ _).
    iInv "Hr" as (M) "[>Hl' HM]".
    wp_apply (wp_send with "Hl'").
    iIntros "Hl' !>". iSplitL "Hl' HM Hl".
    { iNext. iExists _. iFrame "Hl'".
      rewrite comm. iApply big_sepMS_insert.
      iFrame "HM". iExists _, (Some v), _. auto.
    }
    wp_pures.
    awp_apply awp_recv.
    iAaccIntro with "Hrc".
    { eauto with iFrame. }
    iIntros (w) "[? %IN]". set_solver.
    Unshelve. eauto.
  Qed.

  Lemma chan_ref_spec (v : val) :
    {{{ True }}} chan_ref v {{{ l γ, RET LitV (LitLoc l); ref_inv γ l }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl". wp_pures.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    (* iMod (inv_alloc N _ (ref_inv γ l ∅ True) with "[-HΦ]") as "#Hinv". *)
    (* { iIntros "!>". rewrite /ref_inv. iSplit. 2 : { iSplit; done. } *)
    (*   iIntros (Φ'). iModIntro. iIntros "_ H". *)
  Admitted.

End proof.
