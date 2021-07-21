(* An atomic heap defined over the channel primitives in the language. *)

From iris.algebra Require Import excl.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import atomic derived_laws interface.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
From iris Require Import proofmode.environments
                         base_logic.lib.invariants.
From iris.base_logic Require Import lib.ghost_var.
(* TODO: See style guide for recommended import order *)

Import uPred.

From chanlang Require Import
     locations
     class_instances
     lang
     notation
     network_ra
     tactics
     primitive_laws
     proofmode
     localchan.
Set Default Proof Using "Type".

(* See [Stack Item 4 : Mutable references] *)
(* Section 8 : Putting logical atomicity to work *)

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

  (* "Shared state" *)
  Definition ref_inv (γ : gname) (l : loc) : iProp :=
    ∃ M, l ↦ M ∗
          [∗ mset] m ∈ M, ∃ (r : loc) (w : option val) (v : val),
            ⌜m = (#r, option_to_val w)%V⌝ ∗
            ghost_var γ (1/2) v.

  (* "Client state" *)
  Definition ref_mapsto (γ : gname) (l : loc) (v : val) : iProp :=
    ghost_var γ (1/2) v.

  Definition is_ref (γ : gname) (l : loc) : iProp :=
    inv N (ref_inv γ l).

  Lemma chan_get_spec (v : val) l γ:
    is_ref γ l -∗
    {{{ ref_mapsto γ l v }}} chan_get #l @ ⊤ {{{ RET v ; ref_mapsto γ l v }}}.
  Proof.
    iIntros "#Hr !#" (Φ) "Hl HΦ".
    wp_lam. rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    (* Introduce the reply channel *)
    iIntros (rc) "Hrc". wp_pures.
    wp_bind (chan_lang.Send _ _).
    iInv "Hr" as (M) "[>Hl' HM]".
    wp_apply (wp_send with "Hl'").
    iIntros "Hl' !>". iSplitL "Hl' HM Hl".
    { iNext. iExists _. iFrame "Hl'".
      rewrite comm. iApply big_sepMS_insert.
      iFrame "HM". iExists _, None, _. auto. }
    wp_pures.
    awp_apply awp_recv.
    iAaccIntro with "Hrc".
    { eauto with iFrame. }
  Abort.

  Local Lemma chan_srv_spec (l : loc) (v : val) γ:
    is_ref γ l -∗
    {{{ ghost_var γ (1/2) v }}} srv #l v @ ⊤ {{{ RET #(); False }}}.
  Proof.
    (* Note : % moves things to the Coq context *)
    iIntros "#Hr !# %Φ Hl HΦ".
    wp_lam. iLöb as "IH" forall (v).
  Abort.

  (* TODO *)
  Lemma chan_set_spec (v : val) γ l:
    {{{ is_ref γ l }}} chan_set #l v @ ⊤ {{{ RET #() ; ref_mapsto γ l v}}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iLöb as "IH".
    wp_lam.
    rewrite /rpc.
    wp_pures. wp_apply wp_newch; first done.
    (* Reply channel *)
    iIntros (r) "Hr". wp_pures.
    iDestruct "Hl" as (x) "[Hl Ho]".
    wp_apply (wp_send with "Hl").
    iIntros "Hl". wp_pures.
    rewrite /recv. wp_rec.
    iAssert (is_ref γ l)%I with "[Ho Hl]" as "Hl". {
      rewrite /is_ref. iExists _. iSplitL "Hl"; done.
    }
    iSpecialize ("IH" with "Hl HΦ").

    (* iMod (inv_alloc N _ (ref_inv γ l ∅ True) with "[-HΦ]") as "#Hinv". *)
    (* { iIntros "!>". rewrite /ref_inv. iSplit. 2 : { iSplit; done. } *)
    (*   iIntros (Φ'). iModIntro. iIntros "_ H". *)
    (* iDestruct "IH" as "[H H']". *)
  Abort.

  Lemma chan_ref_spec (v : val) :
    {{{ True }}} chan_ref v {{{ l γ, RET LitV (LitLoc l); ref_inv γ l v True}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl". wp_pures.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (ref_inv γ l ∅ True) with "[-HΦ]") as "#Hinv".
    { iIntros "!>". rewrite /ref_inv. iSplit. 2 : { iSplit; done. }
      iIntros (Φ'). iModIntro. iIntros "_ H".
    (* iInv N as ([]) "[Hl HR]". *)
    (* wp_apply (wp_fork with "[]"). *)
    (* - iNext. by iApply srv_spec. *)
    (* - wp_seq. iModIntro. iApply "HΦ". *)
  Admitted.

End proof.
