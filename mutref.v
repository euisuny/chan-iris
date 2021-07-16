(* An atomic heap defined over the channel primitives in the language. *)

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode localchan.

From iris.bi.lib Require Import fractional.
From iris.bi Require Import atomic derived_laws interface.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
From iris Require Import proofmode.environments
                         base_logic.lib.invariants.

Import uPred.

(* See [Stack Item 4 : Mutable references] *)
(* Section 8 : Putting logical atomicity to work *)

Notation "'TRUE'" := (LitBool Datatypes.true).
Notation "'FALSE'" := (LitBool Datatypes.false).

(** A general logically atomic interface for a heap. *)
Class atomic_heap {Σ} `{!chanG Σ} := AtomicHeap {
  (* -- operations -- *)
  ref : val;
  get : val;
  set : val;
  cas : val;
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
  cas_spec (r : loc) (v1 v2 : val) :
    ⊢ <<< ∀ v, mapsto r v >>> cas #r v1 v2 @ ⊤
      <<< if decide (v = v1) then mapsto r v2 else mapsto r v,
          RET (v, #if decide (v = v1) then TRUE else FALSE) >>>;
}.
Global Arguments atomic_heap _ {_}.

Definition expr := chan_lang.expr.

(* Figure 16 *)
Definition srv (r : expr) : val :=
  rec: "loop" "v" :=
    (* Receive on channel [r] (a "reference") *)
    let: "dm" := recv r in
    (* [Fst "dm"] is the reply channel. the second argument
     is the "writeback" to the reference *)
    let: "reply" :=
      λ: "m'" "v'",
        Send (Fst "dm") "m'";; "loop" "v'" in
    match: "m" with
      NONE => "reply" "v" "v" (* GET *)
    | SOME "w" => (* w : (val, option val) *)
        match: Snd "w" with
            NONE => "reply" #() (Fst "w") (* SET *)
        | SOME "v2" =>
          let: "b" := LitV $ LitBool $ bool_decide (Fst "w" = "v") in
          let: "v'" := if "b" then "v2" else Fst "w" in
          "reply" (Fst "w") "v'" (* CAS *)
      end
    end.

Definition rpc : val :=
  λ: "r" "m",
    let: "d" := newch in
    Send "r" ("d", "m");; recv "d".

Definition GET := NONE.
Definition SET w:= SOME (w, NONE).
Definition CAS v1 v2 := SOME (v1, SOME v2).

Definition chan_get : val := λ: "e", rpc "e" GET.
Definition chan_set : val := λ: "e" "e'", rpc "e" (SET "e'").
Definition chan_cas : val := λ: "e" "e1" "e2", rpc "e" (CAS "e1" "e2").

Definition chan_ref : val :=
  λ: "e",
    let: "r" := newch in
    Fork (srv "r" "e");; "r".

Section proof.

  Context `{!chanG Σ}.
  Notation iProp := (iProp Σ).

  Lemma srv_spec r (v : val) :
    {{{ True }}} srv r v {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH". rewrite /srv.
    wp_rec.
  Admitted.

  Lemma chan_ref_spec (v : val) :
    {{{ True }}} chan_ref v {{{ l, RET LitV (LitLoc l); l ↦ {[v]} }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH" forall (v Φ).
    wp_lam. wp_bind (newch)%E.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl". wp_pures.
    wp_apply (wp_fork with "[]").
    - iNext. by iApply srv_spec.
    - wp_seq. iModIntro. iApply "HΦ".
  Admitted.

  Lemma chan_set_spec (r : loc) (v : val):
    ⊢ <<< ∀ w, r ↦ {[w]} >>> chan_set #r v @ ⊤ <<< r ↦ {[v]}, RET #() >>>.
  Proof.
    iIntros (Φ) "HΦ".
    iLöb as "IH".
    wp_lam. wp_pures.
    unfold rpc. wp_lam. wp_pures.
    wp_bind (newch)%E.
    iMod "HΦ" as (M) "[Hl [Hclose _]]".
    iApply wp_newch; first by done.
    iNext. iIntros (l) "H".
    iMod ("Hclose" with "Hl") as "HΦ".
    iModIntro. wp_pures.
    awp_apply awp_send without "HΦ".
  Admitted.

  Lemma chan_get_spec (r : loc) :
    ⊢ <<< ∀ v, r ↦ {[v]} >>> chan_get #r @ ⊤ <<< r ↦ {[v]}, RET v >>>.
  Proof.
    iIntros (Φ) "HΦ".
    iLöb as "IH".
    wp_lam. wp_pures.
    unfold rpc. wp_lam. wp_pures.
    wp_bind (newch)%E.
    iMod "HΦ" as (M) "[Hl [Hclose _]]".
    iApply wp_newch; first by done.
    iNext. iIntros (l) "H".
    iMod ("Hclose" with "Hl") as "HΦ".
    iModIntro. wp_pures.
    awp_apply awp_send without "HΦ".
  Admitted.

  Lemma chan_cas_spec (r : loc) (v1 v2 : val) :
    ⊢ <<< ∀ v, r ↦ {[v]} >>> chan_cas #r v1 v2 @ ⊤
      <<< if decide (v = v1) then r ↦ {[v2]} else r ↦ {[v]},
    RET (v, #if decide (v = v1) then TRUE else FALSE) >>>.
  Proof.
    iIntros (Φ) "HΦ".
    iLöb as "IH".
    wp_lam. wp_pures.
    unfold rpc. wp_lam. wp_pures.
    wp_bind (newch)%E.
    iMod "HΦ" as (M) "[Hl [Hclose _]]".
    iApply wp_newch; first by done.
    iNext. iIntros (l) "H".
    iMod ("Hclose" with "Hl") as "HΦ".
    iModIntro. wp_pures.
    awp_apply awp_send without "HΦ".
  Admitted.

End proof.

Definition chan_mutref `{!chanG Σ} : atomic_heap Σ :=
  {|
    ref_spec := chan_ref_spec;
    get_spec := chan_get_spec;
    set_spec := chan_set_spec;
    cas_spec := chan_cas_spec;
  |}.
