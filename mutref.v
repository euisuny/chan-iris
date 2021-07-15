(* An atomic heap defined over the channel primitives in the language. *)

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode localchan.

From iris.bi.lib Require Import fractional.
From iris.bi Require Import atomic derived_laws interface.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.

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
  mapsto_agree l v1 v2 : mapsto l v1 -∗ mapsto l v2 -∗ ⌜v1 = v2⌝;
  mapsto_persist l v : mapsto l v ==∗ mapsto l v;
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
    let: "dm" := recv r in
    let: "reply" :=
      λ: "m'" "v'",
        Send (Fst "dm") "m'";; "loop" "v'" in
    match: "m" with
      NONE => "reply" "v" "v" (* GET *)
    | SOME "w" =>
        match: Snd "w" with
            NONE => "reply" #() (Fst "w") (* SET *)
          | SOME "v2" => "reply" (Fst "w") "v2" (* CAS *)
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

From iris Require Import proofmode.environments
                         base_logic.lib.invariants.

Section proof.

  Context `{!chanG Σ}.
  Notation iProp := (iProp Σ).

  Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
  Lemma chan_get_spec (r : loc) (v : val):
    ⊢ <<< ∀ w, r ↦ w >>> chan_set #r v @ ⊤ <<< r ↦ {[v]}, RET #() >>>.
  Proof.
    iIntros (Φ) "HΦ". iLöb as "IH".
    wp_lam. wp_pures.
    unfold rpc. wp_lam. wp_pures.
    wp_bind (newch)%E.
    iMod "HΦ" as (M) "[Hl [Hclose _]]".
    iApply wp_newch; first by done.
    iNext. iIntros (l) "H".
    iMod ("Hclose" with "Hl") as "HΦ".
    iModIntro. wp_pures.
    (* awp_apply awp_send without "HΦ". *)
  Admitted.

