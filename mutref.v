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
      (* [Fst "dm"] is the reply channel. the second argument
      is the "writeback" to the reference *)
      let: "reply" :=
        λ: "m'" "v'",
          Send "replychan" "m'";; "loop" "v'" in
      match: "m" with
        NONE => "reply" "v" "v" (* GET *)
      | SOME "w" =>
        "reply" #() "w" (* SET *)
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
(* IY: Either we have this [refG] or we give another field to chanG.. *)
Class refG Σ := RefG { ref_tokG :> inG Σ (exclR unitO) }.
Definition refΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_refΣ {Σ} : subG refΣ Σ → refG Σ.
Proof. solve_inG. Qed.

Section proof.

  Context `{!chanG Σ, !refG Σ}.
  Notation iProp := (iProp Σ).

  Let N := nroot .@ "mutref".

  (* First, we define a "mapsto" operator for the channels. In this case, the
   mapsto will correspond to a channel in the threadpool which stores messages
   that are of the form "GET" and "SET w". *)

  Definition ref_inv (γ : gname) (l : loc) (R : iProp) : iProp :=
    ∃ (v : gmultiset val), l ↦ v ∗ own γ (Excl ()) ∗ R.

  Definition is_ref (γ : gname) (lk : val) (R : iProp) : iProp :=
    ∃ l: loc, ⌜lk = #l⌝ ∧ inv N (ref_inv γ l R).

  Lemma srv_spec (r v : val) :
    {{{ True }}} srv r v {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH". wp_lam.
    wp_pures. wp_bind (recv _)%E.

    (* awp_apply awp_recv. *)
  Admitted.

  (* IY: Are we missing another invariant here? Something like [is_stack]? *)
  Lemma chan_ref_spec (v : val) :
    {{{ True }}} chan_ref v {{{ l, RET LitV (LitLoc l); l ↦ {[+v+]} }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    (* iLöb as "IH". *)
    wp_lam.
    wp_apply wp_newch; first done.
    iIntros (l) "Hl". wp_pures.
    wp_apply (wp_fork with "[]").
    - iNext. by iApply srv_spec.
    - wp_seq. iModIntro. iApply "HΦ".
  Admitted.

End proof.
