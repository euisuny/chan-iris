From iris.program_logic Require Export atomic weakestpre.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.

(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
From iris.bi.lib Require Import atomic.

From chanlang Require Import
     lang notation network_ra tactics primitive_laws.
Set Default Proof Using "Type".

(* To start off, let's try defining a blocking receive. *)
Definition recv : chan_lang.val :=
  rec: "loop" "c" :=
    let: "v" := "TryRecv" "c" in
    match: "v" with
      NONE => "loop" "c"
    | SOME "m" => "m"
    end.

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)

Section atomic_invariants.

  Context `{!chanG Σ}.

  Notation iProp := (iProp Σ).

  Lemma example (l : loc):
    ⊢ <<< ∀ v, True >>> tryrecv l @ ⊤ <<< True, RET v >>>.
  Proof. Abort.

  (* IY: what is [tele]? Seems like some kind of telescoping thing... *)

  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
      [inversion 1; naive_solver
      |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  Global Instance send_atomic s c m : Atomic s (chan_lang.Send (Val c) (Val m)).
  Proof. solve_atomic. Qed.

  (*TODO: [v = ()] in conclusion. *)
  Lemma awp_send (c : loc) (M : gset chan_lang.val) (m : chan_lang.val) :
    ⊢ <<< ∀ v, c ↦ M >>> send(c, m) @ ⊤ <<< c ↦ (M ∪ {[m]}), RET v >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    pose wp_send.
    (* wp_apply_core wp_send ltac:(fun H => iApplyHyp H) *)
    (*               idtac. *)
    (* awp_apply wp_send. *)


  (*   {{{ c ↦ M }}} *)
  (*     send(c, m) *)
  (*   {{{ RET #(); c ↦ (M ∪ {[m]}) }}}. *)
  (* Lemma atomic_recv c : *)
  (*   ⊢ <<< ∀ v, True >>> recv c @ ⊤ <<< True, RET v >>>. *)
  (* Proof. *)

  Abort.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End invariants.
