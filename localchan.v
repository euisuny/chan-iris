From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.

From chanlang Require Import lang notation.

Set Default Proof Using "Type".

(* To start off, let's try defining a blocking receive. *)

Notation TryRecv e := (TryRecv e) (only parsing).
Notation "'tryrecv' e" := (TryRecv (LitV $ LitChan e%E)) (at level 10) : expr_scope.

Notation NewCh := (NewCh) (only parsing).
Notation "'newch' e" := (NewCh (LitV $ LitChan e%E)) (at level 10) : expr_scope.

Definition recv : val :=
  rec: "loop" "c" :=
    let: "v" := "TryRecv" "c" in
    match: "v" with
      NONE => "loop" "c"
    | SOME "m" => "m"
    end.

Definition threadpool := gmap chan_id (option (gset val)).

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)

From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.

Section invariants.

  Context `{LANG: irisG chan_lang Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition true : iProp := ⌜ True ⌝.

  (* Definition newch_inv v : iProp := *)
  (*   ( NONE)%I. *)

  (* Definition wp_newch c : *)
  (*   {{{ true }}} newch c {{{ RET #(); newch_inv v }}}. *)

  Definition recv_inv v (P : iProp) (Q : threadpool -> chan_lang.val -> iProp) : iProp :=
    (P ∗ ⌜v = NONE⌝ ∨ ∃ M m, Q M m ∗ ⌜v = SOMEV m⌝)%I.

  Definition is_recv P Q v :=
    inv N (recv_inv v P Q).

  (* Section 7.2 Proof of blocking receive (10) *)
  Lemma wp_tryrecv P (Q : threadpool -> chan_lang.val -> iProp) c :
    {{{ P }}} tryrecv c {{{ v , RET v; is_recv P Q v }}}.
  Proof.
    iIntros (Φ) "P Q".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ !>". iSplit.
    (* - first by euto with head_step. iMod "Q (tryrecv c)". *)
    (*   unfold head_reducible. iExists _, _, _, _. iSimpl. *)
    (*   iMod "Q".  as  "_". *)
  Admitted.

  Lemma recv_spec c (tp : list chan_lang.expr):
    {{{ True }}} recv c {{{ RET #(); true }}}.
  Proof.
  Abort.

End invariants.
