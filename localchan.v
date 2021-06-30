From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From chanlang Require Import lang notation.

Set Default Proof Using "Type".

(* To start off, let's try defining a blocking receive. *)
Definition recv : val :=
  rec: "loop" "c" :=
    let: "v" := "TryRecv" "c" in
    match: "v" with
      NONE => "loop" "c"
    | SOME "m" => "m"
    end.

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)

Section invariants.

  Context `{LANG: irisG chan_lang Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Lemma recv_spec c (tp : list chan_lang.expr):
    {{{ True }}} recv c {{{ RET #(); true }}}.
  Proof.
  Abort.

End invariants.
