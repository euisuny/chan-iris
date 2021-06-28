From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.

From chanlang Require Import lang notation.

Set Default Proof Using "Type".

(* To start off, let's try defining a blocking receive. *)

Notation TryRecv e := (TryRecv e) (only parsing).
Notation "'tryrecv' e" := (TryRecv e%E) (at level 10) : expr_scope.

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

  Context `{LANG: irisG chan_lang Σ}.
  Notation iProp := (iProp Σ).

  Definition true : iProp := ⌜ True ⌝.

  Lemma recv_spec c :
    {{{ True }}} recv c {{{ RET #(); true }}}.
  Proof.
  Abort.

End invariants.
