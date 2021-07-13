(* An atomic heap defined over the channel primitives in the language. *)

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode.

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
Module chanref.

  Definition expr := chan_lang.expr.

  Parameter (e_newch : expr).
  Parameter (e_send : expr -> expr -> expr).
  Parameter (e_recv : expr -> expr).

  (* Figure 16 *)
  Definition srv (r : expr) : val :=
    rec: "loop" "v" :=
      let: "dm" := e_recv r in
      let: "reply" :=
        λ: "m'" "v'",
          e_send (Fst "dm") "m'";; "loop" "v'" in
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
      let: "d" := e_newch in
      e_send "r" ("d", "m");; e_recv "d".

  Definition GET := NONE.
  Definition SET w:= SOME (w, NONE).
  Definition CAS v1 v2 := SOME (v1, SOME v2).

  Definition get e := rpc e GET.
  Definition set e e' := rpc e (SET e').
  Definition cas e e1 e2 := rpc e (CAS e1 e2).

  Definition ref : val :=
    λ: "e",
      let: "r" := e_newch in
      Fork (srv "r" "e");; "r".

End chanref.

Section proof.
  Context `{!chanG Σ}.

  Definition 
