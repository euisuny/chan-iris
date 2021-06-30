From iris.program_logic Require Export ectx_lifting weakestpre.
From iris.proofmode Require Import tactics.
From chanlang Require Import lang notation network_ra.
From iris Require Import options.

(* Ghost state for reasoning about chan_lang threadpool. *)
Class chanG Σ :=
  ChanG {
      chan_invG : invG Σ;
      chan_gen_networkG :> gen_networkGS chan_id (option (gset val)) Σ;
    }.

Global Instance chan_irisG `{!chanG Σ} : irisG chan_lang Σ :=
  {
  iris_invG := chan_invG;
  state_interp σ _ κs _ := (gen_network_interp σ.(chan))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
