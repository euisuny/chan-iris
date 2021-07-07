From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
From iris.bi Require Import atomic derived_laws interface.
Import uPred.

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws proofmode.
Set Default Proof Using "Type".

(* In the language definitions, we had asynchronous channels.
  Here, we use invariant constructions to define _local channel assertions_. *)

Section atomic_invariants.

  Context `{!chanG Σ}.

  Notation iProp := (iProp Σ).

  (* IY: what is [tele]? Seems like some kind of telescoping thing... *)

  Notation "'val'" := chan_lang.val.

  Lemma awp_send (c : loc) (M : gset val) (m : val) :
    ⊢ <<< c ↦ M >>> send(c, m) @ ⊤ <<< c ↦ (M ∪ {[m]}), RET #() >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as "[H↦ [_ Hclose]]".
    match goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
        reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ _ _ _ _ K))
    end.
    - iSolveTC.
    - let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
        iAssumptionCore.
    - pm_reduce; first [wp_finish].
      iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  (* To start off, let's try defining a blocking receive. *)
  Definition recv : chan_lang.val :=
    rec: "loop" "c" :=
      let: "v" := TryRecv "c" in
      match: "v" with
        NONE => "loop" "c"
      | SOME "m" => "m"
      end.

  Lemma awp_recv (c : loc) (m : val):
    ⊢ <<< ∀ (M : gset val), c ↦ M >>>
        recv (LitV $ LitLoc $ c) @ ⊤
      <<< c ↦ (M ∖ {[m]}) ∧ ⌜m ∈ M⌝, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_bind (tryrecv _)%E. iMod "AU" as (M) "[Hl [Hclose _]]".
    (* iApply wp_tryrecv. *)
    (* wp_recv. *)
   Abort.

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
