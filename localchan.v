From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
From iris.bi Require Import atomic derived_laws interface.

From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws.
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


Notation "'val'" := chan_lang.val.
  Ltac reshape_expr e tac :=
    let rec go K vs e :=
      match e with
      | _                               => lazymatch vs with [] => tac K e | _ => fail end
      | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
      | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
      | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e
      | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2
      | Fst ?e                          => add_item FstCtx vs K e
      | Snd ?e                          => add_item SndCtx vs K e
      | InjL ?e                         => add_item InjLCtx vs K e
      | InjR ?e                         => add_item InjRCtx vs K e
      | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
      | Send ?e (Val ?v)                => add_item (SendLCtx v) vs K e
      | Send ?e1 ?e2                    => add_item (SendRCtx e1) vs K e2
      end
    with add_item Ki vs K e :=
      lazymatch vs with
      | _               => go (Ki :: K) (@nil (val * val)) e
      end
    in
    go (@nil ectx_item) (@nil (val * val)) e.

  Tactic Notation "wp_send" :=
    let solve_mapsto _ :=
      let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
      iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
        fail 1 "wp_store: cannot find 'Store' in wp" e;
      [iSolveTC
      |solve_mapsto ()
      |pm_reduce]
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
        fail 1 "wp_store: cannot find 'Store' in twp" e;
      [solve_mapsto ()
      |pm_reduce]
    | _ => fail "wp_store: not a 'wp'"
    end.

  Lemma tac_wp_expr_eval `{!chanG Σ} Δ s E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
  Proof. by intros ->. Qed.
  Lemma tac_twp_expr_eval `{!chanG Σ} Δ s E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
  Proof. by intros ->. Qed.

  Tactic Notation "wp_expr_eval" tactic3(t) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
        [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      notypeclasses refine (tac_twp_expr_eval _ _ _ _ e _ _ _);
        [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
    | _ => fail "wp_expr_eval: not a 'wp'"
    end.
  Ltac wp_expr_simpl := wp_expr_eval simpl.

  Lemma tac_wp_value_nofupd `{!chanG Σ} Δ s E Φ v :
    envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
  Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
  Lemma tac_twp_value_nofupd `{!chanG Σ} Δ s E Φ v :
    envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
  Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed.

  Lemma tac_wp_pure `{!chanG Σ} Δ Δ' s E K e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
    (* We want [pure_exec_fill] to be available to TC search locally. *)
    pose proof @pure_exec_fill.
    rewrite HΔ' -lifting.wp_pure_step_later //.
  Qed.
  Lemma tac_twp_pure `{!chanG Σ} Δ s E K e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    envs_entails Δ (WP (fill K e2) @ s; E [{ Φ }]) →
    envs_entails Δ (WP (fill K e1) @ s; E [{ Φ }]).
  Proof.
    rewrite envs_entails_eq=> ?? ->.
    (* We want [pure_exec_fill] to be available to TC search locally. *)
    pose proof @pure_exec_fill.
    rewrite -total_lifting.twp_pure_step //.
  Qed.

 From iris Require Import bi.interface.
 Import uPred.

  Lemma tac_wp_send
    Δ Δ' s E i K l m vl Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦ vl)%I →
    match envs_simple_replace i false (Esnoc Enil i (l ↦ (vl ∪ {[m]}))) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ #()) @ s; E {{ Φ }})
    | None => False
    end ->
    envs_entails Δ (WP fill K (chan_lang.Send (LitV $ LitLoc l) (Val m)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq=> ???. intros.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    rewrite -wp_bind. eapply wand_apply; first by eapply wp_send.
    rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. apply later_mono, sep_mono_r, wand_mono; eauto.
  Qed.

  Ltac wp_value_head :=
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
        eapply tac_wp_value_nofupd
    | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
        eapply tac_wp_value_nofupd
    (* | |- envs_entails _ (wp ?s ?E (Val _) _) => *)
    (*     eapply tac_wp_value *)
    | |- envs_entails _ (twp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
        eapply tac_twp_value_nofupd
    | |- envs_entails _ (twp ?s ?E (Val _) (λ _, twp _ ?E _ _)) =>
        eapply tac_twp_value_nofupd
    (* | |- envs_entails _ (twp ?s ?E (Val _) _) => *)
    (*     eapply tac_twp_value *)
    end.

  Ltac wp_finish :=
    wp_expr_simpl;
    try wp_value_head;
    pm_prettify.

  Lemma awp_send (c : loc) (M : gset chan_lang.val) (m : chan_lang.val) :
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

  (* TODO: After defining logical atomic spec to [tryrecv], look at
     [heap_lang.lib.atomic_heap] for atomic heap implementation. *)
End atomic_invariants.
