From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
(* IY: What's the difference between [atomic] at [iris.program_logic]
 and [bi.lib]? *)
From iris.bi Require Import atomic derived_laws interface.


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

  Lemma tac_wp_send
    Δ Δ' s E i K l v v' vl vl' Φ :
    v ∈ vl ->
    v' ∈ vl' ->
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦ vl)%I →
    match envs_simple_replace i false (Esnoc Enil i (l ↦ vl')) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})
    | None => False
    end ->
    envs_entails Δ (WP fill K (chan_lang.Send (LitV $ LitLoc l) (Val v')) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq=> ???. intros.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    rewrite -wp_bind. eapply bi.wand_apply; first by eapply wp_send.
    rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
    rewrite right_id.
  Admitted.

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
      end
    with add_item Ki vs K e :=
      lazymatch vs with
      | []               => go (Ki :: K) (@nil (val * val)) e
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

  (* TODO: [v = ()] in conclusion. *)
  Lemma awp_send (c : loc) (M : gset chan_lang.val) (m : chan_lang.val) :
    ⊢ <<< ∀ v, c ↦ M >>> send(c, m) @ ⊤ <<< c ↦ (M ∪ {[m]}), RET v >>>.
  Proof.
    iIntros (Φ) "AU".
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    (* reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ _ _ _ _ K)). *)

    (* Mod ("Hclose" with "H↦") as "HΦ". done. *)

    (* wp_store. iMod ("Hclose" with "H↦") as "HΦ". done. *)

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
End atomic_invariants.
