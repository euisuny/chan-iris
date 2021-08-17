From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic weakestpre.
From chanlang Require Import
     class_instances lang notation network_ra tactics primitive_laws.
From iris.prelude Require Import options.

Import uPred.

Set Default Proof Using "Type".

Notation val := chan_lang.val.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

(* IY : used for [wp_bind]. finding "hole" in evaluation context *)
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
    (* TODO: Add TryRecv *)
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

Lemma tac_wp_expr_eval `{!chanGS Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
Lemma tac_twp_expr_eval `{!chanGS Σ} Δ s E Φ e e' :
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

Lemma tac_wp_value_nofupd `{!chanGS Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
Lemma tac_twp_value_nofupd `{!chanGS Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed.

Lemma tac_wp_pure `{!chanGS Σ} Δ Δ' s E K e1 e2 φ n Φ :
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
Lemma tac_twp_pure `{!chanGS Σ} Δ s E K e1 e2 φ n Φ :
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

Lemma tac_wp_send `{!chanGS Σ} Δ Δ' s E i K l m vl Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ vl)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ (vl ⊎ {[+m+]}))) Δ' with
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

Lemma tac_wp_tryrecv_fail `{!chanGS Σ} Δ Δ' s E l K Φ M i:
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ M)%I →
  M = ∅ -> envs_entails Δ' (WP fill K (Val $ NONEV) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (tryrecv l) @ s; E {{ Φ }}).
Proof.
  intros H1 H2.
  rewrite envs_entails_eq=> Heq Hfail.
  rewrite -wp_bind. eapply wand_apply.
  { eapply wp_tryrecv_fail; eauto. }
  rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
  apply later_mono, sep_mono_r.
  apply wand_mono; auto.
  rewrite Heq. done.
Qed.

Lemma tac_wp_value `{!chanGS Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by rewrite wp_value_fupd. Qed.
Lemma tac_twp_value `{!chanGS Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> ->. by rewrite twp_value_fupd. Qed.

Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, twp _ ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) _) =>
      eapply tac_twp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;
  try wp_value_head;
  pm_prettify.

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec -- *)
                                      (* handles trivial goals, including [vals_compare_safe]  *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Lemma tac_wp_bind `{!chanGS Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.
Lemma tac_twp_bind `{!chanGS Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_eq=> -> ->. by apply: twp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.
Tactic Notation "wp_lam" := wp_rec; auto.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.


Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; tac_suc H)
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; tac_suc H)
    | _ => fail 1 "wp_apply: not a 'wp'"
    end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
  fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail);
  last iAuIntro.

Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  (* Convert "list of hypothesis" into specialization pattern. *)
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with
        [SGoal $ SpecGoal GSpatial false [] Hs false]); [iAccu|iApplyHyp H])
    ltac:(fun cont => fail);
  last iAuIntro.
