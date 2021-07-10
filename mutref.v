(* See [Stack Item 4 : Mutable references] *)

(* IY: Some stub code for an atomic heap from heap_lang, in case it helps..*)
(* An atomic heap defined over the channel primitives in the language. *)
(* The idea is that *)

(** A general logically atomic interface for a heap. *)
Class atomic_heap {Σ} `{!chanG Σ} := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  free : val;
  load : val;
  store : val;
  cmpxchg : val;
  (* -- predicates -- *)
  mapsto (l : loc) (dq: dfrac) (v : val) : iProp Σ;
  (* -- mapsto properties -- *)
  mapsto_timeless l q v :> Timeless (mapsto l q v);
  mapsto_fractional l v :> Fractional (λ (q : Qp), mapsto l (DfracOwn q) v);
  mapsto_persistent l v :> Persistent (mapsto l DfracDiscarded v);
  mapsto_as_fractional l q v :>
    AsFractional (mapsto l (DfracOwn q) v) (λ q, mapsto l (DfracOwn q) v) q;
  mapsto_agree l dq1 dq2 v1 v2 : mapsto l dq1 v1 -∗ mapsto l dq2 v2 -∗ ⌜v1 = v2⌝;
  mapsto_persist l dq v : mapsto l dq v ==∗ mapsto l DfracDiscarded v;
  (* -- operation specs -- *)
  alloc_spec 
  alloc_spec (v : val) :
    {{{ True }}} alloc v {{{ l, RET #l; mapsto l (DfracOwn 1) v }}};
  free_spec (l : loc) (v : val) :
    {{{ mapsto l (DfracOwn 1) v }}} free #l {{{ l, RET #l; True }}};
  load_spec (l : loc) :
    ⊢ <<< ∀ (v : val) q, mapsto l q v >>> load #l @ ⊤ <<< mapsto l q v, RET v >>>;
  store_spec (l : loc) (w : val) :
    ⊢ <<< ∀ v, mapsto l (DfracOwn 1) v >>> store #l w @ ⊤
      <<< mapsto l (DfracOwn 1) w, RET #() >>>;
  (* This spec is slightly weaker than it could be: It is sufficient for [w1]
  *or* [v] to be unboxed.  However, by writing it this way the [val_is_unboxed]
  is outside the atomic triple, which makes it much easier to use -- and the
  spec is still good enough for all our applications.
  The postcondition deliberately does not use [bool_decide] so that users can
  [destruct (decide (a = b))] and it will simplify in both places. *)
  cmpxchg_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<< ∀ v, mapsto l (DfracOwn 1) v >>> cmpxchg #l w1 w2 @ ⊤
      <<< if decide (v = w1) then mapsto l (DfracOwn 1) w2 else mapsto l (DfracOwn 1) v,
        RET (v, #if decide (v = w1) then true else false) >>>;
}.
Global Arguments atomic_heap _ {_}.

