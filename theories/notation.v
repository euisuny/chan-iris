From iris.program_logic Require Import language.
From chanlang Require Import lang locations.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.
Coercion LitProphecy : proph_id >-> base_lit.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).
Notation tryrecv e := (TryRecv (LitV $ LitLoc e%E)) (only parsing).
Notation send c m := (Send (LitV $ LitLoc c%E) (Val $ m)) (only parsing).
Notation fork e := (Fork (LitV $ LitLoc e%E)) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>
    lots of stuff bla bla bla bla bla bla bla bla
  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the ??: is indented
by two spaces in case the whole ??: does not fit on a single line. *)
Notation "??: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' '??:'  x ,  '/  ' e ']'") : expr_scope.
Notation "??: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' '??:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "??: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' '??:'  x ,  '/  ' e ']'") : val_scope.
Notation "??: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' '??:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%E e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(** Notations for option *)
Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

