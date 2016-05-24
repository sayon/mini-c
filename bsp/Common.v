From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool eqtype seq ssrnat.
From mathcomp.algebra Require Import ssrint.
 
Require Import Coq.Logic.Eqdep.

(*** Quality of life *)
Definition _dollar {Tx Ty} (x:Tx->Ty) (v:Tx) := x v.
Transparent _dollar.

Notation "x $ y" := (@_dollar _ _ x y) (at level 100, right associativity) :core_scope.
Hint Transparent _dollar.
Hint Unfold _dollar.

Definition cast {A B : Type} (a: A ) (H: A= B ) : B. rewrite <- H. exact a. Defined.
Notation "/! x" := (cast x _) (at level 100, no associativity).
Notation "x ?" := (option x) (at level 150, left associativity).




(*** Decidable quality and reflect *)
Definition eq_dec T := forall x y: T, {x = y} + {~ x = y}.
Scheme Equality for nat.
Scheme Equality for unit.

Definition reflect_from_dec {T} (cmp: eq_dec T): (@Equality.axiom T (fun x y => if cmp x y then true else false) ).
  rewrite /Equality.axiom. move=> x y.  
  move: (cmp x y) => [] //=; by constructor.
Qed.

Definition to_cmp {T} {E:eqType} (f: T-> E) (x y: T) := f x == f y .
Notation "//= f , .. , z // " := ( cons (to_cmp f) .. (cons  (to_cmp z) nil)  .. ).
Definition cmp_with {T:Type} (fs: seq (T->T->bool) ) (x y: T) := all (fun f=> f x y) fs.

Definition dec_from_reflect {T:eqType} (Hr: forall (x y:T), reflect (x=y) (x==y)) : eq_dec T.
  rewrite /eq_dec.
  move=> x y.  case: ( Hr x y ); by [apply left | apply right]. Defined.

Definition int_eq_dec := @dec_from_reflect int_eqType (@eqP int_eqType).
Ltac depcomp H := apply EqdepFacts.eq_sigT_eq_dep in H; apply Coq.Logic.Eqdep.EqdepTheory.eq_dep_eq in H.
  
(*** seq helpers *)
Fixpoint  zipwith_when_eqlength {A B} (f: A->B->bool) (x: seq A) (y: seq B) : bool :=
  match x,y with
    | x::xs, y::ys => f x y &&  zipwith_when_eqlength f xs ys
    | nil, nil => true
    | nil, _ | _, nil => false
  end.     

Theorem seq_eq_dec T: eq_dec T -> eq_dec ( seq T ).
  rewrite /eq_dec.
  move=> H s1 s2.
  elim: s1 s2.
  elim; by [left| right ; discriminate].
  move => a l IH [].
       * by right; discriminate. 
       * move=> y ys.
         move: (H a y) => [Ha|Ha]; move: (IH ys) => [Hy|Hy].
         ** inversion Hy; subst; by left.
         ** by right; case=> * *; subst. 
         ** by right; case. 
         ** by right; case.
Qed.

Definition option_find {T:Type} (p: T -> bool) (s:seq T): option T :=
  match filter p s with
    | nil => None
    | x::_ => Some x
    end.

Definition option_nth {T:Type} (s:seq T) (n: nat) := nth None (map (@Some _) s) n.


Definition skip_at {T} (n:nat)  (s:seq T) : seq T :=
  take n s ++ drop n.+1 s.


Definition cat_if_some {T} (l r: option ( seq T) ) : option (seq T):=
  match l, r with
    | Some x, Some y => Some ( x ++ y )
    | _, _ => None
    end.
Notation "x /++/ y" := (cat_if_some x y) (at level 35).



Theorem option_eq_dec (t:eqType) : eq_dec (option t).
  move => x y.
  destruct x, y; try by [left|right].
  case_eq (s == s0); [left|right]; move /eqP in H.
    by subst.
    by case.
Qed.

Canonical option_eqMixin (t:eqType) := EqMixin (reflect_from_dec (option_eq_dec t)).
Canonical option_eqType (t:eqType) := EqType (option t) (option_eqMixin t).



Fixpoint seq_unsome {T} (s: seq (option T)) : option (seq T) :=
  match s with
    | (Some x) :: xs => option_map (cons x) $ seq_unsome xs
    | nil => Some nil
    | None :: _ => None
  end.

Definition uncurry {a b c} (f: a -> b -> c) :  (a * b) -> c :=
  fun x => match x with
             | (m,n) => f m n
           end.

Definition unsome_bool x :=
  match x with
    | Some true => true
    | _ => false
  end.
Definition extract_some {T} (x:  T ? ? ) : T? :=
  match x with
    |Some x => x
    | None => None
  end.
