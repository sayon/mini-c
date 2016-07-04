From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool eqtype seq ssrnat.
From mathcomp.algebra Require Import ssrint.
From Coq.Strings Require Import Ascii String.
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


(*** Strings ***)

Scheme Equality for string.
Lemma ascii_beq_refl a: ascii_beq a a = true.
Proof. by case a; case; case; case; case; case; case; case; case; vm_compute. Qed.

Theorem ascii_eqP: Equality.axiom ascii_beq.
Proof.
  rewrite /Equality.axiom.
  move=> x y.
  case  (ascii_beq x y) eqn: H;  constructor.
  move: x y H.
  case; move=> q w e r t y u i.
  case; move=> q' w' e' r' t' y' u' i'.
  move: q q' w w' e e' r r' t t' y y' u u' i i'.
  do 8! [case; case => //= ].
  rewrite /not.
  move=> Heq. move: Heq H => ->. by rewrite ascii_beq_refl.
Qed.

Canonical ascii_eqMixin := EqMixin ascii_eqP.
Canonical ascii_eqType := EqType ascii ascii_eqMixin.

Lemma string_beq_refl x: string_beq x x = true.
Proof.
  elim x =>//. move=> a s H /=. by rewrite ascii_beq_refl.
Qed.

Lemma string_eqP: Equality.axiom string_beq.
Proof.
  rewrite /Equality.axiom.
  elim; first by case; constructor.
  move=> a s H []; first by constructor.
  move=> b t.
  simpl.
  case (ascii_beq a b) eqn: Heq; move /eqP in Heq.
  rewrite Heq.
  case (H t).
  -  by move=> ->; constructor.
  -  by move=> *; constructor; case.
  constructor. by case.
Qed.

Canonical string_eqMixin := EqMixin string_eqP.
Canonical string_eqType := EqType string string_eqMixin.
  

(*** Decidable quality and reflect *)
Definition eq_dec T := forall x y: T, {x = y} + {~ x = y}.
Structure decidable_eq_mixin := mk_dec_eq {
                                    carrier: Type;
                                           eq_dec_for : eq_dec carrier
                                         }
.

Canonical Structure string_dec_eq_mixin := mk_dec_eq string string_eq_dec.

Scheme Equality for nat.
Canonical Structure nat_dec_eq_mixin := mk_dec_eq nat nat_eq_dec.
Scheme Equality for unit.
Canonical Structure unit_dec_eq_mixin := mk_dec_eq unit unit_eq_dec.

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
Canonical int_dec_eq_mixin := mk_dec_eq int int_eq_dec.

Ltac depcomp H := apply EqdepFacts.eq_sigT_eq_dep in H; apply Coq.Logic.Eqdep.EqdepTheory.eq_dep_eq in H.

Ltac eq_comp c x y := move: (c x y); case; last try do [by [right; case]| right;case; let H' := fresh "H" in move=>H'; by depcomp H'];
                      first try let H' := fresh "H" in move=> H'; subst; try by left.

Ltac eq_compi x y := move: (eq_dec_for _ x y); case; last try do [by [right; case]| right;case; let H' := fresh "H" in move=>H'; by depcomp H'];
                      first try let H' := fresh "H" in move=> H'; subst; try by left.

Theorem pair_eq_dec {T U}: eq_dec T -> eq_dec U -> eq_dec (prod T U).
  move=> HT HU [x y] [a b].
  eq_comp HT x a.
  eq_comp HU y b.
Qed.

Canonical Structure pair_eq_dec_mixin {T U PT PU} := Eval hnf in mk_dec_eq (prod T U) (@pair_eq_dec T U PT PU).

Theorem t: eq_dec (int* nat).
  move=> [a b] [c d].
  eq_compi a c.
  eq_compi b d.
Qed.
          
  
(*** seq helpers *)
Fixpoint  zipwith_when_eqlength {A B} (f: A->B->bool) (x: seq A) (y: seq B) : bool :=
  match x,y with
    | x::xs, y::ys => f x y &&  zipwith_when_eqlength f xs ys
    | nil, nil => true
    | nil, _ | _, nil => false
  end.     

Theorem seq_eq_dec {T}: eq_dec T -> eq_dec ( seq T ).
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

Definition enumerate {T} (s:seq T) : seq (nat * T) :=
  zip (iota 0 (size s)) s.

Definition mod_at {T} (def:T) (i:nat) (mod:T->T)  (s:seq T) := set_nth def s i (mod 
  match option_nth s i with
    | Some el => el
    | None => def
  end).


Definition skip_at {T} (n:nat)  (s:seq T) : seq T :=
  take n s ++ drop n.+1 s.

Definition osplit_seq {T} (i:nat) (s: seq T) : T? * seq T :=
  (option_nth s i, skip_at i s).

Definition insert_at {T} (i:nat) (t:T) (s:seq T) : seq T :=
  (take i s) ++ t::(drop i s).


Definition slice {T} (x s: nat) (sq : seq T) :seq T :=
  take s $ drop x sq.

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

Definition is_some {T} (x:option T) : bool :=
  match x with | Some _ => true | _ => false end.

Definition extract_some {T} (x:  T ? ? ) : T? :=
  match x with
    |Some x => x
    | None => None
  end.


Definition option_bind {T U} (f:T-> U?) (x:T?) :=
  match x with
    | Some x => f x
    | None => None
  end.
                              

Fixpoint  fill {T} (v: T)  (sz: nat)  : seq T :=
  match sz with | n .+1 => v :: (fill v n) | 0 => [::] end.

Definition transformations {A} (init:A) (ts: seq (A->A)) : A :=
  foldl (fun x f=> f x) init ts.


Definition add_n_z (x:nat) (y:int) :=
  match intZmod.addz x y with
    | Negz r => None
    | Posz r => Some r
  end.
