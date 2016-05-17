From mathcomp.ssreflect Require Import all_ssreflect.


Structure sset (T:eqType) := SSet {
                                    seqOf :> seq T;
                                    uniqueness    : uniq seqOf }.

Canonical  sset_subType T := Eval hnf in [subType for seqOf T ].
Canonical  sset_eqMixin T:= Eval hnf in [eqMixin of sset T by <:].
Canonical  sset_eqType T := Eval hnf in  EqType (sset T) (sset_eqMixin T).

Lemma undup_preserves_in {T:eqType} (a:T) (l:seq T) : (a \in l) == (a \in undup l).
  move: l.
  elim =>//=.
  move=> a0 l IH.
  rewrite in_cons.
  case_eq (a == a0).
  move /eqP =><-.

  simpl.
  case_eq (a \in l).
    by move=><-.
      by rewrite in_cons eq_refl.
  move=> Ha.
  simpl.
  case_eq (a0 \in l) =>//=.
  by rewrite in_cons Ha.
Qed.


  
  Definition union {T:eqType} (x y:sset T) : sset T.
  refine (SSet _ (undup (x++y)) _).
  
  destruct x,y.
  simpl.
  move: (undup_uniq seqOf0) => H0.
  move: (undup_uniq seqOf1) => H1.

  

  elim seqOf0. by exact H1.

  move=> a l IH.
  apply undup_uniq.
  Defined.

  Definition intersect {T:eqType} (x y: sset T) : sset T.
    refine (SSet _ ( filter (fun e => e \in seqOf _ y) x ) _ ). 
    apply filter_uniq.
    exact: uniqueness x.
  Defined.

  Definition EmptySet t: sset t.
    refine (SSet _ [::] _).
    done.
  Defined.

  Definition mk_set {T:eqType} (x:T) : sset T. by refine ( SSet _ [:: x ] _ ).
  Defined.

  