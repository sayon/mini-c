From mathcomp.ssreflect Require Import ssreflect eqtype seq ssrbool ssrnat.


Require Import Common Types.
(* Different memory regions *)
Inductive storage := | Heap | Stack | Data | Text | ReadOnlyData.

Scheme Equality for storage. 
Definition storage_eqP := reflect_from_dec storage_eq_dec.
Canonical storage_eqMixin := EqMixin storage_eqP.
Canonical storage_eqType := EqType storage storage_eqMixin.


Inductive block := mk_block {
                       region: storage;
                       block_id: nat;
                       block_size: nat;
                       shared_with: seq nat;
                       el_type: ctype;
                       contents: seq value;
                       (*_ : forall (v:value), v \in contents -> match v with
                                                                 | Value t v => t == el_type
                                                                 | Garbage 
                                                                 | Deallocated
                                                                 | Error => true
                                                               end*)
                                                                
                     }.


Theorem block_eq_dec : eq_dec block.
  rewrite /eq_dec.
  move => [r1 i1 s1 w1 t1 c1] [r2 i2 s2 w2 t2 c2].
  case( r1 == r2) eqn: Hr; case (i1 == i2) eqn:Hi;
  case( w1 == w2) eqn: Hw;
  case( s1 == s2 ) eqn: Hs; case (t1 == t2) eqn: Ht;
  move /eqP in Hr; move /eqP in Hi; move /eqP in Hs; move /eqP in Ht; move /eqP in Hw;
  subst;  try case (c1 == c2) eqn: Hc; try move /eqP in Hc;  subst; try by [right; by case].
  by left. Qed.

Definition block_eqP := reflect_from_dec (block_eq_dec).

Canonical block_eqMixin := EqMixin block_eqP.
Canonical block_eqType := EqType block block_eqMixin.

Definition block_mod_cont f b :=
  match b with
    | mk_block q w e r t C => mk_block q w e r t (f C)
  end.
