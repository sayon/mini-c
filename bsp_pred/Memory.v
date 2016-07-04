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
                       el_type: ctype;
                       contents: seq value;
                       (*_ : forall (v:value), v \in contents -> match v with
                                                                 | Value t v => t == el_type
                                                                 | Garbage 
                                                                 | Deallocated
                                                                 | Error => true
                                                               end*)
                                                                
                     }.

Definition block_beq (x y: block) :=
  (  region x == region y  )
    && (block_id x == block_id y )
    && (block_size x == block_size y)
    && (el_type x == el_type y)
    && (contents x == contents y).

Theorem block_eqP: Equality.axiom block_beq.
  move => x y.
  case (block_beq x y) eqn: H.  
  destruct x, y; constructor.
  rewrite /block_beq in H.
  simpl in H.
  do 4! [ move /andP in H; destruct H].
  by rewrite (eqP H0) (eqP H1) (eqP H2) (eqP H3) (eqP H).
  constructor.
  case.
  move=> H'; subst.
  destruct y.
  rewrite /block_beq in H.
  by do 5! rewrite (eq_refl _) in H.
Defined.


Canonical block_eqMixin := EqMixin block_eqP.
Canonical block_eqType := EqType block block_eqMixin.


Definition block_mod
           mod_region
           mod_block_id
           mod_block_size
           mod_el_type
           mod_contents
           b
  :=
    match b with
      | mk_block q w e  t y => mk_block
                                  (mod_region q)
                                  (mod_block_id w)
                                  (mod_block_size e)
                                  (mod_el_type t)
                                  (mod_contents y)
                                  
    end.
          
Definition block_mod_cont f b := block_mod id id id id f b.


Definition ErrorBlock := mk_block Data 0 0 ErrorType [::].
