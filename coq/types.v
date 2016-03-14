From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.

(* Utility from Coq lists we need for induction *)

Fixpoint In {A:Type} (a:A) (l: seq A) : Prop :=
match l with
  | [::] => False
  | b :: m => b = a \/ In a m
end.

Inductive numeric := | S8 | U8 | S16 | U16 | S32 | U32 | S64 | U64 .

                       
Inductive ctype :=
| Int (_:numeric) 
| Pointer : ctype -> ctype
| Struct: seq ctype -> ctype
| Bot | ErrorType.

Definition Int8 := Int S8.
Definition UInt8 := Int U8.
Definition Int16 := Int S16.
Definition UInt16 := Int U16.
Definition Int32 := Int S32.
Definition UInt32 := Int U32.
Definition Int64 := Int S64.
Definition UInt64 := Int U64.


Fixpoint SizeOf (t:ctype) :=
    match t with 
    | Pointer _ => 8
    | Struct els => foldl (fun x y=>x + y) 0 (map SizeOf els) 
    | Int S8 | Int U8 => 1
    | Int S16 | Int U16 => 2
    | Int S32 | Int U32 => 4
    | Int S64 | Int U64 => 8
    | _ => 0
    end.


Theorem ctype_better_ind (P: ctype -> Prop):
(forall nt, (P (Int nt)))->
(forall p: ctype, P p -> P (Pointer p) ) ->
(forall l, (forall e, In e l -> P e) -> P (Struct l)) ->
(P Bot) -> (P ErrorType) ->
(forall t:ctype, P t).
Proof.
  move=> Hnt Hptr Hstr Hbot Herr. 
  fix 1.
  have StructProof: forall l : seq ctype, P (Struct l). {
    move=> l. apply Hstr. elim: l.
    - by move=> _ [].
    - move=> a l Hin e /= [].
      + by move=><-; exact (ctype_better_ind a).
      + apply Hin.
  }    
  move=>[]; try by [clear ctype_better_ind].
- elim; try by [ clear ctype_better_ind; try move=> c; apply Hptr].
Qed.

Scheme Equality for numeric.

Fixpoint ctype_beq (x y: ctype) {struct x} : bool  :=
let fix process (xs ys: seq ctype) := match xs,ys with
                                        | nil, nil => true
                                        | x::xs, y::ys => ctype_beq x y && process xs ys
                                        | _, nil
                                        | nil, _ => false
                                      end in                                      
match x, y with
  | Int x, Int y => numeric_beq x y
  | Bot, Bot
  | ErrorType, ErrorType => true
  | Pointer px, Pointer py => ctype_beq px py
  | Struct xs, Struct ys => process xs ys
  | _, _ => false
end.

Local Lemma Struct_cons: forall x xs y ys, Struct xs = Struct ys /\ x = y <-> Struct (x::xs) = Struct (y::ys).
Proof. by move=> x xs y ys; split; [move=> [[]] => -> -> | move=> [] -> ->]. Qed.      

Theorem ctype_eqP: Equality.axiom ctype_beq.
Proof.
rewrite /Equality.axiom.
fix 1.
move=> x.
elim x; try do [ by case; constructor ].
(* Pointer *)
- move=>[];  move=> y; elim y; try do [try case; by constructor].
  move => z H2 //=.
  elim; try by constructor.
  move=> c H.
  move: (H2 c).
  move: (ctype_beq z c) => [] [].
    by move=> ->; constructor.
    by move=> *;  constructor; case.
    by move=> ->; constructor.
    by move=> *;  constructor; case.
(* Struct *)
- move =>l.
  elim ; try by constructor.
  
  clear x. 
  elim: l.
  + case; by [apply ReflectT | move=> a l; apply ReflectF]. 
  + move=> a l H []; first by apply ReflectF.
    move=> b m.
    move: (H m) => Hm.
    inversion  Hm as [Hstructs Hstreq| Hstructs Hstreq].
    * destruct (ctype_beq (Struct (a :: l)) (Struct (b :: m))) eqn: Heq_str_big.
      ** apply ReflectT. apply Struct_cons.
      simpl in Heq_str_big.
      split; first by exact Hstructs.
      destruct (ctype_eqP a b) as [Hab|Hab]; [ by exact Hab| by exfalso].
    * apply ReflectF => H_str_big. move: (H m) => Hrefl_eqlm.
      move: (ctype_eqP a b) => Hrefl_ab.
      inversion Hrefl_ab as [Hab Heq_ab|Hab Heq_ab].
      simpl in Heq_str_big. rewrite <- Heq_ab in Heq_str_big. 
      simpl in Heq_str_big. rewrite <-Hstreq in Heq_str_big.
        by inversion Heq_str_big.
    * inversion H_str_big. by exact (Hab H1).
      destruct  (ctype_beq (Struct (a :: l)) (Struct (b :: m))) eqn: Hsab; [apply ReflectT| apply ReflectF].
      ** simpl in Hsab.
      rewrite <-Hstreq in Hsab.
      rewrite Bool.andb_false_r in Hsab. by inversion Hsab.
      **  move=> Heq.
      inversion Heq.
      rewrite H2 in Hstructs. by exfalso.  
Qed.      

Canonical ctype_eqMixin := EqMixin ctype_eqP.
Canonical ctype_eqType := EqType ctype ctype_eqMixin.

(*Definition int_union (x y: numeric) : numeric := match x,y with *)


 
