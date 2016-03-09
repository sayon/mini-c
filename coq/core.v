From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint.
From Coq.Strings Require Import Ascii String.


Module BSPC.
Section TypeSystem.
  (* Utility from Coq lists we need for induction *) 
  Fixpoint In {A:Type} (a:A) (l: seq A) : Prop :=
    match l with
      | [::] => False
      | b :: m => b = a \/ In a m
    end.
  
  Inductive ctype :=
  | Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 
  | Pointer : ctype -> ctype
  | Struct: seq ctype -> ctype
  | Bot | ErrorType.

  Theorem ctype_better_ind (P: ctype -> Prop):
    (P Int8) -> (P UInt8) -> (P Int16) -> (P UInt16) ->
    (P Int32) -> (P UInt32) -> P (Int64) -> P (UInt64) ->
    (forall p: ctype, P p -> P (Pointer p) ) ->
    (forall l, (forall e, In e l -> P e) -> P (Struct l)) ->
    (P Bot) -> (P ErrorType) ->
    (forall t:ctype, P t).
  Proof.
    move=> Hi8 Hui8 Hi16 Hui16 Hi32 Hui32 Hi64 Hui64 Hptr Hstr Hbot Herr.
    fix 1.
    have StructProof: forall l : seq ctype, P (Struct l). {
      move=> l. apply Hstr. elim: l.
      + by move=> _ [].
      + move=> a l Hin e /= [].
        * by move=><-; exact (ctype_better_ind a).
        * apply Hin.
    }    
    move=>[]; try by [clear ctype_better_ind].
    - elim; try by [ clear ctype_better_ind; try move=> c; apply Hptr].
  Qed.
  
  Fixpoint ctype_eq (x y: ctype) {struct x} : bool  :=
    let fix process (xs ys: seq ctype) := match xs,ys with
                                            | nil, nil => true
                                            | x::xs, y::ys => ctype_eq x y && process xs ys
                                            | _, nil
                                            | nil, _ => false
                                          end in                                      
    match x, y with
      | Int8, Int8
      | UInt8, UInt8
      | Int16, Int16
      | UInt16, UInt16
      | Int32, Int32
      | UInt32, UInt32
      | Int64, Int64
      | UInt64, UInt64
      | Bot, Bot
      | ErrorType, ErrorType => true
      | Pointer px, Pointer py => ctype_eq px py
      | Struct xs, Struct ys => process xs ys
      | _, _ => false
    end.

  Lemma Struct_cons: forall x xs y ys, Struct xs = Struct ys /\ x = y <-> Struct (x::xs) = Struct (y::ys).
    move=> x xs y ys.
    split.
      by move=> [[]] => -> ->.
      by move=> [] -> ->.
  Qed.      
    
  Lemma ctype_eqP: Equality.axiom ctype_eq.
  Proof.
    rewrite /Equality.axiom.
    fix 1.
    move=> x.
    elim x; try do [ by case; constructor ].
    (* Pointer *)
    move=> c H y; elim y; try do [by constructor].
    move => z H2 //=. 
    move: (ctype_eq c z) (H z) => [] [].
    - by move=>->; apply ReflectT.
    - by move=> *; apply ReflectF; case.
    - by move=>->; apply ReflectT.
    - by move=> *; apply ReflectF; case.
      move =>l y.
      elim y; try by constructor.
      
      clear x y. move => m.
      elim: l m.
      case. by apply ReflectT.
      by move=> a l; apply ReflectF.
      move=> a l H [].
      by apply ReflectF.
      move=> b m.
      move: (H m) => Hm.
      inversion Hm.
      destruct (ctype_eq (Struct (a :: l)) (Struct (b :: m))) eqn: Heq.
      apply ReflectT.
      apply Struct_cons.
      split.
      exact H1.
      simpl in Heq.
      move: (ctype_eqP a b) => Hr.
      inversion Hr. exact H3.
      rewrite <- H2 in Heq.
      
      simpl in Heq.
      inversion Heq.
      apply ReflectF.
      move=> Hc.
      move: (H m) => Heq'.
      move: (ctype_eqP a b) => Hab.
      inversion Hab.
      simpl in Heq.
      rewrite <- H2 in Heq.
      simpl in Heq.
      rewrite <-H0 in Heq.
      inversion Heq.
      inversion Hc.
      exact (H3 H5).

      destruct  (ctype_eq (Struct (a :: l)) (Struct (b :: m))) eqn: Hsab; [apply ReflectT| apply ReflectF].

      simpl in Hsab.
      rewrite <-H0 in Hsab.
      rewrite Bool.andb_false_r in Hsab. inversion Hsab.

      move=> Heq.
      inversion Heq.
      rewrite H4 in H1.      
      by apply H1.
  Qed.      

  Canonical ctype_eqMixin := EqMixin ctype_eqP.
  Canonical ctype_eqType := EqType ctype ctype_eqMixin.

End TypeSystem.


Definition block_id := nat. Definition block_offset := nat.

Record ptr (t: ctype) := mk_ptr { number: block_id; offset: block_offset; }.
Inductive storage := | Heap | Stack | Data | Text | ReadOnlyData.
Fixpoint coq_type (t: ctype) : Set :=
  match t with
    | Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 => int
    | Pointer t => ptr t
    | Struct ls => seq nat
    | Bot => unit
    | Error => False
  end.

Inductive value (t: ctype) : Set := | Value : coq_type(t) -> value t | Garbage | Deallocated.
Inductive block := mk_block {
                       region: storage;
                       id: block_id;
                       size: nat;
                       el_type: ctype;
                       contents: seq (value el_type)
                              }.
Inductive binop : Set := | Add | Sub | Mul | Div | LAnd | LOr .
Inductive unop: Set := | Neg | Invert | Not | Convert (to:ctype).
Inductive expr :=
| Binop: binop -> expr -> expr -> expr 
| Unop: unop -> expr-> expr
| Lit t: value t->expr
| Var : string -> expr
| Call: block_id -> seq expr -> expr.
(* we implicitly provide a pointer to a block to write result into *)

Record var_descr := declare_var { var_name: string; var_type: ctype }.
Inductive statement :=
| Skip
| Assign: var_descr -> expr -> statement
| Alloc: storage -> ctype -> nat -> statement
| If: expr -> statement -> statement -> statement
| For: statement -> expr -> statement -> statement -> statement
| While: expr -> statement -> statement
| CodeBlock: seq statement -> statement.

Record function := mk_fun{
                       fun_id: block_id;
                       args: seq ctype;
                       returns: ctype;
                       body: seq statement;
                     }.
Record static_ctx := mk_static_ctx {
                        functions: seq (string * function);
                        variables: seq (seq var_descr);
                      }.
Record dynamic_ctx := mk_prog { memory: seq block }.




(* Need to be able to compare types *)
Fixpoint type_solver {code: static_ctx}  (e: expr) : ctype:= Bot.








                              
(*


Fixpoint option_function (p: function -> bool) (functions: seq (string*function)) : option function :=
  match functions with
    | (_,f)::xs => if (p f) then Some f else option_function p xs
    | [::] => None
  end.

Fixpoint function_return_type (for_id: block_id) (functions: seq (string*function)) : ctype :=
  match functions with
    | (_,f)::xs => if (fun_id f == for_id) then returns f else function_return_type for_id xs
    | [::] => ErrorType
  end. 
 *)
