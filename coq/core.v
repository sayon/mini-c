 From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint.
From Coq.Strings Require Import Ascii String.

Module bspc.
Definition block_id := nat. Definition block_offset := nat.
Inductive ctype :=
| Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 
| Pointer : ctype -> ctype
| Struct: seq ctype -> ctype
| Bot | ErrorType.
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
Fixpoint type_solver {code: static_ctx}  (e: expr) : ctype:= Bot.


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
    | Struct (x::xs), Struct (y::ys) => ctype_eq x y && process xs ys
    | Struct nil, Struct nil => true
    | _, _ => false
end.

Lemma eq_ptr: forall x:ctype, ctype_eq (Pointer x) x = false.
Proof. by elim. Qed.

Lemma eq_ptr_r: forall x:ctype, ctype_eq x (Pointer x) = false.
Proof. elim =>//=. by case. Qed.    

Lemma eq_ptr': forall x:ctype, ~ Pointer x = x.
Proof.  rewrite /not. elim; congruence. Qed.

Lemma eq_ptr_ptr: forall x:ctype, ctype_eq (Pointer (Pointer x)) x = false.
Proof. by elim. Qed.

Lemma eq_ptr_ptr': forall x:ctype, ~ Pointer( Pointer x) = x.
Proof. rewrite /not. elim; congruence. Qed.

Lemma eq_str_ptr: forall (x:seq ctype) (y: ctype),  ~ Struct x = Pointer y.
Proof. rewrite /not. elim; congruence. Qed.

Local Lemma eq_ptr_prop: forall (x y: ctype), Pointer x = Pointer y <-> x = y.
Proof. by move=> x y; split; [ congruence | move ->]. Qed.

Local Lemma eq_ptr_bool: forall (x y: ctype), ctype_eq (Pointer x) (Pointer y) <-> ctype_eq x y .
Proof. by []. Qed. 
(*
Lemma ctype_eq_sym: symmetric ctype_eq.
Proof.
  rewrite /symmetric.
  elim; elim; try do [by [] | by case]; try by move=> H // =>[] //= => [] //= [] //= [] //=. 
  * move=> x H1 H2 [] //=.  by case.
  * move=> x H1 [] //=. by case.
  * move=> [] //=. by case.
  * move=> x. (* Donnez-moi une idee! *)

    elim. move=> H.
    simpl.
    case =>//=.
    
    
    l H. elim l.
  + simpl.
    
    case => //=. case =>//=. move => y. 
    case => //=.
    
    
      by [].
      

    case => //. move=> a m. move: (H (Struct m)) => H'.
    elim l; elim m =>//=.
    
    simpl.
    
    rewrite {1 2}/ctype_eq.
    cbv beta.
    
    cbv delta.
         
    
    cbv iota.
    
    cbv delta.
    cbv zeta.
    
    cbv iota.
    cbv iota.    
    
    cbv iota.
    cbv zeta.
    cbv delta.
    cbv iota.
    cbn zeta.
    
    beta in H'.
    
    Arguments  ctype_eq: simpl nomatch.
    Opaque process in ctype_eq.
    simpl.
    simpl in H'.
    
    simpl.
    simpl in H'.     
    rewrite <- H'.
    elim => //. move => a m H'. simpl.

    [] //. move=> a m. move: (H (Struct m)) => H'. simpl. compute.  simpl. simpl. simpl in H'. rewrite <- H'. by []. simpl. 
    case => //=. intros.

    simpl. case => //=. move=> [] //=.  
    move=> []//= [] //=. case. case. 
      ase z; try by []. by case.  simpl. 
    rewrite <-H3.

*)

Lemma ctype_eqP: Equality.axiom ctype_eq.
  move=> x y.
  elim x; elim y; try do [by constructor | elim; by constructor].
  (* Eliminates simple cases like Int8 = Int8 or Int8 <> Int8 *)  
  * clear x y. move=> x H1 y H2. (* :((( *) 
    destruct (ctype_eq (Pointer y) (Pointer x)) eqn: Heq.
    apply ReflectT.
    simpl  in Heq.
    move: (H1 y) => H3.
    rewrite Heq in H3.
    Check ReflectT.
    ReflectT in H3. 
    
    
    simpl.
    
    move=>x H1 y H2.
    simpl.
    
    move: H2 (Pointer x).
    move => H' z.
    admit.

  * clear x y. move=> x H [] => //=; by constructor.
  * clear x y. move=> xs ys. elim xs; elim ys; try  by constructor.
    + move=> x ts H1.  simpl.
    
    
    intros.
    
    have Heq:(ctype_eq y x = true) \/ (ctype_eq y x = false ).
    Check orP.
    Print orP.
    apply orP.
    apply /orP.
      by case (ctype_eq y x).
    move /eqP in Heq.
    
    inversion Heq.
    move /orP in Heq. inversion in Heq. destruct Heq.
    rewrite /orP in Heq.
    simpl.
    move /eqP.
    apply negPf.
    rewrite . orbN.
    
    destruct (ctype_eq y x)  [Htrue | Hfalse].
    
    case: (ctype_eq y x).
    apply ReflectT.
    
    constructor.
    
    congruence.
    
    simpl.
    
    apply ReflectT.
    rewrite eq_ptr_prop. (* WTF ? *)
    
    
    rewrite /ctype_eq.
    
    ove =>y H2.
    generalize dependent y. 

    Print reflect.
    refine (ReflectT _ _).

    move /boolP. rewrite (eq_ptr_bool y x). rewrite <- eq_ptr_prop.

    intros. rewrite (eq_ptr_prop c0). clear x y.  move => [].
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor].
    move=> x H1 y H2.
    move=> H1 []; try by constructor.  move =>[] *; by [move =>*; constructor]. 
    
    move=> H1 []; try by constructor. move => [] => H. by constructor.intros. by constructor.

    done. compute.  eq_str_ptr. move =>H2. constructor.
    move : (H1 (Pointer x)).
    rewrite (eq_ptr x) => H3.
    move: (H3 ( ReflectF (eq_ptr' x) )) => H4.
    compute. constructor.
    congruence.
    
    rewrite (eq_ptr_ptr x) in H3.
    move=> H4.
    Check ReflectF (eq_ptr_ptr' x).
    Check H3 (ReflectF (eq_ptr_ptr' x)).    
    rewrite (eq_ptr' x) in Hab.
    .
    move => H2.
    Print ReflectF.
Print not.    apply ReflectF in Hab.
    rewrite (eq_ptr (Pointer x)) in Hab.
    rewrite ReflectF in Hab.
    
  + move => ->. destruct (H1 x).

    move: (H1 (Pointer x))=> [].
    apply (H1 x). apply ReflectT.
    move: (H1 (Pointer x))=>H2.

    destruct H2 as [H2| H2].
    
    destruct H2.
    
    apply ReflectF.
    
    destruct y.
    
    compute.
  * 










                              
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
