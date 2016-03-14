From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint.
From Coq.Strings Require Import Ascii String.

Require Import types.
Require Import UtilString.

Definition block_id := nat. Definition block_offset := nat.

Record ptr (t: ctype) := mk_ptr { number: block_id; offset: block_offset; }.
Inductive storage := | Heap | Stack | Data | Text | ReadOnlyData.
Fixpoint coq_type (t: ctype) : Set :=
  match t with
    | Int _ => int
    | Pointer t => ptr t
    | Struct ls => seq nat
    | Bot => unit
    | Error => False
  end.

Inductive value (t: ctype) : Set := | Value (v: coq_type(t)) | Garbage | Deallocated.
Inductive block := mk_block {
                       region: storage;
                       id: block_id;
                       size: nat;
                       el_type: ctype;
                       contents: seq (value el_type)
                     }.

Record var_descr := declare_var { var_name: string; var_type: ctype }.
Definition var_descr_beq (x y: var_descr) : bool :=
(  (var_name x) == (var_name y) ) && ((var_type x) == (var_type y)).

Theorem var_descr_eqP: Equality.axiom var_descr_beq.
Proof.
  rewrite /Equality.axiom.
  move=> x y.
  case (var_descr_beq x y) eqn:H; constructor;
  destruct x ; destruct y;
  move: H; rewrite /var_descr_beq.
  by move /andP =>[] /= => /eqP -> => /eqP ->.
  move /andP => H. rewrite /not in H. move=> H'.  apply H. by inversion H'. 
Qed.

Canonical var_descr_eqMixin := EqMixin var_descr_eqP.
Canonical var_descr_eqType := EqType var_descr var_descr_eqMixin.

  
Inductive binop : Set := | Add | Sub | Mul | Div | LAnd | LOr .
Scheme Equality for binop.

Inductive unop: Set := | Neg | Invert | Not | Convert (to:ctype) | Amp | Asterisk .
(* Scheme Equality for unop. Needs coq fix *)

Inductive expr :=
| Lit   (t:ctype) (_:coq_type(t))
| Var   (_:string)
| Binop (_:binop) (_ _: expr)
| Unop  (_:unop)  (_: expr)
| Call (_: string) (_: seq expr).


Inductive statement :=
| Skip
| Assign: var_descr -> expr -> statement
| Alloc: storage -> ctype -> option string -> nat -> statement
| If: expr -> statement -> statement -> statement
| For: statement -> expr -> statement -> statement -> statement
| While: expr -> statement -> statement
| CodeBlock: seq statement -> statement.

Record function := mk_fun{
                       fun_id: block_id;
                       fun_name: string;
                       args: seq ctype;
                       returns: ctype;
                       body: seq statement;
                     }.
Record static_ctx := mk_static_ctx {
                        functions: seq function;
                        variables: seq (seq var_descr);
                      }.
Record dynamic_ctx := mk_prog { memory: seq block }.

Record state : Set := mk_state { static: static_ctx; dynamic: dynamic_ctx }.


Definition option_find {T:Type} (p: T -> bool) (s:seq T): option T :=
  nth None (map (@Some T) s) (find (option_map p) (map (@Some T) s)).


Definition get_var (sc:static_ctx) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (flatten (variables sc)).


Definition get_fun (sc:static_ctx) (name:string) : option function :=
  option_find (fun p: function => fun_name p == name) (functions sc).

Fixpoint type_solver {sc: static_ctx}  (e: expr) : ctype:=
  match e with
    | Lit t _ => t
    | Var name => match get_var sc name with
                    | Some v => var_type v
                    | None => ErrorType
                  end
                    
    | Binop Add l r
    | Binop Sub l r
    | Binop Mul l r
    | Binop Div l r =>
      if @type_solver sc l == @type_solver sc r then @type_solver sc l else Bot
    | Binop _ l r => Bot
    | Unop _ o => @type_solver sc o
    | Call name cargs =>
      match get_fun sc name with
          | None => ErrorType
          | Some f => if (map (@type_solver sc) cargs == args f) then returns f else Bot
      end
        
                            
  end.



Definition LocVar t name := Alloc Stack t (Some name%string) 1. 
Definition ex1 := Alloc Stack (Int S64) (Some "x"%string) 1.
Definition ex2 := LocVar Int8 "x" .
Definition ex3 := LocVar (Pointer Int8) "y".


(*Fixpoint interpreter_step {program:static_ctx} {runtime:dynamic_ctx} (s: statement) {struct ident} : dynamic_ctx := .*)







                              
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
