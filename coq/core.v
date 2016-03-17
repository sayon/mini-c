From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Program.
Require Import types.
Require Import UtilString.
Import Bspc.
Import intZmod.

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

Inductive value (t: ctype) : Set := | Value (v: coq_type(t)) | Garbage | Deallocated | Error.
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
Definition static_ctx_empty := mk_static_ctx [::] [::].

Record dynamic_ctx := mk_prog { memory: seq block }.
Definition dynamic_ctx_empty := mk_prog [::].

Record state : Set := mk_state { static: static_ctx; dynamic: dynamic_ctx }.


Definition option_find {T:Type} (p: T -> bool) (s:seq T): option T :=
  nth None (map (@Some T) s) (find (option_map p) (map (@Some T) s)).


Definition get_var (sc:static_ctx) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (flatten (variables sc)).


Definition get_fun (sc:static_ctx) (name:string) : option function :=
  option_find (fun p: function => fun_name p == name) (functions sc).

Definition eq_value_or_error {A:Type} (tl tr: ctype) (v: ctype -> ctype -> A) (err: A):A :=
 match tl, tr  with
    |Int S8, Int S8 
    |Int U8, Int U8 
    |Int S16, Int S16 
    |Int U16, Int U16 
    |Int S32, Int S32 
    |Int U32, Int U32 
    |Int S64, Int S64 
    |Int U64, Int U64 => v tl tr
    | _, _=> err 
  end
. 

Definition eq_or_err (tl tr: ctype) := eq_value_or_error tl tr (fun  x _ => x) ErrorType.

(*Definition eq_or_err (tl tr: ctype) (v: ctype -> ctype -> ctype): ctype :=
  match tl, tr  with
    |Int S8, Int S8 => Int S8
    |Int U8, Int U8 => Int U8
    |Int S16, Int S16 => Int S16
    |Int U16, Int U16 => Int U16
    |Int S32, Int S32 => Int S32
    |Int U32, Int U32 => Int U32
    |Int S64, Int S64 => Int S64
    |Int U64, Int U64 => Int U64
    | _, _=> ErrorType
  end
.*)


Fixpoint type_solver {sc: static_ctx}  (e: expr) : ctype:=
  let slv := @type_solver sc  in
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
      eq_or_err (slv l) (slv r)
    | Binop _ l r => Bot
    | Unop _ o => slv o
    | Call name cargs =>
      match get_fun sc name with
          | None => ErrorType
          | Some f => if (map slv cargs == args f) then returns f else Bot
      end
        
                            
  end.
 

(* Useful lemmas *)
(*
Lemma binop_preserves_type e op l r ctx kind : e = Binop op l r -> @type_solver ctx e = Int kind ->
                                               @type_solver ctx l = Int kind /\ @type_solver ctx r = Int kind.
Proof.
  move => -> //=.
  by case op; case (@type_solver ctx r);  case (@type_solver ctx l); do [case;case| case | done ].
Qed.  
*)



Definition LocVar t name := Alloc Stack t (Some name%string) 1. 
Definition ex1 := Alloc Stack (Int S64) (Some "x"%string) 1.
Definition ex2 := LocVar Int8 "x" .
Definition ex3 := LocVar (Pointer Int8) "y".
Definition ex_literal := Lit Int64 (Negz 4).

Definition neg_expr := Unop Neg ex_literal.
Definition add_expr := Binop Add neg_expr ex_literal. 


Definition prog_state: Set := static_ctx * dynamic_ctx.
Definition state_empty := (static_ctx_empty, dynamic_ctx_empty).

(*Definition cst {A B : Type} (a : A) (H : A = B) := eq_rect A (fun B0 : Type => B0) a B H.*)
Definition cast {A B : Type} (a: A ) (H: A= B ) : B.
  by rewrite <- H.
Defined.
(*Notation "' x " := (cast x _) (at level 3, left associativity).*)

Program Definition binop_interp (t:ctype) (op: binop) : int -> int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Add => fun x y=> @Value t (cast (addz x y ) _) 
              | _ => (fun _ _ => Error _)
            end
            | _ => (fun _ _ => Error _)
  end
.

Program Definition unop_interp (t:ctype) (op: unop) : int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Neg => fun x => @Value t (cast (oppz x) _) 
              | _ => (fun _ => Error _)
            end
            | _ => (fun _ => Error _)
  end
.

Compute binop_interp Int64 Add (Posz 4) (Posz 9).
Check option_find.
Check variables.
Program Fixpoint iexpr (s:prog_state) (e:expr): value (@type_solver (fst s) e) :=
  let interp := iexpr s in
  let type := @type_solver (fst s) in
  let ret_type := value (type e) in
  let vars := flatten (variables (fst s) ) in
  match e  wi                             | _ , _, _ => fun _ _ => Error _
                           end _ _
                         | _, _ => Error _
                          end
    | _ => Error _
  end
.


Next Obligation. by rewrite Hto. Defined.
Next Obligation. by rewrite Htl. Defined.
Next Obligation. by rewrite Htr. Defined.
Solve Obligations with done.


Eval compute in iexpr (static_ctx_empty, dynamic_ctx_empty) neg_expr.
(* Almost there, the ``types`` are not computed tho *)
Compute iexpr (static_ctx_empty, dynamic_ctx_empty) add_expr.

Eval compute in interpreter_expr ex_literal (pair static_ctx_empty dynamic_ctx_empty).

      
               






  
Fixpoint interpreter_step (st:statement) (s:prog_state) :  prog_state :=
  match s with| (stat,dyn) => match st with
| Skip => s
| Assign var val 
| Alloc: storage -> ctype -> option string -> nat -> statement
| If: expr -> statement -> statement -> statement
| For: statement -> expr -> statement -> statement -> statement
| While: expr -> statement -> statement
| CodeBlock: seq statement -> statement.
      
  end.

              
