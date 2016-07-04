From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
From Coq.Strings Require Import Ascii String.
Require Import Common Types Memory. 


Record var_descr := declare_var { var_name: string; var_type: ctype; location: nat }.
       Definition var_descr_beq (x y: var_descr) : bool :=
         (var_name x == var_name y)  && (var_type x == var_type y) && (location x == location y).
       Theorem var_descr_eq_dec: eq_dec var_descr.
         rewrite /eq_dec.
         decide equality.
         decide equality.
         apply ctype_eq_dec.
         apply string_eq_dec.
       Qed.

       Definition var_descr_eqP := reflect_from_dec var_descr_eq_dec.
       
       Canonical var_descr_eqMixin := EqMixin var_descr_eqP.
       Canonical var_descr_eqType := EqType var_descr var_descr_eqMixin.
       Canonical Structure var_descr_dec_eq_mixin := mk_dec_eq var_descr var_descr_eq_dec.
  
Inductive binop : Set := | Add | Sub | Mul | Div | LAnd | LOr | Eq .
       Scheme Equality for binop.
       Definition binop_eqP := reflect_from_dec binop_eq_dec.
       Canonical binop_eqMixin := EqMixin binop_eqP.
       Canonical binop_eqType := EqType binop binop_eqMixin.
       Canonical Structure binop_dec_eq_mixin := mk_dec_eq binop binop_eq_dec.
       
Inductive unop: Set := | Neg | Invert | Not | Convert (to:ctype) | Amp | Asterisk .
       Definition unop_beq (x y : unop) : bool :=
         match x, y with
           | Neg, Neg  |Invert, Invert | Not, Not | Amp, Amp | Asterisk, Asterisk => true
           | Convert t1, Convert t2 => t1 == t2
           | _, _ => false
         end.

       Lemma unop_eqP: Equality.axiom unop_beq.
         move=> x y.
         case Heq: (unop_beq _ _); move: Heq. 
         case x; case y =>//=; try by constructor.
         move=> t0 t1. by move /eqP =>->; constructor.
         case x; case y => //=; try by constructor.
         move=> t0 t1  /eqP => Hneq. constructor. by case.
       Qed.
       Canonical unop_eqMixin := EqMixin unop_eqP.
       Canonical unop_eqType := EqType unop unop_eqMixin.
       Definition unop_eq_dec := dec_from_reflect unop_eqP.
       Canonical Structure unop_dec_eq_mixin := mk_dec_eq unop unop_eq_dec.

Inductive expr :=
       | Lit  (v:value) (* (t:ctype) (_:coq_type(t))*)
       | Var   (_:string)
       | Binop (_:binop) (_ _: expr)
       | Unop  (_:unop)  (_: expr)
       | BspNProc
       | BspPid.

Inductive statement :=
       | Skip
       | Call : string -> seq expr -> statement (* return values do not exist *)
       | Assign: expr -> expr -> statement
       | Alloc: storage -> ctype -> option string -> nat -> statement
       | If: expr -> statement -> statement -> statement
       | While: expr -> statement -> statement
       | CodeBlock: seq statement -> statement
       | Debug
       | Enter
       | Leave
       | BspSync
       | BspPushReg: expr-> expr-> statement (* ptr and size *)
       | BspPopReg: expr-> statement (* ptr *)
       | BspGet: expr -> expr-> expr-> expr -> expr-> statement (* pid source offset dest size *)
       | BspPut: expr -> expr-> expr-> expr -> expr -> statement (* pid dest offset source size *)
       | BspHpPut: expr -> expr-> expr-> expr -> expr -> statement (* pid dest offset source size *)
       | BspHpGet: expr -> expr-> expr-> expr -> expr-> statement (* pid source offset dest size *)
.

Theorem carrier_eq_dec: forall t, eq_dec (coq_type t).
  rewrite /eq_dec.
  case; try by apply unit_eq_dec.
  - case; apply int_eq_dec.
  - apply ptr_eq_dec.
  - move=> *. apply (seq_eq_dec nat_eq_dec). 
Qed.

Record function := mk_fun {
                       fun_id: nat;
                       fun_name: string;
                       args: seq (string * ctype);
                       body: statement(*;
                       fun_location: nat*)}. (* all functions are void; if they return smth it is written by pointer passed as arg *)



    Canonical Structure expr_eq_dec : eq_dec expr.
       have Hlst: forall (A:Type) (a:A) l,  a :: l = l -> False. by  move=> A a; elim =>//=; move=> a0 l0 IH [] =><-. 
       rewrite /eq_dec.
       fix 1.
       move => x y.
       case x; case y; try by [right| left].
       - move=> v v0.
         eq_compi v0 v.         
       - move=> s0 s.
         eq_compi s s0. 
       - move=> op2 x2 y2 op1 x1 y1.
         eq_compi op1 op2.
         eq_comp expr_eq_dec x1 x2.
         eq_comp expr_eq_dec y1 y2.
       - move=> op1 x1  op2 x2.
         eq_comp expr_eq_dec x2 x1.
         eq_compi op2 op1.
     Defined. 

     Definition expr_eqP := reflect_from_dec expr_eq_dec.
     
     Canonical expr_eqMixin := EqMixin expr_eqP.
     Canonical expr_eqType := EqType expr expr_eqMixin.

     Canonical Structure expr_dec_eq_mixin := mk_dec_eq expr expr_eq_dec.
       
     Theorem statement_eq_dec: eq_dec statement.
       rewrite /eq_dec.   
       fix 1.
       have option_eq_dec t: eq_dec t ->  eq_dec (option t). by rewrite /eq_dec =>H; decide equality.
       decide equality; try apply expr_eq_dec.
       apply ( seq_eq_dec expr_eq_dec).
       apply string_eq_dec.
       apply nat_eq_dec.
       apply (option_eq_dec _ string_eq_dec).
       apply ctype_eq_dec.
       apply storage_eq_dec.
       elim: l l0.
         by case; [left | right].
         move=> a l H l0.
         case l0. by right.
         move=> s l1.
         move: (H l1) => [H0|H0]; move: (statement_eq_dec a s) => [H1|H1]; subst; 
                                                                  try by [left| right; case].
       Defined.

     Definition statement_eqP := reflect_from_dec statement_eq_dec.
     
     Canonical statement_eqMixin := EqMixin statement_eqP.
     Canonical statement_eqType := EqType statement statement_eqMixin.
     Canonical Structure statement_dec_eq_mixin := mk_dec_eq statement statement_eq_dec.
     
     Theorem function_eq_dec: eq_dec function.
       move => [q w e r] [qq ww ee rr].
       eq_comp nat_eq_dec q qq.
       eq_compi w ww.
       eq_comp (seq_eq_dec (pair_eq_dec string_eq_dec ctype_eq_dec)) e ee.
       eq_compi r rr.
         Qed.
     Definition function_eqP := reflect_from_dec function_eq_dec.
     
     Canonical function_eqMixin := EqMixin function_eqP.
     Canonical function_eqType := EqType function function_eqMixin.
     Canonical Structure function_dec_eq_mixin := mk_dec_eq _ function_eq_dec.