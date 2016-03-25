From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Program.
Require Import Program.
Require Import Types.
Require Import UtilString.
Import Bspc.
Import intZmod.  
Require Import Common.

(* Pointer value *)
Inductive ptr (t: ctype) := | Goodptr (at_block: nat) (offset: nat) | Nullptr.

Definition ptr_eq_dec t : eq_dec (ptr t).  by rewrite /eq_dec; repeat decide equality. Qed.

Definition ptr_eqP t := reflect_from_dec (ptr_eq_dec t).
Canonical ptr_eqMixin t := EqMixin (ptr_eqP t).
Canonical ptr_eqType t := EqType (ptr t) (ptr_eqMixin t).

(* Different memory regions *)
Inductive storage := | Heap | Stack | Data | Text | ReadOnlyData.

Scheme Equality for storage. 
Definition storage_eqP := reflect_from_dec storage_eq_dec.
Canonical storage_eqMixin := EqMixin storage_eqP.
Canonical storage_eqType := EqType storage storage_eqMixin.

(* Holders for different value types *)
Definition coq_type (t: ctype) : Set :=
  match t with
    | Int _ => int
    | Pointer t => ptr t
    | Struct ls => seq nat
    | Bot => unit
    | Error => unit
  end.

Section EqValue.
  Inductive value (t: ctype) : Set := | Value (_t:ctype)  (_:_t = t) (v: coq_type _t) | Garbage | Deallocated | Error.
  
  Lemma value_inj T C p x y: @Value T C p x = @Value T C p y -> x = y.
    case.
    move => Hd.
    apply EqdepFacts.eq_sigT_eq_dep in Hd.
    by apply eq_dep_eq in Hd.
  Qed.

  Lemma value_surj T C p x y: x = y -> @Value T C p x = @Value T C p y.
    by move =>->.
  Qed.
  Lemma value_eq_dec {t} (x y: value t) : { x = y } + { ~ x = y }.
    destruct x, y, t; try by [right; intro H];try by left; subst.
    - subst. simpl in *.
      case: (int_eq_dec v v0). subst; try by [move => ->; left]. 
      right. by move /value_inj. 
    - subst; simpl in *. case: (ptr_eq_dec _ v v0).
      move=> ->. by left.
      move=> *. right. by  move /value_inj.
    -  subst. simpl in *.
       case (v == v0) eqn: Heq; move /eqP in Heq;
          by [ left; rewrite Heq | right; move /value_inj].
    -  subst; simpl in *.
       case: (unit_eq_dec v v0);by [move=> ->;left|move=> *; right; move /value_inj ].
    -  subst; simpl in *.
       case: (unit_eq_dec v v0);by [move=> ->;left|move=> *; right; move /value_inj].
  Defined.

  Definition value_eqP (t:ctype) := reflect_from_dec (@value_eq_dec t).
  
  Canonical value_eqMixin (t:ctype) := EqMixin (value_eqP t).
  Canonical value_eqType t := Eval hnf in  EqType (value t) (value_eqMixin t).
End  EqValue.

Inductive block := mk_block {
                       region: storage;
                       block_id: nat;
                       block_size: nat;
                       el_type: ctype;
                       contents: seq (value el_type)
                     }.


Program Definition block_beq x y :=  (cmp_with //= region, block_id, block_size, el_type // x y)
                                       && match el_type x == el_type y with
                                            | true => ( eqseq (contents x ) (cast (contents y) _) )
                                            | false => false
                                          end.
Next Obligation. by rewrite (eqP (Logic.eq_sym Heq_anonymous)). Defined.

Theorem block_eq_dec : eq_dec block.
  rewrite /eq_dec.
  move => [r1 i1 s1 t1 c1] [r2 i2 s2 t2 c2].
  case( r1 == r2) eqn: Hr; case (i1 == i2) eqn:Hi;
  case( s1 == s2 ) eqn: Hs; case (t1 == t2) eqn: Ht;
  move /eqP in Hr; move /eqP in Hi; move /eqP in Hs; move /eqP in Ht;
  subst;  try case (c1 == c2) eqn: Hc; try move /eqP in Hc;  subst; try by [right; by case].
  - by left.
  - right. rewrite /not=> Hn.
    inversion Hn.
    move: (EqdepFacts.eq_sigT_eq_dep _ _ _ _ _ _ H0) => H'.
      by apply eq_dep_eq in H'.
Qed.

Definition block_eqP := reflect_from_dec (block_eq_dec).

Canonical block_eqMixin := EqMixin block_eqP.
Canonical block_eqType := EqType block block_eqMixin.
       
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

  
Inductive binop : Set := | Add | Sub | Mul | Div | LAnd | LOr .
Scheme Equality for binop.

Inductive unop: Set := | Neg | Invert | Not | Convert (to:ctype) | Amp | Asterisk .

Inductive expr :=
| Lit   (t:ctype) (_:coq_type(t))
| Var   (_:string)
| Binop (_:binop) (_ _: expr)
| Unop  (_:unop)  (_: expr)
| Call (_: string) (_: seq expr).


Inductive statement :=
| Skip
| Assign: expr -> expr -> statement
| Alloc: storage -> ctype -> option string -> nat -> statement
| If: expr -> statement -> statement -> statement
| For: statement -> expr -> statement -> statement -> statement
| While: expr -> statement -> statement
| CodeBlock: seq statement -> statement.

Record function := mk_fun{
                       fun_id: nat;
                       fun_name: string;
                       args: seq ctype;
                       returns: ctype;
                       body: seq statement;
                     }.
Record static_ctx : Set := mk_stat_ctx {
                        functions: seq function;
                        variables: seq ( seq ( prod var_descr  nat) );
                       }.
Definition static_ctx_empty:= mk_stat_ctx [::] [::].

Record dynamic_ctx : Set := mk_dyn_ctx { memory: seq block }.
Definition dynamic_ctx_empty := mk_dyn_ctx [::].

Inductive prog_state := | Good: static_ctx -> dynamic_ctx -> prog_state
 | Bad :static_ctx -> dynamic_ctx -> statement -> prog_state.

Definition state_init := Good static_ctx_empty dynamic_ctx_empty .


Definition get_stat p := match p with
                           | Good stat dyn => stat
                           | Bad stat dyn _ => stat
                         end.

Definition get_dyn p := match p with
                           | Good stat dyn => dyn
                           | Bad stat dyn _ => dyn
                         end.


Definition option_find {T:Type} (p: T -> bool) (s:seq T): option T :=
  nth None (map (@Some T) s) (find (option_map p) (map (@Some T) s)).


Definition get_var (sc:static_ctx) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (map fst (flatten (variables sc))).


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

Program Definition eq_value_or_error_proved {A:Type} (tl tr: ctype) (v: tl = tr-> ctype -> ctype -> A) (err: A):A :=
 match tl as tl_, tr as tr_ return tl = tl_-> tr = tr_ -> A with
    |Int S8, Int S8
    |Int U8, Int U8
    |Int S16, Int S16 
    |Int U16, Int U16 
    |Int S32, Int S32 
    |Int U32, Int U32 
    |Int S64, Int S64 
    |Int U64, Int U64 => fun Hl Hr =>  v _ tl tr
    | _, _=> fun _ _ => err 
  end _ _
.
  
Definition eq_or_err (tl tr: ctype) := eq_value_or_error tl tr (fun  x _ => x) ErrorType.


Fixpoint type_solver {sc: static_ctx}  (e: expr) : ctype:=
  let slv := @type_solver sc  in
  match e with
    | Lit t _ => t
    | Var name => match get_var sc name with
                    | Some v => Pointer $ var_type v
                    | None => ErrorType
                  end
    | Binop _ l r => eq_or_err (slv l) (slv r)
    | Unop Asterisk op => match slv op with
                            | Pointer t => t
                            | _ => Bot
                          end
    | Unop _ o => slv o
    | Call name cargs =>
      match get_fun sc name with
          | None => ErrorType
          | Some f => if (map slv cargs == args f) then returns f else Bot
      end
  end.


Program Definition binop_interp (t:ctype) (op: binop) : int -> int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Add => fun x y=> @Value t t _ $ cast (addz x y ) _
              | _ => (fun _ _ => Error _)
            end
            | _ => (fun _ _ => Error _)
  end
.

Program Definition unop_interp (t:ctype) (op: unop) : int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Neg => fun x => @Value t t _ $ cast (oppz x) _
              | _ => fun _ => Error _
            end
            | _ => fun _ => Error _
  end
.

Definition find_block (m: dynamic_ctx) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ memory m.

Definition find_block_state (s:prog_state) (i:nat) : option block :=
  match s with
    | Good _ d => find_block d i
    | Bad  _ _ _ => None
  end.

Program Definition dereference (tp:ctype) (v: value (Pointer tp)) (dyn:dynamic_ctx) : value tp :=
  let ret_type := value tp in
  match v as vo return v = vo -> ret_type with
    | Value (Pointer tp) _  (Goodptr i o) as vo => fun Hto: v = vo =>
      match find_block dyn i  as fb with
        | Some ( mk_block loc _i sz block_type cnt ) =>
          match block_type == tp with
            | true =>  nth (Error _) cnt o
            | false => Error _
          end
            
        | None => Error _
      end
    | _ => fun _ => Error _
  end _.
Next Obligation.  
    by apply /eqP.
Defined.
  

Program Fixpoint iexpr (stat: static_ctx) (dyn: dynamic_ctx) (e:expr): value (@type_solver stat e) :=
  let interp := iexpr stat dyn in
  let type := @type_solver $ stat in
  let ret_type := value $ type e in
  let vars := flatten $ variables stat in
  let blocks := memory dyn in
  match e as e' return e = e' -> value (@type_solver stat e' ) with
    | Lit t v as e' => fun Heq: e = e' => /! Value t t _ v 
    | Var name as e' => fun Heq: e = e' =>
                    match get_var stat name with
                    | Some (declare_var n t i) => match find_block dyn i with
                                                    | Some b => match el_type b == t with
                                                                  | true => /! Value (Pointer t) (Pointer t) _ ( Goodptr t i 0) 
                                                                  | _ => Error _ end
                                                    | None => Error _
                                                  end
                    | None => Error _
                  end
    | Unop opcode op as e' => fun Heq: e = e' =>
      match opcode as code return opcode = code -> value ( type e')  with
        | Asterisk as code =>
          fun Hc: opcode = code =>
            match interp op with
              | Value (Pointer pt) Heq p =>  @dereference pt (/! (interp op))   dyn 
              | _ => Error _
            end 
        | code  =>
          fun Hc : opcode = code =>
          match interp op with
                      | Value (Int kind) _ v  => unop_interp (type e') opcode (/! v )
                      | _ => Error _
                    end
      end _
    | Binop opcode l r as e' =>
      fun Heq: e = e' =>
        match interp l, interp r return value ( type e' ) with
          | Value (Int kx) _ x, Value (Int ky) _ y =>
            @eq_value_or_error (value ( type e') ) (Int kx) (Int ky)
                               (fun _ _ => binop_interp (type e') opcode (cast x _) (cast y _) ) (Error _)
          | _, _ => Error _
        end 
    | Call _ _ => fun _ => Error _ 
  end _
.
Next Obligation.
  rewrite /_dollar. simpl. by rewrite -Heq.  Defined.

(*destruct (type_solver l); destruct (type_solver r).
  rewrite /_dollar. simpl. destruct opcode0 =>//=. simpl. 
  have t:= (@type_solver stat ( Unop opcode0 op)).
  destruct opcode; try done. move: (H op).
  rewrite /_dollar in Heq_anonymous. by  rewrite -Heq_anonymous. Defined.
Next Obligation. rewrite /_dollar in Heq_anonymous. by  rewrite -Heq_anonymous. Defined.
Next Obligation. rewrite /_dollar in Hto. rewrite Hto. by case kind. Defined.
Next Obligation. rewrite /_dollar in Hto. rewrite /_dollar.
                 destruct opcode; try done. by move: (H op).
Defined.
Next Obligation. simpl in Hte. rewrite /_dollar in Hte.  simpl in Hte.
                 by destruct (type_solver l); destruct (type_solver r).
Defined.
Next Obligation. simpl in Hte. symmetry in Hte. rewrite /_dollar in Hte. simpl in Hte. destruct (type_solver l); destruct (type_solver r); try by [done | destruct n]. Defined.
*)

Definition alloc {dc: dynamic_ctx} (b:block) : dynamic_ctx := mk_dyn_ctx ( (memory dc) ++ [:: b] ).

Definition next_block_id (s:dynamic_ctx) : nat := size $ memory $ s.
Fixpoint garbage_values {t:ctype} (sz: nat) : seq (value t) :=
  match sz with | n .+1 => (Garbage t) :: (garbage_values n) | 0 => [::] end.

Definition bind_var (v:var_descr) (i:nat) (ctx:static_ctx) :=
  let rec := (v,i) in
  mk_stat_ctx (functions ctx) $ match variables ctx with
                                    | [::] => [:: [:: rec] ]
                                    | cons x xs => cons (cons rec x) xs
                                  end
.

Definition add_static_ctx (s:prog_state) :=
  match s with
    | Good stat dyn => Good (mk_stat_ctx (functions stat) ( [::] :: variables stat) ) dyn
    | Bad _ _ _ as s => s
  end.

Definition remove_static_ctx (s:prog_state) :=
  match s with | Good stat dyn =>
                match variables stat with
                  | [::] => s
                  | vs::vvs => Good (mk_stat_ctx (functions stat) vvs) dyn
                end
                  | s => s
  end.

Definition block_mod (b: block) (idx: nat) (e: value (el_type b)) : option block :=
  if idx * ( SizeOf (el_type b)) >= block_size b then None
  else Some $ mk_block
         (region b)
         (block_id b)
         (block_size b)
         (el_type b)
         (set_nth (Error _) (contents b) idx e).

Definition ex_block := mk_block Stack 0 64 Int64 (garbage_values 8).
Eval compute in block_mod ex_block 1 (Value Int64 Int64 _ 3).

Definition ErrorBlock := mk_block Data 0 0 ErrorType [::].

Definition option_nth {T:eqType} (s:seq T) (n: nat) := nth None (map Some s) n.

Program Definition mem_write (t: ctype) (id: nat) (pos: nat) (dyn: dynamic_ctx) (val: value t) : option dynamic_ctx :=
  let m := memory dyn in
  let oldblock := option_nth m id in
  match oldblock with
    | Some _oldblock =>
      match ctype_beq t (el_type _oldblock) as Ht with
        | true => match block_mod _oldblock pos (cast val _) with
                            | Some newblock => Some $ mk_dyn_ctx $ set_nth ErrorBlock m id newblock
                            | _ => None
                  end
        | _ => None
      end
    | None => None
  end.
Next Obligation.
  symmetry in Heq_Ht.
  move /eqP in Heq_Ht.
    by rewrite Heq_Ht.
Defined.

Definition add_var (vd:var_descr) (c: static_ctx) (i:nat) :=
  mk_stat_ctx
    (functions c)
    match variables c with
      | [::] => [:: [:: (vd,i) ]]
      | cons x xs => cons (cons (vd,i) x) xs
    end
.

Program Definition is_value_true {t} {c:static_ctx} (v: value t) : option bool:=
  match v as v0 return v = v0 -> option bool with
    | Value (Int kind) _ z as v0 => fun H: v = v0 => Some (@sgz int_numDomainType z != 0)
    | Value (Pointer _) _ Nullptr as v0 => fun H: v = v0=> Some false
    | _ => fun _ => None 
  end _.


 Definition eval ps e: value ( @type_solver ( get_stat ps) e ) :=
 iexpr (get_stat ps) (get_dyn ps) e.

 Program Definition interpreter_step (st:statement) (s:prog_state) :  prog_state :=
  match s with
    |Good stat dyn =>
     let type := @type_solver stat in
     let bad := Bad stat dyn st in
     match st with
       | Skip => s
       | Assign w val  =>
         match eval s w, eval s val with
           | Value (Pointer t) _ vp, Value vtype _ v =>                           
             match vtype == t with | true =>  match vp with
                            | Goodptr to off =>
                              match mem_write t to off dyn (Value t t _  (cast v _) ) with
                                | Some d => Good stat d
                                | None => bad
                              end
                            | Nullptr => bad
                          end
               | _ => bad
             end
           | _, _ => bad
         end                      
     | Alloc loc type o_name sz =>
         let block_id := next_block_id dyn in
         let newdyn := mk_dyn_ctx (memory dyn ++  [:: mk_block loc block_id (sz* SizeOf type) type (garbage_values sz)])  in
         match o_name with
           | None => Good stat newdyn
           | Some name => Good (add_var (declare_var name type block_id) stat block_id ) newdyn
         end
     | If cond _then _else => if @is_value_true _ stat $ @eval s cond
                              then s
                              else
                                s
       | For prest cond postst body => s
       | While cond body => s
       | CodeBlock sts =>s (* add context, execute, throw away context*)
     end
       | s => s 
  end . 

 Next Obligation. by rewrite (eqP $ Logic.eq_sym Heq_anonymous). Defined.   

 
Definition LocVar t name := Alloc Stack t (Some name%string) 1. 

Definition ex1 := Alloc Stack (Int S64) (Some "x"%string) 1.
Definition ex_var_x := LocVar Int8 "x" .
Definition ex_var_py := LocVar (Pointer Int8) "y".
Definition ex_literal := Lit Int64 (Negz 4).

Definition neg_expr := Unop Neg ex_literal.
Definition add_expr := Binop Add neg_expr ex_literal. 

Definition ex_var_x_expr := Var "x".

Definition ex_skip := Skip.
Definition ex_alloc := LocVar Int64 "x".
Definition ex_varalloc_stat  := interpreter_step ex_alloc state_init.
Compute ex_varalloc_stat.

Eval compute in t ex_varalloc_stat ex_var_x_expr.
