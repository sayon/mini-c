From mathcomp Require Import ssreflect.all_ssreflect eqtype.
From mathcomp Require Import algebra.ssrint.

Import intZmod.
 
Require Import Common Types Memory.
Require Import Coq.Strings.String UtilString SSet.

Inductive BinOpKind :=| Add | Sub | Mul | Div | LAnd | LOr. Scheme Equality for BinOpKind.

          Definition binop_eqP := reflect_from_dec BinOpKind_eq_dec.
    
          Canonical BinOpKind_eqMixin := EqMixin binop_eqP.
          Canonical BinOpKind_eqType := EqType BinOpKind BinOpKind_eqMixin.

Inductive UnOpKind := | Neg | Invert | Not | Convert (to:ctype) | Amp | Asterisk .

          Definition UnOpKind_beq (x y : UnOpKind) : bool :=
            match x, y with
              | Neg, Neg  |Invert, Invert | Not, Not | Amp, Amp | Asterisk, Asterisk => true
              | Convert t1, Convert t2 => t1 == t2
              | _, _ => false
            end.

          Lemma UnOpKind_eqP: Equality.axiom UnOpKind_beq.
            - move=> x y.
              case Heq: (UnOpKind_beq _ _); move: Heq. 
              case x; case y =>//=; try by constructor.
              move=> t0 t1. by move /eqP =>->; constructor.
              case x; case y => //=; try by constructor.
              move=> t0 t1  /eqP => Hneq. constructor. by case.
          Qed.
          Canonical UnOpKind_eqMixin := EqMixin UnOpKind_eqP.
          Canonical UnOpKind_eqType := EqType UnOpKind UnOpKind_eqMixin.
          Definition UnOpKind_eq_dec := dec_from_reflect UnOpKind_eqP.
          
Inductive expr :=
| Assign: expr -> expr -> expr
| Binop: BinOpKind -> expr -> expr -> expr
| UnOp: UnOpKind -> expr -> expr
| Var: string -> expr
| Lit: forall t:ctype, coq_type t -> expr
| Call: string -> seq expr -> expr.

Inductive statement :=
| Sexpr : expr -> statement
| If: expr -> statement -> statement -> statement
| While : expr -> statement -> statement
| Return: expr -> statement
| Alloc: storage -> ctype -> option string -> nat -> statement
| Sequence: seq statement -> statement
.
Record var_descr := declare_var { var_name: string; var_type: ctype; location: nat }.
           Theorem var_descr_eq_dec: eq_dec var_descr.
             rewrite /eq_dec. decide equality. decide equality. apply ctype_eq_dec. apply string_eq_dec.
           Qed.
           
           Definition var_descr_eqP := reflect_from_dec var_descr_eq_dec.
           Canonical var_descr_eqMixin := EqMixin var_descr_eqP.
           Canonical var_descr_eqType := EqType var_descr var_descr_eqMixin.


Record function := mk_fun {
                       fun_id: nat;
                       fun_name: string;
                       fun_args: seq ctype;
                       fun_returns: ctype;
                       fun_body: statement;
                     }.

Record static_ctx : Set := mk_stat_ctx {
                        functions: seq function;
                        variables: seq ( seq var_descr );
                             }.

Definition static_ctx_empty:= mk_stat_ctx [::] [::].

Inductive deref := | Deref : forall t:ctype,  ptr t -> deref.

Record dynamic_ctx : Set := mk_dyn_ctx { memory: seq block; reads: seq deref; writes: seq deref }.
(* 0th block for Unit? NO we dont need that
1-N blocks for functions*)

Definition dynamic_ctx_empty := mk_dyn_ctx [::] [::] [::].

Inductive prog_state :=
| Good: static_ctx -> dynamic_ctx -> prog_state
| Bad :static_ctx -> dynamic_ctx -> statement -> prog_state.

Definition state_init := Good (mk_stat_ctx nil [:: [:: declare_var "Unit" Unit 0 ] ]) 
                              dynamic_ctx_empty.

Definition get_stat p := match p with | Good stat _ | Bad stat _ _ => stat end.
Definition get_dyn  p := match p with | Good _ dyn  | Bad _  dyn _ => dyn  end.

Definition get_var (sc:static_ctx) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (flatten (variables sc)).

Definition get_fun (sc:static_ctx) (name:string) : option function :=
  option_find (fun p: function => fun_name p == name) (functions sc).

Definition find_block (m: dynamic_ctx) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ memory m.


Definition fmap_or {T R} (f: T-> R)  (orelse: R)  (x:option T) := match x with | Some x => f x | None => orelse end.
(* Add address shit*)
  
Fixpoint type_solver {sc: static_ctx} (e: expr) : ctype:=
  let type := @type_solver sc  in
  match e with
    | Assign lhs rhs => Unit 
    | Binop code l r => eq_value_or_error_proved_arith (type l) (type r) (fun H x y => x) Bot
    | UnOp Asterisk op => match type op with
                            | Pointer t => t
                            | _ => Bot
                          end
    | UnOp _ o => type o
    | Var name => fmap_or (Pointer \o var_type) ErrorType $ get_var sc name
    | Lit t x => Unit
    | Call name cargs => fmap_or (fun f => if map type cargs == fun_args f then fun_returns f else Bot) ErrorType $ get_fun sc name 
  end.

Inductive ContElem:=
| Cstatement : statement -> ContElem
| Pushctx
| Popctx
| FunEnd.
       

Program Definition binop_interp (t:ctype) (op: BinOpKind) : int -> int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Add => fun x y=> @Value t t _ $ cast (addz x y ) _
              | _ => (fun _ _ => Error _)
            end
            | _ => (fun _ _ => Error _)
  end
.

Program Definition unop_interp (t:ctype) (op: UnOpKind) : int -> value t :=
  match t with |
            Int kind =>
            match op with
              |Neg => fun x => @Value t t _ $ cast (oppz x) _
              | _ => fun _ => Error _
            end
            | _ => fun _ => Error _
  end
.


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


Definition option_nth {T:eqType} (s:seq T) (n: nat) := nth None (map (@Some T) s) n.
Definition block_mod (b: block) (idx: nat) (e: value (el_type b)) : option block :=
  if idx * ( SizeOf (el_type b)) >= block_size b then None
  else @Some _ $ mk_block
         (region b)
         (block_id b)
         (block_size b)
         (el_type b)
         (set_nth (Error _) (contents b) idx e).
Definition ErrorBlock := mk_block Data 0 0 ErrorType [::].

Program Definition mem_write (t: ctype) (id: nat) (pos: nat) (dyn: dynamic_ctx) (val: value t) : option dynamic_ctx :=
  let m := memory dyn in
  let oldblock := option_nth m id in
  match oldblock with
    | Some _oldblock =>
      match ctype_beq t (el_type _oldblock) as Ht with
        | true => let p := Deref t $ Goodptr t id pos in
                  match block_mod _oldblock pos (cast val _) with
                            | Some newblock => @Some _ $ mk_dyn_ctx ( set_nth ErrorBlock m id newblock ) (reads dyn) (p::writes dyn)
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


(* None if UB *) (*
Fixpoint flush_effects (dyn: dynamic_ctx) : option dynamic_ctx :=
  let: mk_dyn_ctx eff mem := dyn in
  match eff with
    | nil => Some dyn
    | (Effect t (Goodptr b off) v)::es => mem_write t b off (mk_dyn_ctx es mem) v
    | _ => None
  end.*)

(*Fixpoint concat_effects (x y: dynamic_ctx) : (seq effect) ? :=
  match  let: mk_dyn_ctx eff mem := dyn in
  match eff with
    | nil => Some dyn
    | (Effect t (Goodptr b off) v)::es => mem_write t b off (mk_dyn_ctx es mem) v
    | _ => None
  end.
*)
Inductive sexpr  : Set :=
| SPush t: value t -> sexpr
| SBinOp: BinOpKind -> sexpr
| SUnOp: UnOpKind -> sexpr
| SCall: string -> sexpr
| SAssign
| SRead: string -> sexpr
.

Fixpoint unsome {T} (s:seq (option T)) :=
  match s with
    | x::xs => match x with
                 | Some x => Some [::x] /++/ unsome xs
                 | None => None
               end
    | nil => Some nil
  end.

Fixpoint to_stack_code (c:static_ctx) (e: expr): seq sexpr ? :=
  let f := to_stack_code c in
  match e with
    | Assign l r => f l /++/ f r /++/ Some [:: SAssign]
    | Binop c l r => f l /++/ f r /++/ Some [:: SBinOp c]
    | UnOp c o => f o /++/ Some [:: SUnOp c]
    | Var x => Some [:: SRead x ]
    | Lit t x => Some [:: @SPush t (Value t t Logic.eq_refl x) ]
    | Call name args => option_map flatten ( unsome (map f args)) /++/ Some [::SCall name ]
  end.

Definition Plus := Binop Add.
Definition Int := Lit Int32.

Let ex_expr := Plus (Int 1) $ Plus (Int 9) $ Plus (Call "f" [::Var "x"]) $ Call "g" [:: Call "h" [:: Var "x"]; Call "k" [::Var "x"]].


Print mk_fun.
Definition Ff := mk_fun 1 "f" [:: Int64] Int64 $ Sequence nil.
Definition Fg := mk_fun 2 "g" [:: Int64; Int64] Int64 $ Sequence nil.
Definition Fh := mk_fun 3 "h" [:: Int64] Int64 $ Sequence nil.
Definition Fk := mk_fun 4 "k" [:: Int64] Int64 $ Sequence nil.
Definition dummy_stat_ctx := mk_stat_ctx [:: Ff; Fg; Fh; Fk] [::[:: declare_var "x" Int64 5]].

Import Types.
Compute to_stack_code dummy_stat_ctx ex_expr.

Inductive stack_elem := | mk_stack_elem: forall t, value t -> dynamic_ctx -> stack_elem.

(* Todo: need to copy all values*)
(* Maybe we need an implicit CONSISTENCY term? *)
Definition apply_writes (from to: dynamic_ctx)  :=
  let wrs := writes from in
  let folder (c: dynamic_ctx?) (d:deref) :=
      match c with
          | Some c => 
      match d with
        | Deref t (Goodptr b o) as p =>
          match dereference t (Value (Pointer t) (Pointer t) Logic.eq_refl (Goodptr _ b o) ) from with
            | Value _ x _  as val => mem_write t b o to val
            | _ => None
          end
        | _ => None
      end
          | None => None
      end
  in

  foldl folder (Some to) wrs.



Check map (fun f:deref => match f with  | Deref t (Goodptrt b o) =>   (writes dynamic_ctx_empty).
  
  .
  
  Definition apply_writes (from to: dynamic_ctx) :=
  let ws := writes from in
  

                    
  Fixpoint merge_dyn_ctx (x y: dynamic_ctx) : dynamic_ctx :=
  match x,y with
    | mk_dyn_ctx  mx rx wx,
      mk_dyn_ctx  my ry wy =>
  end.

Fixpoint isexpr (stat: static_ctx) (dyn: dynamic_ctx) (e:sexpr) (s: seq stack_elem) : seq stack_elem ?:=
  match e with
    | SPush t x => @Some _ $ mk_stack_elem t x dyn :: s
    | SBinOp op =>
      match s with
        | mk_stack_elem tx vx dx  :: mk_stack_elem ty vy dy :: ss =>
          match mergectx dx dy with
            | Some m=>
              eq_value_or_error_proved_arith tx ty
                                             (fun _ _ => Some ( pair ( binop_interp tx op (cast vx _) (cast vy _) ) m::ss) )
                                             None
            | None => None
          end
        | _ => None 
      end
    | SUnOp x => _
    | SCall x => _
    | SAssign => _
    | SRead x => _
  end
.

      match s with
        | (mk_elem (Int _) (Value (Int kx) _ x) dx) ::
          (mk_elem (Int _) (Value (Int ky) _ y)  dy) :: ss =>
          @Some _ $ mk_elem (Int kx)
          ( eq_value_or_error_proved_arith (Int kx) (Int ky)  
                                          (fun _ _ =>  binop_interp (Int kx) op (cast x _) (cast y _) ) (Error _)
                                          )  :: ss
        | _ =>  None
      end

Fixpoint iexpr (stat: static_ctx) (dyn: dynamic_ctx) (e:expr): value (@type_solver stat e) ? * seq ContElem  
      :=
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


Definition ex_block := mk_block Stack 0 64 Int64 (garbage_values 8).
Eval compute in block_mod ex_block 1 (Value Int64 Int64 _ 3).


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

 Print expr.
 (***! Do canonical instances need to be exported? *)
 Print eq_value_or_error.
 Print coq_type.

 Print ctype_beq.


 Fixpoint expr_beq (l r:expr) : bool :=
   let fix process (xs ys: seq expr) := match xs,ys with
                                        | nil, nil => true
                                        | x::xs, y::ys => expr_beq x y && process xs ys
                                        | _, nil
                                        | nil, _ => false
                                      end in
   match l,r with
     | Lit x vx, Lit y vy =>
       for_eq_carriers x y false
                       (fun a b=> a == b)
                       (fun pt px py => px == py)
                       (fun sx sy => sx == sy)
                       (fun _=> true)
                       (fun _=> true) vx vy
     | Var x, Var y => x == y
     | Binop x x0 x1 , Binop y y0 y1 => (x == y) && expr_beq x0  y0 && expr_beq x1 y1
     | Unop x x0, Unop y y0 => (x == y) && expr_beq x0 y0
     | Call x x0 , Call y y0 => (x == y) && process x0 y0
     | _,_ => false
   end.

 Theorem carrier_eq_dec: forall t, eq_dec (coq_type t).
   rewrite /eq_dec.
   case.
   - case; apply int_eq_dec.
   - apply ptr_eq_dec.
   - decide equality. decide equality.
   - decide equality.
   - decide equality.
   - decide equality.
 Qed.


   
 Theorem expr_eq_dec : eq_dec expr.
   Local Lemma Hlst {A} (a:A) l : a :: l = l -> False. by  elim l =>//=; move=> a0 l0 IH [] =><-. Qed.
   rewrite /eq_dec.
   fix 1.
   move => x y.
   case x; case y; try by right.
   - move => t c t0 c0.
     case Ht:(t == t0).
     + move /eqP in Ht; subst.
       move: (carrier_eq_dec t0 c0 c).
       case; [by left; subst
             | by right; move =>[]=> H; depcomp H].
     + by move /eqP in Ht; right; case; move=> He; symmetry in He.
   - by move=> s0 s; move: (string_eq_dec s s0) => []; by[left; subst| right; case]. 
   - move=> op2 x2 y2 op1 x1 y1.
     move: (binop_eq_dec op1 op2) => [Hop|Hop]; 
     move: (expr_eq_dec x1 x2) => [Hx|Hx];
       move: (expr_eq_dec y1 y2) => [Hy|Hy]; try by right;case.
     by rewrite Hx Hy Hop; left. 
   - move=> op1 x1  op2 x2.
     move:(expr_eq_dec x2 x1) => [Hx|Hx]; move:(unop_eq_dec op2 op1) => [Hop|Hop]; subst; try by [right;case].
     by left.
   - move=> sy ly sx lx. 
     move: (string_eq_dec sx sy) => [Hs|Hs]; last by [right;case];subst.
     elim: lx ly.
     + elim; by [left| right ; discriminate].
       move => a l IH [].
       * by right; discriminate. 
       * clear x y. move=> y ys.
         move: (expr_eq_dec a y) => [Ha|Ha]; move: (IH ys) => [Hy|Hy].
         ** inversion Hy; subst; by left.
         ** by right; case=> * *; subst. 
         ** by right; case. 
         ** by right; case.
Qed.

Definition expr_eqP := reflect_from_dec expr_eq_dec.
  
Canonical expr_eqMixin := EqMixin expr_eqP.
Canonical expr_eqType := EqType expr expr_eqMixin.

Theorem statement_eq_dec: eq_dec statement.
   rewrite /eq_dec.   
fix 1.
   decide equality; try apply expr_eq_dec.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   decide equality.
   apply (seq_eq_dec _ ctype_eq_dec).
   decide equality.
   decide equality.
Defined.

Definition statement_eqP := reflect_from_dec statement_eq_dec.

Canonical statement_eqMixin := EqMixin statement_eqP.
Canonical statement_eqType := EqType statement statement_eqMixin.

Program Fixpoint interpreter_step (st:statement) (s:prog_state) (cont: seq statement ):  prog_state * seq statement:=
  match s with
    |Good stat dyn =>
     let type := @type_solver stat in
     let bad := pair (Bad stat dyn st) nil in
     match st with
       | Skip => (s, cont)
       | Assign w val  =>
         match eval s w, eval s val with
           | Value (Pointer t) _ vp, Value vtype _ v =>                           
             match vtype == t with | true =>  match vp with
                            | Goodptr to off =>
                              match mem_write t to off dyn (Value t t _  (cast v _) ) with
                                | Some d => (Good stat d, cont)
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
           | None => (Good stat newdyn, cont)
           | Some name => (Good (add_var (declare_var name type block_id) stat block_id ) newdyn, cont)
         end
     | If cond _then _else => interpreter_step (
                                  if @is_value_true _ stat $ @eval s cond
                                  then  _then else _else ) s cont
     | For prest cond postst body => (s, cont)
     | While cond body => (s, cont)
     | CodeBlock ss => (s, (Enter::ss) ++ (Leave :: cont))
     | Enter => (add_static_ctx s, cont)
     | Leave => (remove_static_ctx s, cont)
     end
       | s => (s, nil)
  end . 

 Next Obligation. by rewrite (eqP $ Logic.eq_sym Heq_anonymous). Defined.   

 
Definition LocVar t name := Alloc Stack t (Some name%string) 1. 

Notation "{  x1 ; .. ; xn }" := (CodeBlock(  cons x1  .. (cons xn nil) ..) ) (at level 35, left associativity) : c. 
Notation "'int8 x " := (LocVar Int8 x) (at level 200, no associativity) :c.
Notation "'uint8 x " := (LocVar UInt8 x) (at level 200, no associativity) :c.
Notation "'int16 x " := (LocVar Int16 x) (at level 200, no associativity) :c.
Notation "'uint16 x " := (LocVar UInt16 x) (at level 200, no associativity) :c.
Check Assign (Var "x") (Lit Int64 4).

Notation "' v := value" := (Assign (Var v) (value) ) (at level 200, no associativity) :c.
Delimit Scope c with c.
Definition sample_prog := {
                           {
                             'int8 "x";
                             'int8 "y";
                             ' "x" := Lit Int8 4 ;
                             ' "y" := Lit Int8 (Negz 9)
                           } ;
                           {
                             'int16 "x";
                             'int16 "y";
                             ' "x" := Lit Int16 2
                           }
                         }%c .

Compute interpreter_step sample_prog state_init nil .

Fixpoint interpret (steps: nat) (state: prog_state) (cont: seq statement): prog_state * seq statement :=
  match steps, cont with
    | S steps_left, s::ss =>
      match interpreter_step s  state ss with
        | (Good stat dyn as newstate, newcont) => interpret steps_left newstate newcont
        | (Bad _ _ _ as bs, _) => (bs, cont)
      end
    | _, _ => (state, cont)
  end
