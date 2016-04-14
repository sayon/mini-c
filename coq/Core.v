From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool.
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Program.
Require Import Program.
Require Import UtilString.
Require Import ProofIrrelevance.
Import intZmod.  
Require Import Common Types Memory Extraction.


       
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
       Definition binop_eqP := reflect_from_dec binop_eq_dec.
       Canonical binop_eqMixin := EqMixin binop_eqP.
       Canonical binop_eqType := EqType binop binop_eqMixin.
       
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

Inductive expr :=
       | Lit   (t:ctype) (_:coq_type(t))
       | Var   (_:string)
       | Binop (_:binop) (_ _: expr)
       | Unop  (_:unop)  (_: expr).

Inductive statement :=
       | Skip
       | Call : expr -> seq expr -> statement (* return values do not exist *)
       | Assign: expr -> expr -> statement
       | Alloc: storage -> ctype -> option string -> nat -> statement
       | If: expr -> statement -> statement -> statement
(*       | For: statement -> expr -> statement -> statement -> statement*)
       | While: expr -> statement -> statement
       | CodeBlock: seq statement -> statement
       | Enter
       | Leave .

Record function := mk_fun {
                       fun_id: nat;
                       fun_name: string;
                       args: seq ctype;
                       body: statement; }. (* all functions are void; if they return smth it is written by pointer passed as arg *)

Record static_ctx : Set := mk_stat_ctx { functions: seq function; variables: seq ( seq var_descr ) }.
       Definition stat_ctx_empty:= mk_stat_ctx [::] [::].
       Definition stat_ctx_mod (s:static_ctx)
                  (mfuns: seq function -> seq function) (mvars: seq (seq var_descr)  -> seq (seq var_descr )) :=
         mk_stat_ctx (mfuns $ functions s) (mvars $ variables s).

Record dynamic_ctx : Set := mk_dyn_ctx { memory: seq block; call_stack: seq statement }.
       Definition dyn_ctx_mod (d:dynamic_ctx)
                  (mmem: seq block -> seq block) (mcs: seq statement -> seq statement) :=
         mk_dyn_ctx (mmem $ memory d) (mcs $ call_stack d).
  
       Definition dynamic_ctx_empty := mk_dyn_ctx [::] [::].
       Definition dyn_ctx_push (d:dynamic_ctx) (s:statement) : dynamic_ctx := mk_dyn_ctx (memory d) (s::call_stack d).
       Definition get_var (sc:static_ctx) (name:string) : option var_descr :=
         option_find (fun p: var_descr => var_name p == name) (flatten (variables sc)).
       Definition get_fun (sc:static_ctx) (name:string) : option function :=
         option_find (fun p: function => fun_name p == name) (functions sc).

Fixpoint type_solver {sc: static_ctx}  (e: expr) : ctype:=
  let slv := @type_solver sc  in
  match e with
    | Lit t _ => t
    | Var name => match get_var sc name with
                    | Some v => Pointer $ var_type v
                    | None => ErrorType
                  end
    | Binop _ l r => eq_value_or_error_arith (slv l) (slv r) (fun t _ => t) ErrorType
    | Unop Asterisk op => match slv op with
                            | Pointer t => t
                            | _ => Bot
                          end
    | Unop _ o => slv o
  end.




Program Definition binop_interp (t:ctype) (op: binop) : int -> int -> value t :=
  match t with
    | Int kind =>
      match op with
        |Add => fun x y=> @Value t t _ $ cast (addz x y ) _
        |Sub => fun x y=> @Value t t _ $ cast (addz x (oppz y) ) _
        | _ => (fun _ _ => Error _)
      end
    | _ => (fun _ _ => Error _)
  end.
Solve All Obligations with done.

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

Program Definition dereference (tp:ctype) (v: value (Pointer tp)) (dyn:dynamic_ctx) : value tp :=
  let ret_type := value tp in
  match v as vo return v = vo -> ret_type with
    | Value (Pointer tp) _  (Goodptr i o) as vo => fun Hto =>
      match option_nth (memory dyn) i  as fb with
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
  symmetry in Heq_anonymous.
  by move /eqP in Heq_anonymous.
Defined.
(*
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
  *)



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
                    | Some (declare_var n t loc) => match find_block dyn loc  with
                                                    | Some b => match el_type b == t with
                                                                  | true => Value (Pointer t) (Pointer t) _ ( Goodptr t loc 0) 
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
            eq_value_or_error_proved_arith (Int kx) (Int ky) (fun H tx ty => binop_interp (type e') opcode (cast x _) (cast y _) ) (Error _)
          | _, _ => Error _
        end 
(*    | Call _ _ => fun _ => Error _ *)
  end _
.
Next Obligation.
  rewrite /_dollar. simpl. by rewrite -Heq.  Defined.


      Definition alloc_block {dc: dynamic_ctx} (b:block) : dynamic_ctx := mk_dyn_ctx ( (memory dc) ++ [:: b] ) (call_stack dc).

      Definition next_block_id (s:dynamic_ctx) : nat := size $ memory $ s.

      Fixpoint garbage_values {t:ctype} (sz: nat) : seq (value t) :=
        match sz with | n .+1 => (Garbage t) :: (garbage_values n) | 0 => [::] end.

      Definition bind_var (v:var_descr) (i:nat) (ctx:static_ctx) :=
        mk_stat_ctx (functions ctx) $ match variables ctx with
                                        | [::] => [:: [:: v] ]
                                        | cons x xs => cons (cons v x) xs
                                      end.
      
      
Inductive prog_state :=
      | Good: static_ctx -> dynamic_ctx -> prog_state
      | Bad : static_ctx -> dynamic_ctx -> statement -> prog_state.
      
      Definition stat_init := mk_stat_ctx nil [:: nil (*[:: declare_var "Unit" Unit 0 ] *) ].
      Definition get_stat p := match p with | Good s _ | Bad s _ _ => s end.
      Definition get_dyn p := match p with | Good _ d| Bad _ d _ => d end.

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


Program Definition mem_write (t: ctype) (id: nat) (pos: nat) (dyn: dynamic_ctx) (val: value t) : dynamic_ctx ?:=
  let m := memory dyn in
  let oldblock := option_nth m id in
  match oldblock with
    | Some _oldblock =>
      match ctype_beq t (el_type _oldblock) as Ht with
        | true => match block_mod _oldblock pos (cast val _) with
                            | Some newblock => Some $ mk_dyn_ctx  (set_nth ErrorBlock m id newblock) (call_stack dyn)
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

Definition add_var (vd:var_descr) (c: static_ctx):=
  mk_stat_ctx
    (functions c)
    match variables c with
      | [::] => [:: [:: vd ]]
      | cons x xs => cons (cons vd x) xs
    end
.

Program Definition is_value_true {t} {c:static_ctx} (v: value t) : option bool:=
  match v as v0 return v = v0 -> option bool with
    | Value (Int kind) _ z as v0 => fun H: v = v0 => Some (@sgz int_numDomainType z != 0)
    | Value (Pointer _) _ Nullptr as v0 => fun H: v = v0=> Some false
    | _ => fun _ => None 
  end _.

Lemma value_inj a b c  v1 v2: Value a b c v1 = Value a b c v2 -> v1 = v2.
  move=> H.
  inversion H.
  by depcomp H1.
Defined.  
  
Definition eval ps e: value ( @type_solver ( get_stat ps) e ) :=
  iexpr (get_stat ps) (get_dyn ps) e.


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
       have Hlst: forall (A:Type) (a:A) l,  a :: l = l -> False. by  move=> A a; elim =>//=; move=> a0 l0 IH [] =><-. 
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
     Qed.  

     Definition expr_eqP := reflect_from_dec expr_eq_dec.

     Canonical expr_eqMixin := EqMixin expr_eqP.
     Canonical expr_eqType := EqType expr expr_eqMixin.
     
     Theorem statement_eq_dec: eq_dec statement.
       rewrite /eq_dec.   
       fix 1.
       have option_eq_dec t: eq_dec t ->  eq_dec (option t). by rewrite /eq_dec =>H; decide equality.
       decide equality.
       apply ( seq_eq_dec _ expr_eq_dec).
       apply expr_eq_dec.
       apply expr_eq_dec.
       apply expr_eq_dec.     
       apply nat_eq_dec.
       apply (option_eq_dec _ string_eq_dec).
       apply ctype_eq_dec.
       apply storage_eq_dec.
       apply expr_eq_dec.
       apply expr_eq_dec.
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

     (* Todo: make the lists potentially infinite? *)
     
Program Fixpoint interpreter_step (s: prog_state) : prog_state :=
  match s with
    | Good _ (mk_dyn_ctx _ nil) => s
    | Good ((mk_stat_ctx funs vars) as oldstat) ((mk_dyn_ctx mem (st::ss)) as olddyn) =>
      let dyn := mk_dyn_ctx mem ss in
      let bad := Bad oldstat olddyn st in
    match st with
      | Skip => Good oldstat dyn
      | Call x x0 => s (* TODO *)
      | Assign w val  =>
        match eval s w, eval s val with
          | Value (Pointer t) _ (Goodptr to off), Value vtype _ v =>                           
            match vtype == t with
              | true =>
                    match mem_write t to off dyn (Value t t _  (cast v _) ) with
                      | Some d => Good oldstat d
                      | None => bad
                    end
              | _ => bad
            end
          | _, _ => bad
        end                      
      | Alloc loc type o_name sz =>
        let block_id := next_block_id dyn in
        let newdyn := dyn_ctx_mod dyn (fun m=> m ++ [:: mk_block loc block_id (sz* SizeOf type) type (garbage_values sz)]) id  in
        match o_name with
          | None => Good oldstat newdyn
          | Some name => Good (add_var (declare_var name type block_id) oldstat ) newdyn
        end
      | If cond _then _else => let cont := match @is_value_true _ oldstat $ eval s cond with
                                 | Some true => _then
                                 | _ => _else
                               end in
                                 Good oldstat $ dyn_ctx_mod dyn id (cons cont)
      | While cond body => match @is_value_true _ oldstat $ eval s cond with
                             | Some true => Good oldstat $ dyn_ctx_mod olddyn id (cons body)
                             | _ => Good oldstat dyn
                           end
      | CodeBlock sts => let bc := [:: Enter] ++ sts ++ [::Leave] in
                         let newdyn := dyn_ctx_mod dyn id (cat bc) in
                         Good oldstat newdyn
      | Enter => add_static_ctx $ Good oldstat dyn
      | Leave => remove_static_ctx $ Good oldstat dyn
    end
    | Bad stat dyn state => s
  end.

Next Obligation.
  symmetry in Heq_anonymous.
  by rewrite (eqP Heq_anonymous).
Defined. 
Next Obligation.
  have Hp: Pointer H2 = Pointer t.
  rewrite H3.
  by rewrite wildcard'.
  inversion Hp.
  subst.
  case => H.
  subst.
  rewrite (proof_irrelevance _ H3 wildcard') in H.
  apply value_inj in H.
  inversion H.
Defined.
  
Definition LocVar t name := Alloc Stack t (Some name%string) 1. 

Notation "{  x1 ; .. ; xn }" := (CodeBlock(  cons x1  .. (cons xn nil) ..) ) (at level 35, left associativity) : c. 
Notation "'int8 x " := (LocVar Int8 x) (at level 200, no associativity) :c.
Notation "'uint8 x " := (LocVar UInt8 x) (at level 200, no associativity) :c.
Notation "'int16 x " := (LocVar Int16 x) (at level 200, no associativity) :c.
Notation "'uint16 x " := (LocVar UInt16 x) (at level 200, no associativity) :c.
Check Assign (Var "x") (Lit Int64 4).

Notation "' v := value" := (Assign (Var v) (value) ) (at level 200, no associativity) :c.
Delimit Scope c with c.
Definition test_assign := {
                           'int8 "x";
                           ' "x" := Lit Int8 4
                           }%c.

Definition sample_prog1 := {
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
Definition init_state_for (s:statement) := Good (stat_ctx_mod stat_init (fun _=> [:: mk_fun 0 "main" nil s ] ) id ) $
                                                mk_dyn_ctx  nil [:: s] .
                                                


Fixpoint interpret (steps:nat) (state: prog_state) :=
  match steps with | 0 => state
                | S steps => match state with
                               |Bad _ _ _ => state
                               |Good _ _ => interpret steps $ interpreter_step state
                             end
  end.

Definition statement_state (s:prog_state) (st:statement) := match s with
                                                              | Good x dc => Good x $ dyn_ctx_mod dc id (cons st)
                                                              | Bad x x0 x1 => s
                                                            end.
Definition isbad s := match s with | Bad _ _ _ => true | _ => false end.

Compute interpret 4 (init_state_for test_assign).

Definition ts := Eval compute in interpret 6 (init_state_for sample_prog1).

Open Scope c.
Compute interpreter_step $ statement_state ts $ ' "x" := Lit Int8 10 . 




        Extraction "tt.ml" t.


Eval compute in eval (fst testr) (Var "x").


Definition ex1 := Alloc Stack (Int S64) (Some "x"%string) 1.
Definition ex_var_x := LocVar Int8 "x" .
Definition ex_var_py := LocVar (Pointer Int8) "y".
Definition ex_literal := Lit Int64 (Negz 4).

Definition neg_expr := Unop Neg ex_literal.
Definition add_expr := Binop Add neg_expr ex_literal. 

Definition ex_var_x_expr := Var "x".

Definition ex_skip := Skip.
xcDefinition ex_alloc := LocVar Int64 "x".
Definition ex_varalloc_stat  := interpreter_step ex_alloc state_init.
Compute ex_varalloc_stat.


Eval compute in eval ex_varalloc_stat ex_var_x_expr.

