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

  
Inductive binop : Set := | Add | Sub | Mul | Div | LAnd | LOr | Eq .
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
       | EDeallocated (t:ctype)
       | EGarbage (t:ctype)
       | Var   (_:string)
       | Binop (_:binop) (_ _: expr)
       | Unop  (_:unop)  (_: expr).

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
       | Leave .

Record function := mk_fun {
                       fun_id: nat;
                       fun_name: string;
                       args: seq (string * ctype);
                       body: statement;
                       fun_location: nat}. (* all functions are void; if they return smth it is written by pointer passed as arg *)

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
    | EDeallocated t => t
    | EGarbage t => t
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




Definition binop_interp (t:ctype) (op: binop) : int -> int -> value :=
  match t with
    | Int num => match op with
                   | Add => fun x y=> Value (Int num) $ addz x y
                   | Sub => fun x y=> Value (Int num) $ addz x (oppz y)
                   | Mul => fun x y => Value (Int num) $ intRing.mulz x y
                   | Eq  => fun x y=> Value (Int num) $ Posz $ if x == y then 1 else 0
                   | _ => fun _ _ => Error
                 end
    | _ => fun _ _ => Error
  end.

Definition unop_interp (t:ctype) (op:unop) : int -> value  :=
  match t with
    | Int kind =>
      match op with
        | Neg => fun x => Value (Int kind) $ oppz x
        | Not => fun x => Value (Int kind) $ Posz $ if sgz x == 0 then 1 else 0
        | _ => fun _ => Error
      end
    | _ => fun _ => Error
  end.
  
Definition find_block (m: dynamic_ctx) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ memory m.

Definition dereference (dyn:dynamic_ctx) (v:value) : value :=
  match v with
    | Value (Pointer pt) (Goodptr i o) =>
      match option_nth (memory dyn) i with
        | Some (mk_block lo _i sz block_type contents) =>
          if block_type == pt then nth Error contents o else Error
        | None => Error
      end
    | _ => Error
  end.

Fixpoint iexpr (stat:static_ctx) (dyn: dynamic_ctx) (e:expr) : value :=
  let interp := iexpr stat dyn in
  let type := @type_solver stat in
  let vars := flatten $ variables stat in
  let blocks := memory dyn in
  match e with
    | Lit t v => Value t v
    | EDeallocated t => Deallocated
    | EGarbage t => Garbage
    | Var name => match get_var stat name  with
                    | Some (declare_var n t loc) =>
                      match find_block dyn loc with
                        | Some b =>
                          if el_type b == t
                          then Value (Pointer t) (Goodptr t loc 0)
                          else Error
                        | None => Error
                      end
                    | None => Error
                  end
    | Binop opcode l r =>
      match interp l, interp r with
        | Value (Int kx) x, Value (Int ky) y =>
          eq_value_or_error_arith (Int kx) (Int ky) (fun tx ty => binop_interp (type e) opcode x y) Error
        | _, _ => Error
      end
    | Unop Asterisk op => match interp op with
                            | Value (Pointer pt) p => dereference dyn (interp op)
                            |_ => Error
                          end
    | Unop code op =>
      match interp op with
        | Value (Int kind) v => unop_interp (type e) code v
        |_ => Error
      end
  end.

      Definition alloc_block {dc: dynamic_ctx} (b:block) : dynamic_ctx := mk_dyn_ctx ( (memory dc) ++ [:: b] ) (call_stack dc).

      Definition next_block_id (s:dynamic_ctx) : nat := size $ memory $ s.

      Fixpoint garbage_values (sz: nat) : seq value :=
        match sz with | n .+1 => Garbage :: (garbage_values n) | 0 => [::] end.

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

Definition block_mod (b: block) (idx: nat) (e: value) : block? :=
        if idx * ( SizeOf (el_type b)) >= block_size b then None else
          match e with
            | Value t v =>
              match el_type b == t with
                | true => Some $ mk_block
                               (region b)
                               (block_id b)
                               (block_size b)
                               (el_type b)
                               (set_nth Error (contents b) idx (Value t v))
                | false => None
              end
            | Garbage as e
            | Deallocated as e=>  Some $ mk_block
                               (region b)
                               (block_id b)
                               (block_size b)
                               (el_type b)
                               (set_nth Error (contents b) idx e)
            | Error => None
        end.

Definition ex_block := mk_block Stack 0 64 Int64 (garbage_values 8).
Eval compute in block_mod ex_block 1 (Value Int64 3).

Definition ErrorBlock := mk_block Data 0 0 ErrorType [::].

Definition mem_write (dyn: dynamic_ctx)  (bid:nat) (pos: nat) (val:value) : dynamic_ctx? :=
  let m := memory dyn in
  let oldblock := option_nth m bid in
  let can_write v tp := match v with
                          | Value t v => t == tp
                          | Garbage 
                          | Deallocated => true
                          | Error => false
                        end in
  match oldblock with
    | Some oldblock =>
      if can_write val $ el_type oldblock then
        option_map (fun newblock=> dyn_ctx_mod dyn (fun _=> set_nth ErrorBlock m bid newblock) id) $  block_mod oldblock pos val
      else None
    | None => None
  end.

Definition add_var (vd:var_descr) (c: static_ctx):=
  mk_stat_ctx
    (functions c)
    match variables c with
      | [::] => [:: [:: vd ]]
      | cons x xs => cons (cons vd x) xs
    end
.

Definition is_value_true {c:static_ctx} (v: value) : option bool:=
  match v with
    | Value (Int kind) z => Some $ sgz z != 0
    | Value (Pointer _) Nullptr => Some false
    | Value (Pointer _) (Goodptr _ _) => Some true 
    | _ => None 
  end.

(*Lemma value_inj a  v1 v2: Value a v1 = Value a b c v2 -> v1 = v2.
  move=> H.
  inversion H.
  by depcomp H1.
Defined.  *)
  
Definition eval ps e: value :=
  iexpr (get_stat ps) (get_dyn ps) e.


Theorem carrier_eq_dec: forall t, eq_dec (coq_type t).
  rewrite /eq_dec.
  case; try by apply unit_eq_dec.
  - case; apply int_eq_dec.
  - apply ptr_eq_dec.
  - move=> *. apply (seq_eq_dec _ nat_eq_dec). 
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
       - move=> t0 t; move: (ctype_eq_dec t0 t) =>[].
         by move => ->; left.
         by move=> H; right; case=> H'; symmetry in H'. 
       - move=> t0 t; move: (ctype_eq_dec t0 t) =>[].
           by move => ->; left.
           by move=> H; right; case=> H'; symmetry in H'.
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
       apply string_eq_dec.
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

     (* Add: 
* Check if expression types are corresponding to arguments;
* Throw in assignments 
*)
     

Definition LitFromExpr (ps: prog_state) (e:expr): expr ?:=
  match eval ps e  with
    | Value t v => Some $ Lit t v 
    | Garbage =>  None 
    | Deallocate => None 
  end .


Definition prologue_arg (ps: prog_state) (name:string) (t:ctype) (e:expr) :=
  option_map (fun l =>  [:: Alloc Stack t (Some name) 1; Assign (Var name) l] ) $ LitFromExpr ps e.

Definition prologue_args (ps:prog_state) (f:function) (es: seq expr) :=
  let vals :=  map (fun a => prologue_arg ps (fst (fst a)) (snd (fst a)) (snd a)) $ zip (args f) es in
  foldl cat_if_some (Some nil) vals.

Definition prologue_for (ps: prog_state) (f:function) (argvals: seq expr) : option ( seq statement)  :=
  option_map (cons Enter) $ prologue_args ps f argvals.
(*
Definition epilogue_arg (ps: prog_state) (name:string) (t:ctype) (e:expr) :=
  Some [:: Assign (Var name) (EDeallocated t)] .


Definition epilogue_args (ps:prog_state) (f:function) (es: seq expr) :=
  let vals :=  map (fun a => epilogue_arg ps (fst (fst a)) (snd (fst a)) (snd a)) $ zip (args f) es in
  foldl cat_if_some (Some nil) vals.
 *)

Definition epilogue_for (ps: prog_state) (f:function) (argvals: seq expr) : option ( seq statement)  := Some [:: Leave].
(*  option_map (fun x => x ++ [:: Leave]) $ epilogue_args ps f argvals. *)

Definition fun_by_address {t} (p: ptr t) (stat:static_ctx) (dyn:dynamic_ctx) : function? :=
  match p with 
    | Goodptr b o => option_find (fun f=> fun_location f == b) $ functions stat
    | _ => None
  end.
Definition extract_some {T} (x:  T ? ? ) : T? :=
  match x with
    |Some x => x
    | None => None
  end.

Fixpoint interpreter_step (s: prog_state) : prog_state :=
  match s with
    | Good _ (mk_dyn_ctx _ nil) => s
    | Good ((mk_stat_ctx funs vars) as oldstat) ((mk_dyn_ctx mem (st::ss)) as olddyn) =>
      let dyn := mk_dyn_ctx mem ss in
      let bad := Bad oldstat olddyn st in
    match st with
      | Skip => Good oldstat dyn
      | Call fname fargs =>
        match get_fun oldstat fname with
          | Some f =>
            match prologue_for s f fargs, epilogue_for s f fargs with
              | Some prologue, Some epilogue =>
                Good oldstat $ dyn_ctx_mod dyn id (fun x => prologue ++ body f :: epilogue ++ x)
              | _, _ => bad
            end
          | None => bad
        end
      | Debug => s         
      | Assign w val  =>
        match eval s w, eval s val with
          | Value (Pointer t)  (Goodptr to off), Value vtype v =>                           
            if vtype == t then
                match mem_write dyn to off  (Value _ v ) with
                      | Some d => Good oldstat d
                      | None => bad
                end
                  else bad
          | Value (Pointer t) (Goodptr to off) , Deallocated as v
          | Value (Pointer t) (Goodptr to off) , Garbage as v=>
                match mem_write dyn to off  v with
                      | Some d => Good oldstat d
                      | None => bad
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
      | If cond _then _else => let cont := match @is_value_true oldstat $ eval s cond with
                                 | Some true => _then
                                 | _ => _else
                               end in
                                 Good oldstat $ dyn_ctx_mod dyn id (cons cont)
      | While cond body => match @is_value_true oldstat $ eval s cond with
                             | Some true => Good oldstat $ dyn_ctx_mod olddyn id (cons body)
                             | _ => Good oldstat dyn
                           end
      | CodeBlock sts => let bc := [:: Enter] ++ sts ++ [::Leave] in
                         let newdyn := dyn_ctx_mod dyn id (cat bc) in
                         Good oldstat newdyn
      | Enter => add_static_ctx $ Good oldstat dyn
      | Leave =>let newdyn :=
                    match variables $ oldstat with
                      | v::vv =>
                        @foldl  (var_descr) (option dynamic_ctx)
                               (fun sd v => extract_some $ option_map (fun sd=>mem_write sd (location v) 0 Deallocated) sd) (Some dyn) v
                      | nil => None
                    end in
                match newdyn with
                  | Some newdyn => remove_static_ctx $ Good oldstat newdyn
                  | None => bad
                end
    end
    | Bad stat dyn state => s
  end.


Definition init_state_for (s:statement) := Good (stat_ctx_mod stat_init (fun _=> [:: mk_fun 0 "main" nil s 0 ] ) id ) $
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

Definition start_from_0th_fun (c:static_ctx): dynamic_ctx :=
  match ohead $ functions c with
    | None => dynamic_ctx_empty
    | Some main => dyn_ctx_push dynamic_ctx_empty (body main)
  end.
Definition init_state_for_prog (sc: static_ctx) := Good sc (start_from_0th_fun sc).


Definition LocVar t name := Alloc Stack t (Some name%string) 1. 

Notation "{{  x1 ; .. ; xn }}" := (CodeBlock(  cons x1  .. (cons xn nil) ..) ) (at level 35, left associativity) : c. 
Notation "'int8 x " := (LocVar Int8 x) (at level 200, no associativity) :c.
Notation "'uint8 x " := (LocVar UInt8 x) (at level 200, no associativity) :c.
Notation "'int16 x " := (LocVar Int16 x) (at level 200, no associativity) :c.
Notation "'uint16 x " := (LocVar UInt16 x) (at level 200, no associativity) :c.
Notation "'int32 x " := (LocVar Int32 x) (at level 200, no associativity) :c.
Notation "'uint32 x " := (LocVar UInt32 x) (at level 200, no associativity) :c.
Notation "'int64 x " := (LocVar Int64 x) (at level 200, no associativity) :c.
Notation "'uint64 x " := (LocVar UInt64 x) (at level 200, no associativity) :c. 


Notation "' v := value" := (Assign v (value) ) (at level 200, no associativity) :c.
Notation " /* v " := (Unop Asterisk v) (at level 200, right associativity) :c.
Notation " /i n  " := (Lit Int64 n) (at level 210, no associativity) :c.
Delimit Scope c with c.
Open Scope string.
Open Scope c.

Definition GetVar s := ( Unop Asterisk ( Var s ) ).
Definition Arg := Var.
Definition AddrVar := Var.


Definition test_assign := {{
                           'int8 "x";
                           ' Var "x" := /i 4 
                            }}.

Definition sample_call : static_ctx :=
  mk_stat_ctx [::
                 mk_fun 0 "main" [::] ({{
                                           'int64 "x";
                                           Call "f" [:: Var "x"]
                                         }}) 0;
                mk_fun 1 "f" [:: ("x", (Pointer Int64)) ]
                       ({{
                           ' Var "x"  := /i 2
                          }}) 1 ]
              nil.
(* 
if (x == 1) res <- 1 else 
{
alloc y;
y <- x;
y <- fact (x - 1) 
res <- res * y
}
*)
Definition sample_fact : static_ctx :=
  mk_stat_ctx [::
                 mk_fun 0 "main" [::] ({{
                                           'int64 "x";
                                           ' Var "x" := /i 1;
                                           Call "f" [:: AddrVar "x"; /i 6 ];
                                           Debug
                                         }}) 0;
                
                mk_fun 1 "f" [:: ("res", (Pointer Int64)); ("x", Int64) ]
                       ({{
                            If (Binop Eq ( GetVar "x" ) ( /i 0 ) )
                               (' /* (Var "res") :=  /i 1 )
                               ({{
                                    'int64 "y";
                                    ' AddrVar "y" := GetVar "x";
                                   Call "f" [::AddrVar "y"; Binop Sub (GetVar "x") (/i (Posz 1)) ];
                                   
                                   Assign ( /* Var "res"  ) $ Binop Mul ( /* (GetVar "res") ) (GetVar "y")
                                          }})
                          }}) 1 ]
              nil.


Definition halts (ps: prog_state):= exists n:nat, call_stack ( get_dyn ( interpret n ps )) = nil.
  
  

Fixpoint unsome {T} (s:seq (option T) ) :=
  match s with
    | (Some s ):: ss => s :: unsome ss
    | None :: _=>  nil
    | nil => nil
  end.

Fixpoint unsome3 {T A B} (s:seq (A * B * (option T)) ) :=
  match s with
    | (x, y, Some s ):: ss => (x,y,s) :: unsome3 ss
    | _ => nil
  end.

Definition dumpvars (ps: prog_state) :=
  let stat := get_stat ps in
  let cntns (n:nat) := option_map contents $ find_block (get_dyn ps) n in
  let varinfo :=  get_var stat in
  let varnames := undup $ map var_name $  flatten (variables  stat) in
  let vards := map varinfo varnames in
unsome3 $  unsome $  map (option_map (fun vd => (var_name vd, var_type vd,  cntns $ location vd))) vards.
Definition is_good ps := match ps with | Good _ _  => true | _ => false end.

Let f := fun steps=>
        let state := interpret steps $ init_state_for_prog sample_fact in state.
(*        (is_good state, dumpvars state, get_dyn state).*) 
Compute f  1 .
Compute f  2 .
Compute f  3 .
Compute f  4 .
Compute f  5 .
Compute f  6 .
Compute f  7 .
Compute f  8 .
Compute f  500.
