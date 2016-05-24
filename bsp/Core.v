From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
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
       | BspPopReg: expr-> expr-> statement (* ptr and size *)
       | BspGet: expr -> expr-> expr-> expr -> expr-> statement (* pid source offset dest size *)
       | BspPut: expr -> expr-> expr-> expr -> expr -> statement. (* pid dest offset source size *)

Record function := mk_fun {
                       fun_id: nat;
                       fun_name: string;
                       args: seq (string * ctype);
                       body: statement;
                       fun_location: nat}. (* all functions are void; if they return smth it is written by pointer passed as arg *)


Inductive get_query := Get t:  nat-> ptr t-> int -> ptr t -> nat -> get_query .
Inductive put_query := Put t:  nat-> seq value -> ptr t -> nat -> put_query .
Inductive push_query := Push: anyptr -> nat -> push_query.
Inductive pop_query := Pop: anyptr -> pop_query.


Record proc_state := mk_proc_state {
                         proc_id : nat;
                         proc_symbols : seq (seq var_descr);
                         proc_queue_get: seq get_query;
                         proc_queue_put: seq put_query;
                         proc_queue_pop_reg: seq pop_query;
                         proc_queue_push_reg: seq push_query;
                         proc_memory: seq block;
                         proc_conts: seq statement;
                         proc_registered_locs: seq ( anyptr * nat )                         
                       }.
Definition ps_mod_f
           mod_syms    
           mod_queue_get 
           mod_queue_put 
           mod_queue_pop 
           mod_queue_push
           mod_memory    
           mod_conts     
           mod_reg_locs  
           (ps: proc_state) : proc_state :=
  mk_proc_state
    (proc_id ps)
    (mod_syms ps)
    (mod_queue_get ps)
    (mod_queue_put ps)
    (mod_queue_pop ps)
    (mod_queue_push ps)
    (mod_memory ps)
    (mod_conts ps)
    (mod_reg_locs ps)
.

Definition ps_mod
           mod_syms    
           mod_queue_get 
           mod_queue_put 
           mod_queue_pop 
           mod_queue_push
           mod_memory  
           mod_conts   
           mod_reg_locs : proc_state -> proc_state :=
  ps_mod_f
    (mod_syms \o proc_symbols)
    (mod_queue_get \o proc_queue_get)
    (mod_queue_put \o proc_queue_put)
    (mod_queue_pop \o proc_queue_pop_reg)
    (mod_queue_push \o proc_queue_push_reg)
    (mod_memory \o proc_memory)
    (mod_conts \o proc_conts)
    (mod_reg_locs \o proc_registered_locs).

Definition ps_mod_syms       f := ps_mod f  id id id id id id id.
Definition ps_mod_queue_get  f := ps_mod id f  id id id id id id.
Definition ps_mod_queue_put  f := ps_mod id id f  id id id id id.
Definition ps_mod_queue_pop  f := ps_mod id id id f  id id id id.
Definition ps_mod_queue_push f := ps_mod id id id id f  id id id.
Definition ps_mod_mem        f := ps_mod id id id id id f  id id.
Definition ps_mod_cont       f := ps_mod id id id id id id f  id.
Definition ps_mod_reg_loc    f := ps_mod id id id id id id id f .

Inductive error_code := | OK | BadPointer | ModNonExistingBlock | PointerOutsideBlock| BadWriteLocation | TypeMismatch | WritingGarbage | NonExistingSymbol | GenericError | InvalidPopReg | InvalidPushReg | InvalidGet | InvalidPut.
Scheme Equality for error_code.
Canonical error_code_eqMixin := EqMixin (reflect_from_dec error_code_eq_dec).
Canonical error_code_eqType := EqType error_code error_code_eqMixin.



Inductive machine_state :=
| MGood: seq proc_state -> seq function -> machine_state
| MBad:  seq ((error_code * option statement) * proc_state) -> seq function -> machine_state.

Definition ms_source s := match s with | MGood _ f | MBad  _  f => f end.
Definition ms_procs s := match s with | MGood p _ => p | MBad  p _ => map snd p end.

Definition proc_state_empty:= @nil (seq var_descr).

Definition perform_enter (ps: proc_state) : proc_state := ps_mod_syms (cons nil) ps.

Definition get_var (ps:proc_state) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (flatten (proc_symbols ps)).

Definition get_fun (s:machine_state) (name:string) : option function :=
         option_find (fun p: function => fun_name p == name) $ ms_source s.

Fixpoint type_solver {ps:proc_state}  (e: expr) : ctype:=
  let slv := @type_solver ps  in
  match e with
    | Lit t _ => t
    | EDeallocated t => t
    | EGarbage t => t
    | Var name => match get_var ps name with
                    | Some v => Pointer $ var_type v
                    | None => ErrorType
                  end
    | Binop _ l r => eq_value_or_error_arith (slv l) (slv r) (fun t _ => t) ErrorType
    | Unop Asterisk op => match slv op with
                            | Pointer t => t
                            | _ => Bot
                          end
    | Unop _ o => slv o
    | BspNProc => Int64
    | BspPid => Int64
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
  
Definition find_block (ps: proc_state) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ proc_memory ps.

Definition dereference (ps: proc_state) (v:value) : value :=
  match v with
    | Value (Pointer pt) (Goodptr i o) =>
      match option_nth (proc_memory ps) i with
        | Some (mk_block lo _i sw sz block_type contents) =>
          if block_type == pt then nth Error contents o else Error
        | None => Error
      end
    | _ => Error
  end.

Fixpoint iexpr (ms:machine_state) (pid:nat) (e:expr) : value :=
  match ms with
    | MBad  _ _ => Error

    | MGood procs _ => 
      match option_nth procs pid with
        | None => Error
        | Some ps =>
          let interp := iexpr ms pid in
          let type := @type_solver ps in
          let vars := flatten $ proc_symbols ps in
          let blocks := proc_memory ps in

          match e with
            | BspNProc => Value Int64 $ size procs
            | BspPid => Value Int64 $ pid
            | Lit t v => Value t v
            | EDeallocated t => Deallocated
            | EGarbage t => Garbage
            | Var name => match get_var ps name  with
                            | Some (declare_var n t loc) =>
                              match find_block ps loc with
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
                                    | Value (Pointer pt) p => dereference ps (interp op)
                                    |_ => Error
                                  end
            | Unop code op =>
              match interp op with
                | Value (Int kind) v => unop_interp (type e) code v
                |_ => Error
              end
          end
      end
  end.

Definition alloc_block (ps: proc_state) (b:block) : proc_state := ps_mod_mem (cat [:: b] ) ps.

Definition next_block_id : proc_state -> nat := size \o proc_memory.

Fixpoint  fill_values (sz: nat) (v:value) : seq value :=
  match sz with | n .+1 => v :: (fill_values n v) | 0 => [::] end.

Definition bind_var (v:var_descr) (b_id:nat) :=
  ps_mod_syms (fun vs => match vs with
                           | nil => cons [::v] nil
                           | cons x xs => cons (cons v x) xs
                         end).



Definition block_mod_cont f b :=
  mk_block
    (region b)
    (block_id b)
    (block_size b)
    (shared_with b)
    (el_type b)
    (f (contents b)).
(*
Definition block_mod (b: block) (idx: nat) (e: value) : block? :=
        if idx * ( SizeOf (el_type b)) >= block_size b then None else
          match e with
            | Value t v =>
              match el_type b == t with
                | true => Some $ mk_block
                               (region b)
                               (block_id b)
                               (block_size b)
                               (shared_with b)
                               (el_type b)
                               (set_nth Error (contents b) idx (Value t v))
                | false => None
              end
            | Garbage as e
            | Deallocated as e=>  Some $ mk_block
                               (region b)
                               (block_id b)
                               (block_size b)
                               (shared_with b)
                               (el_type b)
                               (set_nth Error (contents b) idx e)
            | Error => None
        end.
*)
Definition ex_block : block := mk_block Stack 0 64 nil Int64 (fill_values 8 Garbage).
Eval compute in block_mod_cont (const $ [:: Value Int64 3]) ex_block.

Definition ErrorBlock := mk_block Data 0 0 nil ErrorType [::].

Definition can_write (b:block) (i:nat) (v:value) : error_code :=
  match option_nth (contents b) i, v with
    | Some (Value bt bv), (Value t v) => if (el_type b == t) && (bt == t) then OK else TypeMismatch
    | Some Garbage, Value t v => if el_type b == t then OK else TypeMismatch
    | Some Deallocated, _ => BadWriteLocation
    | Some _, Deallocated => WritingGarbage
    | Some _, Error => GenericError
    | Some _, Garbage => WritingGarbage
    | Some Error, _ => GenericError
    | None, _ => BadWriteLocation
  end.

Definition mem_write  (bid:nat) (pos: nat) (val:value) (ps: proc_state): (error_code * proc_state) :=
  let m := proc_memory ps in
  let oldblock := option_nth m bid in
  match oldblock with
    | Some oldblock =>
      if can_write oldblock pos val == OK then
        let newblockcnt := set_nth val (contents oldblock) pos val in
        let newblock := block_mod_cont (const newblockcnt) oldblock in
        let newmem := set_nth ErrorBlock m bid newblock in
        (OK, ps_mod_mem (const newmem) ps)
      else (can_write oldblock pos val, ps)
    | None => (ModNonExistingBlock, ps)
  end.

Definition mem_write_block (bid:nat) (val:value) (ps: proc_state): (error_code * proc_state) :=
  let lastidx := option_map block_size $ option_nth (proc_memory ps) bid in
  let fix process idx s :=
      match idx with
        | 0 => mem_write bid idx val s
        | S i => match mem_write bid idx val s with
                   | (OK, ns) => process i ns
                   | o => o
                 end
      end in
  match lastidx with
    | Some lastidx => process lastidx ps
    | None => (GenericError, ps)
  end.


Definition add_var (vd: var_descr) := ps_mod_syms
                                        (fun s=> match s with
                                                   | nil => cons [::vd] nil
                                                   | cons x xs => cons (cons vd x) xs
                                                 end).

Definition is_value_true {ps:proc_state} (v: value) : option bool:=
  match v with
    | Value (Int kind) z => Some $ sgz z != 0
    | Value (Pointer _) Nullptr => Some false
    | Value (Pointer _) (Goodptr _ _) => Some true 
    | _ => None 
  end.
  

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
       - by left.
       - by left.
     Qed. 

     Definition expr_eqP := reflect_from_dec expr_eq_dec.
     
     Canonical expr_eqMixin := EqMixin expr_eqP.
     Canonical expr_eqType := EqType expr expr_eqMixin.
       
     Theorem statement_eq_dec: eq_dec statement.
       rewrite /eq_dec.   
       fix 1.
       have option_eq_dec t: eq_dec t ->  eq_dec (option t). by rewrite /eq_dec =>H; decide equality.
       decide equality; try apply expr_eq_dec.
       apply ( seq_eq_dec _ expr_eq_dec).
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

     (* Todo: make the lists potentially infinite? *)

     (* Add: 
* Check if expression types are corresponding to arguments;
* Throw in assignments 
*)
     

Definition LitFromExpr (ms: machine_state) (pid:nat) (e:expr): expr ? :=
  match iexpr ms pid e  with
    | Value t v => Some $ Lit t v 
    | Garbage =>  None 
    | Deallocate => None 
  end .


Definition prologue_arg (ms: machine_state) (pid:nat) (name:string) (t:ctype) (e:expr) :=
  option_map (fun l =>  [:: Alloc Stack t (Some name) 1; Assign (Var name) l] ) $ LitFromExpr ms pid e.

Definition prologue_args (ms:machine_state) (pid:nat) (f:function) (es: seq expr) :=
  let vals :=  map (fun a => prologue_arg ms pid (fst (fst a)) (snd (fst a)) (snd a)) $ zip (args f) es in
  foldl cat_if_some (Some nil) vals.

Definition prologue_for (ms: machine_state) (pid:nat) (f:function) (argvals: seq expr) : option ( seq statement)  :=
  option_map (cons Enter) $ prologue_args ms pid f argvals.

Definition epilogue_for (ms: machine_state) (pid:nat) (f:function) (argvals: seq expr) : option ( seq statement)  := Some [:: Leave].

(*Definition fun_by_address {t} (p: ptr t) (stat:static_ctx) (dyn:dynamic_ctx) : function? :=
  match p with 
    | Goodptr b o => option_find (fun f=> fun_location f == b) $ functions stat
    | _ => None
  end.*)


Definition states_folder (ms:machine_state) (proc_step_result : (error_code * (statement?) * proc_state)) :=
  match ms with
    | MBad  _ _ => ms
    | MGood states funs => ms
  end.
Definition apply_writes  (v:value) (s:proc_state) (vars: seq var_descr) :=
  let fix process ids st :=
      match ids with
        | i :: iis =>
          match mem_write_block i v st with
            | (OK, st) =>  process iis st
            | o => o
          end
        | nil => (OK, st)
      end
  in
  process (map location vars) s.

Definition init_value (t:ctype) (l: storage) : value :=
  match l with
    | Heap 
    | Stack
    | Text => Garbage
    | ReadOnlyData => Garbage (*FIXME: Should be 0*)
    | Data =>  Garbage (*FIXME: Should be 0*)
  end.

Definition add_n_z (x:nat) (y:int) :=
  match addz x y with
    | Negz r => None
    | Posz r => Some r
  end.

Definition ptr_add {t} (p: ptr t) (z:int) : ptr t ? :=
  match p with
    | Nullptr => None
    | Goodptr b o => Some $ Goodptr t b $ add_n_z o z
  end.

Definition read_proc_memory (ms:machine_state) (pid:nat) (bid offset size:nat) : (ctype * seq value)? :=
match ms with
  | MGood  pss fs  =>
    match option_nth pss pid with
      | None => None
      | Some ps => match option_nth (proc_memory ps) bid with
                     | Some bl => Some (el_type bl, take size (drop offset (contents bl)))
                     | None => None
                   end
    end
  | MBad _ _ => None
end.

Fixpoint write_proc_memory (ms:machine_state) (pid:nat) (bid offset: nat) (vals: seq value) : machine_state? :=
match ms with
  | MGood  pss fs  =>
    match option_nth pss pid, vals  with
      | None,_ => None
      | Some ps, v::vs =>
        match mem_write bid offset v ps with
          | (OK, news) => let newms := MGood (set_nth ps pss offset news) fs in
                          write_proc_memory newms pid bid (offset.+1) vs
          | _ => None
        end
      | _, nil => Some ms
    end
  | MBad _ _ => None
end.

Definition transformations {A} (init:A) (ts: seq (A->A)) : A :=
  foldl (fun x f=> f x) init ts.

Definition ms_mod_proc_all (f:proc_state->proc_state) (ms:machine_state) :=
  match ms with
    | MGood ps fs  => MGood (map f ps) fs
    | MBad _ _ =>  ms
  end.
  
Definition ms_mod_proc (pid:nat) (f:proc_state->proc_state) :=
  ms_mod_proc_all (fun p=> if proc_id p == pid then f p else p).

Definition push_reg_to_p_transform (p:push_query): proc_state -> proc_state :=
  match p with
    | Push pt sz => ps_mod_reg_loc (cons (pt, sz))
  end.

Definition push_reg_to_ms_transform (frompid: nat) (p:push_query) :machine_state -> machine_state :=
  ms_mod_proc frompid ( push_reg_to_p_transform p ).

Definition apply_push_regs (ms: machine_state) : machine_state :=
  let pushes := flatten $ map (fun p => map  (push_reg_to_ms_transform (proc_id p)) (proc_queue_push_reg p)) (ms_procs ms) in
  ms_mod_proc_all  (ps_mod_queue_push (const nil))   $ transformations ms pushes.

  
Definition slice_pop_requests (ms:machine_state) : (seq pop_query * machine_state) ? :=
  let queries := seq_unsome $ map ( ohead \o proc_queue_pop_reg ) $ ms_procs ms in
  let newms := ms_mod_proc_all (ps_mod_queue_pop (drop 1)) ms in
  option_map (fun x => (x, newms)) queries.


Definition pop_reg_position (q:pop_query) (proc:proc_state) :  nat ? :=
  let queue := proc_registered_locs proc in
  match q with | Pop pt =>
                 let pos := find (fun rec => fst rec == pt) queue in
                 if pos >= size queue then None else Some pos
  end.

Definition coherent_reg_positions  (ms:machine_state) :=
  match option_map fst $ slice_pop_requests ms with
    | Some qs =>
      unsome_bool $  option_map (@constant _) $ seq_unsome $ map (uncurry pop_reg_position) $ zip qs (ms_procs ms)
    | None => false
  end.

Definition apply_pop_regs (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _  => ms
    | MGood ps fs =>
      let bad := MBad ( map (fun x=> pair (pair InvalidPopReg None) x) (ms_procs ms))  fs  in
      if coherent_reg_positions ms then
        match slice_pop_requests ms with
          | Some (req::reqs , reduced_ms) =>
            match seq_unsome
                    $ map (fun pc=> option_map (fun pos => ps_mod_reg_loc (skip_at pos) pc) $ pop_reg_position req pc)
                             (ms_procs ms) with
              | Some ss => MGood ss fs
              | None => bad
            end
          | _ => bad
        end
      else bad
  end.


Definition get_to_ms_transform (pid:nat) (q:get_query) (ms:machine_state) : machine_state  :=
  let bad := MBad (map (pair (pair InvalidGet None)) (ms_procs ms)) $ ms_source ms in
  match q with
    | Get t frompid (Goodptr bid offset) offset' (Goodptr bid_to offset_to) size =>
      match add_n_z offset offset' with
          | Some offset=>
            match read_proc_memory ms frompid bid offset size with
              | Some (t, vals) => match write_proc_memory ms frompid bid_to offset_to vals with
                                    | Some ms => ms
                                    | None => bad
                                  end
              | None => bad
            end
          | None => bad
      end
    | _ => bad
  end.

Definition apply_gets (ms:machine_state) : machine_state :=
  transformations ms $ flatten $
                  map (fun p=> map (get_to_ms_transform (proc_id p)) (proc_queue_get p)) (ms_procs ms).


Fixpoint interpreter_step (ms: machine_state) : machine_state :=
  let pex_state := prod (prod error_code  (statement?)) proc_state in
  let interpret_proc s : pex_state :=
      let pid := proc_id s in
      match proc_conts s with
        | nil => ((OK, None), s)
        | cur_statement::stts =>
          let ok_with s := ((OK, Some cur_statement), s) in
          let err code := ((code, Some cur_statement), s) in
          let loop := ok_with s in
          let skip :=  ok_with $ ps_mod_cont (const stts) s in
          let eval := iexpr ms pid in
          match cur_statement with
            | Skip => skip
            | Call fname fargs =>
              
              match get_fun ms fname with
                | Some f =>
                  match prologue_for ms pid f fargs, epilogue_for ms pid f fargs with
                    | Some prologue, Some epilogue =>
                      ok_with $ ps_mod_cont (cat (prologue ++ body f :: epilogue)) s
                    | _, _ => err GenericError
                  end
                | None => err NonExistingSymbol
              end
                
            | Assign w val  =>
              match eval w, eval val with
                | Value (Pointer t)  (Goodptr to off), Value vtype v =>                           
                  if vtype == t then
                    match mem_write to off (Value _ v ) s with
                      | (OK, ns) => ok_with ns
                      | (code, _) => err code
                    end
                  else err TypeMismatch
                | Value (Pointer t) (Goodptr to off) , Deallocated as v
                | Value (Pointer t) (Goodptr to off) , Garbage as v=>
                  match mem_write to off v s with
                      | (OK, ns) => ok_with ns
                      | (code, _) => err code
                  end
                | _, _ => err TypeMismatch
              end                      
          

            | Alloc loc type o_name sz =>
              let newps :=
                  ps_mod_mem (cons $ mk_block loc (next_block_id s) (sz* SizeOf type) nil type (fill_values sz (init_value type loc)) ) s in
              ok_with match o_name with
                | None => newps
                | Some name => add_var (declare_var name type (next_block_id s)) newps
              end

            | If cond _then _else =>
              match @is_value_true s $ eval cond with
                | Some true => ok_with $ ps_mod_cont (const (_then::stts)) s
                | Some false => ok_with $ ps_mod_cont (const (_else::stts)) s
                | None => err TypeMismatch
              end
            | While cond body =>
              match @is_value_true s $ eval cond with
                | Some true => ok_with $  ps_mod_cont (cons body) s
                | Some false => ok_with $ ps_mod_cont (const stts) s
                | None => err TypeMismatch
              end
            | CodeBlock sts => let bc := [:: Enter] ++ sts ++ [:: Leave] in
                               ok_with $ ps_mod_cont (const $ bc ++ stts) s
            | Debug => loop
            | Enter => ok_with $ ps_mod_syms (cons nil) s
            | Leave => match proc_symbols s with
                         | nil => ((GenericError, Some cur_statement), s)
                         | ctx::css => match apply_writes Deallocated s ctx with
                                         | (OK, state) => ok_with state
                                         | (code, s) => err code 
                                       end
                       end                        
            | BspSync => loop (* wait for sync = error code? *)
            | BspPushReg x sz =>
              match eval x, eval sz with
                | Value (Pointer t)  (Goodptr to off),  Value (Int S64) (Posz sz) =>
                  ok_with $ ps_mod_queue_push (cat [:: Push (AnyPtr t (Goodptr t to off)) sz]) s
                | _, _ => err TypeMismatch
              end
             
            | BspPopReg x sz => match eval x with
                | Value (Pointer t)  (Goodptr to off) =>
                  ok_with $ ps_mod_queue_pop (cat [:: Pop (AnyPtr t (Goodptr t to off)) ]) s
                | _ => err TypeMismatch
              end
             
            | BspGet pid_from source offset dest size =>
              match eval pid_from, eval source, eval offset, eval dest, eval size with
                | Value (Int S64) (Posz pid_from),
                  Value (Pointer t) ((Goodptr source_base source_offset) as source_ptr),
                  Value (Int S64) offset,
                  Value (Pointer u) (Goodptr dest_base dest_offset),
                  Value (Int S64) size =>
                  if t == u then
                    match offset, size with
                        | Posz offset, Posz size =>
                  ok_with $ ps_mod_queue_get ( cat [:: Get t pid_from source_ptr offset (Goodptr t dest_base dest_offset) size ] ) s
                        | _,_ => err PointerOutsideBlock
                                        end
                  else
                    err TypeMismatch
                | _,_, _,_,_ => err InvalidGet
              end
            
            | BspPut to_pid dest offset source size =>
              match eval to_pid, eval dest, eval offset, eval source, eval size with
                | Value (Int S64) (Posz to_pid),
                  Value (Pointer t_dest) (Goodptr dest_base dest_offset),
                  Value (Int S64) offset,
                  Value (Pointer t_source) (Goodptr source_base source_offset),
                  Value (Int S64) size =>
                  if t_dest == t_source then
                    match size, add_n_z dest_offset offset with
                      | Posz size, Some offset =>
                        match read_proc_memory ms pid source_base source_offset size with
                          | Some (read_type, vals) =>
                            if read_type == t_dest then
                              ok_with $ ps_mod_queue_put (cat [:: Put t_dest to_pid vals (Goodptr t_dest dest_base dest_offset) size]) s
                            else
                              err TypeMismatch
                          | None => err InvalidPut
                        end
                      | _,_ => err InvalidPut
                    end
                  else err TypeMismatch
                | _, _, _, _, _ => err InvalidPut
              end
          end
      end
  in
 (* let apply_gets (init:machine_state) (sss: seq proc_state) :machine_state :=
      let queues := map  sss (fun ps => (proc_id x, proc_queue_get x)) in
      let get_transformer (write_to_pid:nat) (g:get) (oldms:machine_state) : machine_state :=
          match g with
            | Get gt gpid ptr=>
          write_proc_memory oldms write_to_pid 
          in
      (fun procst oldmst => write_proc_memory oldst 
  in*)
  match ms with
    | MBad _ _ => ms
    | MGood pstates funcs =>
      let synchronize: machine_state->machine_state :=
          apply_gets \o apply_push_regs \o apply_pop_regs  in
      let stepped_procs := map interpret_proc pstates in
      let waiting_sync (r: pex_state) := match r with | ((OK, Some BspSync), _) => true | _ => false end in
      let running_good r := match r with | ((OK, _), _) => true | _ => false end in
      let good_next_state := MGood (map snd stepped_procs) funcs in
      if all waiting_sync stepped_procs then synchronize good_next_state  else
        if all running_good stepped_procs then good_next_state else MBad stepped_procs funcs
  end
.

Inductive istep : machine_state -> machine_state -> Prop :=
| istep_app s s' : interpreter_step s = s' -> istep s s'.



(*Definition init_state_for (s:statement) := Good (stat_ctx_mod stat_init (fun _=> [:: mk_fun 0 "main" nil s 0 ] ) id ) $
                                                mk_dyn_ctx  nil [:: s] .
                          *)                      


Fixpoint interpret (steps:nat) (state: machine_state) : machine_state :=
  match steps with | 0 => state
                | S steps => match state with
                               | MBad _ _ => state
                               | MGood _ _ => interpret steps $ interpreter_step state
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
