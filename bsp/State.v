From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Program.Basics.
Require Import UtilString.
Import intZmod.     
Require Import Syntax Common Types Memory.


       
Inductive get_query := Get t:  nat-> ptr t-> int -> ptr t -> nat -> get_query .
Inductive put_query := Put t: value -> ptr t -> nat -> put_query .

    Theorem put_query_eq_dec: eq_dec put_query.
      rewrite /eq_dec.
      move=> x y; case x; case y.
      move=> t v p n t0 v0 p0 n0.
      move: (ctype_eq_dec t0 t) => [Heqt|Heqt];
        move: (value_eq_dec v0 v) => [Heqv|Heqv];
        move: (nat_eq_dec n0 n) => [Heqn|Heqn]; subst; try
      move: (ptr_eq_dec _ p0 p) => [Heqp|Heqp]; try by [right;case].
      subst; by left.
      right.
      case.
      move=> H.
      by depcomp H.
    Qed.
    Definition put_query_eqP := reflect_from_dec put_query_eq_dec.
    
    Canonical put_query_eqMixin := EqMixin put_query_eqP.
    Canonical put_query_eqType := EqType put_query put_query_eqMixin.

  

Inductive push_query := Push: anyptr -> nat -> push_query.
Inductive pop_query := Pop: anyptr -> pop_query.


Record proc_state := mk_proc_state {
                         proc_id : nat;
                         proc_symbols : seq (seq var_descr);
                         proc_queue_get: seq get_query;
                         proc_queue_put: seq ( seq put_query );
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
| MBad:  seq ((error_code * option statement) * proc_state) -> seq function -> machine_state
| MNeedSync: seq( seq (seq put_query) )-> seq proc_state -> seq function -> machine_state.

Definition ms_source s := match s with | MGood _ f | MBad  _  f | MNeedSync _ _ f => f end.
Definition ms_procs s := match s with | MGood p _ | MNeedSync _ p _ => p | MBad  p _ => map snd p end.

Definition proc_state_empty:= @nil (seq var_descr).


Definition get_var (ps:proc_state) (name:string) : option var_descr :=
  option_find (fun p: var_descr => var_name p == name) (flatten (proc_symbols ps)).

Definition get_fun (s:machine_state) (name:string) : option function :=
         option_find (fun p: function => fun_name p == name) $ ms_source s.


Definition add_var (vd: var_descr) := ps_mod_syms
                                        (fun s=> match s with
                                                   | nil => cons [::vd] nil
                                                   | cons x xs => cons (cons vd x) xs
                                                 end).
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
Definition ErrorBlock := mk_block Data 0 0 nil ErrorType [::].


Definition mem_write  (bid:nat) (pos: nat) (val:value) (ps: proc_state): (error_code * proc_state) :=
  let m := proc_memory ps in
  let oldblock := option_nth m bid in
  match oldblock with
    | Some oldblock =>
      let err_code_write := can_write oldblock pos val in
      if err_code_write == OK then
        let newblockcnt := set_nth val (contents oldblock) pos val in
        let newblock := block_mod_cont (const newblockcnt) oldblock in
        let newmem := set_nth ErrorBlock m bid newblock in
        (OK, ps_mod_mem (const newmem) ps)
      else (err_code_write , ps)
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


