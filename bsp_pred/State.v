From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Program.Basics.
Import intZmod.          
Require Import Syntax Common Types Memory. 
 

       
Inductive get_query := Get t:  nat-> ptr t-> int -> ptr t -> nat -> get_query .
   Theorem get_query_eq_dec: eq_dec get_query.
     move=> [t_x pid_x src_x off_x dest_x size_x] [ t_y pid_y src_y off_y dest_y size_y].
     eq_compi t_x t_y.
     eq_compi pid_x pid_y.
     eq_compi off_x off_y.
     eq_compi size_x size_y.
     eq_comp (ptr_eq_dec t_y) src_x src_y.
     eq_comp (ptr_eq_dec t_y) dest_x dest_y.
   Qed.
    
    Definition get_query_eqP := reflect_from_dec get_query_eq_dec.
    
    Canonical get_query_eqMixin := EqMixin get_query_eqP.
    Canonical get_query_eqType := EqType get_query get_query_eqMixin.

   
Inductive put_query := Put t: value -> ptr t -> nat -> put_query .

   Theorem put_query_eq_dec: eq_dec put_query.
     rewrite /eq_dec.
     move=> [t_x v_x p_x o_x] [t_y v_y p_y o_y].
     eq_compi t_x t_y.
     eq_compi o_x o_y.
     eq_compi v_x v_y.
     eq_compi p_x p_y.
   Qed.
    
    Definition put_query_eqP := reflect_from_dec put_query_eq_dec.
    
    Canonical put_query_eqMixin := EqMixin put_query_eqP.
    Canonical put_query_eqType := EqType put_query put_query_eqMixin.
    Canonical Structure put_query_dec_eq_mixin := mk_dec_eq put_query put_query_eq_dec.

  

    Inductive push_query := Push: anyptr -> nat -> push_query.
    Theorem push_query_eq_dec: eq_dec push_query.
      move=> [p_x s_x] [p_y s_y].
      eq_compi p_x p_y.
      eq_compi s_x s_y.
    Qed.

    Definition push_query_eqP := reflect_from_dec push_query_eq_dec.
    
    Canonical push_query_eqMixin := EqMixin push_query_eqP.
    Canonical push_query_eqType := EqType push_query push_query_eqMixin.
    Canonical Structure push_query_dec_eq_mixin := mk_dec_eq push_query push_query_eq_dec.

    Inductive pop_query := Pop: anyptr -> pop_query.
    Theorem pop_query_eq_dec: eq_dec pop_query.
      move=> [px] [py]; eq_compi px py.
      Qed.
    Definition pop_query_eqP := reflect_from_dec pop_query_eq_dec.
    
    Canonical pop_query_eqMixin := EqMixin pop_query_eqP.
    Canonical pop_query_eqType := EqType pop_query pop_query_eqMixin.
    Canonical Structure pop_query_dec_eq_mixin := mk_dec_eq pop_query pop_query_eq_dec.

Record proc_state := mk_proc_state {
                         proc_id : nat;
                         proc_symbols : seq (seq var_descr);
                         proc_queue_get: seq get_query;
                         proc_queue_put: seq ( seq put_query );
                         proc_queue_pop_reg: seq pop_query;
                         proc_queue_push_reg: seq push_query;
                         proc_memory: seq block;
                         proc_conts: seq statement;
                         proc_registered_locs: seq ( anyptr * nat );
                         proc_queue_hpput: seq (seq (anyptr * value));
                         proc_queue_hpget: seq (seq (anyptr * value))
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
           mod_queue_hpput
           mod_queue_hpget           
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
    (mod_queue_hpput ps)
    (mod_queue_hpget ps)
.

Definition ps_mod
           mod_syms    
           mod_queue_get 
           mod_queue_put 
           mod_queue_pop 
           mod_queue_push
           mod_memory  
           mod_conts   
           mod_reg_locs
           mod_queue_hpput
           mod_queue_hpget           
: proc_state -> proc_state :=
  ps_mod_f
    (mod_syms \o proc_symbols)
    (mod_queue_get \o proc_queue_get)
    (mod_queue_put \o proc_queue_put)
    (mod_queue_pop \o proc_queue_pop_reg)
    (mod_queue_push \o proc_queue_push_reg)
    (mod_memory \o proc_memory)
    (mod_conts \o proc_conts)
    (mod_reg_locs \o proc_registered_locs)
    (mod_queue_hpput \o proc_queue_hpput)
    (mod_queue_hpget \o proc_queue_hpget)
.

Definition ps_mod_syms         f := ps_mod f  id id id id id id id id id.
Definition ps_mod_queue_get    f := ps_mod id f  id id id id id id id id.
Definition ps_mod_queue_put    f := ps_mod id id f  id id id id id id id.
Definition ps_mod_queue_pop    f := ps_mod id id id f  id id id id id id.
Definition ps_mod_queue_push   f := ps_mod id id id id f  id id id id id.
Definition ps_mod_mem          f := ps_mod id id id id id f  id id id id.
Definition ps_mod_cont         f := ps_mod id id id id id id f  id id id.
Definition ps_mod_reg_loc      f := ps_mod id id id id id id id f  id id.
Definition ps_mod_queue_hpput  f := ps_mod id id id id id id id id f  id.
Definition ps_mod_queue_hpget  f := ps_mod id id id id id id id id id f .

    Theorem proc_state_eq_dec: eq_dec proc_state.
      move=> [q w e r t y u i o p l] [qq ww ee rr tt yy uu ii oo pp ll].
      eq_compi q qq.
      eq_comp (seq_eq_dec (seq_eq_dec var_descr_eq_dec)) w ww.
      eq_comp (seq_eq_dec get_query_eq_dec) e ee.
      eq_comp (seq_eq_dec (seq_eq_dec put_query_eq_dec)) r rr.
      eq_comp (seq_eq_dec pop_query_eq_dec) t tt.
      eq_comp (seq_eq_dec push_query_eq_dec) y yy.
      eq_comp (seq_eq_dec (dec_from_reflect block_eqP)) u uu.
      eq_comp (seq_eq_dec statement_eq_dec) i ii.
      eq_comp (seq_eq_dec (pair_eq_dec anyptr_eq_dec nat_eq_dec)) o oo.
      eq_comp (seq_eq_dec (seq_eq_dec (pair_eq_dec  anyptr_eq_dec value_eq_dec))) p pp.
      eq_comp (seq_eq_dec (seq_eq_dec (pair_eq_dec  anyptr_eq_dec value_eq_dec))) l ll.
    Qed.

    Definition proc_state_eqP := reflect_from_dec proc_state_eq_dec.
    Canonical proc_state_eqMixin := EqMixin proc_state_eqP.
    Canonical proc_state_eqType := EqType proc_state proc_state_eqMixin.
    Canonical Structure proc_dec_eq_mixin := mk_dec_eq proc_state proc_state_eq_dec.

    
Inductive error_code := | OK | BadPointer | ModNonExistingBlock | PointerOutsideBlock| BadWriteLocation | TypeMismatch | WritingGarbage | NonExistingSymbol | GenericError | InvalidPopReg | InvalidPushReg | InvalidGet | InvalidPut.
    Scheme Equality for error_code.
    Canonical error_code_eqMixin := EqMixin (reflect_from_dec error_code_eq_dec).
    Canonical error_code_eqType := EqType error_code error_code_eqMixin.
    Canonical Structure error_code_dec_eq_mixin := mk_dec_eq error_code error_code_eq_dec.




Inductive machine_state :=
| MGood: seq proc_state -> seq function -> machine_state
| MBad:  seq (error_code * proc_state) -> seq function -> machine_state.

    Theorem machine_state_eq_dec: eq_dec machine_state.
      move => x y. case x; case y; try by [right;discriminate]; clear x y;
      move=> l f ll ff; eq_comp (seq_eq_dec function_eq_dec) ff f.
      by eq_comp (seq_eq_dec proc_state_eq_dec) ll l.
      by eq_comp (seq_eq_dec (pair_eq_dec error_code_eq_dec proc_state_eq_dec)) ll l.
    Qed.        
        
Definition ms_source s := match s with | MGood _ f | MBad  _  f => f end.
Definition ms_procs s := match s with | MGood p _ => p | MBad p _ => map snd p end.

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




Definition ms_mod_proc_all (f:proc_state->proc_state) (ms:machine_state) :=
  match ms with
    | MGood ps fs  => MGood (map f ps) fs
    | MBad _ _ =>  ms
  end.

Definition ms_mod_proc_all_or_fail (f:proc_state->proc_state ?) (ms:machine_state) :=

  match ms with
    | MGood ps fs  =>   let newprocs := seq_unsome (map f ps) in
                              option_map (fun p => MGood p fs) newprocs
    | MBad _ _ =>  None
  end.


Definition ms_for_proc {T} (ms:machine_state) (pid:nat) (f: proc_state -> T) : T? :=
  option_map f $  option_nth (ms_procs ms) pid.

  
Definition ms_mod_proc (pid:nat) (f:proc_state->proc_state) : machine_state->machine_state :=
  ms_mod_proc_all (fun p=> if proc_id p == pid then f p else p).

(*
Definition can_write (b:block) (i:nat) (v:value) : error_code :=
  match option_nth (contents b) i, v with
    | Some Garbage, val => if el_type b == type_of_val val then OK else TypeMismatch
    | Some Deallocated, _ => BadWriteLocation
    | Some _, Deallocated => WritingGarbage
    | Some _, Error => GenericError
    | Some _, Garbage => WritingGarbage
    | Some Error, _ => GenericError
    | None, _ => BadWriteLocation
    | Some vx, vy  => if (el_type b == type_of_val vy) && (el_type b == type_of_val vx) then OK else TypeMismatch
  end.


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
  end.*)

Definition regenerate_block (b:block) (newtype: ctype) : block :=
  let new_seq_len := fst $ div.edivn (block_size b) (size_of newtype) in
                             block_mod id id id (const newtype) (const (fill Garbage new_seq_len ) ) b.
                        

           
Definition write (bid:nat) (offset_bytes: nat) (new_val:value) (ps:proc_state) : error_code * proc_state :=
  match option_nth (proc_memory ps) bid with
    | Some old_block =>
      let blk := if (el_type old_block == type_of_val new_val) || (new_val == Deallocated) 
                 then old_block        
                 else regenerate_block old_block (type_of_val new_val) in
      let: (quot, rem) := div.edivn offset_bytes (size_of (type_of_val new_val)) in
      if (new_val == Garbage) then (WritingGarbage, ps) else
      if (rem == 0) && ( offset_bytes + size_of (type_of_val new_val ) <= (block_size blk) )
      then let newblk := block_mod_cont (mod_at Garbage quot (const new_val)) blk in
           (OK, ps_mod_mem (fun m => set_nth ErrorBlock m bid newblk) ps )
      else (BadWriteLocation, ps) 
    | None => (ModNonExistingBlock, ps)
  end
.

                                                            
Definition write_to (pid bid offset_bytes : nat) new_val ms :machine_state :=
  let procs := ms_procs ms in
  let oks:= map (pair OK) procs in
  match option_map (write bid offset_bytes new_val) (option_nth procs pid) with
    | Some (OK, p) => ms_mod_proc pid (const p) ms
    | None => MBad nil (ms_source ms)
    | Some (code, p) => MBad (mod_at (code, p) pid (map_fst (const code)) oks) (ms_source ms)
  end.




Definition mem_mod_block (bid:nat) (f:block->block) (ps:proc_state) : proc_state :=
  ps_mod_mem (mod_at ErrorBlock bid f) ps.

Definition mem_fill_block (bid:nat) (val:value) (ps: proc_state): proc_state :=
  let block_trans := block_mod id id id match val with
                         | Garbage 
                         | Deallocated 
                         | Error => id
                         | x =>  const $ type_of_val x 
                       end (map (const val))
  in
 
  mem_mod_block bid block_trans ps.


Definition divn x := fst \o div.edivn x.
Definition remn x := snd \o div.edivn x.

Definition dereference (ps: proc_state) (v:value) : value :=
  match v with
    | ValuePtr (AnyPtr pt (Goodptr i o)) =>
      match option_nth (proc_memory ps) i with
        | Some (mk_block lo _i sz block_type contents) =>
          if (block_type == pt) && ( o < sz ) && (remn o (size_of pt) == 0)
          then
            nth Garbage contents (divn o (size_of pt))
          else Error
        | None => Error
      end
    | _ => Error
  end.








(* TODO: handle byte sizes instead of elements' counts *)
