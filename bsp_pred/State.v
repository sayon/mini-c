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

   
Inductive put_query := Put t: value -> ptr t -> int -> put_query .

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

Inductive hpput_query := HpPutQuery: anyptr -> anyptr -> nat -> hpput_query.

    Theorem hpput_query_eq_dec : eq_dec hpput_query.
      move=> [src dst off] [src' dst' off'].
      eq_compi src src'.
      eq_compi dst dst'.
      eq_compi off off'.
    Qed.

    Definition hpput_query_eqP := reflect_from_dec hpput_query_eq_dec.
    
    Canonical hpput_query_eqMixin := EqMixin hpput_query_eqP.
    Canonical hpput_query_eqType := EqType hpput_query hpput_query_eqMixin.
    Canonical Structure hpput_query_dec_eq_mixin := mk_dec_eq hpput_query hpput_query_eq_dec.


Inductive hpget_query := HpGetQuery: anyptr -> anyptr -> nat -> hpget_query.

    Theorem hpget_query_eq_dec : eq_dec hpget_query.
      move=> [src dst off] [src' dst' off'].
      eq_compi src src'.
      eq_compi dst dst'.
      eq_compi off off'.
    Qed.

    Definition hpget_query_eqP := reflect_from_dec hpget_query_eq_dec.
    
    Canonical hpget_query_eqMixin := EqMixin hpget_query_eqP.
    Canonical hpget_query_eqType := EqType hpget_query hpget_query_eqMixin.
    Canonical Structure hpget_query_dec_eq_mixin := mk_dec_eq hpget_query hpget_query_eq_dec.

        
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
                         proc_queue_hpput: seq (seq hpput_query );
                         proc_queue_hpget: seq (seq hpget_query )
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
      eq_comp (seq_eq_dec (seq_eq_dec hpput_query_eq_dec)) p pp.
      eq_comp (seq_eq_dec (seq_eq_dec hpget_query_eq_dec)) l ll.
    Qed.

    Definition proc_state_eqP := reflect_from_dec proc_state_eq_dec.
    Canonical proc_state_eqMixin := EqMixin proc_state_eqP.
    Canonical proc_state_eqType := EqType proc_state proc_state_eqMixin.
    Canonical Structure proc_dec_eq_mixin := mk_dec_eq proc_state proc_state_eq_dec.

    
Inductive error_code := | OK | BadPointer | ModNonExistingBlock | PointerOutsideBlock| BadWriteLocation | TypeMismatch | WritingGarbage | NonExistingSymbol | GenericError | InvalidPopReg | InvalidPushReg | InvalidGet | InvalidPut | InvalidHpPut | InvalidHpGet.
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

    
Definition bad_state (pid: nat) (ec: error_code) (src: machine_state) : machine_state :=
  match src with
      | MBad _ _  => src
      | MGood procs fs => MBad (map (fun p => if pid == proc_id p then pair ec p else pair OK p) procs) fs
  end.

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

Definition proc_count (ms:machine_state) : nat := size $ ms_procs ms.

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
  in mem_mod_block bid block_trans ps.



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


Definition ms_mod_proc_option (pid:nat) (f: proc_state -> proc_state? ) (ec: error_code) (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _ => ms
    | MGood procs fs =>
      let bad :=  MBad ( map (fun p => pair (if proc_id p == pid then ec else OK) p) procs) fs in
      match option_nth procs pid with
        | Some proc => match f proc with
                         | Some newproc => ms_mod_proc pid (const newproc) ms
                         | None => bad
                       end
        | _ => bad
      end
  end.



Definition has_bsp_queues ps := match ps with
                                  | mk_proc_state _ _ nil nil nil nil _ _ _ nil nil => false
                                  | _ => true
                                end.

Definition ps_should_sync ps := match proc_conts ps with | BspSync :: _ => true  | _ => false end.
                                 

Definition ms_should_sync (ms:machine_state) :=
  all  ps_should_sync (ms_procs ms).


Definition not_empty {T} (s: seq T) := size s > 0.


Definition ps_should_pop ps : bool := (ps_should_sync ps) &&  (not_empty $ proc_queue_pop_reg ps) .


Definition ps_should_push ps : bool := (ps_should_sync ps) && (~~ ps_should_pop ps) && (not_empty $ proc_queue_push_reg ps ).


Definition ps_should_get ps : bool := (ps_should_sync ps)
                                     && (~~ ps_should_pop ps)
                                     && (~~ ps_should_push ps)
                                     && (not_empty $ proc_queue_get ps ).

Definition ps_should_put ps : bool := (ps_should_sync ps)
                                     && (~~ ps_should_pop ps)
                                     && (~~ ps_should_push ps)
                                     && (~~ ps_should_get ps)
                                     && (has not_empty $ proc_queue_put ps ).

Definition  remove_sync_statements (ms:machine_state) : machine_state :=
  ms_mod_proc_all (ps_mod_cont (drop 1)) ms.


Definition ps_advance := ps_mod_cont (drop 1).

Definition alloc_block (ps: proc_state) (b:block) : proc_state := ps_mod_mem (cat [:: b] ) ps.

Definition next_block_id : proc_state -> nat := size \o proc_memory.


Definition fill_block_raw (bid : nat) (v:value) :=
  ps_mod_mem (mod_at ErrorBlock bid (block_mod_cont (map (const v)))).

Definition mark_deallocated vds ps : proc_state :=
  let f (p : var_descr)  := match p with
                              | declare_var _ _ bid => fill_block_raw bid Deallocated
                            end in
  transformations ps $ map f vds.

Definition registered {T} (pt: ptr T) (pr:proc_state) : anyptr * nat ? :=
  match pt with
    | Goodptr b o =>
      let pred x y := match x with | AnyPtr _ (Goodptr bb oo) =>  (bb == b) && (oo == o) | _ => false end in
      option_find (uncurry pred) (proc_registered_locs pr)
    | _ => None
  end.
