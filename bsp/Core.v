From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Program.
Require Import Program.
Require Import UtilString.
Import intZmod.    
Require Import Common Syntax Types State Memory TestUtils.


Fixpoint type_solver {ps:proc_state}  (e: expr) : ctype:=
  let slv := @type_solver ps  in
  match e with
    | Lit x => type_of_val x
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

Definition div_sgn x y := match x,y with
                            | Posz _, Posz _
                            | Negz _, Negz _ => Posz 1
                            | _,_ => Negz 1
                          end.
                                                            

Definition idiv x y := intRing.mulz (div_sgn x y)
                                    match x,y with
                                      | Posz x, Posz y 
                                      | Negz x, Negz y
                                      | Posz x, Negz y
                                      | Negz x, Posz y => fst (div.edivn x y)
                                    end.

Definition num_value (num:numeric) : int->value :=
  match num with
    | S8 => ValueI8
    | U8 => ValueU8
    | S16 => ValueI16
    | U16 => ValueU16
    | S32 => ValueI32
    | U32 => ValueU32
    | S64 => ValueI64
    | U64 => ValueU64
  end.

Definition binop_interp (t:ctype) (op: binop) : int -> int -> value :=
  match t with
    | Int kind =>   let v := num_value kind  in
                   match op with
                   | Add => fun x y=> v $ addz x y
                   | Sub => fun x y=> v $ addz x (oppz y)
                   | Mul => fun x y=> v $ intRing.mulz x y
                   | Eq  => fun x y=> v $ Posz $ if x == y then 1 else 0
                   | Div => fun x y=> v $ idiv x y
                   | _ => fun _ _ => Error
                 end
    | _ => fun _ _ => Error
  end.

Definition unop_interp (t:ctype) (op:unop) : int -> value  :=
  match t with
    | Int kind =>
      match op with
        | Neg => fun x => num_value kind $ oppz x
        | Not => fun x => num_value kind $ Posz $ if sgz x == 0 then 1 else 0
        | _ => fun _ => Error
      end
    | _ => fun _ => Error
  end.
  
Definition find_block (ps: proc_state) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ proc_memory ps.



Definition read_proc_memory (ms:machine_state) (pid:nat) (bid offset size:nat) : (ctype * seq value)? :=
  match ms with
    | MNeedSync _ pss fs 
    | MGood  pss fs  =>
      match option_nth pss pid with
        | None => None
        | Some ps => match option_nth (proc_memory ps) bid with
                       | Some bl => Some (el_type bl, slice offset size $ contents bl)
                       | None => None
                     end
      end
    | MBad _ _ => None
  end.


Definition dereference (ps: proc_state) (v:value) : value :=
  match v with
    | ValuePtr (AnyPtr pt (Goodptr i o)) =>       
      match option_nth (proc_memory ps) i with
        | Some (mk_block lo _i sz block_type contents) =>
          if block_type == pt then nth Error  contents o else Error
        | None => Error
      end
    | _ => Error
  end.
(*
Program Definition ValueFromLit (t: ctype) (l: coq_type t) : value :=
  match t with
    | Int S8 => ValueOfType S8 (cast l _ )
    | Int U8 => _
    | Int S16 => _
    | Int U16 => _
    | Int S32 => _
    | Int U32 => _
    | Int S64 => _
    | Int U64 => _
    | Pointer p => _
    | Struct ls => _
    | Bot => _
    | Unit => _
    | ErrorType => _
  end
.*)

Fixpoint iexpr (ms:machine_state) (pid:nat) (e:expr) : value :=
  match ms with
    | MBad  _ _ => Error
    | MNeedSync _ _ _ => Error
    | MGood procs _ => 
      match option_nth procs pid with
        | None => Error
        | Some ps =>
          let interp := iexpr ms pid in
          let type := @type_solver ps in
          let vars := flatten $ proc_symbols ps in
          let blocks := proc_memory ps in

          match e with
            | BspNProc => ValueI64 $ size procs
            | BspPid => ValueI64 $ pid
            | Lit v => v 
            | Var name => match get_var ps name  with
                            | Some (declare_var n t loc) =>
                              match find_block ps loc with
                                | Some b =>
                                  if el_type b == t
                                  then ValuePtr (AnyPtr t (Goodptr t loc 0))
                                  else Error
                                | None => Error
                              end
                            | None => Error
                          end
                            
            | Binop opcode l r =>
              match interp l, interp r with
                      | ValueI64 x, ValueI64 y 
                      | ValueI32 x, ValueI32 y
                      | ValueI16 x, ValueI16 y
                      | ValueI8  x, ValueI8  y
                      | ValueU64 x, ValueU64 y
                      | ValueU32 x, ValueU32 y
                      | ValueU16 x, ValueU16 y
                      | ValueU8  x, ValueU8  y => binop_interp (type l) opcode x y                                             
                      | _, _ => Error
              end

            | Unop Asterisk op => match interp op with
                                    | ValuePtr _ => dereference ps (interp op)
                                    |_ => Error
                                  end
            
            | Unop code op =>
              match interp op with
                | ValueI64 x
                | ValueI32 x
                | ValueI16 x
                | ValueI8  x
                | ValueU64 x
                | ValueU32 x
                | ValueU16 x
                | ValueU8  x => unop_interp (type e) code x
                |_ => Error
              end
          end
      end
  end.

Definition alloc_block (ps: proc_state) (b:block) : proc_state := ps_mod_mem (cat [:: b] ) ps.

Definition next_block_id : proc_state -> nat := size \o proc_memory.

Definition ex_block : block := mk_block Stack 0 64 Int64 (fill Garbage 8).

(* FIXME maybe we should implement type changes ? *)


Definition is_value_true {ps:proc_state} (v: value) : option bool:=
  match v with
    | ValueI64 x
    | ValueI32 x
    | ValueI16 x
    | ValueI8  x
    | ValueU64 x
    | ValueU32 x
    | ValueU16 x
    | ValueU8  x => Some $ sgz x != 0
    | ValuePtr (AnyPtr _ Nullptr) => Some false
    | ValuePtr (AnyPtr _ _) => Some true 
    | _ => None 
  end.  
 

Definition LitFromExpr (ms: machine_state) (pid:nat) (e:expr): expr :=
  Lit (iexpr ms pid e).
 
Definition prologue_arg (ms: machine_state) (pid:nat) (name:string) (t:ctype) (e:expr) : seq statement :=
  let l :=  LitFromExpr ms pid e in
  [:: Alloc Stack t (Some name) 1; Assign (Var name) l].


Definition prologue_args (ms:machine_state) (pid:nat) (f:function) (es: seq expr) : seq statement :=
  let vals :=  map (fun a => prologue_arg ms pid (fst (fst a)) (snd (fst a)) (snd a)) $ zip (args f) es in
  flatten vals.

Definition prologue_for (ms: machine_state) (pid:nat) (f:function) (argvals: seq expr) : seq statement  :=
  cons Enter $ prologue_args ms pid f argvals.

Definition epilogue_for (ms: machine_state) (pid:nat) (f:function) (argvals: seq expr) : seq statement  :=[:: Leave].

(* add tests *)

Definition apply_writes  (v:value) (s:proc_state) (vars: seq var_descr): proc_state ? :=
  let transforms_pairs := map (fun vd=> mem_write (location vd) 0 v ) vars in
  let good := all (fun x=> fst (x s) == OK) transforms_pairs in
  if good then Some  $ transformations s (  map (fun f => snd \o f) transforms_pairs ) else None.


Check assert_eq _ : apply_writes (ValueI64 34)
        (mk_proc_state 0 [:: [::]; [:: declare_var "x" Int64 0; declare_var "y" Int32 1] ] nil nil nil nil (**)
                       [::
                          mk_block Stack 0 1 Int64 [:: ValueI64 99] ;
                          mk_block Stack 1 1 Int32 [:: ValueI64 99] 
                       ]

                       nil nil) [:: declare_var "x" Int64 0] = Some
         {|
         proc_id := 0;
         proc_symbols := [[];
                         [{|
                          var_name := "x";
                          var_type := Int S64;
                          location := 0 |};
                         {|
                         var_name := "y";
                         var_type := Int S32;
                         location := 1 |}]]%list;
         proc_queue_get := []%list;
         proc_queue_put := []%list;
         proc_queue_pop_reg := []%list;
         proc_queue_push_reg := []%list;
         proc_memory := [{|
                         region := Stack;
                         block_id := 0;
                         block_size := 1;
                         el_type := Int S64;
                         contents := [ValueI64 34] |};
                        {|
                        region := Stack;
                        block_id := 1;
                        block_size := 1;
                        el_type := Int S32;
                        contents := [ValueI64 99] |}]%list;
         proc_conts := []%list;
         proc_registered_locs := []%list |}.


Definition init_value (t:ctype) (l: storage) : value :=
  match l with
    | Heap 
    | Stack
    | Text
    | ReadOnlyData  
    | Data => Garbage
  end.


Fixpoint write_proc_memory (ms:machine_state) (pid:nat) (bid offset: nat) (vals: seq value) : machine_state? :=
  match ms with
    | MNeedSync _ pss fs
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

Definition state_from_main (bspnproc:nat) (f:function) :machine_state :=
  let procs := map (fun pid=> mk_proc_state pid nil nil nil nil nil nil [:: body f ] nil) (iota 0 bspnproc) in
  MGood procs [::f].

Let dumb_state := let ms := state_from_main 2 (mk_fun 0 "" nil Skip) in
                  ms_mod_proc 1 (ps_mod_mem (const [:: mk_block Stack 0 10 Int64 (fill (ValueI64 44) 10)])) ms.

Compute write_proc_memory dumb_state 1 0 1 [:: ValueI64 1; ValueI64 2].
(*BUG*)

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

Definition has_to_pop (ms:machine_state) : bool :=
  has (fun x => size (proc_queue_pop_reg x) != 0) (ms_procs ms).

Definition apply_pop_regs (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _  => ms
    | MNeedSync _ _ _  => ms
    | MGood ps fs => if all (fun x=> size (proc_queue_pop_reg x) == 0) (ms_procs ms) then ms else
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

Definition vals_to_put (t:ctype) (startptr: ptr t) (offset:nat) (vvs: seq value) : seq put_query :=
  let trans p := match p with | (i, v) =>  Put t v startptr (offset + i) end in
  map trans $ enumerate vvs.


Definition add_put_queries
           (to:nat)
           (t:ctype)
           (startptr: ptr t)
           (offset:nat)
           (vvs:seq value): proc_state -> proc_state :=
  ps_mod_queue_put $ mod_at nil to $ cat (vals_to_put t startptr offset vvs).
 
    

Definition puts_for_pid (pid:nat) (ms:machine_state) :seq ( seq put_query ):=
  let allqueues := (map proc_queue_put (ms_procs ms)) in
  match seq_unsome $ map ((flip option_nth) pid) allqueues with
    | Some puts_into_pid =>  puts_into_pid 
    | None => nil
  end.

Definition proc_count (ms:machine_state) : nat := size $ ms_procs ms.


Definition has_puts_conflicts (ms:machine_state) : bool :=
  let proc_affected (i:nat) := map undup (puts_for_pid i ms) in
  let proc_good i := uniq $ flatten (proc_affected i) in
  ~~( all proc_good $ nat_seq (proc_count ms)).

Definition all_puts (ms:machine_state) : seq (seq (seq put_query) ):=
  map ((flip puts_for_pid) ms) (nat_seq (proc_count ms)).

Definition put_query_to_ms_transform (pid:nat) (p:put_query) (ms:machine_state): machine_state? :=
match p with
  | Put t v (Goodptr bid offset)   off => write_proc_memory ms pid bid offset [:: v]
  | _ => None
end.

Definition option_bind {T U} (f:T-> U?) (x:T?) :=
  match x with
    | Some x => f x
    | None => None
  end.
                                                      

Definition apply_puts_for_id (pid:nat) (ms:machine_state) : machine_state :=
  let  puts := flatten $ puts_for_pid pid ms in
  let transforms := map option_bind $ map (put_query_to_ms_transform pid) puts in
  match transformations (Some ms) transforms with
    | Some ms => ms
    | None => MBad ( map (pair (pair InvalidPut None))  (ms_procs ms)) (ms_source ms)
  end.
         
Definition clear_puts (ms:machine_state) : machine_state :=
  ms_mod_proc_all  (ps_mod_queue_put (const nil)) ms.

Definition apply_puts (ms:machine_state) : machine_state :=
  if has_puts_conflicts ms then MNeedSync (all_puts ms) (ms_procs (clear_puts ms)) (ms_source ms) else
  clear_puts $ transformations ms $ map apply_puts_for_id $ nat_seq $ size $ ms_procs ms.

Definition  remove_sync_statements (ms:machine_state) : machine_state :=
  ms_mod_proc_all (ps_mod_cont (drop 1)) ms.

Fixpoint interpreter_step (ms: machine_state) : machine_state :=
  let pex_state := prod (prod error_code  (statement?)) proc_state in
  let interpret_proc s : pex_state :=
      let pid := proc_id s in
      match proc_conts s with
        | nil => ((OK, None), s)
        | cur_statement::stts =>
          let loop := ((OK, Some cur_statement), s) in
          let s := ps_mod_cont (const stts) s  in
          let ok_with s := ((OK, Some cur_statement), s) in
          let err code := ((code, Some cur_statement), s) in
          let skip :=  ok_with s in
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
                         | ctx::css => ok_with (ps_mod_syms (const css) s)
                                               (*match apply_writes Deallocated s ctx with
                                         | (OK, state) => ok_with (ps_mod_syms (const css) state)
                                         | (code, s) => err code 
                                       end*)
                       end                        
            | BspSync => loop (* wait for sync = error code? *)
            | BspPushReg x sz =>
              match eval x, eval sz with
                | Value (Pointer t)  (Goodptr to off),  Value (Int S64) (Posz sz) =>
                  ok_with $ ps_mod_queue_push (cat [:: Push (AnyPtr t (Goodptr t to off)) sz]) s
                | _, _ => err TypeMismatch
              end
             
            | BspPopReg x => match eval x with
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
                              ok_with $
(add_put_queries to_pid t_dest (Goodptr t_dest dest_base dest_offset) offset  vals ) s
                                     
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
  match ms with
    | MNeedSync _ _ _ => ms
    | MBad _ _ => ms
    | MGood pstates funcs =>
      let synchronize: machine_state->machine_state := remove_sync_statements \o apply_puts \o
          apply_gets \o apply_push_regs \o apply_pop_regs  in
      let stepped_procs := map interpret_proc pstates in
      let waiting_sync (r: pex_state) := match r with | ((OK, Some BspSync), _) => true | _ => false end in
      let running_good r := match r with | ((OK, _), _) => true | _ => false end in
      let good_next_state := MGood (map snd stepped_procs) funcs in
      if all waiting_sync stepped_procs then
        synchronize good_next_state  else
        if all running_good stepped_procs then good_next_state else MBad stepped_procs funcs
  end
.

Definition option_nth3 {T:eqType} (x y z:nat) (s:seq ( seq ( seq T ) ) ) : T? :=
  match option_nth s x with
    | Some q => match option_nth q y with
                  | Some w => option_nth w z
                  |None => None
                end
    |None=>None
  end
.


Inductive istep : machine_state -> machine_state -> Prop :=
| istep_good s s' ps fs : s' = MGood ps fs -> interpreter_step s = s' -> istep s s'
| istep_sync_ok s s' ps fs: s = MNeedSync nil ps fs -> s' = MGood ps fs -> istep s s'
| istep_sync_conf s s' qp ps fs p newq x y z:
    s = MNeedSync qp ps fs ->
    option_nth3 x y z qp = Some p ->
    newq = mod_at nil x (mod_at nil y (skip_at z )) qp ->
    s' = MNeedSync newq ps fs ->
    istep s s'.


Definition state_from_main (bspnproc:nat) (f:function) :machine_state :=
  let procs := map (fun pid=> mk_proc_state pid nil nil nil nil nil nil [:: body f ] nil) (nat_seq bspnproc) in
  MGood procs [::f].

Definition LitI := Lit Int64 .
Definition LocVar t name := Alloc Stack t (Some name%string) 1.

Definition terminated (s:machine_state) : bool := all (fun x=>size x == 0) (map proc_conts (ms_procs s)).


Fixpoint interpret (steps:nat) (state: machine_state) : machine_state :=
  match steps with | 0 => state
                | S steps => match state with
                               | MNeedSync _ _ _ 
                               | MBad _ _ => state
                               | MGood _ _ => interpret steps $ interpreter_step state
                             end
  end.

Definition is_mgood (ms:machine_state) := match ms with
                                            | MGood _ _ => true
                                            | _ => false

                                          end.
Definition prop_is_mgood (ms:machine_state) := exists ps fs, ms = MGood ps fs.



Definition defined_and_terminates (s:machine_state) := exists n, terminated (interpret n s) /\ prop_is_mgood( interpret n s).


Definition testprog : function :=
  mk_fun 0 "main" nil $ CodeBlock [::
                                     LocVar Int64 "x" ;
                                     BspPushReg (Var "x") (LitI (SizeOf Int64))
                                                   ]

.



Theorem dnt_sample: defined_and_terminates (state_from_main 4 testprog).
  rewrite /defined_and_terminates.  
  exists 10.
  split. done.
  exists (ms_procs (interpret 10 (state_from_main 4 testprog))).  
  exists (ms_source (interpret 10 (state_from_main 4 testprog))). (*here reflexivity hangs!*)
  by cbv.
Qed.

Definition testprog2 : function :=
  mk_fun 0 "main" nil $ CodeBlock [::
                                     LocVar Int64 "x" ;
                                    BspPushReg (Var "x") (LitI (SizeOf Int64));
                                    BspSync ;
                                    BspPopReg (Var "x");
                                    BspSync
                                  ].


Theorem dnt_sample2: defined_and_terminates (state_from_main 4 testprog2).
  rewrite /defined_and_terminates.
  Compute (interpret 1 (state_from_main 4 testprog2)).
  Compute (interpret 2 (state_from_main 4 testprog2)).
  Compute (interpret 3 (state_from_main 4 testprog2)).
  Compute (interpret 4 (state_from_main 4 testprog2)).
  Compute (interpret 5 (state_from_main 4 testprog2)).
  Compute (interpret 6 (state_from_main 4 testprog2)).
  Compute apply_pop_regs (interpret 6 (state_from_main 4 testprog2)).

  Eval cbv in (interpret 7 (state_from_main 4 testprog2)).
           
  exists 100.
  split. cbv.
  done.
  exists (ms_procs (interpret 10 (state_from_main 4 testprog))).  
  exists (ms_source (interpret 10 (state_from_main 4 testprog))). (*here reflexivity hangs!*)
  by cbv.
Qed.



Definition current_instrs (s:machine_state) : seq statement :=
  flatten $ map (take 1) (map proc_conts (ms_procs s)).

Definition is_pop (s:statement) : bool := match s with | BspPopReg _ => true | _ => false end.

Definition good_for_pop (ps: proc_state) : bool :=
  match ohead $ proc_conts ps with
    | Some (BspPopReg x) => size (proc_registered_locs ps) != 0
    | _ => true
  end.

Definition good_for_pops ms :=
  all good_for_pop (ms_procs ms).

                         
Definition pops_ok s:= is_mgood s -> forall n, prop_is_mgood ( interpret n s ) /\ good_for_pops (interpret n s).

Theorem if_terminates_states_stays s (n:nat): defined_and_terminates s -> exists n, forall m, m >= n -> interpret n s = interpret m s .
  move => H.
  case H.
  move=> x H'.
  rewrite /defined_and_terminates in H.
  destruct H' as [H0 H1].
  destruct H as [y [H2 Hy]].
  
  

Admitted.
(*  move=> H.
  case H.
  move=> x H'.
  exists x.
  destruct H'.
  elim.
  simpl.
  by case x.
  move=> m H2 H3.
  rewrite H2.
  
  simpl.
  rewrite /terminated in H0.
  
  done.
  done.
  
  Search (_ <= 0).
  
  rewrite 
  done.
  move=> m H3 H4.*)
   
Theorem pops_ok_sample: pops_ok (state_from_main 2 testprog2).
  rewrite /pops_ok.
  move => H n.
  induction n =>//.
            destruct IHn.
  rewrite /is_mgood in H0.
  

  
  simpl.
  rewrite -H1.
  simpl.
  
  case IHn.
  
       
    by simpl.
  
  simpl.
  
  split.
  induction n.  
  compute.
  
  simpl.
  
  simpl.
  
  compute.
  
move=> Hg n.
  induction n. split. done.
  simpl.
  case s. move => * *.
  compute.
  
  simpl.
  
  rewrite good_for_pops.
  
  left.
  =>//=.
  simpl.
    by left.
   


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
