From mathcomp.ssreflect Require Import ssreflect ssrnat seq eqtype ssrbool ssrfun. 
From mathcomp.algebra Require Import ssrint ssralg.
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Program.
Require Import Program.
Import intZmod.

Require Import Coq.Relations.Relation_Operators.

 
Require Import Common Syntax Types State Memory.


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
                            | _ => ErrorType
                          end
    | Unop _ o => slv o
    | BspNProc => Int64
    | BspPid => Int64
  end.


Definition binop_interp (t:ctype) (op: binop) x y : value :=
  match t with
    | Int kind =>let v := num_value kind  in
                   match op with
                   | Add => v $ addz x y
                   | Sub => v $ addz x (oppz y)
                   | Mul => v $ intRing.mulz x y
                   | Eq  => v $ Posz $ if x == y then 1 else 0
                   | Div =>  v $ idiv x y
                   | _ => Error
                 end
    | _ => Error
  end.

Definition unop_interp (t:ctype) (op:unop) x : value  :=
  match t with
    | Int kind =>
      match op with
        | Neg => num_value kind $ oppz x
        | Not => num_value kind $ Posz $ if sgz x == 0 then 1 else 0
        | _ => Error
      end
    | _ => Error
  end.
  
Definition find_block (ps: proc_state) (i: nat)  : option block :=
  option_find (fun b=> block_id b == i) $ proc_memory ps.

Definition option_subrange {T} (from sz: nat) (s: seq T) : (seq T ) ? :=
  if size s >= from + sz then Some (take sz (drop from s)) else None.

Definition read_proc_memory (ps:proc_state) (p: anyptr) (sz: nat) : (ctype * seq value) ? :=
  match p with
    | AnyPtr t (Goodptr b o) =>
      match remn sz (size_of t), option_nth (proc_memory ps) b with
        | 0, Some block => if remn o (size_of t) == 0
                        then option_map (pair t) $ option_subrange (divn o (size_of t)) (divn sz (size_of t)) (contents block)
                        else None
        | _, _ => None
      end
    | _ => None
  end.
  
Definition read_memory (ms:machine_state) (pid:nat) (pt: anyptr) (sz:nat) : (ctype * seq value)? :=
  match ms with
    | MGood  pss fs  =>
      match option_nth pss pid with
        | Some p => read_proc_memory p pt sz

        | None => None
      end
    | MBad _ _ => None
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
                      | ValuePtr p, v
                      | v, ValuePtr p => ptr_add_val p v                          
                      | _, _ => Error
              end

            | Unop Asterisk op => match interp op with
                                    | ValuePtr _  => dereference ps (interp op)
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


Definition ex_block : block := mk_block Stack 0 64 Int64 (fill Garbage 8).

(* FIXME maybe we should implement type changes ? *)


Definition is_value_true {ps:proc_state} (v: value) : bool ? :=
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


Definition init_value (t:ctype) (l: storage) : value :=
  match l with
    | Heap 
    | Stack
    | Text
    | ReadOnlyData  
    | Data => Garbage
  end.

Definition  write_proc_memory (bid offset: nat) (val: value) (ps: proc_state ) : proc_state ? :=
  match option_nth (proc_memory ps) bid with
    | Some b => if block_size b > offset  then
                Some $  ps_mod_mem (mod_at ErrorBlock bid (block_mod_cont (mod_at Error offset (const val) ))) ps
                else None
                       
    | None => None
  end.



Definition mult_write_proc_memory (bid offset: nat) (vals: seq value) (ps: proc_state ) : proc_state ? :=
  let mts:= map (uncurry (fun val off => write_proc_memory bid off val )) $ zip vals (iota offset (size vals)) in
                    mon_transformations ps mts.

Fixpoint write_memory (ms:machine_state) (pid:nat) (bid offset: nat) (vals: seq value) : machine_state :=
  let f p := if proc_id p == pid then mult_write_proc_memory bid offset vals p else Some p in
  match  seq_unsome $ map f $ ms_procs ms with
    | Some pss => match ms with
                    | MGood _ fs => MGood pss fs
                    | bad => bad end
    | None => MBad (map (fun p => pair (if proc_id p == pid then BadWriteLocation else OK) p ) (ms_procs ms)) (ms_source ms) 
  end.

Definition state_from_main (bspnproc:nat) (f:function) :machine_state :=
  let procs := map (fun pid=> mk_proc_state pid nil nil nil nil nil nil [:: body f ] nil nil nil) (iota 0 bspnproc) in
  MGood procs [::f].


Definition push_reg_to_p_transform (p:push_query): proc_state -> proc_state :=
  match p with
    | Push pt sz => ps_mod_reg_loc (cons (pt, sz))
  end.

Definition push_reg_to_ms_transform (frompid: nat) (p:push_query) :machine_state -> machine_state :=
  ms_mod_proc frompid ( push_reg_to_p_transform p ).

Definition apply_push_regs_procs ps : proc_state ? :=
  match (proc_queue_push_reg ps) with
    | (Push p sz) ::_ => Some $ ps_mod_reg_loc (cons (p,sz)) $ ps_mod_queue_push (drop 1) ps
    | nil => None
  end.


Definition apply_push_regs (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _ => ms
    |MGood procs fs =>
     match seq_unsome (map apply_push_regs_procs procs) with
       | Some procs => MGood procs fs
       | None => MBad (map (pair InvalidPushReg) procs) fs
     end
  end.
  
Definition slice_pop_requests (ms:machine_state) : (seq pop_query * machine_state) ? :=
  let queries := seq_unsome $ map ( ohead \o proc_queue_pop_reg ) $ ms_procs ms in
  let newms := ms_mod_proc_all (ps_mod_queue_pop (drop 1)) ms in
  option_map (fun x => (x, newms)) queries.

   

Definition pop_reg_position (q:pop_query) (proc:proc_state) :  nat ? :=
  match  q with | Pop pt => option_find_pos (fun rec => fst rec == pt) (proc_registered_locs proc) end
.




Definition proc_next_pop_from_pos ps :=
  match proc_queue_pop_reg ps with
    | (Pop (AnyPtr _ (Goodptr b o )))::qs =>
      option_find_pos (fun r => match r with | (AnyPtr _ (Goodptr bb oo), _) => (b == bb) && (o == oo) | _ => false end) (proc_registered_locs ps)
    | _ => None
  end.

Definition proc_pop_query ps : proc_state? :=
  match proc_next_pop_from_pos ps with
          | Some pos => Some $  ps_mod_queue_pop (skip_at 0) $ ps_mod_reg_loc (skip_at pos) ps
          | None => None
  end
.

Definition coherent_reg_positions ms :=
  match seq_unsome $  map proc_next_pop_from_pos (ms_procs ms) with
    | Some positions => constant positions
    | None => false
  end.

Definition apply_pop_regs_one (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _ => ms
    | MGood oldprocs fs =>
      let newprocs := map proc_pop_query oldprocs in
      match seq_unsome newprocs,  coherent_reg_positions ms with
        | Some procs, true => MGood procs fs
        | _, _ => MBad ( zip (map (fun p => match p with | Some _ => OK | _ => InvalidPopReg end) newprocs) oldprocs) fs
      end
  end.

 

Definition apply_pop_regs (ms:machine_state) : machine_state :=
  match ms with
    | MBad _ _  => ms
    | MGood ps fs => if all (fun x=> size (proc_queue_pop_reg x) == 0) (ms_procs ms) then ms else
      let bad := MBad ( map (pair InvalidPopReg) (ms_procs ms))  fs  in
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


Definition anyptr_same (x y: anyptr) :=
  match x, y with
    | AnyPtr _ (Goodptr xb xo), AnyPtr _ (Goodptr yb yo) => (xb == yb) && (xo == yo)
    | _, _ => false
  end.

 
Definition put_queries (dest_ps:proc_state) (to_reg_location_at: nat?) (offset: nat) (vvs: seq value) : seq put_query ? :=
  match to_reg_location_at with
    | Some to_reg_location_at=>
      match  option_nth (proc_registered_locs dest_ps) to_reg_location_at with
          | Some ( AnyPtr t (Goodptr b o), sz) =>
            if (o + muln (size vvs) (size_of t) ) > sz
            then None
            else
              Some $ map (uncurry (fun i v => Put _ v (Goodptr t b o) (addz offset (muln i (size_of t)) ) ) ) $ enumerate vvs
          | _ => None
      end
    | _ => None
  end.

Definition ms_add_put_queries_raw (dest_pid src_pid: nat) (queries: seq put_query) :machine_state -> machine_state :=
  ms_mod_proc dest_pid (ps_mod_queue_put (mod_at nil src_pid (cat queries))).

Definition ms_add_put_queries (dest_pid src_pid :nat) (src_regptr: anyptr) (offset: nat) (vals:seq value) (ms:machine_state) : machine_state :=
  match ms with
      | MGood procs fs =>
        match option_nth procs src_pid, option_nth procs dest_pid with
          | Some src_proc, Some dest_proc =>
            let oto_reg_location_at := option_find_pos (anyptr_same src_regptr \o fst) (proc_registered_locs src_proc) in
            match put_queries dest_proc oto_reg_location_at offset vals with
              | Some queries => ms_add_put_queries_raw dest_pid src_pid queries ms
              | _ => bad_state dest_pid GenericError ms
            end
          | _, _ => bad_state dest_pid InvalidPut ms
        end
      | _ => ms
  end.


         


Inductive ss_reduce (s s' : machine_state) : Prop :=
  (* OK *)
| ss_skip pid: forall procs source proc _procs proc' _conts,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Skip :: _conts ->
                    proc' = ps_advance proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)
| ss_assign pid: forall procs source proc _procs proc' _conts w val t to off v,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (Assign w val) :: _conts ->
                    iexpr s pid w = ValuePtr (AnyPtr t (Goodptr t to off)) ->
                    iexpr s pid val = v ->
                    (OK, proc') = write to off v (ps_advance proc) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_alloc_anon pid:  forall procs source proc _procs proc' _conts loc type sz newb,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Alloc loc type None sz :: _conts ->
                    newb = mk_block loc (next_block_id proc) (muln sz (size_of type)) type (fill (init_value type loc) sz) ->
                    proc' = ps_advance (alloc_block proc newb) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)
| ss_alloc pid:  forall procs source proc _procs proc' _conts loc type name sz b,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Alloc loc type (Some name) sz :: _conts ->
                    b = mk_block loc (next_block_id proc) (muln sz (size_of type)) type (fill (init_value type loc) sz) ->
                    proc' = ps_advance ( add_var
                              (declare_var name type (next_block_id proc))
                              (alloc_block proc b) ) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)
| ss_if_true pid: forall procs source proc _procs proc' _conts _cond _then _else,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (If _cond _then _else) :: _conts ->
                    @is_value_true proc (iexpr s pid _cond)= Some true ->
                    proc' = ps_mod_cont (const (_then::_conts)) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_if_false pid: forall procs source proc _procs proc' _conts _cond _then _else,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (If _cond _then _else) :: _conts ->
                    @is_value_true proc (iexpr s pid _cond)= Some false ->
                    proc' = ps_mod_cont (const (_else::_conts)) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_while_true pid: forall procs source proc _procs proc' _conts _cond _body,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (While _cond _body) :: _conts ->
                    @is_value_true proc (iexpr s pid _cond)= Some true ->
                    proc' = ps_mod_cont (cons _body) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_while_false pid: forall procs source proc _procs proc' _conts _cond _body,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (While _cond _body) :: _conts ->
                    @is_value_true proc (iexpr s pid _cond) = Some false ->
                    proc' = ps_mod_cont (const _conts) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'

(* OK *)                              
| ss_codeblock pid: forall procs source proc _procs proc' _conts stts,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = CodeBlock stts :: _conts ->
                    proc' = ps_mod_cont (const $ [:: Enter] ++ stts ++ [::Leave] ++ _conts) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_call pid: forall procs source proc _procs proc' _conts f fname fargs,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Call fname fargs :: _conts ->
                    Some f = get_fun s fname ->
                    proc' = ps_mod_cont (const $ prologue_for s pid f fargs ++ body f :: epilogue_for s pid f fargs ++ _conts) proc ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                              
| ss_enter pid: forall procs source proc _procs proc' _conts,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Enter :: _conts ->
                    proc' = ps_advance ( ps_mod_syms (cons nil) proc) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)                 
| ss_leave pid: forall procs source proc _procs proc' _conts ctx css,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = Leave :: _conts ->
                    proc_symbols proc = ctx::css ->
                    proc' = ps_mod_syms (const css) ( mark_deallocated ctx (ps_advance proc)) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)
| ss_bsp_push pid: forall procs source proc _procs proc' _conts x sz t to off isz,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = BspPushReg x sz :: _conts ->
                    iexpr s pid x = ValuePtr (AnyPtr t (Goodptr t to off)) ->
                    iexpr s pid sz = ValueI64 (Posz isz) ->
                    
                    proc' = ps_mod_queue_push (cons $ Push (AnyPtr t (Goodptr t to off)) isz) (ps_mod_cont (const _conts) proc) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
(* OK *)
| ss_bsp_pop pid: forall procs source proc _procs proc' _conts x  t to off,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = BspPopReg x :: _conts ->
                    iexpr s pid x = ValuePtr (AnyPtr t (Goodptr t to off)) ->
                    proc' = ps_mod_queue_pop (cat [:: Pop (AnyPtr t (Goodptr t to off)) ]) (ps_mod_cont (const _conts) proc) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'

(* OK *)
| ss_bsp_get pid: forall procs source proc _procs proc' _conts pid_from src offset dest sz npid_from t source_base source_offset ioffset  dest_base dest_offset nsz query,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = BspGet pid_from  src offset dest sz :: _conts ->
                    iexpr s pid pid_from = ValueI64 (Posz npid_from) ->
                    iexpr s pid src = ValuePtr (AnyPtr t ((Goodptr t source_base source_offset) ))->
                    iexpr s pid offset = ValueI64 ioffset ->
                    iexpr s pid dest = ValuePtr (AnyPtr t (Goodptr t dest_base dest_offset))  ->
                    iexpr s pid sz = ValueI64 (Posz nsz) ->
                    query = Get t npid_from ((Goodptr t source_base source_offset) ) ioffset (Goodptr t dest_base dest_offset) nsz ->
                    proc' = ps_mod_queue_get (cons query) (ps_mod_cont (const _conts) proc) ->
                    s' = MGood (insert_at pid proc' _procs) source ->
                    ss_reduce s s'
| ss_bsp_put pid: forall procs source proc _procs
                         eto_pid edest eoffset esource esize
                         to_pid
                         tdest odest bdest
                         offset
                         tsource bsource osource
                         sz
                         read_type vals
                         proc' _conts s'' ,
                    
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = BspPut eto_pid edest eoffset esource esize :: _conts ->

                    iexpr s pid eto_pid = ValueI64 (Posz to_pid) ->
                    iexpr s pid edest = ValuePtr (AnyPtr tdest (Goodptr tdest bdest odest)) ->
                    
                    iexpr s pid eoffset = ValueI64 (Posz offset) ->
                    iexpr s pid esource = ValuePtr (AnyPtr tsource (Goodptr tsource bsource osource )) ->
                    iexpr s pid esize = ValueI64 (Posz sz) ->

                    read_memory s pid (AnyPtr tsource (Goodptr tsource bsource osource )) sz = Some ( read_type, vals ) ->
                    
                    proc' = ps_advance proc ->
                    s'' = MGood (insert_at pid proc' _procs) source ->
                    s' = ms_add_put_queries to_pid pid  (AnyPtr tdest (Goodptr tdest bdest odest))  offset vals s'' ->
                    ss_reduce s s'


    
(* !! *) (*

                | BspPut to_pid dest offset source size => 
                  match eval to_pid, eval dest, eval offset, eval source, eval size with
                    | ValueI64 (Posz to_pid),
                      ValuePtr (AnyPtr _ destptr),
                      ValueI64 (Posz noffset),
                      ValuePtr (AnyPtr _ sourceptr),
                      ValueI64 (Posz size) =>
                      if is_goodptr sourceptr && is_goodptr destptr then
                        match read_memory ms pid (AnyPtr _ sourceptr) size with
                          | Some (read_type, vals)=>
                            ms_add_put_queries to_pid pid (AnyPtr _ destptr)  noffset vals ms

                          | _ => bad_with InvalidPut
                        end
                      else bad_with InvalidPut
                    | _, _, _, _, _ => bad_with InvalidPut
                  end

| ss_bsp_put pid: forall procs source proc _procs proc' _conts epid edest eoffset esource esize to_pid tdest dest_base dest_offset offset tsource source_base source_offset sourceptr destptr sz_bytes read_type _dstptr  ___procs ___fs s'' vals otherproc ,
                    s = MGood procs source ->
                    osplit_seq pid procs = (Some proc, _procs) ->
                    proc_conts proc = (BspPut epid edest eoffset esource esize) :: _conts ->
                    iexpr s pid epid = ValueI64 (Posz to_pid) ->
                    iexpr s pid edest = ValuePtr (AnyPtr tdest destptr) ->
                    iexpr s pid eoffset = ValueI64 (Posz offset) ->
                    iexpr s pid esource = ValuePtr (AnyPtr tsource sourceptr) ->
                    iexpr s pid esize = ValueI64 (Posz sz_bytes) ->
                    
                    destptr = Goodptr tdest dest_base dest_offset ->
                    sourceptr = Goodptr tsource source_base source_offset ->

                    
                    Some (read_type, vals) = read_memory s pid (AnyPtr tsource sourceptr) sz_bytes ->
                    ptr_add destptr offset = Some _dstptr ->
                    proc' = ps_advance proc ->
                    s'' = MGood (insert_at pid proc' _procs) source ->
                    Some otherproc = option_find (fun p=> proc_id p == to_pid) (ms_procs s'')  -> 
                    s' = ms_add_put_queries otherproc proc' (AnyPtr tdest destptr) offset vals  s''->
                    s' = MGood ___procs ___fs ->                       
                    ss_reduce s s'
*)

(* OK *)
| ss_sync_end: forall procs source,
                     s = MGood procs source ->
                     all ps_should_sync procs ->
                     all (negb \o has_bsp_queues) procs ->
                     s' = remove_sync_statements s ->
                     ss_reduce s s'
(* OK *)                               
| ss_sync_pop: forall procs source _procs ,
                 s = MGood procs source ->
                 all ps_should_sync procs ->
                 has ps_should_pop procs ->
                 s' = apply_pop_regs_one s ->
                 s' = MGood _procs source ->
                 ss_reduce s s'
(* OK *)                           
| ss_sync_push: forall procs source _procs ,
                 s = MGood procs source ->
                 all ps_should_sync procs ->
                 all (negb \o ps_should_pop) procs ->
                 has ps_should_push procs ->
                 s' = apply_push_regs s ->
                 s' = MGood _procs source ->
                 ss_reduce s s'
(* OK *)                           
| ss_sync_get pid: forall procs source proc _procs proc' _conts,
                 s = MGood procs source ->
                 all ps_should_sync procs ->
                 all (negb \o ps_should_pop) procs ->
                 all (negb \o ps_should_push) procs ->
                 osplit_seq pid procs = (Some proc, _procs) ->
                 ps_should_get proc ->
                 proc' = ps_mod_cont (const _conts) proc ->
                 s' = MGood (insert_at pid proc' _procs) source ->
                 ss_reduce s s'
                          
| ss_sync_put pid from_pid: forall procs source _procs proc' proc  q qs b newo o ioff t v regsize  __procs __fs,
                 s = MGood procs source ->
                 all ps_should_sync procs ->
                 all (negb \o ps_should_pop) procs ->
                 all (negb \o ps_should_push) procs ->
                 all (negb \o ps_should_get) procs ->
                 
                 osplit_seq pid procs = (Some proc, _procs) ->
                 ps_should_put proc ->
                 option_nth (proc_queue_put proc) from_pid =  Some (q :: qs) ->
                 q = Put t v (Goodptr t b o) ioff ->
                 @registered t (Goodptr t b o) proc = Some (AnyPtr t (Goodptr t b o), regsize)->
                 
                 proc' = ps_mod_queue_put (mod_at nil from_pid (const qs) ) proc ->
                 Some newo = add_n_z o ioff ->
                 regsize >= newo + size_of t ->
                 s' =  write_memory (MGood (insert_at pid proc' _procs) source ) pid b newo [:: v]   ->
                 s' = MGood __procs __fs ->
                                                                                                    
                 ss_reduce s s'

.

Definition bs_reduce := clos_refl_trans_1n _ ss_reduce.





(*Theorem test_skip: ss_reduce (MGood [:: ps ] _) (MGood [:: ] _).*)
Definition is_goodptr {T} (p:ptr T) := match p with | Goodptr _ _  => true | _ => false end.

Definition interpret_ss (ms:machine_state) (pid:nat) : machine_state :=
    match osplit_seq pid (ms_procs ms) with
      | (None, _ ) => MBad (map (pair OK) (ms_procs ms)) (ms_source ms)
      | (Some s, procs) =>
          match proc_conts s with
            | nil => ms
            | cur_statement::stts =>
              let ok_with s := MGood (insert_at pid s procs) (ms_source ms) in
              let loop := ok_with s in
              let bad_with ec := MBad (insert_at pid (ec, s) (map (pair OK) procs)) (ms_source ms) in
              let news := ps_advance s in
              let skip :=  ok_with news in
              let eval := iexpr ms pid in
              match cur_statement with
                | Skip => skip
                | Call fname fargs =>              
                  match get_fun ms fname with
                    | Some f =>
                      let prologue := prologue_for ms pid f fargs in
                      let epilogue := epilogue_for ms pid f fargs in
                      ok_with $ ps_mod_cont (cat (prologue ++ body f :: epilogue)) news
                    | None => bad_with NonExistingSymbol
                  end
                    
                | Assign w val  =>
                  match eval w, eval val with
                    | ValuePtr (AnyPtr t (Goodptr to off)), v =>                           
                        match write to off v (ps_advance s) with
                          | (OK, ns) => ok_with ns
                          | (code, _) => bad_with code
                        end
                    | _, _ => bad_with TypeMismatch
                  end                      
                    
                    
                | Alloc loc type o_name sz =>
                  let newps :=
                      ps_mod_mem (cons $ mk_block loc (next_block_id s) (sz * size_of type) type (fill (init_value type loc) sz) ) s in
                  (ok_with \o ps_advance) match o_name with
                            | None => newps
                            | Some name => add_var (declare_var name type (next_block_id s)) newps
                          end
                          
                | If cond _then _else =>
                  match @is_value_true s $ eval cond with
                    | Some true => ok_with $ ps_mod_cont (const (_then::stts)) s
                    | Some false => ok_with $ ps_mod_cont (const (_else::stts)) s
                    | None => bad_with TypeMismatch
                  end
                | While cond body =>
                  match @is_value_true s $ eval cond with
                    | Some true => ok_with $  ps_mod_cont (cons body) s
                    | Some false => ok_with news
                    | None => bad_with TypeMismatch
                  end
                | CodeBlock sts => let bc := [:: Enter] ++ sts ++ [:: Leave] in
                                   ok_with $ ps_mod_cont (cat bc) news
                | Debug => bad_with GenericError
                | Enter => ok_with $ ps_mod_syms (cons nil) news
                | Leave => match proc_symbols s with
                             | nil => bad_with GenericError
                             | ctx::css => ok_with $ ( mark_deallocated ctx)  (ps_mod_syms (const css) news)
                           (*match apply_writes Deallocated s ctx with
                                         | (OK, state) => ok_with (ps_mod_syms (const css) state)
                                         | (code, s) => err code 
                                       end*)
                           end                        
                | BspSync => loop (* wait for sync = error code? *)
                | BspPushReg x sz =>
                  match eval x, eval sz with
                    | ValuePtr (AnyPtr t  (Goodptr to off)),  ValueI64 (Posz sz) =>
                      ok_with $ ps_mod_queue_push (cat [:: Push (AnyPtr t (Goodptr t to off)) sz]) news
                    | _, _ => bad_with TypeMismatch
                  end
                    
                | BspPopReg x => match eval x with
                                   | ValuePtr (AnyPtr t (Goodptr to off)) =>
                                     ok_with $ ps_mod_queue_pop (cat [:: Pop (AnyPtr t (Goodptr t to off)) ]) news
                                   | _ => bad_with TypeMismatch
                                 end
                                   
                | BspGet pid_from source offset dest size =>
                  match eval pid_from, eval source, eval offset, eval dest, eval size with
                    | ValueI64 (Posz pid_from),
                      ValuePtr (AnyPtr t ((Goodptr source_base source_offset) as source_ptr)),
                      ValueI64 offset,
                      ValuePtr (AnyPtr u (Goodptr dest_base dest_offset)),
                      ValueI64 size =>
                      if t == u then
                        match offset, size with
                          | Posz offset, Posz size =>
                            ok_with $ ps_mod_queue_get ( cat [:: Get t pid_from source_ptr offset (Goodptr t dest_base dest_offset) size ] ) news
                          | _,_ => bad_with PointerOutsideBlock
                        end
                      else
                        bad_with TypeMismatch
                    | _,_, _,_,_ => bad_with InvalidGet
                  end
                    
                | BspPut to_pid dest offset source size => 
                  match eval to_pid, eval dest, eval offset, eval source, eval size with
                    | ValueI64 (Posz to_pid),
                      ValuePtr (AnyPtr _ destptr),
                      ValueI64 (Posz noffset),
                      ValuePtr (AnyPtr _ sourceptr),
                      ValueI64 (Posz size) =>
                      if is_goodptr sourceptr && is_goodptr destptr then
                        match read_memory ms pid (AnyPtr _ sourceptr) size with
                          | Some (read_type, vals)=> ms_mod_proc pid ps_advance $ 
                            ms_add_put_queries to_pid pid (AnyPtr _ destptr)  noffset vals ms

                          | _ => bad_with InvalidPut
                        end
                      else bad_with InvalidPut
                    | _, _, _, _, _ => bad_with InvalidPut
                  end
                    
                | BspHpPut to_pid dest offset source size => skip
                | BspHpGet pid_from source offset dest size => skip
                                  
              end
          end
      
    end.
Definition IntPtr b o:=  AnyPtr Int64 ( Goodptr _ b o).
Definition VIntPtr b o := ValuePtr $ IntPtr b o.

Definition LocVarBlock id t v := mk_block Stack id (size_of t) t [:: v].
Definition LocVarBlockInt64 id v := LocVarBlock id Int64 (ValueI64 v).


Definition test_put_state := MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        nil
                                        [:: nil ; nil ]
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        nil
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         [:: nil; nil]
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 4; LocVarBlockInt64 1 5; LocVarBlockInt64 2 6 ]
                                         [:: BspPut (Lit $ ValueI64 0)
                                            (Lit $ VIntPtr 1 0)
                                            (Lit $ ValueI64 0)
                                            (Lit $ VIntPtr 0 0)
                                            (Lit $ ValueI64 8) ]
                                        
                                         [:: ( IntPtr 1 0, 8 )]

                                         nil
                                         nil ] nil.     



