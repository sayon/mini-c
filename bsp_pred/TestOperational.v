From mathcomp Require Import ssreflect seq ssrint ssrfun.  
From Coq.Strings Require Import Ascii String.
Require Import Coq.Program.Basics.  

Require Import Syntax Common State Types State Memory.  

 
Require Import Operational.    

Open Scope string.

Definition testfun instr := mk_fun 0 "main" nil instr.
Definition tproc pid  cont : proc_state := mk_proc_state pid nil nil nil nil nil nil cont nil nil nil.
Definition teststate instr := MGood  [:: tproc 0 nil ; tproc 1 [:: instr ] ]
                                     [:: testfun instr].
Definition empty2 instr := MGood [:: tproc 0 nil ; tproc 1 nil ] [:: testfun instr].

Theorem test_skip:  ss_reduce (teststate Skip) (empty2 Skip).
    by eapply ( ss_skip _ _ 1). Qed.

Import Relation_Operators.

Theorem ss_implies_bs s s': ss_reduce s s' -> bs_reduce s s'.
  move=> H.
  eapply rt1n_trans.
  eapply H.
  eapply rt1n_refl.
Qed.

Theorem test_skip_bs: bs_reduce (teststate Skip) (empty2 Skip).
  by eapply ss_implies_bs ; eapply (ss_skip _ _ 1).
Qed.


Definition reduce_interp s := ss_reduce s (interpret_ss s 1).

Theorem test_skip': reduce_interp (teststate Skip).
  by eapply (ss_skip _ _ 1).
Qed.  

Theorem test_alloc_anon: reduce_interp (teststate (Alloc Stack Int64 None 1)).
    by eapply (ss_alloc_anon _ _ 1).
Qed.

Theorem test_alloc: reduce_interp (teststate (Alloc Stack Int64 (Some "hey") 1)).
    by eapply (ss_alloc _ _ 1).
Qed.

Definition prog_if_true := If (Lit (ValueI64 (Posz 4))) (Alloc Stack Int64 None 1) (Alloc Stack Int64 None 2).

Theorem test_if_true: reduce_interp (teststate prog_if_true).
    by eapply (ss_if_true _ _ 1).
Qed.

Compute interpret_ss (teststate prog_if_true) 1.

Definition prog_if_false := If (Lit (ValueI8 (Posz 0))) (Alloc Stack Int64 None 1) (Alloc Stack Int64 None 2).

Theorem test_if_false: reduce_interp (teststate prog_if_false).
    by eapply (ss_if_false _ _ 1).
Qed.

Definition prog_while_true := While (Lit (ValueI64 (Posz 1))) (Alloc Stack Int64 None 0).
Definition prog_while_false := While (Lit (ValueI64 (Posz 0))) (Alloc Stack Int64 None 0).

Theorem test_while_true: reduce_interp (teststate prog_while_true).
    by eapply (ss_while_true _ _ 1).
Qed.


Theorem test_while_false: reduce_interp (teststate prog_while_false).
    by eapply (ss_while_false _ _ 1).
Qed.

Theorem test_codeblock: reduce_interp (teststate $ CodeBlock [:: Alloc Stack Int64 None 0 ] ).
    by eapply (ss_codeblock _ _ 1).
Qed.

Definition state_with_mem := interpret_ss (teststate $ Alloc Stack Int64 (Some "x") 1) 1.

Definition mix_statement ms pid stat := ms_mod_proc pid (ps_mod_cont (cons stat)) ms.

Compute  mix_statement state_with_mem 1 $ Assign (Lit (ValuePtr (AnyPtr Int64 (Goodptr Int64 0 0)))) (Lit (ValueI64 (Posz 11))).
Compute interpret_ss  ( mix_statement state_with_mem 1 $ Assign (Lit (ValuePtr (AnyPtr Int64 (Goodptr Int64 0 0)))) (Lit (ValueI64 (Posz 11)))) 1.

Theorem test_assign: reduce_interp (mix_statement state_with_mem 1 $ Assign (Lit (ValuePtr (AnyPtr Int64 (Goodptr Int64 0 0)))) (Lit (ValueI64 (Posz 11)))).
  by eapply (ss_assign _ _ 1).
Qed.

Theorem test_assign_type_conv: reduce_interp (mix_statement state_with_mem 1 $ Assign (Lit (ValuePtr (AnyPtr Int32 (Goodptr _ 0 0)))) (Lit (ValueI64 (Posz 11)))).
  by eapply (ss_assign _ _ 1).
Qed.

Definition simple_state pid vars mem cont := mk_proc_state pid vars nil nil nil nil mem cont nil nil nil.

Definition call_state := MGood [::
                                  simple_state 0 nil nil nil;
                                 simple_state 1 nil nil [:: Call "f" nil] 
                               ] [:: mk_fun 0 "main" nil Skip;
                                   mk_fun 1 "f" nil $ Alloc Stack Int64 (Some "x") 1 ].

Theorem test_call: reduce_interp call_state.
   by eapply (ss_call _ _ 1).
Qed.

Theorem test_enter: reduce_interp (teststate Enter).
 by eapply (ss_enter _ _ 1).
Qed.

Definition LocVarBlock id t v := mk_block Stack id (size_of t) t [:: v].
Definition LocVarBlockInt64 id v := LocVarBlock id Int64 (ValueI64 v).

Definition test_leave_state := MGood
                                 [::
                                    simple_state 0 nil nil nil;
                                   simple_state 1 [:: [:: declare_var "x" Int64 0 ] ; [:: declare_var "y" Int32 1 ] ]
                                                [:: LocVarBlockInt64 0 6; LocVarBlockInt64 1 4]
                                                    [:: Leave] 
                                 ] [:: ].
Compute interpret_ss test_leave_state 1.

Theorem test_leave: reduce_interp test_leave_state.
    by  eapply (ss_leave _ _ 1).
Qed.

Definition pushreg_state := MGood [::
                                     simple_state 0 nil nil nil;
                                    simple_state 1 nil [:: LocVarBlockInt64 0 6 ]
                                                 [::
                                                    BspPushReg
                                                    (Lit (ValuePtr (AnyPtr Int32 (Goodptr _ 0 0))))
                                                    (Lit (ValueI64 (Posz (size_of Int64)))) ]
                                  ]
                                  nil.

Theorem test_pushreg: reduce_interp pushreg_state.
    by eapply (ss_bsp_push _ _ 1).
Qed.

Compute interpret_ss pushreg_state 1.

Definition popreg_state := MGood [::
                                     simple_state 0 nil nil nil;
                                    simple_state 1 nil [:: LocVarBlockInt64 0 6 ]
                                                 [::
                                                    BspPopReg
                                                    (Lit (ValuePtr (AnyPtr Int32 (Goodptr _ 0 0)))) ]
                                  ]
                                  nil.

Theorem test_popreg: reduce_interp popreg_state.
    by eapply (ss_bsp_pop _ _ 1).
Qed.

Definition IntPtr b o:=  AnyPtr Int64 ( Goodptr _ b o).
Definition VIntPtr b o := ValuePtr $ IntPtr b o.

Theorem test_get: reduce_interp ( teststate $
                                             BspGet
                                             (Lit $ ValueI64 0)
                                             (Lit $ VIntPtr 0 0)
                                             (Lit $ ValueI64 0)
                                             (Lit $ VIntPtr 0 0)
                                             (Lit $ ValueI64 (Posz 0))).
    by  eapply (ss_bsp_get _ _ 1).
Qed.

Notation "{* b o : t }" := (AnyPtr t (Goodptr t b o)) (at level 55, no associativity).

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
                                            (Lit $ VIntPtr 2 0)
                                            (Lit $ ValueI64 0)
                                            (Lit $ VIntPtr 1 0)
                                            (Lit $ ValueI64 8) ]
                                        
                                         [:: ( IntPtr 2 0, 8 )]

                                         nil
                                         nil ] nil.     

Compute interpret_ss test_put_state 1.

Definition test_put: reduce_interp test_put_state.
  by eapply (ss_bsp_put _ _ 1).
Qed.

Theorem test_sync_end1 : ss_reduce (MGood [::
                                             simple_state 0 nil nil  [:: BspSync] ;
                                            simple_state 1 nil nil [:: BspSync]
                                          ]
                                          nil)
                                   (MGood [::
                                             simple_state 0 nil nil  nil ;
                                            simple_state 1 nil nil nil
                                          ]
                                          nil).
by  eapply (ss_sync_end ).
Qed.
(*
Definition test_sync_pop_state :=
  ms_mod_proc 1 (
                ps_mod_queue_pop (cons $ Pop $  IntPtr 0 0 )
c                                 \o ps_mod_reg_loc ( cons ( IntPtr 0 0 , 8) )
                                 \o ps_mod_cont (cons BspSync)
                                 \o ps_mod_mem (const 
              )
$  empty_state 2.*)

Definition test_sync_pop_state := MGood [::
                                              mk_proc_state
                                                0
                                                nil
                                                nil
                                                nil
                                                [:: Pop $ IntPtr 0 0]
                                                nil
                                                [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                                [:: BspSync]
                                                [:: ( IntPtr 0 0, 8 )]
                                                nil
                                                nil ;
                                             mk_proc_state
                                                1
                                                nil
                                                nil
                                                nil
                                                [:: Pop $ IntPtr 1 0]
                                                nil
                                                [:: LocVarBlockInt64 0 11; LocVarBlockInt64 1 4; LocVarBlockInt64 2 13 ]
                                                [:: BspSync]
                                                [:: ( IntPtr 1 0, 8 )]
                                                nil
                                                nil ] nil.

Theorem test_sync_pop : ss_reduce test_sync_pop_state  (apply_pop_regs_one test_sync_pop_state).
  eapply (ss_sync_pop _ _); try done.
Qed.

Definition test_sync_push_state := MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        nil
                                        nil
                                        nil
                                        [:: Push (IntPtr 0 0) (size_of Int64) ]
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        nil
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: Push (IntPtr 1 0) (size_of Int64) ]
                                         [:: LocVarBlockInt64 0 11; LocVarBlockInt64 1 4; LocVarBlockInt64 2 13 ]
                                         [:: BspSync]
                                         nil
                                         nil
                                         nil ] nil.

Definition test_sync_push_state' := MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        nil
                                        nil
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 11; LocVarBlockInt64 1 4; LocVarBlockInt64 2 13 ]
                                         [:: BspSync]
                                         [:: ( IntPtr 1 0, 8 )]

                                         nil
                                         nil ] nil.


Theorem test_sync_push: ss_reduce test_sync_push_state test_sync_push_state'.
    by eapply (ss_sync_push _ _). Qed.

Definition test_sync_get_state := MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        [:: Get _ 1 (Goodptr Int64 0 0) (Posz 0) (Goodptr Int64 0 0) 8 ]
                                        nil
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 4; LocVarBlockInt64 1 5; LocVarBlockInt64 2 6 ]
                                         [:: BspSync]
                                         [:: ( IntPtr 1 0, 8 )]

                                         nil
                                         nil ] nil.     
Definition test_sync_get_state':= MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        [:: Get _ 1 (Goodptr Int64 0 0) (Posz 0) (Goodptr Int64 0 0) 8 ]
                                        nil
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 4; LocVarBlockInt64 1 5; LocVarBlockInt64 2 6 ]
                                         [:: BspSync]
                                         [:: ( IntPtr 1 0, 8 ) ]

                                         nil
                                         nil ] nil.     


Theorem test_sync_get : ss_reduce  test_sync_get_state test_sync_get_state'.
    by eapply (ss_sync_get _ _ 0).
Qed.

Definition test_sync_put_state :=  MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        nil
                                        [:: nil; [:: Put  _ (ValueI64 6) (Goodptr Int64 0 0) 0 ]]
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 10; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 4; LocVarBlockInt64 1 5; LocVarBlockInt64 2 6 ]
                                         [:: BspSync]
                                         [:: ( IntPtr 1 0, 8 ) ]

                                         nil
                                         nil ] nil.
Definition test_sync_put_state' :=  MGood
                                     [::
                                        mk_proc_state
                                        0
                                        nil
                                        nil
                                        [:: nil; nil]
                                        nil
                                        nil
                                        [:: LocVarBlockInt64 0 6; LocVarBlockInt64 1 11]
                                        [:: BspSync]
                                        [:: ( IntPtr 0 0, 8 )]
                                        nil
                                        nil ;
                                       mk_proc_state
                                         1
                                         nil
                                         nil
                                         nil
                                         nil
                                         nil
                                         [:: LocVarBlockInt64 0 4; LocVarBlockInt64 1 5; LocVarBlockInt64 2 6 ]
                                         [:: BspSync]
                                         [:: ( IntPtr 1 0, 8 ) ]

                                         nil
                                         nil ] nil. 

Theorem test_sync_put : ss_reduce test_sync_put_state test_sync_put_state'.
by  eapply (ss_sync_put _ _ 0 1).
Qed.
