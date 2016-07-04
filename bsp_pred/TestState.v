From mathcomp Require Import ssrint seq. 
Require Import Common Types Memory State.

Local Definition sample_block s := mk_block Data 0 (s * size_of (Int S64)) Int64 $ fill (ValueI64 0) s.
Local Definition ps s : proc_state := mk_proc_state 0 nil nil nil nil nil [:: sample_block s ] nil nil nil nil .


Check Logic.eq_refl:  mem_fill_block 0 (ValueI32 11) ( ps 2 )= {|
                        proc_id := 0;
                        proc_symbols := [::];
                        proc_queue_get := [::];
                        proc_queue_put := [::];
                        proc_queue_pop_reg := [::];
                        proc_queue_push_reg := [::];
                        proc_memory := [:: {|
                                            region := Data;
                                            block_id := 0;
                                            block_size := 16;
                                            el_type := Int S32;
                                            contents := [:: ValueI32 11; ValueI32 11] |}];
                        proc_conts := [::];
                        proc_registered_locs := [::] |}.

Check Logic.eq_refl : mem_fill_block 0 (ValueI32 11) (ps 2) = {|
                        proc_id := 0;
                        proc_symbols := [::];
                        proc_queue_get := [::];
                        proc_queue_put := [::];
                        proc_queue_pop_reg := [::];
                        proc_queue_push_reg := [::];
                        proc_memory := [:: {|
                                            region := Data;
                                            block_id := 0;
                                            block_size := 16;
                                            el_type := Int S32;
                                            contents := [:: ValueI32 11; ValueI32 11] |}];
                        proc_conts := [::];
                        proc_registered_locs := [::] |}.

Check Logic.eq_refl : write  0 4 (ValueI32 66) (mem_fill_block 0 (ValueI32 11) (ps 2) ) = (OK, {|
                                                                                             proc_id := 0;
                                                                                             proc_symbols := [::];
                                                                                             proc_queue_get := [::];
                                                                                             proc_queue_put := [::];
                                                                                             proc_queue_pop_reg := [::];
                                                                                             proc_queue_push_reg := [::];
                                                                                             proc_memory := [:: {|
                                                                                                                 region := Data;
                                                                                                                 block_id := 0;
                                                                                                                 block_size := 16;
                                                                                                                 el_type := Int S32;
                                                                                                                 contents := [:: ValueI32 11; ValueI32 66] |}];
                                                                                             proc_conts := [::];
                                                                                             proc_registered_locs := [::] |} ).


Check Logic.eq_refl : write  0 6 (ValueI32 66) (mem_fill_block 0 (ValueI32 11) (ps 2) ) = (BadWriteLocation, {|
                                                                                             proc_id := 0;
                                                                                             proc_symbols := [::];
                                                                                             proc_queue_get := [::];
                                                                                             proc_queue_put := [::];
                                                                                             proc_queue_pop_reg := [::];
                                                                                             proc_queue_push_reg := [::];
                                                                                             proc_memory := [:: {|
                                                                                                                 region := Data;
                                                                                                                 block_id := 0;
                                                                                                                 block_size := 16;
                                                                                                                 el_type := Int S32;
                                                                                                                 contents := [:: ValueI32 11; ValueI32 11] |}];
                                                                                             proc_conts := [::];
                                                                                             proc_registered_locs := [::] |} ).

Check Logic.eq_refl : write  0 8 (ValueI32 66) (mem_fill_block 0 (ValueI32 11) (ps 2) ) = (OK, {|
                                                                                             proc_id := 0;
                                                                                             proc_symbols := [::];
                                                                                             proc_queue_get := [::];
                                                                                             proc_queue_put := [::];
                                                                                             proc_queue_pop_reg := [::];
                                                                                             proc_queue_push_reg := [::];
                                                                                             proc_memory := [:: {|
                                                                                                                 region := Data;
                                                                                                                 block_id := 0;
                                                                                                                 block_size := 16;
                                                                                                                 el_type := Int S32;
                                                                                                                 contents := [:: ValueI32 11; ValueI32 11; ValueI32 66] |}];
                                                                                             proc_conts := [::];
                                                                                             proc_registered_locs := [::] |} ).

Check Logic.eq_refl:  write   0 12 (ValueI32 66) (mem_fill_block 0 (ValueI32 11) (ps 2) )
                      = (OK,
                         {|
                           proc_id := 0;
                           proc_symbols := [::];
                           proc_queue_get := [::];
                           proc_queue_put := [::];
                           proc_queue_pop_reg := [::];
                           proc_queue_push_reg := [::];
                           proc_memory := [:: {|
                                               region := Data;
                                               block_id := 0;
                                               block_size := 16;
                                               el_type := Int S32;
                                               contents := [:: ValueI32 11; 
                                                             ValueI32 11; Garbage; 
                                                             ValueI32 66] |}];
                           proc_conts := [::];
                           proc_registered_locs := [::];
                           proc_queue_hpput := [::];
                           proc_queue_hpget := [::] |}).
Check Logic.eq_refl:  write   0 11 (ValueI32 66) (mem_fill_block 0 (ValueI32 11) (ps 2) )
                      = (BadWriteLocation, (mem_fill_block 0 (ValueI32 11) (ps 2) ) ).
