Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.algebra.ssrint.

Module Memory.

  
(* C language types *)
Inductive ctype :=
| Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 
| Pointer : ctype -> ctype
| Struct: seq ctype -> ctype.


Record ptr (t: ctype) := mk_ptr { block_id: nat; offset: nat; }.


(* Which memory region is storing the data *)
Inductive storage :=
| Heap
| Stack
| Data
| Text
| ReadOnlyData.

(* Which coq type acts as a holder for memory cell value *)
Fixpoint coq_type (t: ctype) : Set :=
  match t with
    | Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 => int
    | Pointer t => nat * nat
    | Struct ls => seq nat
  end .
    
Inductive value (t: ctype) : Set :=
| Value : coq_type(t) -> value t
| Garbage
| Deallocated.

    
Inductive Block := mk_block {
                       region: storage;
                       id: nat;
                       size: nat;
                       el_type: ctype;
                       contents: seq (value el_type)
                              }.


(* Examples *)

Definition block1 := mkblock 
Check mk_block Stack 0 1024 (Struct [:: Int8; Int32]) [:: (Va].

(* struct { char c; int t [4]; } mystruct *)

Definition example_block_char := mk_block Stack 0 1 Int8 [:: (Garbage Int8) ].
Definition example_block_int := mk_block Stack 1 16 Int32 [:: Garbage Int32 ; Garbage Int32;  Garbage Int32 ; Garbage Int32 ].
Definition example_mystruct := Value (Struct [:: Int8; Int32] ) [:: 0 ; 1].



End Memory.
