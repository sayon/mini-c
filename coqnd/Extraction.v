Require Import Ascii String.
From mathcomp.algebra Require Import ssrint.

Extract Inductive ascii => char
        [
          "(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
        ]
        "(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
        "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec =>  "(=)".

Extract Inductive nat => "int"
        [ "0" "(fun x -> x + 1)" ]
          "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Inductive int => "int"
                           [ "(fun x-> x)" "(fun x-> (0-x))" ]  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".


