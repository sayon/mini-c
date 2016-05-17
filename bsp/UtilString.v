From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype.
From Coq.Strings Require Import Ascii String.

Scheme Equality for string.
Lemma ascii_beq_refl a: ascii_beq a a = true.
Proof. by case a; case; case; case; case; case; case; case; case; vm_compute. Qed.

Theorem ascii_eqP: Equality.axiom ascii_beq.
Proof.
  rewrite /Equality.axiom.
  move=> x y.
  case  (ascii_beq x y) eqn: H;  constructor.
  move: x y H.
  case; move=> q w e r t y u i.
  case; move=> q' w' e' r' t' y' u' i'.
  move: q q' w w' e e' r r' t t' y y' u u' i i'.
  do 8! [case; case => //= ].
  rewrite /not.
  move=> Heq. move: Heq H => ->. by rewrite ascii_beq_refl.
Qed.

Canonical ascii_eqMixin := EqMixin ascii_eqP.
Canonical ascii_eqType := EqType ascii ascii_eqMixin.

Lemma string_beq_refl x: string_beq x x = true.
Proof.
  elim x =>//. move=> a s H /=. by rewrite ascii_beq_refl.
Qed.

Lemma string_eqP: Equality.axiom string_beq.
Proof.
  rewrite /Equality.axiom.
  elim; first by case; constructor.
  move=> a s H []; first by constructor.
  move=> b t.
  simpl.
  case (ascii_beq a b) eqn: Heq; move /eqP in Heq.
  rewrite Heq.
  case (H t).
  -  by move=> ->; constructor.
  -  by move=> *; constructor; case.
  constructor. by case.
Qed.

Canonical string_eqMixin := EqMixin string_eqP.
Canonical string_eqType := EqType string string_eqMixin.
  
