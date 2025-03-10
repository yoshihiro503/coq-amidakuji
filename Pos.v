Require Import Sumbool Arith List FinFun.
Require Import Eq Common Fin.

Parameter Kuji : Set.
Axiom Kuji_Finite : Finite Kuji.
Axiom Kuji_eqdec : forall (x y: Kuji), {x = y}+{x <> y}.
Canonical Kuji_eqDec := @Pack Kuji Kuji_eqdec.

Section Pos.
Variable height_ : nat.
Notation height := (S height_).
Definition vpos := Fin.t height.

Definition vpos_eqdec : forall (x y: vpos), {x = y}+{x <> y} :=
  Fin.eq_dec.
Canonical vpos_eqDec := @Pack vpos vpos_eqdec.

Lemma vpos_Finite : Finite vpos.
Proof. now apply Fin_Finite. Qed.

Definition t := (Kuji * vpos)%type.

Lemma t_Finite : Finite t.
Proof.
  apply prod_Finite; [apply Kuji_Finite| apply vpos_Finite].
Qed.

Definition vpos_of_nat (n: nat): vpos.
  refine (if lt_dec n height then (@Fin.of_nat_lt n _ _)
          else (@Fin.of_nat_lt height_ _ _)).
  - exact l.
  - apply Nat.lt_succ_diag_r.
Defined.

Definition eq_dec := Eq.prod_eqDec Kuji_eqDec vpos_eqDec.
Parameter err : t.
End Pos.
