Require Import String.
Require Import Arith.
Require Import Dec.
Set Implicit Arguments.

Record eqDec : Type := Pack {
  sort : Type;
  eq_dec :  forall x y: sort, {x = y} + {x <> y}
}.

Canonical nat_eqDec := @Pack nat Nat.eq_dec.

Canonical bool_eqDec : eqDec := @Pack bool Bool.bool_dec.

Notation "x =? y" := (@eq_dec _ x y). (* level 70 *)
Notation "x <>? y" := (Dec.not (@eq_dec _ x y)) (at level 70).

(* Compute (1 =? 2).
Compute (true =? false). *)

Definition prod_cmp (eqA eqB: eqDec) (x y: eqA.(sort) * eqB.(sort)) : {x = y} + {x <> y}.
  refine (map  _ (eqA.(eq_dec) (fst x) (fst y) && eqB.(eq_dec) (snd x) (snd y))).
  refine (
      let '(x1, x2) := x in
      let '(y1, y2) := y in
      conj (fun '(conj e1 e2) => _) (fun b => _)).
  - simpl in e1, e2. now rewrite e1, e2.
  - simpl.
    split.
    -- apply (f_equal fst b).
    -- apply (f_equal snd b).
Defined.

Canonical prod_eqDec (eqA eqB : eqDec) : eqDec :=
  @Pack (eqA.(sort) * eqB.(sort)) (@prod_cmp eqA eqB).

Fixpoint list_dec (eqA : eqDec) (x y: list eqA.(sort)) : dec (x = y).
  destruct x, y; [now left| now right| now right| ].
  destruct (s =? s0); [| right].
  - subst s0.
    destruct (list_dec eqA x y); [left | right].
    + now subst y.
    + now injection.
  - now injection.
Defined.

Canonical list_eqDec (eqA: eqDec) : eqDec :=
  @Pack (list eqA.(sort)) (list_dec eqA).

Definition option_dec (eqA : eqDec) (x y: option eqA.(sort)) : dec (x = y).
  refine (match x, y with
          | None, None => left _
          | Some a, Some b => if a =? b then left _
                              else right _
          | Some _, None => right _
          | None, Some _ => right _
          end); try discriminate.
  - now rewrite e.
  - now injection 1.
  - now auto.
Defined.

Canonical option_eqDec (eqA : eqDec) : eqDec :=
  @Pack (option eqA.(sort)) (option_dec eqA).

(*Require Import List.
Import ListNotations.
Check [1;2;3] =? [4;5]. *)

Inductive yesno :=
| Yes : yesno
| No  : yesno.

Definition yesno_dec (x y: yesno) : {x = y} + {x <> y}.
  destruct x, y.
  - now left.
  - now right.
  - now right.
  - now left.
Defined.

Canonical yesno_eqDec := @Pack yesno yesno_dec.
