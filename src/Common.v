Set Implicit Arguments.
Require Import Arith FinFun.

Definition app {A B: Type} (f: A -> B) x := f x.
Notation "x |> f" := (app f x) (at level 50).

Lemma prod_Finite (A B: Type):
    Finite A -> Finite B -> Finite (A * B).
Proof.
  intros [xs fullA] [ys fullB].
  exists (List.list_prod xs ys). intros [a b]. now apply List.in_prod.
Qed.

Module Option.
Definition t (A: Type) := option A.
Definition map {A B:Type} (f: A -> B) (o: t A) :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.
Definition isNone {A:Type} (o : t A): {o = None} + {o <> None}.
  now refine (match o with
              | None => left _ _
              | Some _ => right _ _
              end).
Defined.
Definition value {A: Type} default (o: option A) :=
  match o with
  | None => default
  | Some x => x
  end.

Lemma map_inj {A B : Type} (f: A -> B):
  (forall x y, f x = f y -> x = y) ->
  forall o1 o2, map f o1 = map f o2 -> o1 =o2.
Proof.
  intros finj [x|] [y|]; try now auto. simpl.
  injection 1 as fxy. now rewrite finj with x y.
Qed.
End Option.

Module Sumbool.
  Require Export Sumbool.

  Definition IsLeft {A B:Prop} (sb: {A}+{B}) := exists a, sb = left a.
End Sumbool.

Module List.
  Require Export List.
  Require Import FinFun Dec.

  Import ListNotations.
  Inductive Last {A :Type}: list A -> A -> Prop :=
  | LastUnit x: Last [x] x
  | LastCons y x xs : Last xs y -> Last (x :: xs) y.

  Lemma lastP {A: Type} (xs : list A) (d y: A):
    xs <> [] ->
    Last xs y <-> last xs d = y.
  Proof.
    induction xs; [now idtac|]. intros _. simpl. destruct xs.
    - simpl. now split; [inversion 1| intros ->; constructor].
    -rewrite <- IHxs; [|discriminate].
     now split; [inversion 1|constructor].
  Qed.

  Lemma Full_incl {A:Type} (xs all: list A) :
    FinFun.Full all -> incl xs all.
  Proof. intros full x xin. apply full. Qed.

  Fixpoint filter_dec {A:Type} {P : A -> Prop} (fdec: forall x, {P x}+{~P x}) (xs : list A) :=
    match xs with
    | [] => []
    | x :: xs => if fdec x then x :: filter_dec fdec xs
                else filter_dec fdec xs
    end.

  Fixpoint find_map {A B: Type} (f: A -> option B) (xs : list A) : option B :=
    match xs with
    | [] => None
    | x :: xs =>
        match f x with
        | None => find_map f xs
        | Some y => Some y
        end
    end.

  Lemma find_map_some [A B: Type] (f : A -> option B) (xs : list A) [y : B]:
    find_map f xs = Some y -> exists x, In x xs /\ f x = Some y.
  Proof.
    induction xs; only 1: discriminate. simpl. case_eq (f a).
    - intros b efa. injection 1 as eb. subst. exists a. now split; [left|].
    - intros _ fm. destruct IHxs as [x [inx fx]]; [assumption|].
      exists x. now split; [right|].
  Qed.

  Lemma find_map_none [A B: Type] (f : A -> option B) (xs : list A):
    find_map f xs = None -> forall x : A, In x xs -> f x = None.
  Proof.
    induction xs; only 1: now auto. simpl.
    case_eq (f a); only 1: discriminate. intros fa fxs x [ax|  inx].
    - now subst x.
    - now apply IHxs.
  Qed.


  Lemma NoDup_app {A:Type} (xs ys: list A) (x y : A) :
    NoDup (xs ++ ys) -> In x xs -> In y ys -> x <> y.
  Proof.
    induction xs; [now auto|]. simpl.
    rewrite NoDup_cons_iff. intros [nin nodup] [ax|inx ] iny.
    - intro xy. subst. elim nin. apply in_or_app. now right.
    - now apply IHxs.
  Qed.

  Definition max_nat (xs : list nat) :=
    fold_left (fun sum x => x + sum) xs 0.


End List.


Module Fin.
  Require Import Fin.
  Declare Scope fin_scope.
  Section Fin.
  Variable size : nat.
  Definition to_nat (x: Fin.t size): nat := proj1_sig (to_nat x).

  Definition le (x y: Fin.t size) :=
    (to_nat x) <= (to_nat y).
  Definition lt (x y: Fin.t size) :=
    (to_nat x) < (to_nat y).
  Notation "n <= m" := (le n m) : fin_scope.
  Notation "n < m" := (lt n m) : fin_scope.

  Definition succ_opt (x: Fin.t size) : option (Fin.t size).
    destruct (Vectors.Fin.to_nat x) as [nx ltx].
    destruct (lt_dec (S nx) size); [apply Some| apply None].
    (* S nx < size の場合は Some *)
    now apply (of_nat_lt l).
  Defined.

  Lemma to_nat_inj x y: to_nat x = to_nat y -> x = y.
  Proof. now apply to_nat_inj. Qed.

  Open Scope fin_scope.

  Lemma succ_opt_S (x: Fin.t size):
    (S (to_nat x) < size)%nat ->
    exists (Sx: Fin.t size), succ_opt x = Some Sx /\ to_nat Sx = S (to_nat x).
  Proof.
    unfold succ_opt. intros Sx_size. unfold to_nat in *.
    case_eq (Vectors.Fin.to_nat x). intros nx xsize ex.
    rewrite ex in Sx_size. simpl in Sx_size.
    destruct (lt_dec (S nx) size); [|now auto].
    remember (to_nat_of_nat l).
    exists (of_nat_lt l). split; [now auto|].
    now rewrite e.
  Qed.

  Lemma succ_opt_None (x: Fin.t size):
    (size <= S (to_nat x))%nat -> succ_opt x = None.
  Proof.
    unfold succ_opt. unfold to_nat. intros Sx_size.
    case_eq (Vectors.Fin.to_nat x). intros nx xsize ex.
    rewrite ex in Sx_size. simpl in Sx_size.
    destruct (lt_dec (S nx) size); [|now auto].
    now apply Nat.le_ngt in Sx_size.
  Qed.

  Lemma succ_opt_to_nat x sx:
    succ_opt x = Some sx -> S (to_nat x) = to_nat sx.
  Proof.
    destruct (lt_dec (S (to_nat x)) size).
    - destruct (succ_opt_S x l) as [y [xy ySx]].
      rewrite xy. injection 1 as e. now rewrite <- ySx, e.
    - now rewrite succ_opt_None; [| apply not_lt].
  Qed.

  Lemma succ_opt_inj z x y:
    succ_opt x = Some z ->
    succ_opt y = Some z -> x = y.
  Proof.
    intros esx esy.
    apply succ_opt_to_nat in esx, esy.
    apply to_nat_inj. rewrite <- esy in esx. now injection esx.
  Qed.

(*  Lemma neq_succ_opt_diag x : succ_opt x <> Some x. *)

  Definition le_dec (x y: Fin.t size) : {x <= y} + {~x <= y}.
    now destruct (le_dec (to_nat x) (to_nat y)); [left|right].
  Defined.

  Definition lt_dec (x y: Fin.t size) : {x < y} + {~x < y}.
    now destruct (lt_dec (to_nat x) (to_nat y)); [left|right].
  Defined.

  Lemma lt_le_incl n m: (n < m) -> (n <= m).
  Proof. now apply Nat.lt_le_incl. Qed.

  Lemma lt_to_nat x y: x < y -> (to_nat x < to_nat y)%nat.
  Proof. now auto. Qed.

  Lemma le_succ_l: forall Sn n m , succ_opt n = Some Sn ->
                               Sn <= m <-> n < m.
  Proof.
    intros. unfold le, lt.
    rewrite <- Nat.le_succ_l.
    now rewrite succ_opt_to_nat with _ Sn.
  Qed.

  End Fin.
End Fin.
