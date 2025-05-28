Set Implicit Arguments.

Definition dec P := {P} + {~P}.

Definition not P (x: dec P) : dec (~P).
  refine (match x with
  | left p => right _
  | right np => left _
  end); tauto.
Defined.

Definition and P Q (x : dec P) (y : dec Q) : dec (P /\ Q) :=
  match x with
  | left p =>
      match y with
      | left q => left (conj p q)
      | right nq => right (fun pq => nq (proj2 pq))
      end
  | right np => right (fun pq => np (proj1 pq))
  end.

Notation "p && q" := (and p q).

Definition or P Q (x : dec P) (y : dec Q) : dec (P \/ Q) :=
  match x with
  | left p => left (or_introl p)
  | right np =>
      match y with
      | left q => left (or_intror q)
      | right nq => right (or_ind np nq)
      end
  end.
Notation "p || q" := (or p q).

Definition impl P Q (x : dec P) (y : dec Q) : dec (P -> Q) :=
  match x with
  | left p =>
      match y with
      | left q => left (fun _ => q)
      | right nq => right (fun pq => nq (pq p))
      end
  | right np => left (fun p => False_rec _ (np p))
  end.

Notation "p -->? q" := (impl p q) (at level 40).

Definition map P P' (f : P <-> P') (x : dec P) : dec P' :=
  match x with
  | left p => left (proj1 f p)
  | right np => right (fun p' => np (proj2 f p'))
  end.
