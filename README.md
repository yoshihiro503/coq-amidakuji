# Prove that the Amida lottery does not loop endlessly

I proved that any amidakuji lottery can lead to the answer.

## What is amidakuji here?

* There is a finite number of lots (vertical bars)
* There are a finite number of horizontal paths connecting the dots on the vertical bars.
* The horizontal path can go not only to the horizontal line, but also to a distant lottery or up itself.

What is not allowed

* There is no back to square one
* There is no connecting the same point to point
* No one-way line
* No paths like Mario blocks that collapse once you pass through them
There is no such thing as a fork in the road where you can choose which way to go

## Why did I prove it?

I thought I would prove it after the topic came up in PPL.

## Rough idea

### An idea to formally define the amidakuji lottery

Given a set of lots (vertical bars), I represented the data of a single amidakuji lottery by a set of horizontal roads.

For example, this amidakuji lottery is represented as three horizontal paths, A0--B2, A1--B0, and B1--C0. The endpoints are pairs of endpoints, and the indexes of the endpoints are the height of the points, one at a time from the top to the bottom, with the highest number being the highest. In each lottery, the function of going from point to point of the amidauji lottery is performed until it can no longer be applied, and the history of the points is the result of the lottery.

### Ideas for proving the termination

Color the segments of the vertical bars that you passed through. If you start from the top, you will never pass through the same vertical section again. This is because if you want to pass the same vertical section, the previous vertical section must be the same, but the first vertical section can never be passed again. Since the total amount of longitudinal segments is finite, it must stop.

We have proved the following two properties, proving that there is no infinite loop.

* The first longitudinal segment is only passed the first time.
* Once a longitudinal segment is passed, there is only one longitudinal segment passed immediately before it.

## Formal Definition of Amitabha Lottery by Rocq

Formalized using the theorem prover Rocq1 (formerly Coq).

```coq
(* Define a line joining the lottery as a pair of positions at both ends *)
Definition Bypath := (Pos * Pos)%type.

Definition AmidaP (bs: list Bypath): Prop :=
  (* same Pos never appears twice *)
  (let '(ps1, ps2) := split bs in NoDup (ps1 ++ ps2))
  (* each lottery has a max of clauses and all clauses are included *)
  /\ forall kuji i, Fin.lt i (vpos_of_nat height_ (vmax_ bs kuji)) ->
                PosIn (kuji, i) bs.

Definition Amida := {bs : list Bypath | AmidaP bs}.
```

Definition of scanning algorithm on Amida

```coq
(* one move of Pos *)
Definition next pos : option Pos := ...

(* function to apply the next function recursively until none, since the stoppage property is not obvious at this stage.
   (* upper limit of recurrence fuel is set since the stop nature is not clear at this stage *)
Fixpoint run fuel pos : list Pos :=
  match fuel with
  | O => []
  | S p => match next pos with
           | None => [pos]
           | Some pos' => pos :: run p pos'
           end
  end.
```

## Theorem

```coq
Definition init (kuji : Kuji) : Pos := (kuji, F1).

Theorem main: forall amida kuji,
  exists fuel, Finished amida (run amida fuel (init kuji)).
```

## Acknowledgments

The proof given here is just a formalization of the proof given orally by id:KeisukeNakano. Also, this topic was started by id:ku-ma-me and @Seasawher. We had @tanaka_akr discuss the formulation using Rocq(Coq) with us. I thank you all very much.
