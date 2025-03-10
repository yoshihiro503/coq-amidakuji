Require Import Sumbool Arith List FinFun.
Require Import Eq Common Fin Pos.
Import ListNotations.

(*前提:
- くじは有限本
- 上に登るとか、交差を許す
- くじを結ぶ線は有限本、有限長
- 線は枝分かれしない
*)
Parameter height_ : nat.
Definition Pos := Pos.t height_.
Definition Bypath := (Pos * Pos)%type.
Definition vmax_ (b: list Bypath) kuji : nat :=
  let '(ps1, ps2) := List.split b in
  List.length (List.filter_dec (fun pos => fst pos =? kuji) (ps1 ++ ps2)).

Inductive PosIn (pos: Pos) : list Bypath -> Prop :=
| InLeft  : forall other bs, PosIn pos ((pos, other) :: bs)
| InRight : forall other bs, PosIn pos ((other, pos) :: bs)
| InCons : forall bs p1 p2, PosIn pos bs -> PosIn pos ((p1, p2) :: bs).

Lemma PosIn_In pos body:
  PosIn pos body -> exists pos', In (pos, pos') body \/ In (pos', pos) body.
Proof.
  induction 1; try exists other; [left|right|].
  - now constructor.
  - now constructor.
  - destruct IHPosIn as [pos' [left | right]]; exists pos'.
    + now left; right.
    + now right; right.
Qed.


Definition AmidaP (bs: list Bypath): Prop :=
  (* 同じPosは2回現れない *)
  (let '(ps1, ps2) := split bs in NoDup (ps1 ++ ps2))
  (* 各くじで節のmaxがあって、全部の節が含まれる *)
  /\ forall kuji i, Fin.lt i (vpos_of_nat height_ (vmax_ bs kuji)) ->
                PosIn (kuji, i) bs.

Definition Amida := {bs : list Bypath | AmidaP bs}.

Parameter A B C: Kuji.
Parameter f0 f1 f2 f3 : vpos height_.

Definition example : Amida.
  exists [ ((A,f0), (B,f1)); ((B,f0), (B,f3)); ((B,f2), (C,f0))].
Admitted.

Section Amida.
Variable amida : Amida. (* あみだくじを一つ固定 *)
Notation body := (proj1_sig amida).

Definition vmax (kuji: Kuji): vpos height_ := vpos_of_nat _ (vmax_ body kuji).

Lemma in_split {A:Type} pairs (x y:A) xs ys:
  In (x, y) pairs -> split pairs = (xs, ys) -> In x xs /\ In y ys.
Proof.
  intros inp splitp.
  pose (in_split_l pairs (x, y) inp).
  pose (in_split_r pairs (x, y) inp).
  rewrite splitp in *. now split.
Qed.

Lemma amida_body_notIn_r p1 p2 l:
  In (p1, p2) body -> ~ In (l, p1) body.
Proof.
  destruct amida as [body [nodup ex]]. simpl.
  case_eq (split body). intros ps1 ps2 splitb. rewrite splitb in nodup.
  intros in1 in2.
  destruct (in_split _ _ _ ps1 ps2 in1 splitb) as [inp1 inp2].
  destruct (in_split _ _ _ ps1 ps2 in2 splitb) as [inl inp1'].
  now destruct (List.NoDup_app _ _ nodup inp1 inp1') .
Qed.

Lemma amida_body_notIn_l p1 p2 r:
  In (p1, p2) body -> ~ In (p2, r) body.
Proof.
  destruct amida as [body [nodup ex]]. simpl.
  case_eq (split body). intros ps1 ps2 splitb. rewrite splitb in nodup.
  intros in1 in2.
  destruct (in_split _ _ _ ps1 ps2 in1 splitb) as [inp1 inp2].
  destruct (in_split _ _ _ ps1 ps2 in2 splitb) as [inp2' inr].
  now destruct (List.NoDup_app _ _ nodup inp2' inp2) .
Qed.

Lemma amida_body_inj_r p1 p2 p2':
  In (p1, p2) body -> In (p1, p2') body -> p2 = p2'.
Proof.
  intros inp inp'.
  destruct (In_nth _ _ (Pos.err _, Pos.err _) inp) as [i [lti nthi]].
  destruct (In_nth _ _ (Pos.err _, Pos.err _) inp') as [j [ltj nthj]].
  destruct amida as [body [nodup ex]]. simpl in *.
  rewrite split_nth in nthi. injection nthi.
  rewrite split_nth in nthj. injection nthj.
  intros  nthj_p2' nthj_p1 nthi_p2 nthi_p1.
  rewrite <- split_length_l in lti.
  rewrite <- split_length_l in ltj.
  rewrite <- nthj_p2', <- nthi_p2. f_equal.
  case_eq (split body). intros ps1 ps2 splitb. rewrite splitb in *.
  destruct (in_split _ _ _ ps1 ps2 inp splitb) as [inp1 inp2].
  destruct (in_split _ _ _ ps1 ps2 inp' splitb) as [_ inp2'].
  apply NoDup_app_remove_r in nodup.
  replace ps1 with (fst (split body)) in nodup; [|now rewrite splitb].
  rewrite <- nthj_p1 in nthi_p1.
  now apply (NoDup_nth (fst (split body)) (Pos.err _)).
Qed.

Lemma amida_body_inj_l p1 p2 p1':
  In (p1, p2) body -> In (p1', p2) body -> p1 = p1'.
Proof.
  intros inp inp'.
  destruct (In_nth _ _ (Pos.err _, Pos.err _) inp) as [i [lti nthi]].
  destruct (In_nth _ _ (Pos.err _, Pos.err _) inp') as [j [ltj nthj]].
  destruct amida as [body [nodup ex]]. simpl in *.
  rewrite split_nth in nthi. injection nthi.
  rewrite split_nth in nthj. injection nthj.
  intros  nthj_p2 nthj_p1' nthi_p2 nthi_p1.
  rewrite <- split_length_r in lti.
  rewrite <- split_length_r in ltj.
  rewrite <- nthi_p1, <- nthj_p1'. f_equal.
  case_eq (split body). intros ps1 ps2 splitb. rewrite splitb in *.
  destruct (in_split _ _ _ ps1 ps2 inp splitb) as [inp1 inp2].
  destruct (in_split _ _ _ ps1 ps2 inp' splitb) as [inp1' _].
  apply NoDup_app_remove_l in nodup.
  replace ps2 with (snd (split body)) in nodup; [|now rewrite splitb].
  rewrite <- nthj_p2 in nthi_p2.
  now apply (NoDup_nth (snd (split body)) (Pos.err _)).
Qed.

Lemma amida_body_vmax kuji i:
  Fin.lt i (vmax kuji) -> PosIn (kuji, i) body.
Proof.
  unfold vmax. destruct amida as [body [nodup ex]]. simpl in *. now apply ex.
Qed.

Definition init (kuji : Kuji) : Pos := (kuji, F1).
Definition hnext_ (pos: Pos): option Pos (*全単射のはず*) :=
  List.find_map (fun '(l, r) =>
               if l =? pos then Some r
               else if r =? pos then Some l
                    else None) (proj1_sig amida).
Definition hnext pos := Option.value (Pos.err _) (hnext_ pos).

Lemma hnext_In_inv p p':
  hnext_ p = Some p' -> In (p, p') body \/ In (p', p) body.
Proof.
  intros hnextp.
  destruct (List.find_map_some _ _ hnextp) as [[x y] [inx Hxy]].
  destruct (x =? p).
  - injection Hxy as ey. subst. now left.
  - destruct (y =? p); [|discriminate].
    injection Hxy as ex. subst. now right.
Qed.


Lemma hnext_PosIn (pos: Pos) :
  PosIn pos body -> hnext_ pos <> None.
Proof.
  intros posIn hnextp. destruct (PosIn_In _ _ posIn) as [pos' [l|r]].
  -
    eapply List.find_map_none in hnextp; [|apply l]. simpl in hnextp.
    now destruct (prod_cmp Kuji_eqDec (vpos_eqDec height_) pos pos).
  -
    eapply List.find_map_none in hnextp; [|apply r]. simpl in hnextp.
    destruct (prod_cmp Kuji_eqDec (vpos_eqDec height_) pos' pos); [now auto|].
    now destruct (prod_cmp Kuji_eqDec (vpos_eqDec height_) pos pos).
Qed.

Lemma hnext_inj_aux p' p1 p2:
  hnext_ p1 = Some p' ->
  hnext_ p2 = Some p' -> p1 = p2.
Proof.
  intros hnext1 hnext2.
  destruct (hnext_In_inv _ _ hnext1).
  - (* In (p1, p') bodyのとき *)
    destruct (hnext_In_inv _ _ hnext2).
    + now apply amida_body_inj_l with p'.
    + now destruct (amida_body_notIn_l p1 p' p2 H).
  - (* In (p', p1) bodyのとき *)
    destruct (hnext_In_inv _ _ hnext2).
    + now destruct (amida_body_notIn_r p' p1 p2 H).
    + now apply amida_body_inj_r with p'.
Qed.

Lemma hnext_inj p1 p2:
  PosIn p1 body -> PosIn p2 body -> hnext p1 = hnext p2 -> p1 = p2.
Proof.
  unfold hnext. intros posIn1 posIn2.
  apply hnext_PosIn in posIn1, posIn2.
  case_eq (hnext_ p1); [|now auto]. intros p1' p1p1'. simpl.
  case_eq (hnext_ p2); [|now auto]. intros p2' p2p2'. simpl.
  intros e. subst p2'.
  now apply hnext_inj_aux with p1'.
Qed.

Definition vnext '(kuji, n) : option Pos :=
  if Fin.lt_dec n (vmax kuji) then
    Option.map (fun Sn => (kuji, Sn)) (Fin.succ_opt n)
  else None.

Axiom height_enough_big: forall kuji,
  (Fin.to_nat (vmax kuji)) < height_.

Lemma lt_height kuji i: Fin.lt i (vmax kuji) ->
                        S (Fin.to_nat i) < S height_.
Proof.
  intros lti.
  apply Fin.lt_to_nat in lti.
  rewrite <- Nat.succ_lt_mono.
  now eapply Nat.lt_trans, (height_enough_big kuji).
Qed.

Lemma vnext_inj p' p1 p2:
  vnext p1 = Some p' ->
  vnext p2 = Some p' -> p1 = p2.
Proof.
  destruct p1 as [k1 i], p2 as [k2 j]. destruct p' as [k' x].
  unfold vnext. simpl.
  destruct (Fin.lt_dec i (vmax k1)) as [lti|nlti]; [|discriminate].
  destruct (Fin.lt_dec j (vmax k2)) as [ltj|nltj]; [|discriminate].
  destruct (Fin.succ_opt_S i) as [si [succ_i to_nat_Si]];
    [ now apply lt_height with k1|].
  rewrite succ_i. simpl. injection 1 as ek1 esi. subst.
  destruct (Fin.succ_opt_S j) as [sj [succ_j to_nat_Sj]];
    [ now apply lt_height with k2|].
  rewrite succ_j. simpl. injection 1 as ek2 esj. subst. f_equal.
  now apply Fin.succ_opt_inj with x.
Qed.

Lemma vnext_not_init k p :
  ~ vnext p = Some (init k).
Proof.
  unfold vnext. destruct p as [k' i].
  destruct (Fin.lt_dec i (vmax k')); [|now auto].
  case_eq (Fin.succ_opt i); [|now auto]. simpl. intros Si eSi.
  unfold init. injection 1 as kk Si0.
  pose (Fin.succ_opt_to_nat _ eSi). now rewrite Si0 in e.
Qed.

Definition next pos :=
  match hnext_ pos with
  | None => None
  | Some pos' => vnext pos'
  end.

Lemma next_not_init k p :
  ~ next p = Some (init k).
Proof.
  unfold next. now destruct (hnext_ p); [apply vnext_not_init |].
Qed.


(* 変換は単射的である *)
Lemma next_inj pos' pos1 pos2:
  next pos1 = Some pos' ->
  next pos2 = Some pos' ->  pos1 = pos2.
Proof.
  unfold next.
  case_eq (hnext_ pos1); [|now auto]. intros pos1' hnext1 vnext1.
  case_eq (hnext_ pos2); [|now auto]. intros pos2' hnext2 vnext2.
  apply hnext_inj_aux with pos1'; [now apply hnext1|].
  rewrite hnext2. f_equal. now apply vnext_inj with pos'.
Qed.

Fixpoint run fuel pos : list Pos :=
  match fuel with
  | O => []
  | S p => match next pos with
           | None => [pos]
           | Some pos' => pos :: run p pos'
           end
  end.

Lemma PosFinite : Finite Pos.
Proof. apply t_Finite. Qed.


Lemma length_run' fuel: forall pos,
  length (run fuel pos) <= fuel.
Proof.
  induction fuel; [now auto|].
  intros pos. simpl. destruct (next pos).
  - simpl. apply le_n_S. now apply IHfuel.
  - simpl. now auto with arith.
Qed.

Lemma run_fuel_O pos: run 0 pos = [].
Proof. now auto. Qed.
Lemma run_fuel_S f pos: exists tl, run (S f) pos = pos :: tl.
Proof.
  simpl. now destruct (next pos); [exists (run f p)| exists []].
Qed.

Lemma run_cons' fuel tl pos hd : run fuel pos = hd :: tl -> run fuel pos = pos :: tl.
Proof.
  destruct fuel; [discriminate|].
  unfold run. destruct (next pos).
  - injection 1. fold run. intros. now subst.
  - injection 1. intros. now subst.
Qed.

Lemma run_cons fuel tl pos hd : run fuel pos = hd :: tl -> pos = hd.
Proof.
  destruct fuel; [discriminate|].
  unfold run. destruct (next pos); now injection 1.
Qed.

Lemma run_app xs ys fuel pos pos':
  run fuel pos = (xs ++ pos' :: ys) ->
  run (fuel - length xs) pos' = pos' :: ys.
Proof.
  revert fuel pos. induction xs; simpl; intros fuel pos.
  - rewrite Nat.sub_0_r.
    intro erun.
    replace pos' with pos; [now apply run_cons' with pos'|].
    now apply (run_cons fuel ys).
  - destruct fuel as [|fuel]; [discriminate|].
    simpl. destruct (next pos).
    + injection 1 as posa erun. now apply IHxs with p.
    + injection 1 as posa.
      now destruct (app_cons_not_nil _ _ _  H).
Qed.

Lemma run_nth fuel pos0 i pi:
  nth_error (run fuel pos0) i = Some pi ->
  exists ps, run fuel pos0 = ps ++ run (fuel - length ps) pi /\ length ps = i.
Proof.
  revert fuel pos0. induction i; intros fuel pos0.
  - simpl. case_eq (run fuel pos0); [discriminate|]. intros p' l.
    intros erun. injection 1 as epi. subst.
    exists [].  simpl. split; [|now auto].
    rewrite Nat.sub_0_r.
    rewrite <- (run_cons _ _ _ _ erun).
    now apply run_cons' in erun.
  - destruct fuel as[|fuel]; [discriminate|].
    simpl. destruct (next pos0); [|now rewrite nth_error_nil].
    intros nthi. destruct (IHi fuel p) as [ps [erun len]]; [assumption|].
    exists (pos0 :: ps). simpl. rewrite len. split; [| now auto].
    f_equal. now rewrite <- len, <- erun.
Qed.

Definition P kuji n pos := (*initから始まるpos列*)
  exists fuel, nth_error (run fuel (init kuji)) n = Some pos.

Lemma P0 kuji pos: P kuji 0 pos <-> pos = init kuji.
Proof.
  split.
  - destruct 1 as [fuel nth0]. simpl in nth0.
    destruct fuel as [|fuel]; [discriminate|].
    destruct (run_fuel_S fuel (init kuji)) as [tl erun].
    rewrite erun in nth0. now injection nth0.
  - intros ->. exists 1.  simpl. now destruct (next (init kuji)).
Qed.

Lemma P_S_aux fuel i pos0 p_i:
  nth_error (run fuel pos0) (S i) = Some p_i ->
  exists prev, nth_error (run fuel pos0) i = Some prev.
Proof.
  intros nthSi. assert (S i < length (run fuel pos0)).
  - apply nth_error_Some. now rewrite nthSi.
  - case_eq (nth_error (run fuel pos0) i).
    + intros prev nthi. now exists prev.
    + intros nthi. apply nth_error_None in nthi. apply Nat.lt_succ_l in H.
      now apply Nat.le_ngt in nthi.
Qed.

Lemma P_S kuji i pos: P kuji (S i) pos -> exists prev, P kuji i prev.
Proof.
  intros [fuel nthSi].
  destruct (P_S_aux fuel _ _ _ nthSi). now exists x, fuel.
Qed.

Lemma P_S_next fuel p0 p_i p_Si i:
  nth_error (run fuel p0) i = Some p_i ->
  nth_error (run fuel p0) (S i) = Some p_Si ->
  next p_i = Some p_Si.
Proof.
  intros nthi nthSi.
  destruct (nth_error_split _ _ nthi) as [left [right [erun leni]]].
  rewrite erun in nthi, nthSi.
  rewrite nth_error_app2 in nthi; [|now subst i].
  rewrite nth_error_app2 in nthSi; [| now subst i; auto with arith].
  apply run_app in erun. revert erun.
  case_eq (fuel - length left); [now auto|].  intros fuel' feq.
  rewrite Nat.sub_succ_l in nthSi; [|now subst i].
  rewrite nth_error_cons in nthSi.
  simpl. destruct (next p_i).
  - (* p_i の次があるとき: *)
    injection 1 as erun'. subst right. subst i.
    rewrite Nat.sub_diag in *.
    simpl in nthi, nthSi.
    revert nthSi. case_eq (run fuel' p); [now auto|]. intros t' tl.
    intros erun et. apply run_cons in erun. now subst.
  - (* p_i の次がないとき: nth の S i があることに矛盾 *)
    injection 1 as eright. subst right. now rewrite nth_error_nil in nthSi.
Qed.


Lemma P_S' kuji i pos:
  P kuji (S i) pos -> exists prev, P kuji i prev /\ next prev = Some pos.
Proof.
  intros [fuel nthSi]. destruct (P_S_aux fuel _ _ _ nthSi). exists x. split.
  - now exists fuel.
  - now apply P_S_next with fuel (init kuji) i.
Qed.

Lemma nP_S_init kuji i: ~P kuji (S i) (init kuji).
Proof.
  intros PSi. destruct (P_S' _ _ _ PSi) as [prev [Pi nextp]].
  now elim (next_not_init _ _ nextp).
Qed.


Lemma unique_path_aux x kuji i j : P kuji i x -> P kuji j x -> i = j.
Proof.
  revert x j. induction i; intros x j Pi Pj.
  - destruct j; [now auto|].
    rewrite P0 in Pi. rewrite Pi in Pj.
    now destruct (nP_S_init _ _ Pj).
  - destruct j.
    + rewrite P0 in Pj. rewrite Pj in Pi. now destruct (nP_S_init _ _ Pi).
    + apply P_S' in Pi, Pj. destruct Pi as [previ [Pprevi nexti]].
      destruct Pj as [prevj [Pprevj nextj]].
      rewrite (next_inj  x prevj previ) in Pprevj; try assumption.
      now rewrite (IHi previ j).
Qed.

Lemma unique_path fuel x kuji i j :
    nth_error (run fuel (init kuji)) i = Some x ->
    nth_error (run fuel (init kuji)) j = Some x ->
    i = j.
Proof.
  intros nthi nthj. now apply (unique_path_aux x kuji); exists fuel.
Qed.


Lemma NoDup_run : forall fuel kuji, NoDup (run fuel (init kuji)).
Proof.
  intros fuel kuji. apply NoDup_nth_error. intros i j len e.
  apply nth_error_Some in len.
  case_eq (nth_error (run fuel (init kuji)) i); [|now idtac].
  intros p some_i. rewrite some_i in e.
  now apply (unique_path fuel p kuji).
Qed.

Parameter err : Pos.

Definition Finished poss := exists pos, List.Last poss pos /\ next pos = None.
Definition Finished_dec poss: {Finished poss} + {~Finished poss}.
  refine (match poss with
          | [] => right _
          | pos :: ps => if next (last (pos :: ps) pos) =? None then left _
                        else right _
          end).
  - destruct 1 as [p [lp]]. now inversion lp.
  - set (last (pos :: ps) pos) as l.
    exists l. split; [|now auto].
    now erewrite (List.lastP pos l).
  - intros [posn [lp nxt]].
    rewrite List.lastP in lp; [|now auto].
    now rewrite lp in n.
Defined.

Lemma NotFinished_next fuel pos pos':
  ~Finished (run (1 + fuel) pos) ->
  next pos = Some pos' ->
  ~Finished (run fuel pos').
Proof.
  simpl. intros nfinS extb fin.
  rewrite extb in nfinS.
  destruct fin as [pos_n [lposn nextn]]. destruct nfinS.
  exists pos_n. split; [|assumption].
  now constructor.
Qed.

Lemma length_run fuel : forall pos,
  ~ Finished (run fuel pos) -> length (run fuel pos) = fuel.
Proof.
  induction fuel; [now idtac|].
  intros pos notFinished. simpl.
  case_eq (next pos). intros pos' nextS.
  - apply NotFinished_next with _ _ pos' in notFinished; [|now auto].
    simpl. now rewrite IHfuel.
  - intro nextN. elim notFinished. simpl. rewrite nextN. unfold Finished.
    exists pos. now split; [constructor|].
Qed.

Theorem main: forall kuji,
  exists fuel, Finished (run fuel (init kuji)).
Proof.
  intros kuji.
  destruct PosFinite as [all full].
  remember (length all) as Max.
  exists (1 + Max). destruct (Finished_dec (run (1 + Max) (init kuji))); [now idtac|].
  apply (length_run _ (init kuji)) in n. elim (Nat.nle_succ_diag_l Max).
  simpl Nat.add in n. rewrite <- n. rewrite HeqMax at 2.
  apply NoDup_incl_length; [apply NoDup_run|].
  now apply List.Full_incl.
Qed.

End Amida.
