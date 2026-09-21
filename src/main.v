Inductive istream (A: Type): Type :=
  | iCons: A -> @istream A -> @istream A.

Lemma istream_empty:
  forall (A: Type) (s: istream A),
  False.
Proof.
  intros A s.
  induction s.
  auto.
Qed.

CoInductive stream (A: Type): Type :=
  | Cons: A -> stream A -> stream A.
Arguments Cons {A} _ _.

Definition hd {A: Type} (s: stream A): A :=
  match s with
    | Cons x _ => x
  end.
Definition tl {A: Type} (s: stream A): stream A :=
  match s with
    | Cons _ xs => xs
  end.

CoFixpoint const {A: Type} (a: A): stream A :=
  Cons a (const a).

CoFixpoint map {A B: Type} (f: A -> B) (s: stream A): stream B :=
  Cons (f (hd s)) (map f (tl s)).

Lemma obs1:
  forall (A: Type) (f: A -> A) (a: A),
  hd (map f (const a)) = f a.
Proof.
  intros A f a.
  auto.
Qed.

Lemma obs2:
  forall (A: Type) (f: A -> A) (a: A),
  hd (tl (map f (const a))) = f a.
Proof.
  intros A f a.
  auto.
Qed.

(* Lemma whole:
  forall (A: Type) (f: A -> A) (a: A),
  map f (const a) = const (f a).
Proof.
  intros A f a.
  simpl.
Abort. *)

Inductive iEqSt {A: Type} (s1 s2: stream A): Prop :=
  | ieqst:
    hd s1 = hd s2 ->
    iEqSt (tl s1) (tl s2) ->
    iEqSt s1 s2.
Lemma ieqst_empty:
  forall (A: Type) (s1 s2: stream A),
  iEqSt s1 s2 ->
  False.
Proof.
  intros A s1 s2 Hieqst.
  induction Hieqst.
  auto.
Qed.

CoInductive EqSt {A: Type} (s1 s2: stream A): Prop :=
  | eqst:
    hd s1 = hd s2 ->
    EqSt (tl s1) (tl s2) ->
    EqSt s1 s2.

Lemma EqSt_refl:
  forall (A: Type) (s: stream A),
  EqSt s s.
Proof.
  cofix CIH.
  intros A s.
  apply eqst.

  -
  auto.

  -
  apply CIH.
Qed.

(* Lemma bogus:
  forall (A: Type) (s1 s2: stream A),
  EqSt s1 s2.
Proof.
  cofix CIH.
  apply CIH.
Abort. *)

Lemma map_const:
  forall (A: Type) (f: A -> A) (a: A),
  EqSt (map f (const a)) (const (f a)).
Proof.
  cofix CIH.
  intros A f a.
  apply eqst.

  -
  auto.

  -
  apply CIH.
Qed.

Lemma EqSt_coind:
  forall (A: Type) (R: stream A -> stream A -> Prop),
  (forall (s1 s2: stream A), R s1 s2 -> (hd s1) = (hd s2)) ->
  (forall (s1 s2: stream A), R s1 s2 -> R (tl s1) (tl s2)) ->
  forall (s1 s2: stream A), R s1 s2 -> EqSt s1 s2.
Proof.
  intros A R Hhd Htl.
  cofix CIH.
  intros s1 s2 Hr.
  apply eqst.

  -
  apply Hhd.
  apply Hr.

  -
  apply CIH.
  apply Htl.
  apply Hr.
Qed.

Lemma map_const2:
  forall (A: Type) (f: A -> A) (a: A),
  EqSt (map f (const a)) (const (f a)).
Proof.
  intros A f a.
  apply EqSt_coind with (
    R :=
      fun s1 s2 =>
        s1 = map f (const a)
        /\
        s2 = const (f a)
  ).

  -
  intros s1 s2 H.
  destruct H; subst.
  auto.

  -
  intros s1 s2 H.
  destruct H; subst.
  auto.

  -
  auto.
Qed.

Lemma map_map:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (s: stream A),
  EqSt (map g (map f s)) (map (fun x => g (f x)) s).
Proof.
  intros A B C.
  cofix CIH.
  intros f g s.
  apply eqst.

  -
  auto.

  -
  apply CIH.
Qed.

Lemma map_map2:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (s: stream A),
  EqSt (map g (map f s)) (map (fun x => g (f x)) s).
Proof.
  intros A B C f g s.
  apply EqSt_coind with (
    R :=
      fun s1 s2 =>
        exists t,
          s1 = (map g (map f t))
          /\
          s2 = (map (fun x => g (f x)) t)
  ).

  -
  intros s1 s2 H.
  destruct H as [t H].
  destruct H; subst.
  auto.

  -
  intros s1 s2 H.
  destruct H as [t H].
  destruct H; subst.
  eexists.
  split.

  --
  simpl.
  auto.

  --
  simpl.
  auto.

  -
  exists s.
  auto.
Qed.

Fixpoint nth {A: Type} (n: nat) (s: stream A): A :=
  match n with
  | O => hd s
  | S n' => nth n' (tl s)
  end.

Lemma EqSt_nth:
  forall (A: Type) (s1 s2: stream A),
  EqSt s1 s2 ->
  (forall (n: nat), nth n s1 = nth n s2).
Proof.
  intros A s1 s2 Heqst n.
  generalize dependent s2.
  generalize dependent s1.
  induction n; intros s1 s2 Heqst.

  -
  simpl.
  inversion Heqst as [Hhd Htl].
  auto.

  -
  simpl.
  inversion Heqst as [Hhd Htl].
  apply IHn.
  auto.
Qed.

Lemma nth_EqSt:
  forall (A: Type) (s1 s2: stream A),
  (forall (n: nat), nth n s1 = nth n s2) ->
  EqSt s1 s2.
Proof.
  intros A.
  apply EqSt_coind with (
    R :=
      fun t1 t2 =>
        forall n, nth n t1 = nth n t2
  ).

  -
  intros s1 s2 Hntheq.
  specialize (Hntheq 0).
  simpl in Hntheq.
  auto.

  -
  intros s1 s2 Hntheq n.
  specialize (Hntheq (S n)).
  simpl in Hntheq.
  auto.
Qed.

Lemma EqSt_nth_iff:
  forall (A: Type) (s1 s2: stream A),
  (forall n, nth n s1 = nth n s2) <-> EqSt s1 s2.
Proof.
  intros A s1 s2.
  split.

  -
  apply nth_EqSt.

  -
  apply EqSt_nth.
Qed.
