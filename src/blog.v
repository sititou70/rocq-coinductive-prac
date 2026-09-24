From Stdlib Require Import Lia.

(* ---------------- 
  不動点
---------------- *)

(* 普遍集合 U := 0 | 🍌 | S U （有限および無限） *)
CoInductive U: Type :=
  | U_O: U
  | U_Banana: U
  | U_S: U -> U
  .

(* ∞ = S ∞ *)
CoFixpoint inf: U := U_S inf.

(* match で包んでも値は同じ。
   match に置かれた cofix は1段展開されるので、inf や plus の定義を展開するのに使う *)
Lemma unfold_U:
  forall (u: U),
  u = match u with
        | U_O => U_O
        | U_Banana => U_Banana
        | U_S x' => U_S x'
      end.
Proof.
  intros u.
  destruct u; reflexivity.
Qed.

(* ∞ の定義より *)
Lemma inf_eq:
  inf = U_S inf.
Proof.
  apply (unfold_U inf).
Qed.

(* 生成関数 F(X) = {0} ∪ {S n | n ∈ X} *)
Inductive F (X: U -> Prop): U -> Prop :=
  | F_O: F X U_O
  | F_S: forall (n: U), X n -> F X (U_S n)
  .

Definition set1 (u: U): Prop :=
  False.
Definition set2 (u: U): Prop :=
  u = U_O.
Definition set3 (u: U): Prop :=
  u = U_Banana.
Inductive set4: U -> Prop :=
  | set4_O: set4 U_O
  | set4_S: forall u, set4 u -> set4 (U_S u)
  .
Inductive set5: U -> Prop :=
  | set5_O: set5 U_O
  | set5_Banana: set5 U_Banana
  | set5_S: forall u, set5 u -> set5 (U_S u)
  .
Definition set6 (u: U): Prop :=
  set4 u \/ u = inf.

Definition included (X1 X2: U -> Prop): Prop :=
  forall u: U, X1 u -> X2 u.
Theorem set1_subset:
  ~ included (F set1) set1 /\ included set1 (F set1).
Proof.
  unfold included.
  split.

  -
  intros Hcontra.
  specialize (Hcontra U_O).
  lapply Hcontra; clear Hcontra.

  --
  intros Hcontra.
  inversion Hcontra.

  --
  apply F_O.

  -
  intros u H.
  inversion H.
Qed.

Theorem set2_subset:
  ~ included (F set2) set2 /\ included set2 (F set2).
Proof.
  unfold included.
  split.

  -
  intros Hcontra.
  specialize (Hcontra (U_S U_O)).
  lapply Hcontra; clear Hcontra.

  --
  intros Hcontra.
  inversion Hcontra.

  --
  apply F_S.
  unfold set2.
  auto.

  -
  intros u H.
  inversion H; subst.
  apply F_O.
Qed.
Theorem set3_subset:
  ~ included (F set3) set3 /\ ~ included set3 (F set3).
Proof.
  unfold included.
  split.

  -
  intros Hcontra.
  specialize (Hcontra (U_S U_Banana)).
  lapply Hcontra; clear Hcontra.

  --
  intros Hcontra.
  inversion Hcontra.

  --
  apply F_S.
  unfold set3.
  auto.

  -
  intros Hcontra.
  specialize (Hcontra U_Banana).
  lapply Hcontra; clear Hcontra.

  --
  intros Hcontra.
  inversion Hcontra.

  --
  unfold set3.
  auto.
Qed.
Theorem set4_subset:
  included (F set4) set4 /\ included set4 (F set4).
Proof.
  unfold included.
  split.

  -
  intros u H.
  induction H.

  --
  apply set4_O.

  --
  apply set4_S.
  auto.

  -
  intros u H.
  induction H.

  --
  apply F_O.

  --
  apply F_S.
  auto.
Qed.
Theorem set5_subset:
  included (F set5) set5 /\ ~ included set5 (F set5).
Proof.
  unfold included.
  split.

  -
  intros u H.
  induction H.

  --
  apply set5_O.

  --
  apply set5_S.
  auto.

  -
  intros Hcontra.
  specialize (Hcontra U_Banana).
  lapply Hcontra; clear Hcontra.

  --
  intros Hcontra.
  inversion Hcontra.

  --
  apply set5_Banana.
Qed.
Theorem set6_subset:
  included (F set6) set6 /\ included set6 (F set6).
Proof.
  unfold included.
  unfold set6.
  split.

  -
  intros u H.
  induction H.

  --
  left.
  apply set4_O.

  --
  destruct H.

  ---
  left.
  apply set4_S.
  auto.

  ---
  right.
  subst.
  rewrite <- inf_eq.
  auto.

  -
  intros u H.
  destruct u.

  --
  apply F_O.

  --
  destruct H.

  ---
  inversion H.

  ---
  rewrite inf_eq in H.
  inversion H.

  --
  apply F_S.
  destruct H.

  ---
  left.
  inversion H.
  auto.

  ---
  right.
  rewrite inf_eq in H.
  inversion H.
  auto.
Qed.

(* ---------------- 
  帰納法の例
---------------- *)

(* U 上だと足し算や掛け算を自前で用意することになるので、この節は Rocq 標準の nat で議論する *)

(* 0 + 1 + ... + n *)
Fixpoint sum (n: nat): nat :=
  match n with
    | 0 => 0
    | S n' => sum n' + S n'
  end.

(* F を nat 上で考えたもの（μF = nat） *)
Inductive F_nat (X: nat -> Prop): nat -> Prop :=
  | F_nat_Zero: F_nat X 0
  | F_nat_S: forall n, X n -> F_nat X (S n)
  .

(* X = {n | 0 + 1 + ... + n = n(n + 1) / 2} *)
Definition X_ind (n: nat): Prop :=
  2 * sum n = n * (n + 1).

(* F(X) ⊆ X *)
Theorem FX_sub_X_ind:
  forall (n: nat),
  F_nat X_ind n -> X_ind n.
Proof.
  intros n H.
  destruct H as [| n IHn].
  - (* 0 ∈ X *)
    unfold X_ind.
    simpl.
    reflexivity.
  - (* S n ∈ X（帰納法の仮定 IHn: n ∈ X） *)
    unfold X_ind in *.
    simpl sum.
    nia.
Qed.

(* ---------------- 
  余帰納法の例1
---------------- *)

(* X = {∞} *)
Definition X_ex1 (u: U): Prop :=
  u = inf.

(* X ⊆ F(X) *)
Theorem X_ex1_sub_FX:
  forall (u: U),
  X_ex1 u -> F X_ex1 u.
Proof.
  intros u H.
  inversion H; subst.
  rewrite inf_eq.
  apply F_S.
  auto.
Qed.

(* ---------------- 
  余帰納法の例2
---------------- *)

(* 足し算 *)
CoFixpoint plus (u1 u2: U): U :=
  match u1 with
    | U_O => u2
    | U_Banana => u2
    | U_S u1' => U_S (plus u1' u2)
  end.

(* 足し算の定義より *)
Lemma plus_S:
  forall (u1 u2: U),
  plus (U_S u1) u2 = U_S (plus u1 u2).
Proof.
  intros u1 u2.
  rewrite (unfold_U (plus (U_S u1) u2)).
  reflexivity.
Qed.

(* 生成関数 G(X) = {(0, 0)} ∪ {(🍌, 🍌)} ∪ {(S n, S m) | (n, m) ∈ X} *)
Inductive G (X: U -> U -> Prop): U -> U -> Prop :=
  | G_O: G X U_O U_O
  | G_Banana: G X U_Banana U_Banana
  | G_S: forall u1 u2, X u1 u2 -> G X (U_S u1) (U_S u2)
  .

(* N ∪ {∞} = νF *)
CoInductive conat: U -> Prop :=
  | conat_Zero: conat U_O
  | conat_S: forall u, conat u -> conat (U_S u)
  .

(* X = {(∞ + n, ∞) | n ∈ N ∪ {∞}} *)
Definition X_ex2 (u1 u2: U): Prop :=
  exists n, conat n /\ u1 = plus inf n /\ u2 = inf.

(* X ⊆ G(X) *)
Theorem X_ex2_sub_GX:
  forall (u1 u2: U),
  X_ex2 u1 u2 -> G X_ex2 u1 u2.
Proof.
  intros u1 u2 [n [Hconatn [Hu1 Hu2]]].
  subst.
  (* (∞ + n, ∞) ∈ G(X) *)
  rewrite inf_eq.
  (* (S ∞ + n, S ∞) ∈ G(X) *)
  rewrite plus_S.
  (* (S (∞ + n), S ∞) ∈ G(X) *)
  apply G_S.
  (* (∞ + n, ∞) ∈ X *)
  exists n.
  split.

  -
  auto.

  -
  split; auto.
Qed.
