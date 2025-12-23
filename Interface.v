
Require Import Lia.
Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import MaxMinLib.MaxMin.
Require Import Coq.Logic.Classical_Prop.

Local Open Scope sets.

(* MaxMin in Z *)

Section Z.

Theorem Z_le_total: forall x y, {Z.le x y} + {Z.le y x}.
Proof. intros. destruct (Z_le_dec x y); [left | right]; lia. Qed.

#[export] Instance Zle_TotalOrder: TotalOrder Z.le := {
  le_refl := Z.le_refl;
  le_trans := Z.le_trans;
  le_antisym := Z.le_antisymm;
  le_total := Z_le_total;
}.

End Z.


(* MaxMin in Nat *)

Section Nat.

Theorem Nat_le_total: forall x y, {Nat.le x y} + {Nat.le y x}.
Proof. intros. destruct (le_ge_dec x y); [left | right]; auto. Qed. 

#[export] Instance NatLe_TotalOrder: TotalOrder Nat.le := {
  le_refl := Nat.le_refl;
  le_trans := Nat.le_trans;
  le_antisym := Nat.le_antisymm;
  le_total := Nat_le_total;
}.


(* 只有在nat(良序关系)上且谓词为最小值时，存在性引理才成立 *)

Theorem min_nonempty_exists {A: Type}: 
  forall (f: A -> nat) (P: A -> Prop),
    (exists a, P a) -> 
    exists b, min_value_of_subset Nat.le P f b.
Proof.
  intros f P [a0 Ha0].
  remember (f a0) as n eqn:Heqn.
  revert a0 Ha0 Heqn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros a0 Ha0 Heqn.
  destruct (classic (exists a', P a' /\ f a' < f a0)) as [Hsmaller | Hminimal].
  - destruct Hsmaller as [a' [Ha' Hlt]].
    assert (f a' < n) by lia.
    eapply (IH (f a')); eauto.
  - exists (f a0).
    exists a0; split; auto. 
    split; auto.
    intros a Ha.
    destruct (Nat.le_gt_cases (f a0) (f a)) as [Hle | Hgt].
    * exact Hle.
    * exfalso. apply Hminimal.
      exists a; split; auto.
Qed.

(* 索引并集性质: 最小值的并集的最小值 = 并集的最小值 *)

Theorem min_union_iff {A: Type}:
  forall (f: A -> nat) (P Q: A -> Prop),
    min_value_of_subset Nat.le (P ∪ Q) f == 
    min_value_of_subset Nat.le (min_value_of_subset Nat.le P f ∪ min_value_of_subset Nat.le Q f) id.
Proof.
  intros; split; intros. 
  - destruct H as [? [[[]] ?]]; exists a; split; auto; split.
    * left; exists x; split; firstorder. 
    * intros; destruct H2; destruct H2 as [? [[] ?]]; subst; firstorder.  
    * right; exists x; split; firstorder. 
    * intros; destruct H2; destruct H2 as [? [[] ?]]; subst; firstorder.  
  - destruct H as [? []]; subst; unfold id. 
    destruct H as [[[a []]|[b []]] Hismin]; 
    [exists a | exists b]; split; auto.
    + split; [left; destruct H; auto| intros ? []]. 
      * apply H in H1; auto. 
      * pose proof min_nonempty_exists f Q ltac:(exists b; auto) as [fb' [b' []]].
        subst; unfold id in Hismin. 
        pose proof Hismin (f b') ltac:(right; exists b'; split; auto). 
        apply H2 in H1. 
        lia.  
    + split; [right; destruct H; auto| intros a []]. 
      * pose proof min_nonempty_exists f P ltac:(exists a; auto) as [fa' [a' []]].
        subst; unfold id in Hismin. 
        pose proof Hismin (f a') ltac:(left; exists a'; split; auto). 
        apply H2 in H1. 
        lia. 
      * apply H in H1; auto. 
Qed.

End Nat.

Section Nat_op.

(* None is +inf *)

Definition Nat_op_le: option nat -> option nat -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Nat.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Nat_op_plus: option nat -> option nat -> option nat :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Nat_op_min (x y: option nat) : option nat :=
  match x, y with
  | Some xv, Some yv => Some (min xv yv)
  | Some xv, None    => Some xv
  | None,    Some yv => Some yv
  | None,    None    => None
  end.

Theorem Nat_op_le_refl: forall x, Nat_op_le x x.
Proof. intros. destruct x; simpl; auto. Qed.

Theorem Nat_op_le_trans: forall x y z, Nat_op_le x y -> Nat_op_le y z -> Nat_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Nat_op_le_antisym: forall x y, Nat_op_le x y -> Nat_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed.

Theorem Nat_op_le_total: forall x y, {Nat_op_le x y} + {Nat_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Nat_le_total.
Qed.

#[export] Instance Nat_op_le_TotalOrder: TotalOrder Nat_op_le := {
  le_refl := Nat_op_le_refl;
  le_trans := Nat_op_le_trans;
  le_antisym := Nat_op_le_antisym;
  le_total := Nat_op_le_total
}.

End Nat_op.




Section Z_op.

Local Open Scope Z.

(* None is +inf *)

Definition Z_op_le: option Z -> option Z -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Z.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Z_op_plus: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Z_op_min: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some xv, Some yv => Some (Z.min xv yv)
  | Some xv, None    => Some xv
  | None,    Some yv => Some yv
  | None,    None    => None
  end.

Theorem Z_op_le_refl: forall x, Z_op_le x x.
Proof. intros. destruct x; simpl; lia. Qed.

Theorem Z_op_le_trans: forall x y z, Z_op_le x y -> Z_op_le y z -> Z_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Z_op_le_antisym: forall x y, Z_op_le x y -> Z_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed. 

Theorem Z_op_le_total: forall x y, {Z_op_le x y} + {Z_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Z_le_total.
Qed.

#[export] Instance Z_op_le_TotalOrder: TotalOrder Z_op_le := {
  le_refl := Z_op_le_refl;
  le_trans := Z_op_le_trans;
  le_antisym := Z_op_le_antisym;
  le_total := Z_op_le_total
}.

End Z_op.