Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Set Default Goal Selector "!".


(* Definition Pid := nat. *)

Definition rotate_left (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => t ++ [h]
  end.

Definition head (l : list nat) : nat :=
  match l with
  | [] => O
  | h :: t => h
  end.

Fixpoint round_robin (n : nat) ( p: list nat) : list nat :=
  match n with
  | O => []
  | S n' => [head(p)] ++ round_robin n' (rotate_left p)
  end.

Compute round_robin 27 [1;2;3].