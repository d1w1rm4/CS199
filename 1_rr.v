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

Definition rotate_left (l : list (list nat)) : list(list nat) :=
  match l with
  | [] => []
  | h :: t =>  t ++ [h]
end.

Compute rotate_left [[1;1;1];[2;2;2];[3;3;3]].

Fixpoint round_robin (l : list (list nat)) : list nat :=
  match l with
  | [] => []
  | [] :: t => round_robin t
  | (h1 :: t1) :: t => h1 :: round_robin ([t1] ++ t)
  end.


Compute round_robin [[1;1;1];[2;2;2];[3;3;3]].

Definition data : list (list nat) :=
  [[1; 4; 7; 9]; [2; 5]; [3; 6; 8; 10; 11; 12]].

Compute roundRobin data.
(* Output: [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] *)

Compute roundRobin [[1; 2; 3]].
(* Output: [1; 2; 3] *)