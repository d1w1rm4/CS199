Require Import List.
Require Import Nat.
Import ListNotations.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

(*************** START ***************)

Definition quantum : nat := 5.

Definition output : list nat := [].

Inductive job : Type :=
  | taskj (id : nat) (burst_time : nat).

Definition unfinished (j : job) : bool :=
  match j with
  | taskj _ burst_time => Nat.ltb 0 burst_time
  end.

Definition joblist := list job.

Definition example_joblist : joblist :=
  [taskj 1 15; taskj 2 10; taskj 3 20].

Definition burst_reduce (j : job) : job :=
  match j with
  | taskj id burst_time => taskj id (burst_time - quantum)
  end.

Definition get_id (j : job) : nat :=
  match j with
  | taskj id burst_time => id
  end.

Fixpoint sum_burst_times (jl : joblist) : nat :=
  match jl with
  | [] => 0
  | taskj _ burst_time :: tl => burst_time + sum_burst_times tl
  end.

Fixpoint rr_sched (t : nat) (l : joblist) (output : list nat) : list nat :=
  match t with
  | 0 => output
  | S t' =>
      match l with
      | [] => output
      | h :: t =>
          let reduced_h := burst_reduce h in
          let new_output := output ++ [get_id h] in
          rr_sched (S t' - quantum) (filter unfinished (t ++ [reduced_h])) new_output
      end
  end.

Definition example_output := rr_sched (sum_burst_times example_joblist) example_joblist [].
Compute example_output.

(***************  END  ***************)