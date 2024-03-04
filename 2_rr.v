Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Lists.List.
From Coq Require Export Arith.PeanoNat.
Export ListNotations.

Inductive Process :=
  | P : nat -> Process.

Definition next_process (total_processes : nat) (p : Process) : Process :=
  match p with
  | P n => P ((n + 1) mod total_processes)
  end.

Fixpoint round_robin (total_processes n : nat) (p : Process) : list Process :=
  match n with
  | O => []
  | S n' => p :: round_robin total_processes n' (next_process total_processes p)
  end.

Compute round_robin 3 10 (P 0).

(* TO DO: 1. Incorporate Burst Times per process (do not run 0 burst time) and Quantum
          2. Make Input of Round Robin a List of processes and not number of processes *)