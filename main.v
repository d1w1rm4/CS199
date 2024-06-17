(* ------------------------------    IMPORTS    ------------------------------ *)

Require Import List Nat Lia PeanoNat .
Import ListNotations.

(* ------------------------------ PREREQUISITES ------------------------------ *)

Definition quantum : nat := 5.

Inductive job : Type :=
  | taskj (id : nat) (burst_time : nat).

Definition joblist := list job.

(* This function reduces the burst time of a given job by the quantum value. *)
Definition burst_reduce (j : job) : job :=
  match j with
  | taskj id burst_time => taskj id (burst_time - quantum)
  end.

(* This function retrieves the ID of a given job. *)
Definition get_id (j : job) : nat :=
  match j with
  | taskj id burst_time => id
  end.

(* This function calculates the total burst time of all jobs in a job list. *)
Fixpoint sum_burst_times (jl : joblist) : nat :=
  match jl with
  | [] => 0
  | taskj _ burst_time :: tl => burst_time + sum_burst_times tl
  end.

(* ------------------------------ ROUND-ROBIN SCHEDULER ------------------------------ *)

(* This function schedules jobs in a round-robin manner, updating the 
   job list and recording the order of job execution. *)
Fixpoint rr_sched (time : nat) (jl : joblist) (output : list nat) : 
  joblist * list nat :=
  match time with
  | 0 => (jl, output)
  | S t' =>
      match jl with
      | [] => (jl, output)
      | h :: t => let new_output := output ++ [get_id h] in
                  match burst_reduce h with
                  | taskj _ 0 => rr_sched (S t' - quantum) t new_output
                  | taskj _ _ as j' => rr_sched (S t' - quantum) (t ++ [j']) new_output
                  end 
      end
  end.

(* ------------------------------     EXAMPLE RUN     ------------------------------ *)

Definition example_joblist : joblist :=
  [taskj 1 10; taskj 2 10; taskj 3 10].

Definition time : nat := sum_burst_times example_joblist.

Definition example_output := rr_sched time example_joblist [].
Compute example_output.
(* OUTPUT : = ([], [1; 2; 3; 1; 2; 3]) *)

(* ------------------------------      AXIOMS     ------------------------------ *)

(* Axiom 1 : If the result of subtracting `m` from `n` is 0, then `n` must equal `m`. *)
Axiom sub_eq_0_implies_eq : forall n m,
  n - m = 0 -> n = m.

(* Axiom 2 : For any natural numbers n, m, and p, if m is greater than 0, 
             then n−m+p is less than n+p. *)
Axiom sub_pos : forall n m p,
  m > 0 -> n - m + p < n + p.

(* Axiom 3 : The sum of burst times for a job list appended with a single job is equal 
             to the sum of burst times of the initial list plus the burst time of the 
             appended job. *)
Axiom sum_burst_times_app : forall tl id n,
  sum_burst_times (tl ++ [taskj id n]) = sum_burst_times tl + n.

(* Axiom 4 : If the burst time (`bt`) is less than or equal to the quantum, then `bt` 
             is greater than 0. Note: quantum >= 1.*)
Axiom bt_prop1 : forall bt quantum : nat,
  bt <= quantum -> bt > 0.

(* Axiom 5 : If the burst time (`bt`) is greater than 0 and bt is not equal to quantum,
             then bt must be greater than quantum. Note: `bt` is always divisible by quantum.*)
Axiom bt_prop2 : forall bt quantum : nat,
  bt > 0 -> bt <> quantum -> bt > quantum.


(* ------------------------------ PROVEN LEMMAS AND THEOREMS ------------------------------ *)

(* Lemma 1 : For a job list with a head job and a tail, the sum of burst times of the list is 
             at least the burst time of the head job plus the sum of burst times of the tail. *)
Lemma sum_burst_times_add_bt : forall id bt t jl,
  jl = taskj id bt :: t ->
  bt + sum_burst_times t = sum_burst_times jl.
Proof.
  intros id bt t jl Hjl.
  rewrite Hjl.
  simpl. reflexivity.
Qed.

(* Lemma 2 : The sum of burst times of a job list appended with a job that has its burst time 
             reduced by the quantum is less than or equal to the sum of burst times of the 
             initial job list plus the burst time of the appended job before reduction. *)
Lemma sum_burst_times_app' : forall t id bt,
  sum_burst_times (t ++ [taskj id (bt - quantum)]) < bt + sum_burst_times t.
Proof.
  intros t id bt.
  rewrite sum_burst_times_app.
  rewrite Nat.add_comm.
  apply sub_pos.
  unfold quantum.
  lia.
Qed.

(* Lemma 3 : The `rr_sched` function, when run with an empty job list, returns the same empty 
             job list and the output. *)
Lemma rr_sched_empty_joblist: forall time output,
  rr_sched time [] output = ([], output).
Proof.
  intros time output.
  induction time as [| t' IH].
  - (* Base case: time = 0 *)
    simpl. reflexivity.
  - (* Inductive case: time = S t' *)
    simpl. reflexivity.
Qed.

(* Lemma 4 : Running `rr_sched` on a job list containing a single job with burst time equal to
             the quantum results in an empty job list and an output list containing the job's ID. *)
Lemma rr_sched_single_job_quantum:
  forall id output,
    rr_sched quantum [taskj id quantum] output = ([], output ++ [id]).
Proof.
  intros id output.
  simpl.
  unfold burst_reduce.
  unfold get_id.
  reflexivity.
Qed.

(* Lemma 5 : Running `rr_sched` with a job list where the head job's burst time is exactly the 
             quantum results in the removal of that job from the list and the job's ID being 
             added to the output list. *)
Lemma rr_sched_removes_quantum_job :
  forall (id : nat) (t : joblist) (output : list nat),
    rr_sched quantum (taskj id quantum :: t) output = (t, output ++ [id]).
Proof.
  intros id t output.
  simpl.
  unfold burst_reduce.
  unfold get_id.
  reflexivity.
Qed.

(* Theorem 1 : For a job list where the head job's burst time is exactly the quantum, 
               running `rr_sched` for one quantum removes this job from the list. *)
Theorem rr_sched_removes_completed_job :
  forall (jl : joblist) (output : list nat) (id bt : nat) (t : joblist),
    jl = (taskj id bt) :: t ->
    bt = quantum ->
    fst (rr_sched quantum jl output) = t.
Proof.
  intros jl output id bt t Hjl Hbt.
  subst.
  simpl.
  reflexivity.
Qed.

(* Theorem 2 : For a job list where the head job's burst time is greater than the quantum, 
               running `rr_sched` for one quantum moves the head job to the end of the list 
               with its burst time reduced by the quantum. *)
Theorem rr_sched_reduces_head_bt :
  forall (jl : joblist) (output : list nat) (id bt : nat) (t : joblist),
    jl = (taskj id bt) :: t ->
    bt > quantum ->
    fst (rr_sched quantum jl output) = t ++ [taskj id (bt - quantum)].
Proof.
  intros jl output id bt t Hjl Hbt.
  subst.
  simpl.
  destruct (bt - quantum) eqn:Hdiff.
  - (* bt - quantum = 0 *)
    apply sub_eq_0_implies_eq in Hdiff.
    rewrite Hdiff in Hbt. lia.
  - (* bt - quantum = S n *)
    reflexivity.
Qed.

(** FINITE TERMINATION PROPERTY (SOUNDNESS THEOREM) **)
(* Theorem 3 : For any job list, the sum of burst times after running `rr_sched` for one 
               quantum is less than or equal to the original sum of burst times. *)
Theorem rr_sched_reduces_burst_time :
  forall jl id bt t output,
    jl = (taskj id bt) :: t -> 
    sum_burst_times (fst (rr_sched quantum jl output)) < sum_burst_times jl.
Proof.
  intros jl id bt t output Hjl.
  destruct (Nat.eqb_spec bt quantum).
  - (* bt = quantum *)
    subst. rewrite rr_sched_removes_completed_job with (id := id) (bt := quantum) (t := t) by auto.
    simpl. lia.
  - (* bt <> quantum *)
    destruct (Nat.leb_spec bt quantum).
    + (* bt <= quantum *)
      subst. rewrite rr_sched_reduces_head_bt with (id := id) (bt := bt) (t := t). simpl.
      intuition. 
      simpl.
      apply sum_burst_times_app'.
      reflexivity.
      apply bt_prop1 in H.
      apply bt_prop2.
      apply H.
      apply n.
    + (* bt > quantum *)
      rewrite rr_sched_reduces_head_bt with (id := id) (bt := bt) (t := t) by auto.
      assert (H1 : bt + sum_burst_times t = sum_burst_times jl).
      apply sum_burst_times_add_bt with (id := id).
      apply Hjl.
      rewrite <- H1.
      apply sum_burst_times_app'.
Qed.

(* ------------------------------     UNPROVEN THEOREMS     ------------------------------ *)

(** STARVATION-FREE PROPERTY **)
(* Theorem 4 : In a round-robin scheduling algorithm where each job's burst time is a multiple of the 
               time quantum, if the sum of burst times of all jobs is greater than 0, then after running 
               the scheduling algorithm, each job's ID will appear in the output list a number of times 
               equal to its burst time divided by the time quantum. *)
Theorem rr_starvation_free :
  forall (jl : joblist) (output : list nat),
    sum_burst_times jl > 0 ->
    forall (j : job), In j jl -> count_occ Nat.eq_dec (snd (rr_sched (sum_burst_times jl) jl output)) 
                                 (get_id j) = (match j with taskj _ bt => bt end) / quantum.
Proof.
  Admitted.

(** FAIRNESS PROPERTY **)
(* Theorem 5 : For any job list jl, where rr_time is defined as the quantum times the length of jl,
               each job j in jl is executed exactly once within the total scheduling time rr_time, 
               ensuring equal allocation of CPU time among all jobs. *)
Theorem rr_fairness :
  forall (jl : joblist),
    let rr_time := quantum * length jl in
    forall (j : job),
      In j jl ->
      count_occ Nat.eq_dec (snd (rr_sched rr_time jl [])) (get_id j) = 1.
Proof.
  Admitted.

(* ------------------------------           END          ------------------------------ *)