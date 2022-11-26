(*
neuron ~ node (threshold)
synapse ~ edge (weights, delays)

=> neuron has a "potential" 
=> after a synapse fires, weight is added or subtracted to neuron potential 
=> potential >= threshold -> "fire" each outgoing synapse and resets potential 
=> "leak" -> potentials settle to base value over time 

inputs => fire events (time + weight) to input neurons
outputs => times that output neurons fire 

how to program:
1. A) define a graph of synapses connecting neurons
   B) set input + output neurons
2. send input spikes of specified weights at discrete time intervals
3. read outputs

Example AND with leak
(node1, node2, weight, delay)
("A", "A&B", 0.5, 1)
("B", "A&B", 0.5, 1)

Example OR with leak
(node1, node2, weight, delay)
("A", "A|B", 1, 1)
("B", "A|B", 1, 1)
*)

Require Import Arith List String Logic ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module Leak.
(*
Some assumptions we will make:
    1) All synapses have delay = 1
    2) Potential starts at 0
    3) All leaf neurons must have synapse with weight 0 to themselves
*)

(* the only constructor for neuron takes a name and threshold *)
Inductive Neuron : Type :=
neuron : string -> Z -> Neuron.
Definition neuron_name (n : Neuron) : string :=
    match n with
    | neuron x _ => x
    end.
Definition neuron_thresh (n : Neuron) : Z :=
    match n with
    | neuron _ x => x
    end.

(* two neurons are equivalent if their names are the same, i.e. thresholds are ignored *)
Definition neuron_eq (n1 n2 : Neuron) : bool :=
    let v1 := neuron_name n1 in
    let v2 := neuron_name n2 in
    if string_dec v1 v2 then true else false.
Example neuron_eq_correct1: neuron_eq (neuron "abc" 5) (neuron "abc" 5) = true.
Proof. auto. Qed.
Example neuron_eq_correct2: neuron_eq (neuron "abc" 5) (neuron "abc" (-1)) = true.
Proof. auto. Qed.
Example neuron_eq_correct3: neuron_eq (neuron "abc" 5) (neuron "def" 5) = false.
Proof. auto. Qed.

(*
potentials is a list of (Neuron, potential)
this allows us to look up a Neuron and get it's current potential
potentials ~ registers in that they are storing a value for us that we can query

we can set potential to n           (set)
we can set potential to 0           (reset)
we can set potential to curr + n    (add)
*)
Definition potentials := list (Neuron * Z).
Definition set_potential (p: potentials) (x: Neuron) (n: Z) : potentials :=
    cons (x, n) p.
Definition reset_potential (p: potentials) (x: Neuron) : potentials :=
    cons (x, 0) p.
Fixpoint plookup (p: potentials) (x: Neuron) : Z :=
    match p with
    | nil => 0 (* we state that potential starts at 0 *)
    | cons (x', n) p' => if neuron_eq x x' then n else plookup p' x
    end.
Definition add_potential (p: potentials) (x: Neuron) (n: Z) : potentials :=
    set_potential p x ((plookup p x) + n).

(*
graph is a list of synapses (neuron1, neuron2, weight)
each pair represents a directed edge from neuron1 --> neuron2
__this list should never change during the execution of a program__

slookup returns a list of synapses that fire as a result of the firing of neuron n
each synapse is represented in the list by the destination neuron and weight
*)
Definition graph := list (Neuron * Neuron * Z).
Definition set_synapse (g: graph) (n1: Neuron) (n2: Neuron) (w: Z) : graph :=
    cons (n1, n2, w) g.
Definition out_synapses := list (Neuron * Z).
Fixpoint slookup (g: graph) (n: Neuron) : out_synapses :=
    match g with
    | nil => nil
    | cons (n1, n2, w) g' =>
        let recurse := slookup g' n in
        if neuron_eq n n1 then cons (n2, w) recurse else recurse
    end.


(*
direct encoding of binary values
true is represented by potential >= threshold
false is represented by potential < threshold
*)
Definition encode (p: potentials) (x: Neuron) (b: bool) : potentials :=
    if b then set_potential p x (neuron_thresh x) else reset_potential p x. 
Definition decode (p: potentials) (x: Neuron) : bool :=
    plookup p x >=? (neuron_thresh x).

Definition encode_test := neuron "*" 3.
Example encode_correct: forall b, plookup (encode [] encode_test b) encode_test = if b then 3 else 0.
Proof. destruct b; auto. Qed.

(*
Define our state as a combination of the current potentials of all neurons and
the synapses defining our graph
*)
Inductive state : Type :=
    pair : potentials -> graph -> state.
Definition get_potentials (s : state) : potentials :=
    match s with
    | pair x _ => x
    end.
Definition get_graph (s : state) : graph :=
    match s with
    | pair _ x => x
    end.

(*
Given an input state,
step one timestep and return resulting state
    1) Identify all neurons above threshold
    2) Fire neurons we found
*)
Fixpoint step' (p : potentials) (g : graph) : potentials :=
    match g with
    | [] => [] (* no synapses left to fire *)
    | (n1, n2, w) :: g' =>
        if decode p n1 then
        add_potential (step' p g') n2 w (* n1 should fire this synapse, add weight to n2 *)

        (*
        this synapse is not fired, it should not lose it's potential
        when making recursive call, set potential for n1 to 0 so that we don't double count
        *)
        else add_potential (step' (reset_potential p n1) g') n1 (plookup p n1)
    end.
Definition step (st : state) : state :=
    pair (step' (get_potentials st) (get_graph st)) (get_graph st).

Fixpoint step_n (n: nat) (st: state) : state :=
    match n with
    | O => st
    | S n' => step_n n' (step st)
    end.

(* update the potential of a neuron in a given state *)
Definition update_state (st : state) (x : Neuron) (p : Z) : state :=
    pair (set_potential (get_potentials st) x p) (get_graph st).

(* run for n steps and check if neuron out has potential >= threshold *)
Definition eval (steps : nat) (st : state) (out : Neuron) : bool :=
    decode (get_potentials (step_n steps st)) out.

Module TestNoLeak.
Definition a := neuron "A" 1.
Definition b := neuron "B" 2.
Definition inputs := encode [] a true.
Definition synapses := set_synapse (set_synapse [] b b 0) a b 1.
Definition initial_state := pair inputs synapses.
Example values_after_one_step:
    plookup (get_potentials (step initial_state)) a = 0 /\
    plookup (get_potentials (step initial_state)) b = 1.
Proof. auto. Qed.
Example b_does_not_fire: eval 1 initial_state b = false.
Proof. auto. Qed.
Example values_after_two_steps:
    plookup (get_potentials (step_n 2 initial_state)) a = 0 /\
    plookup (get_potentials (step_n 2 initial_state)) b = 1.
Proof. auto. Qed.
End TestNoLeak.

(*
Given a list of all neurons, a initial state, and an output neuron, compute the
result in `steps` number of steps. If out has potential >= threshold, result is true,
else result is false
*)
Definition in1 := neuron "A" 1.
Definition in2 := neuron "B" 1.
Definition inputs (a b : bool) := encode (encode [] in1 a) in2 b.

Module or.
Definition out := neuron "A|B" 1.
Definition synapses := set_synapse (set_synapse [] in1 out 1) in2 out 1.
Definition initial_state (a b : bool) := pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, eval 1 (initial_state a b) out = orb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_two_steps: forall a b, eval 2 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.
Example potential_resets:
    forall (a b : bool),
    plookup (get_potentials (step_n 2 (initial_state a b))) in1 = 0 /\
    plookup (get_potentials (step_n 2 (initial_state a b))) in2 = 0 /\
    plookup (get_potentials (step_n 2 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End or.

Module incorrect_and.
Definition out := neuron "A&B" 2.
Definition synapses := set_synapse (set_synapse (set_synapse [] out out 0) in1 out 1) in2 out 1.
Definition initial_state (a b : bool) := pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, eval 1 (initial_state a b) out = andb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_two_steps: forall a b, eval 2 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.

(*
We want to show that computing (a, b) = (1, 0) and (a, b) = (0, 1) one after the other results in
**incorrect** output due to potentials not leaking. i.e. node "A&B" leaks the half potential of 1 before it
is fired again
*)
Example and_leak_correct:
    eval 1 (initial_state true false) out = false /\
    eval 1 (update_state (step (initial_state true false)) in2 1) out = true.
Proof. auto. Qed.
Example and_leak_correct_reverse:
    eval 1 (initial_state false true) out = false /\
    eval 1 (update_state (step (initial_state false true)) in1 1) out = true.
Proof. auto. Qed.
End incorrect_and.

Module and.
Definition t1 := neuron "Ta" 1.
Definition t2 := neuron "Tb" 1.
Definition h1 := neuron "Ha" 1.
Definition h2 := neuron "Hb" 1.
Definition out := neuron "A&B" 2.
Definition synapses := set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse []
                        in1 t1 1)
                        in2 t2 1)
                        t1 h1 1)
                        t2 h2 1)
                        in1 out 1)
                        in2 out 1)
                        h1 out (-1))
                        h2 out (-1))
                        out h1 (-1))
                        out h2 (-1).
Definition initial_state (a b : bool) := pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, eval 1 (initial_state a b) out = andb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_three_steps:
    forall a b,
        plookup (get_potentials (step_n 3 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End and.

Module xor.
Definition h1 := neuron "A&~B" 1.
Definition h2 := neuron "B&~A" 1.
Definition out := neuron "A^B" 1.
Definition synapses := set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse (set_synapse []
                        in1 h1 1)
                        in2 h2 1)
                        h1 out 1)
                        h2 out 1)
                        out out 0)
                        h1 h2 1)
                        h2 h1 1)
                        in1 h2 (-1))
                        in2 h1 (-1).
Definition initial_state (a b : bool) := pair (inputs a b) synapses.

Example computes_in_two_steps: forall a b, eval 2 (initial_state a b) out = xorb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_three_steps:
forall a b,
    plookup (get_potentials (step_n 3 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End xor.

End Leak.