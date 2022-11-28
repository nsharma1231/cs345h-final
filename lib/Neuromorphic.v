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
Add LoadPath "lib" as Lib.
Require Import Arith List String Logic ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module Neuromorphic.
(*
Some assumptions we will make:
    1) All synapses have delay = 1
    2) Potential starts at 0
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

(* update the potential of a neuron in a given state *)
Definition update_state (st : state) (x : Neuron) (p : Z) : state :=
    pair (set_potential (get_potentials st) x p) (get_graph st).

End Neuromorphic.