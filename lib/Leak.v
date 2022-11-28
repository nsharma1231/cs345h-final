Add LoadPath "lib" as Lib.
Require Import Lib.Neuromorphic.
Require Import Arith List String Logic ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module Leak.
(*
We assume all neruons leak their potential after one timestep.
Given an input state,
step one timestep and return resulting state
    1) Identify all neurons above threshold
    2) Fire neurons we found
*)
Fixpoint step' (p : Neuromorphic.potentials) (g : Neuromorphic.graph) : Neuromorphic.potentials :=
    match g with
    | [] => [] (* no synapses left to fire *)
    | (n1, n2, w) :: g' =>
        if Neuromorphic.decode p n1 then
        Neuromorphic.add_potential (step' p g') n2 w (* n1 should fire this synapse, add weight to n2 *)
        else step' p g' (* this synapse is not fired *)
    end.
Definition step (st : Neuromorphic.state) : Neuromorphic.state :=
    Neuromorphic.pair (step' (Neuromorphic.get_potentials st) (Neuromorphic.get_graph st)) (Neuromorphic.get_graph st).

Fixpoint step_n (n: nat) (st: Neuromorphic.state) : Neuromorphic.state :=
    match n with
    | O => st
    | S n' => step_n n' (step st)
    end.

(* run for n steps and check if neuron out has potential >= threshold *)
Definition eval (steps : nat) (st : Neuromorphic.state) (out : Neuromorphic.Neuron) : bool :=
    Neuromorphic.decode (Neuromorphic.get_potentials (step_n steps st)) out.

End Leak.