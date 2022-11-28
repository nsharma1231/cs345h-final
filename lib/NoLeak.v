Add LoadPath "lib" as Lib.
Require Import Lib.Neuromorphic.
Require Import Arith List String Logic ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module NoLeak.
(*
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

        (*
        this synapse is not fired, it should not lose it's potential
        when making recursive call, set potential for n1 to 0 so that we don't double count
        *)
        else
        Neuromorphic.add_potential (step' (Neuromorphic.reset_potential p n1) g') n1 (Neuromorphic.plookup p n1)
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
    
Module TestNoLeak.
Definition a := Neuromorphic.neuron "A" 1.
Definition b := Neuromorphic.neuron "B" 2.
Definition inputs := Neuromorphic.encode [] a true.
Definition synapses := Neuromorphic.set_synapse (Neuromorphic.set_synapse [] b b 0) a b 1.
Definition initial_state := Neuromorphic.pair inputs synapses.
Example values_after_one_step:
    Neuromorphic.plookup (Neuromorphic.get_potentials (step initial_state)) a = 0 /\
    Neuromorphic.plookup (Neuromorphic.get_potentials (step initial_state)) b = 1.
Proof. auto. Qed.
Example b_does_not_fire: eval 1 initial_state b = false.
Proof. auto. Qed.
Example values_after_two_steps:
    Neuromorphic.plookup (Neuromorphic.get_potentials (step_n 2 initial_state)) a = 0 /\
    Neuromorphic.plookup (Neuromorphic.get_potentials (step_n 2 initial_state)) b = 1.
Proof. auto. Qed.
End TestNoLeak.

End NoLeak.