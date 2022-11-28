Add LoadPath "lib" as Lib.
Require Import Lib.Neuromorphic Lib.Leak Lib.NoLeak.
Require Import Arith List String Logic ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module Examples.

Definition in1 := Neuromorphic.neuron "A" 1.
Definition in2 := Neuromorphic.neuron "B" 1.
Definition inputs (a b : bool) := Neuromorphic.encode (Neuromorphic.encode [] in1 a) in2 b.

(**** Examples with Leak ****)
Module OrLeak.
Definition out := Neuromorphic.neuron "A|B" 1.
Definition synapses := [(in1, out, 1);(in2, out, 1)].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, Leak.eval 1 (initial_state a b) out = orb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_two_steps: forall a b, Leak.eval 2 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.
Example potential_leaks:
    forall (a b : bool) (n : Neuromorphic.Neuron),
    Neuromorphic.plookup (Neuromorphic.get_potentials (Leak.step_n 2 (initial_state a b))) n = 0.
Proof. destruct a, b; auto. Qed.
End OrLeak.

Module AndLeak.
Definition out := Neuromorphic.neuron "A&B" 2.
Definition synapses := [(in1, out, 1);(in2, out, 1)].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, Leak.eval 1 (initial_state a b) out = andb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_two_steps: forall a b, Leak.eval 2 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.
Example potential_leaks:
    forall (a b : bool) (n : Neuromorphic.Neuron),
    Neuromorphic.plookup (Neuromorphic.get_potentials (Leak.step_n 2 (initial_state a b))) n = 0.
Proof. destruct a, b; auto. Qed.

(*
We want to show that computing (a, b) = (1, 0) and (a, b) = (0, 1) one after the other results in
correct output due to potentials leaking. i.e. node "A&B" leaks the half potential of 1 before it
is fired again
*)
Example and_leak_correct:
    Leak.eval 1 (initial_state true false) out = false /\
    Leak.eval 1 (Neuromorphic.update_state (Leak.step (initial_state true false)) in2 1) out = false.
Proof. auto. Qed.
Example and_leak_correct_reverse:
    Leak.eval 1 (initial_state false true) out = false /\
    Leak.eval 1 (Neuromorphic.update_state (Leak.step (initial_state false true)) in1 1) out = false.
Proof. auto. Qed.
End AndLeak.

Module XorLeak.
Definition h1 := Neuromorphic.neuron "A&~B" 1.
Definition h2 := Neuromorphic.neuron "B&~A" 1.
Definition out := Neuromorphic.neuron "A^B" 1.
Definition synapses := [(in1, h1, 1);(in1, h2, (-1));(in2, h1, (-1));(in2, h2, 1);(h1, out, 1);(h2, out, 1)].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_two_steps: forall a b, Leak.eval 2 (initial_state a b) out = xorb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_three_steps: forall a b, Leak.eval 3 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.
Example potential_leaks:
    forall (a b : bool) (n : Neuromorphic.Neuron),
    Neuromorphic.plookup (Neuromorphic.get_potentials (Leak.step_n 3 (initial_state a b))) n = 0.
Proof. destruct a, b; auto. Qed.
End XorLeak.

(**** Examples without Leak ****)
Module OrNoLeak.
Definition out := Neuromorphic.neuron "A|B" 1.
Definition synapses := [(in1, out, 1);(in2, out, 1)].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, NoLeak.eval 1 (initial_state a b) out = orb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_two_steps: forall a b, NoLeak.eval 2 (initial_state a b) out = false.
Proof. destruct a, b; auto. Qed.
Example potential_resets:
    forall (a b : bool),
    Neuromorphic.plookup (Neuromorphic.get_potentials (NoLeak.step_n 2 (initial_state a b))) in1 = 0 /\
    Neuromorphic.plookup (Neuromorphic.get_potentials (NoLeak.step_n 2 (initial_state a b))) in2 = 0 /\
    Neuromorphic.plookup (Neuromorphic.get_potentials (NoLeak.step_n 2 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End OrNoLeak.

Module AndNoLeak.
Definition t1 := Neuromorphic.neuron "Ta" 1.
Definition t2 := Neuromorphic.neuron "Tb" 1.
Definition h1 := Neuromorphic.neuron "Ha" 1.
Definition h2 := Neuromorphic.neuron "Hb" 1.
Definition out := Neuromorphic.neuron "A&B" 2.
Definition synapses :=  [(in1, t1, 1);(in2, t2, 1);(t1, h1, 1);(t2, h2, 1);
                         (in1, out, 1);(in2, out, 1);(h1, out, (-1));(h2, out, (-1));
                         (out, h1, (-1));(out, h2, (-1))].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_one_step: forall a b, NoLeak.eval 1 (initial_state a b) out = andb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_three_steps:
    forall a b,
        Neuromorphic.plookup (Neuromorphic.get_potentials (NoLeak.step_n 3 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End AndNoLeak.

Module XorNoLeak.
Definition h1 := Neuromorphic.neuron "A&~B" 1.
Definition h2 := Neuromorphic.neuron "B&~A" 1.
Definition out := Neuromorphic.neuron "A^B" 1.
Definition synapses := [(in1, h1, 1);(in2, h2, 1);(h1, out, 1);(h2, out, 1);(out, out, 0);
                        (h1, h2, 1);(h2, h1, 1);(in1, h2, (-1));(in2, h1, (-1))].
Definition initial_state (a b : bool) := Neuromorphic.pair (inputs a b) synapses.

Example computes_in_two_steps: forall a b, NoLeak.eval 2 (initial_state a b) out = xorb a b.
Proof. destruct a, b; auto. Qed.
Example clears_in_three_steps:
forall a b,
    Neuromorphic.plookup (Neuromorphic.get_potentials (NoLeak.step_n 3 (initial_state a b))) out = 0.
Proof. destruct a, b; auto. Qed.
End XorNoLeak.

End Examples.