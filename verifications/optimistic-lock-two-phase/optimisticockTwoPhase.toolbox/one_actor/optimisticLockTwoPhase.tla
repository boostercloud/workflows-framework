----------------------- MODULE optimisticLockTwoPhase -----------------------
EXTENDS TLC, Integers
(***************************************************************************)
(* Algorithm to perform a two step action in an external system in a       *)
(* concurrency resilient way.                                              *)
(*                                                                         *)
(* The resulting algorithm should:                                         *)
(*                                                                         *)
(* - Prepare and confirm the action.                                       *)
(*                                                                         *)
(* - Be able to recover from a failed previous attempt.                    *)
(*                                                                         *)
(* - Prevent double booking if two process attempt the same action against *)
(* the same resouce.                                                       *)
(***************************************************************************)

(*--fair algorithm optimisticLockTwoPhase
variable
  stock = 1,
  deliveryOrders = <<>>;
begin

while stock > 0 do
  stock := stock - 1;
end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1b4f11eb" /\ chksum(tla) = "d6f12ce0")
VARIABLES stock, deliveryOrders, pc

vars == << stock, deliveryOrders, pc >>

Init == (* Global variables *)
        /\ stock = 1
        /\ deliveryOrders = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF stock > 0
               THEN /\ stock' = stock - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ stock' = stock
         /\ UNCHANGED deliveryOrders

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
