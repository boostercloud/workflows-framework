----------------------- MODULE optimisticLockTwoPhase -----------------------
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

(*--algorithm optimisticLockTwoPhare
variable
  stock = 1,
  deliveryOrders = <<>>;
begin
skip;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "15af6952" /\ chksum(tla) = "3907cac5")
VARIABLES stock, deliveryOrders, pc

vars == << stock, deliveryOrders, pc >>

Init == (* Global variables *)
        /\ stock = 1
        /\ deliveryOrders = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << stock, deliveryOrders >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
