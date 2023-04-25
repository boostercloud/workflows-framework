----------------------- MODULE optimisticLockTwoPhase -----------------------
EXTENDS TLC, Integers, Sequences
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
define
OrdersWereMade ==
  <>[] (deliveryOrders /= <<>>)
end define;
  
  
begin

while stock > 0 do
  deliveryOrders :=
    Append(
      deliveryOrders,
      [ amount |-> 1, confirmed |-> FALSE ]);
  \*deliveryOrders[0].confirmed := TRUE;
  stock := stock - 1;
end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1f10c94d" /\ chksum(tla) = "d8bb88ab")
VARIABLES stock, deliveryOrders, pc

(* define statement *)
OrdersWereMade ==
  <>[] (deliveryOrders /= <<>>)


vars == << stock, deliveryOrders, pc >>

Init == (* Global variables *)
        /\ stock = 1
        /\ deliveryOrders = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF stock > 0
               THEN /\ deliveryOrders' = Append(
                                           deliveryOrders,
                                           [ amount |-> 1, confirmed |-> FALSE ])
                    /\ stock' = stock - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << stock, deliveryOrders >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
