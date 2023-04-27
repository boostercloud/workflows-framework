----------------------- MODULE optimisticLockTwoPhase -----------------------
EXTENDS Integers, Sequences
CONSTANT OrderCount
(***************************************************************************)
(* Algorithm to perform a two step action in an external system in a       *)
(* concurrency resilient way.  It is assumed that the third party allows   *)
(* us to introduce a unique way to identify the action in all of its       *)
(* steps.                                                                  *)
(*                                                                         *)
(* The resulting algorithm should:                                         *)
(*                                                                         *)
(* - Prepare and confirm the action.                                       *)
(*                                                                         *)
(* - Be able to recover from a failed previous attempt.                    *)
(*                                                                         *)
(* - Prevent double booking if two process attempt the same action against *)
(* the same resouce.                                                       *)
(*                                                                         *)
(* - As a consequence, it should be idempotent.                            *)
(*                                                                         *)
(* The third party must provide:                                           *)
(*                                                                         *)
(* - A mechanism to add metadata to the process, and subsequently query it *)
(* based on that data, in order to identify it.                            *)
(*                                                                         *)
(* - A way to determine the order of creation of a process to determine    *)
(* the victim in case of a conflict.  This can be done via random numbers  *)
(* if there's no deterministic way to find the process that started first. *)
(***************************************************************************)

(***************************************************************************)
(* The process that will be modelled after an integration with a third     *)
(* party that manages logistics.                                           *)
(*                                                                         *)
(* A delivery must be created to send an order to the customer.            *)
(*                                                                         *)
(* The delivery must be linked to an order.                                *)
(*                                                                         *)
(* The delivery must be confirmed.                                         *)
(*                                                                         *)
(* Only one delivery per order must be confirmed.                          *)
(***************************************************************************)

(*--fair algorithm optimisticLockTwoPhase
variables
  orders = [ o \in 1..OrderCount |-> [ id |-> o, processed |-> FALSE ] ],
  deliveries = [ o \in 1..(OrderCount + 1) |-> [ id |-> o, confirmed |-> TRUE ] ];
  
define
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDeliveredOnce ==
  <>[]
    /\ Len(orders) = Len(ConfirmedDeliveries)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN ConfirmedDeliveries:
       orders[oIdx].id = deliveries[dIdx].id
end define;
begin
skip;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "25135d5d" /\ chksum(tla) = "8d4cdf19")
VARIABLES orders, deliveries, pc

(* define statement *)
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDeliveredOnce ==
  <>[]
    /\ Len(orders) = Len(ConfirmedDeliveries)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN ConfirmedDeliveries:
       orders[oIdx].id = deliveries[dIdx].id


vars == << orders, deliveries, pc >>

Init == (* Global variables *)
        /\ orders = [ o \in 1..OrderCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ deliveries = [ o \in 1..(OrderCount + 1) |-> [ id |-> o, confirmed |-> TRUE ] ]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << orders, deliveries >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
