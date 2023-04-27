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
  deliveries = <<>>,
  orderIndex = -1,
  deliveryIndex = -1;
  
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

while \E oIdx \in DOMAIN orders: ~orders[oIdx].processed do
  orderIndex := CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed;
  deliveries := Append(deliveries, [ id |-> orders[orderIndex].id, confirmed |-> FALSE ]);
  deliveryIndex := CHOOSE dIdx \in DOMAIN deliveries: ~deliveries[dIdx].confirmed;
  deliveries[deliveryIndex].confirmed := TRUE;
  orders[orderIndex].processed := TRUE;
end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "59b34f4d" /\ chksum(tla) = "cf11896c")
VARIABLES orders, deliveries, orderIndex, deliveryIndex, pc

(* define statement *)
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDeliveredOnce ==
  <>[]
    /\ Len(orders) = Len(ConfirmedDeliveries)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN ConfirmedDeliveries:
       orders[oIdx].id = deliveries[dIdx].id


vars == << orders, deliveries, orderIndex, deliveryIndex, pc >>

Init == (* Global variables *)
        /\ orders = [ o \in 1..OrderCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ deliveries = <<>>
        /\ orderIndex = -1
        /\ deliveryIndex = -1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF \E oIdx \in DOMAIN orders: ~orders[oIdx].processed
               THEN /\ orderIndex' = (CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed)
                    /\ deliveries' = Append(deliveries, [ id |-> orders[orderIndex'].id, confirmed |-> FALSE ])
                    /\ deliveryIndex' = (CHOOSE dIdx \in DOMAIN deliveries': ~deliveries'[dIdx].confirmed)
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << deliveries, orderIndex, deliveryIndex >>
         /\ UNCHANGED orders

Lbl_2 == /\ pc = "Lbl_2"
         /\ deliveries' = [deliveries EXCEPT ![deliveryIndex].confirmed = TRUE]
         /\ orders' = [orders EXCEPT ![orderIndex].processed = TRUE]
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << orderIndex, deliveryIndex >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
