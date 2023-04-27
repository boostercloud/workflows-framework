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
  deliveries = <<>>;
  
define
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDeliveredOnce ==
  <>[]
    /\ Len(orders) = Len(ConfirmedDeliveries)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN ConfirmedDeliveries:
       orders[oIdx].id = deliveries[dIdx].id
end define;
process main = "processor"
variables 
  orderIndex = -1,
  deliveryIndex = -1;
begin
Loop:
  while \E oIdx \in DOMAIN orders: ~orders[oIdx].processed do
    ChooseOrder:
      orderIndex := CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed;
    CreateDelivery:
      deliveries := Append(deliveries, [ id |-> orders[orderIndex].id, confirmed |-> FALSE ]);
      deliveryIndex := Len(deliveries);
    ConfirmDelivery:
      deliveries[deliveryIndex].confirmed := TRUE;
    MarkOrderAsProcessed:
      orders[orderIndex].processed := TRUE;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "5a7a025b" /\ chksum(tla) = "667d52a3")
VARIABLES orders, deliveries, pc

(* define statement *)
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDeliveredOnce ==
  <>[]
    /\ Len(orders) = Len(ConfirmedDeliveries)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN ConfirmedDeliveries:
       orders[oIdx].id = deliveries[dIdx].id

VARIABLES orderIndex, deliveryIndex

vars == << orders, deliveries, pc, orderIndex, deliveryIndex >>

ProcSet == {"processor"}

Init == (* Global variables *)
        /\ orders = [ o \in 1..OrderCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ deliveries = <<>>
        (* Process main *)
        /\ orderIndex = -1
        /\ deliveryIndex = -1
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop == /\ pc["processor"] = "Loop"
        /\ IF \E oIdx \in DOMAIN orders: ~orders[oIdx].processed
              THEN /\ pc' = [pc EXCEPT !["processor"] = "ChooseOrder"]
              ELSE /\ pc' = [pc EXCEPT !["processor"] = "Done"]
        /\ UNCHANGED << orders, deliveries, orderIndex, deliveryIndex >>

ChooseOrder == /\ pc["processor"] = "ChooseOrder"
               /\ orderIndex' = (CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed)
               /\ pc' = [pc EXCEPT !["processor"] = "CreateDelivery"]
               /\ UNCHANGED << orders, deliveries, deliveryIndex >>

CreateDelivery == /\ pc["processor"] = "CreateDelivery"
                  /\ deliveries' = Append(deliveries, [ id |-> orders[orderIndex].id, confirmed |-> FALSE ])
                  /\ deliveryIndex' = Len(deliveries')
                  /\ pc' = [pc EXCEPT !["processor"] = "ConfirmDelivery"]
                  /\ UNCHANGED << orders, orderIndex >>

ConfirmDelivery == /\ pc["processor"] = "ConfirmDelivery"
                   /\ deliveries' = [deliveries EXCEPT ![deliveryIndex].confirmed = TRUE]
                   /\ pc' = [pc EXCEPT !["processor"] = "MarkOrderAsProcessed"]
                   /\ UNCHANGED << orders, orderIndex, deliveryIndex >>

MarkOrderAsProcessed == /\ pc["processor"] = "MarkOrderAsProcessed"
                        /\ orders' = [orders EXCEPT ![orderIndex].processed = TRUE]
                        /\ pc' = [pc EXCEPT !["processor"] = "Loop"]
                        /\ UNCHANGED << deliveries, orderIndex, deliveryIndex >>

main == Loop \/ ChooseOrder \/ CreateDelivery \/ ConfirmDelivery
           \/ MarkOrderAsProcessed

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
