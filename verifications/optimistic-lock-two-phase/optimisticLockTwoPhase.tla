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

AllOrdersDelivered ==
  LET cd == ConfirmedDeliveries IN
    /\ Len(orders) = Len(cd)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN cd:
       orders[oIdx].id = cd[dIdx].id

AllOrdersDeliveredOnce ==
  \* Play with the forever bit of it.
  <>[] AllOrdersDelivered

NoDoubleBookings ==
  \A dIdx \in DOMAIN ConfirmedDeliveries:
  ~\E oDI \in (DOMAIN ConfirmedDeliveries) \ {dIdx}:
  ConfirmedDeliveries[dIdx].id = ConfirmedDeliveries[oDI].id
end define;
fair process main \in {"handler1","handler2"}
variables 
  orderIndex = -1;
begin
Loop:
  while \E oIdx \in DOMAIN orders: ~orders[oIdx].processed do
    ChooseOrder:
      if ~\E oIdx \in DOMAIN orders: ~orders[oIdx].processed then
        goto Break;
      else
        orderIndex := CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed;
      end if;
    CreateDelivery:
      if (~\E di \in DOMAIN deliveries: deliveries[di].source = self /\ deliveries[di].id = orders[orderIndex].id) then
        deliveries := Append(deliveries, [ id |-> orders[orderIndex].id, confirmed |-> FALSE, source |-> self ]);
      end if;
    TryConfirmDelivery:
      with deliveryIndex = CHOOSE di \in DOMAIN deliveries: deliveries[di].id = orders[orderIndex].id /\ deliveries[di].source = self do
        if (\E di \in DOMAIN deliveries: di < deliveryIndex /\ deliveries[di].id = orders[orderIndex].id) then
          goto Break;
        else
          deliveries[deliveryIndex].confirmed := TRUE;
        end if;    
      end with;  
    MarkOrderAsProcessed:
      orders[orderIndex].processed := TRUE;
    Break:
      skip;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b1d196bf" /\ chksum(tla) = "87d920d")
VARIABLES orders, deliveries, pc

(* define statement *)
ConfirmedDeliveries == SelectSeq(deliveries,LAMBDA d: d.confirmed)

AllOrdersDelivered ==
  LET cd == ConfirmedDeliveries IN
    /\ Len(orders) = Len(cd)
    /\ \A oIdx \in DOMAIN orders:
       \E dIdx \in DOMAIN cd:
       orders[oIdx].id = cd[dIdx].id

AllOrdersDeliveredOnce ==

  <>[] AllOrdersDelivered

NoDoubleBookings ==
  \A dIdx \in DOMAIN ConfirmedDeliveries:
  ~\E oDI \in (DOMAIN ConfirmedDeliveries) \ {dIdx}:
  ConfirmedDeliveries[dIdx].id = ConfirmedDeliveries[oDI].id

VARIABLE orderIndex

vars == << orders, deliveries, pc, orderIndex >>

ProcSet == ({"handler1","handler2"})

Init == (* Global variables *)
        /\ orders = [ o \in 1..OrderCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ deliveries = <<>>
        (* Process main *)
        /\ orderIndex = [self \in {"handler1","handler2"} |-> -1]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF \E oIdx \in DOMAIN orders: ~orders[oIdx].processed
                    THEN /\ pc' = [pc EXCEPT ![self] = "ChooseOrder"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << orders, deliveries, orderIndex >>

ChooseOrder(self) == /\ pc[self] = "ChooseOrder"
                     /\ IF ~\E oIdx \in DOMAIN orders: ~orders[oIdx].processed
                           THEN /\ pc' = [pc EXCEPT ![self] = "Break"]
                                /\ UNCHANGED orderIndex
                           ELSE /\ orderIndex' = [orderIndex EXCEPT ![self] = CHOOSE oIdx \in DOMAIN orders: ~orders[oIdx].processed]
                                /\ pc' = [pc EXCEPT ![self] = "CreateDelivery"]
                     /\ UNCHANGED << orders, deliveries >>

CreateDelivery(self) == /\ pc[self] = "CreateDelivery"
                        /\ IF (~\E di \in DOMAIN deliveries: deliveries[di].source = self /\ deliveries[di].id = orders[orderIndex[self]].id)
                              THEN /\ deliveries' = Append(deliveries, [ id |-> orders[orderIndex[self]].id, confirmed |-> FALSE, source |-> self ])
                              ELSE /\ TRUE
                                   /\ UNCHANGED deliveries
                        /\ pc' = [pc EXCEPT ![self] = "TryConfirmDelivery"]
                        /\ UNCHANGED << orders, orderIndex >>

TryConfirmDelivery(self) == /\ pc[self] = "TryConfirmDelivery"
                            /\ LET deliveryIndex == CHOOSE di \in DOMAIN deliveries: deliveries[di].id = orders[orderIndex[self]].id /\ deliveries[di].source = self IN
                                 IF (\E di \in DOMAIN deliveries: di < deliveryIndex /\ deliveries[di].id = orders[orderIndex[self]].id)
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Break"]
                                         /\ UNCHANGED deliveries
                                    ELSE /\ deliveries' = [deliveries EXCEPT ![deliveryIndex].confirmed = TRUE]
                                         /\ pc' = [pc EXCEPT ![self] = "MarkOrderAsProcessed"]
                            /\ UNCHANGED << orders, orderIndex >>

MarkOrderAsProcessed(self) == /\ pc[self] = "MarkOrderAsProcessed"
                              /\ orders' = [orders EXCEPT ![orderIndex[self]].processed = TRUE]
                              /\ pc' = [pc EXCEPT ![self] = "Break"]
                              /\ UNCHANGED << deliveries, orderIndex >>

Break(self) == /\ pc[self] = "Break"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Loop"]
               /\ UNCHANGED << orders, deliveries, orderIndex >>

main(self) == Loop(self) \/ ChooseOrder(self) \/ CreateDelivery(self)
                 \/ TryConfirmDelivery(self) \/ MarkOrderAsProcessed(self)
                 \/ Break(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"handler1","handler2"}: main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {"handler1","handler2"} : WF_vars(main(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
