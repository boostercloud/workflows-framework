----------------------- MODULE optimisticLockTwoPhase -----------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS InitialStock
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
(***************************************************************************)

(*--fair algorithm optimisticLockTwoPhase
variable
  stock = InitialStock,
  deliveries = <<>>,
  orders = [ id: 1..InitialStock , processed: {FALSE} ];
define
DeliveriesWereMade == <>[] (deliveries /= <<>>)

DeliveriesWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveries: deliveries[oIdx].confirmed)

NeverInTheRed == stock >= 0

AreTherePendingOrders ==
  (\E o \in orders: o.processed = FALSE)
end define;
  
process orderProcessor \in { "ord1" } 
variables dIdx = -1, orderId = -1;
begin
  Loop:
  while AreTherePendingOrders do
    PickOrder:
      orderId := (CHOOSE o \in orders: o.processed = FALSE).id;
    CreateDelivery:
      deliveries :=
        Append(
          deliveries,
          [ amount |-> 1, confirmed |-> FALSE, orderID |-> orderId ]);
    ConfirmDelivery:
      dIdx := CHOOSE di \in DOMAIN deliveries: deliveries[di].orderID = orderId;
      deliveries[dIdx].confirmed := TRUE;
    ThirdPartyReducesStock:
      stock := stock - deliveries[1].amount;
    MarkAsProcessed:
      orders := 
        (orders \ {CHOOSE o \in orders: o.id = orderId})
        \union
        {[ processed |-> TRUE, orderId |-> orderId]};
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b57a2186" /\ chksum(tla) = "68f0cfbd")
VARIABLES stock, deliveries, orders, pc

(* define statement *)
DeliveriesWereMade == <>[] (deliveries /= <<>>)

DeliveriesWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveries: deliveries[oIdx].confirmed)

NeverInTheRed == stock >= 0

AreTherePendingOrders ==
  (\E o \in orders: o.processed = FALSE)

VARIABLES dIdx, orderId

vars == << stock, deliveries, orders, pc, dIdx, orderId >>

ProcSet == ({ "ord1" })

Init == (* Global variables *)
        /\ stock = InitialStock
        /\ deliveries = <<>>
        /\ orders = [ id: 1..InitialStock , processed: {FALSE} ]
        (* Process orderProcessor *)
        /\ dIdx = [self \in { "ord1" } |-> -1]
        /\ orderId = [self \in { "ord1" } |-> -1]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF AreTherePendingOrders
                    THEN /\ pc' = [pc EXCEPT ![self] = "PickOrder"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << stock, deliveries, orders, dIdx, orderId >>

PickOrder(self) == /\ pc[self] = "PickOrder"
                   /\ orderId' = [orderId EXCEPT ![self] = (CHOOSE o \in orders: o.processed = FALSE).id]
                   /\ pc' = [pc EXCEPT ![self] = "CreateDelivery"]
                   /\ UNCHANGED << stock, deliveries, orders, dIdx >>

CreateDelivery(self) == /\ pc[self] = "CreateDelivery"
                        /\ deliveries' = Append(
                                           deliveries,
                                           [ amount |-> 1, confirmed |-> FALSE, orderID |-> orderId[self] ])
                        /\ pc' = [pc EXCEPT ![self] = "ConfirmDelivery"]
                        /\ UNCHANGED << stock, orders, dIdx, orderId >>

ConfirmDelivery(self) == /\ pc[self] = "ConfirmDelivery"
                         /\ dIdx' = [dIdx EXCEPT ![self] = CHOOSE di \in DOMAIN deliveries: deliveries[di].orderID = orderId[self]]
                         /\ deliveries' = [deliveries EXCEPT ![dIdx'[self]].confirmed = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "ThirdPartyReducesStock"]
                         /\ UNCHANGED << stock, orders, orderId >>

ThirdPartyReducesStock(self) == /\ pc[self] = "ThirdPartyReducesStock"
                                /\ stock' = stock - deliveries[1].amount
                                /\ pc' = [pc EXCEPT ![self] = "MarkAsProcessed"]
                                /\ UNCHANGED << deliveries, orders, dIdx, 
                                                orderId >>

MarkAsProcessed(self) == /\ pc[self] = "MarkAsProcessed"
                         /\ orders' = (orders \ {CHOOSE o \in orders: o.id = orderId[self]})
                                      \union
                                      {[ processed |-> TRUE, orderId |-> orderId[self]]}
                         /\ pc' = [pc EXCEPT ![self] = "Loop"]
                         /\ UNCHANGED << stock, deliveries, dIdx, orderId >>

orderProcessor(self) == Loop(self) \/ PickOrder(self)
                           \/ CreateDelivery(self) \/ ConfirmDelivery(self)
                           \/ ThirdPartyReducesStock(self)
                           \/ MarkAsProcessed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in { "ord1" }: orderProcessor(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
