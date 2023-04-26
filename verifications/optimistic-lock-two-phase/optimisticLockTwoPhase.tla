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
  stock = 2,
  deliveryOrders = <<>>;
define
OrdersWereMade == <>[] (deliveryOrders /= <<>>)

OrdersWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveryOrders: deliveryOrders[oIdx].confirmed)

NeverInTheRed == stock >= 0
end define;
  
process orderer \in { "ordr" }
begin
  Loop:
  while stock > 0 do
    CreateOrder:
      deliveryOrders :=
        Append(
          deliveryOrders,
          [ amount |-> 1, confirmed |-> FALSE ]);
    ConfirmOrder:
      deliveryOrders[1].confirmed := TRUE;
      stock := stock - deliveryOrders[1].amount;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d4d515c5" /\ chksum(tla) = "d72285d7")
VARIABLES stock, deliveryOrders, pc

(* define statement *)
OrdersWereMade == <>[] (deliveryOrders /= <<>>)

OrdersWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveryOrders: deliveryOrders[oIdx].confirmed)

NeverInTheRed == stock >= 0


vars == << stock, deliveryOrders, pc >>

ProcSet == ({ "ordr" })

Init == (* Global variables *)
        /\ stock = 2
        /\ deliveryOrders = <<>>
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF stock > 0
                    THEN /\ pc' = [pc EXCEPT ![self] = "CreateOrder"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << stock, deliveryOrders >>

CreateOrder(self) == /\ pc[self] = "CreateOrder"
                     /\ deliveryOrders' = Append(
                                            deliveryOrders,
                                            [ amount |-> 1, confirmed |-> FALSE ])
                     /\ pc' = [pc EXCEPT ![self] = "ConfirmOrder"]
                     /\ stock' = stock

ConfirmOrder(self) == /\ pc[self] = "ConfirmOrder"
                      /\ deliveryOrders' = [deliveryOrders EXCEPT ![1].confirmed = TRUE]
                      /\ stock' = stock - deliveryOrders'[1].amount
                      /\ pc' = [pc EXCEPT ![self] = "Loop"]

orderer(self) == Loop(self) \/ CreateOrder(self) \/ ConfirmOrder(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in { "ordr" }: orderer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
