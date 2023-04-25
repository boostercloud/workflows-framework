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
OrdersWereMade == <>[] (deliveryOrders /= <<>>)

OrdersWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveryOrders: deliveryOrders[oIdx].confirmed)

NeverInTheRed == stock >= 0
end define;
  
  
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
      stock := stock - 1;
  end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3dd9e18" /\ chksum(tla) = "649d94cf")
VARIABLES stock, deliveryOrders, pc

(* define statement *)
OrdersWereMade == <>[] (deliveryOrders /= <<>>)

OrdersWereVerified ==
  <>[] (\A oIdx \in DOMAIN deliveryOrders: deliveryOrders[oIdx].confirmed)

NeverInTheRed == stock >= 0


vars == << stock, deliveryOrders, pc >>

Init == (* Global variables *)
        /\ stock = 1
        /\ deliveryOrders = <<>>
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF stock > 0
              THEN /\ pc' = "CreateOrder"
              ELSE /\ pc' = "Done"
        /\ UNCHANGED << stock, deliveryOrders >>

CreateOrder == /\ pc = "CreateOrder"
               /\ deliveryOrders' = Append(
                                      deliveryOrders,
                                      [ amount |-> 1, confirmed |-> FALSE ])
               /\ pc' = "ConfirmOrder"
               /\ stock' = stock

ConfirmOrder == /\ pc = "ConfirmOrder"
                /\ deliveryOrders' = [deliveryOrders EXCEPT ![1].confirmed = TRUE]
                /\ stock' = stock - 1
                /\ pc' = "Loop"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop \/ CreateOrder \/ ConfirmOrder
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
