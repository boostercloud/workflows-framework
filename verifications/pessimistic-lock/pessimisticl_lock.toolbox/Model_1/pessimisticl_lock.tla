------------------------- MODULE pessimisticl_lock -------------------------
EXTENDS Integers, Sequences
CONSTANT BugCount
(***************************************************************************)
(* Algorithm to perform a single step action in an external system in a    *)
(* concurrency resilient way.  It is assumed that the third party allows   *)
(* us to introduce a unique way to identify the action in all of its       *)
(* steps.                                                                  *)
(*                                                                         *)
(* It is also needed to have a central locking storage.                    *)
(*                                                                         *)
(* The resulting algorithm should:                                         *)
(*                                                                         *)
(* - Guarantee that only one instance of the process attempts the action.  *)
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
(***************************************************************************)

(***************************************************************************)
(* The process will be modelled after an integration with a third party    *)
(* that creates customer support tickets for users that report a bug in    *)
(* the product.                                                            *)
(*                                                                         *)
(* A ticket has to eventually be created for every bug.                    *)
(*                                                                         *)
(* Only one ticket can be created per bug.                                 *)
(***************************************************************************)

(*--fair algorithm pessimisticLock
variables
  bugs = [ o \in 1..BugCount |-> [ id |-> o, processed |-> FALSE ] ],
  lockStorage = <<>>,
  tickets = <<>>;

define
  AllBugsProcessed == \A b \in DOMAIN bugs: bugs[b].processed

  Completed ==
    <>[] AllBugsProcessed
end define;

fair process main \in { "main1", "main2" }
variables
  currentBugIndex = -1,
  errors = 0;
begin
Loop:
  while \E b \in DOMAIN bugs: ~bugs[b].processed do
    ChooseBug:
      currentBugIndex := CHOOSE b \in DOMAIN bugs: ~bugs[b].processed;
    Process:
      bugs[currentBugIndex].processed := TRUE;
    Break:
      skip;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d4db2522" /\ chksum(tla) = "74643c13")
VARIABLES bugs, lockStorage, tickets, pc

(* define statement *)
AllBugsProcessed == \A b \in DOMAIN bugs: bugs[b].processed

Completed ==
  <>[] AllBugsProcessed

VARIABLES currentBugIndex, errors

vars == << bugs, lockStorage, tickets, pc, currentBugIndex, errors >>

ProcSet == ({ "main1", "main2" })

Init == (* Global variables *)
        /\ bugs = [ o \in 1..BugCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ lockStorage = <<>>
        /\ tickets = <<>>
        (* Process main *)
        /\ currentBugIndex = [self \in { "main1", "main2" } |-> -1]
        /\ errors = [self \in { "main1", "main2" } |-> 0]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF \E b \in DOMAIN bugs: ~bugs[b].processed
                    THEN /\ pc' = [pc EXCEPT ![self] = "ChooseBug"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << bugs, lockStorage, tickets, currentBugIndex, 
                              errors >>

ChooseBug(self) == /\ pc[self] = "ChooseBug"
                   /\ currentBugIndex' = [currentBugIndex EXCEPT ![self] = CHOOSE b \in DOMAIN bugs: ~bugs[b].processed]
                   /\ pc' = [pc EXCEPT ![self] = "Process"]
                   /\ UNCHANGED << bugs, lockStorage, tickets, errors >>

Process(self) == /\ pc[self] = "Process"
                 /\ bugs' = [bugs EXCEPT ![currentBugIndex[self]].processed = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Break"]
                 /\ UNCHANGED << lockStorage, tickets, currentBugIndex, errors >>

Break(self) == /\ pc[self] = "Break"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Loop"]
               /\ UNCHANGED << bugs, lockStorage, tickets, currentBugIndex, 
                               errors >>

main(self) == Loop(self) \/ ChooseBug(self) \/ Process(self) \/ Break(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in { "main1", "main2" }: main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in { "main1", "main2" } : WF_vars(main(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
