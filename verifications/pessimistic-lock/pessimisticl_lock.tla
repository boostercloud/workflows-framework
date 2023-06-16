------------------------- MODULE pessimisticl_lock -------------------------
EXTENDS Integers, Sequences, TLC
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
  NoDuplicateReports ==
    \A t \in DOMAIN tickets:
    ~\E t2 \in (DOMAIN tickets) \ {t}:
      tickets[t].bugId = tickets[t2].bugId
  
  AllBugsMarked == \A b \in DOMAIN bugs: bugs[b].processed
  
  AllBugsReported ==
    \A b \in DOMAIN bugs:
    \E t \in DOMAIN tickets:
      bugs[b].id = tickets[t].bugId
  
  Min(set) == CHOOSE v \in set: \A v2 \in set \ {v}: v < v2

  HasOldestLockFor(id, prc) ==
    IF lockStorage = <<>> THEN FALSE ELSE
    LET 
      locksForId == SelectSeq(lockStorage, LAMBDA l: l.id = id)
      oldestLockIndex == Min(DOMAIN locksForId)
    IN locksForId[oldestLockIndex].prc = prc

  Completed ==
    /\ <>[] AllBugsMarked
    /\ <>[] AllBugsReported
end define;

fair process main \in {"main1", "main2"}
variables
  currentBugIndex = -1,
  errors = 0;
begin
Loop:
  while \E b \in DOMAIN bugs: ~bugs[b].processed do
    ChooseBug:
      if \A b \in DOMAIN bugs: bugs[b].processed then
        goto Break;
      else
        currentBugIndex := CHOOSE b \in DOMAIN bugs: ~bugs[b].processed;
      end if;
    RequestLock:
      (*********************************************************************)
      (* The check is not needed in the implementation, we can safely      *)
      (* insert a new lock on every attempt and have the older locks       *)
      (* expire, but the model checker will get into an infinite loop if   *)
      (* locks keep getting added.                                         *)
      (*********************************************************************)
      if ~\E l \in DOMAIN lockStorage: lockStorage[l].id = bugs[currentBugIndex].id then
        lockStorage :=
          Append(lockStorage, [prc |-> self, id |-> bugs[currentBugIndex].id]);
      end if;
    VerifyLock:
      if ~HasOldestLockFor(bugs[currentBugIndex].id, self) then
        goto Break;
      end if;
    Report:
      tickets := Append(tickets, [bugId |-> bugs[currentBugIndex].id]);
    MarkAsProcessed:
      bugs[currentBugIndex].processed := TRUE;
    Break:
      skip;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "733d5c99" /\ chksum(tla) = "3a21be3b")
VARIABLES bugs, lockStorage, tickets, pc

(* define statement *)
NoDuplicateReports ==
  \A t \in DOMAIN tickets:
  ~\E t2 \in (DOMAIN tickets) \ {t}:
    tickets[t].bugId = tickets[t2].bugId

AllBugsMarked == \A b \in DOMAIN bugs: bugs[b].processed

AllBugsReported ==
  \A b \in DOMAIN bugs:
  \E t \in DOMAIN tickets:
    bugs[b].id = tickets[t].bugId

Min(set) == CHOOSE v \in set: \A v2 \in set \ {v}: v < v2

HasOldestLockFor(id, prc) ==
  IF lockStorage = <<>> THEN FALSE ELSE
  LET
    locksForId == SelectSeq(lockStorage, LAMBDA l: l.id = id)
    oldestLockIndex == Min(DOMAIN locksForId)
  IN locksForId[oldestLockIndex].prc = prc

Completed ==
  /\ <>[] AllBugsMarked
  /\ <>[] AllBugsReported

VARIABLES currentBugIndex, errors

vars == << bugs, lockStorage, tickets, pc, currentBugIndex, errors >>

ProcSet == ({"main1", "main2"})

Init == (* Global variables *)
        /\ bugs = [ o \in 1..BugCount |-> [ id |-> o, processed |-> FALSE ] ]
        /\ lockStorage = <<>>
        /\ tickets = <<>>
        (* Process main *)
        /\ currentBugIndex = [self \in {"main1", "main2"} |-> -1]
        /\ errors = [self \in {"main1", "main2"} |-> 0]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF \E b \in DOMAIN bugs: ~bugs[b].processed
                    THEN /\ pc' = [pc EXCEPT ![self] = "ChooseBug"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << bugs, lockStorage, tickets, currentBugIndex, 
                              errors >>

ChooseBug(self) == /\ pc[self] = "ChooseBug"
                   /\ IF \A b \in DOMAIN bugs: bugs[b].processed
                         THEN /\ pc' = [pc EXCEPT ![self] = "Break"]
                              /\ UNCHANGED currentBugIndex
                         ELSE /\ currentBugIndex' = [currentBugIndex EXCEPT ![self] = CHOOSE b \in DOMAIN bugs: ~bugs[b].processed]
                              /\ pc' = [pc EXCEPT ![self] = "RequestLock"]
                   /\ UNCHANGED << bugs, lockStorage, tickets, errors >>

RequestLock(self) == /\ pc[self] = "RequestLock"
                     /\ IF ~\E l \in DOMAIN lockStorage: lockStorage[l].id = bugs[currentBugIndex[self]].id
                           THEN /\ lockStorage' = Append(lockStorage, [prc |-> self, id |-> bugs[currentBugIndex[self]].id])
                           ELSE /\ TRUE
                                /\ UNCHANGED lockStorage
                     /\ pc' = [pc EXCEPT ![self] = "VerifyLock"]
                     /\ UNCHANGED << bugs, tickets, currentBugIndex, errors >>

VerifyLock(self) == /\ pc[self] = "VerifyLock"
                    /\ IF ~HasOldestLockFor(bugs[currentBugIndex[self]].id, self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "Break"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Report"]
                    /\ UNCHANGED << bugs, lockStorage, tickets, 
                                    currentBugIndex, errors >>

Report(self) == /\ pc[self] = "Report"
                /\ tickets' = Append(tickets, [bugId |-> bugs[currentBugIndex[self]].id])
                /\ pc' = [pc EXCEPT ![self] = "MarkAsProcessed"]
                /\ UNCHANGED << bugs, lockStorage, currentBugIndex, errors >>

MarkAsProcessed(self) == /\ pc[self] = "MarkAsProcessed"
                         /\ bugs' = [bugs EXCEPT ![currentBugIndex[self]].processed = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "Break"]
                         /\ UNCHANGED << lockStorage, tickets, currentBugIndex, 
                                         errors >>

Break(self) == /\ pc[self] = "Break"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Loop"]
               /\ UNCHANGED << bugs, lockStorage, tickets, currentBugIndex, 
                               errors >>

main(self) == Loop(self) \/ ChooseBug(self) \/ RequestLock(self)
                 \/ VerifyLock(self) \/ Report(self)
                 \/ MarkAsProcessed(self) \/ Break(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"main1", "main2"}: main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {"main1", "main2"} : WF_vars(main(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
