---- MODULE 13_BC ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)

-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

(* NotifyOthers is used to notify the other threads that are waiting for a
   message in the buffer. If the thread t is a producer, it notifies all
   consumers, otherwise it notifies all producers. *)
NotifyOthers(t) ==
    LET S ==
        IF t \in Producers
            THEN waitSet \ Producers
            ELSE waitSet \ Consumers
    IN
        IF S /= {}
          THEN \E x \in S:
                    waitSet' = waitSet \ {x}
          ELSE
            UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>

-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOthers(t)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)

Get(t) ==
   \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOthers(t)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \E t \in RunningThreads: \/ /\ t \in Producers
                                    /\ Put(t, t)
                                 \/ /\ t \in Consumers
                                    /\ Get(t)

Spec == Init /\ [][Next]_vars

(* 2. <<<<<<<<<< *)
\* FairSpec ==
\*     /\ Spec
\*     /\ \A t \in Producers:
\*             WF_vars(Put(t,t))

(* 3. <<<<<<<<<< *)
\* FairSpec ==
\*     /\ Spec
\*     /\ WF_vars(Next)


NoDeadlock ==
    waitSet /= (Producers \cup Consumers)

(* 1. <<<<<<<<<< *)
NoStarvation == \A p \in Producers: []<>(<<Put(p, p)>>_vars)

=============================================================================

topic:
    only a state machine so far
    no temporal logic
    but we can calculate that something must happen eventually

    starvation
    WF for Put(t,t)

summary:
    \* FairSpec 2
    here: p1 remains in the waitSet ==> starvation

    \* FairSpec 3
    here: p1 never gets the change to produce ==> starvation