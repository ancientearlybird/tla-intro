---- MODULE 02_Refinement ----
EXTENDS TLC

CONSTANTS PARTICIPANTS, PIZZAS, NO_PIZZA

VARIABLES chosen, ordered, msgs


vars == << chosen, ordered, msgs >>

(* all messages in the process *)
Messages ==
    [type: {"DecideOnPizza"}]                                               \* ask everyone to decide on a pizza
    \* \union
    \* [type: {"TellCoordinator"}, participant: PARTICIPANTS, pizza: PIZZAS ]  \* tell the coordinator which pizza was chosen

(* type checking *)
TypeOK ==
    /\ DOMAIN ordered = PARTICIPANTS
    /\ DOMAIN chosen = PARTICIPANTS
    /\ \A p \in PARTICIPANTS:
        /\ ordered[p] \in PIZZAS \union {NO_PIZZA}
        /\ chosen[p] \in PIZZAS \union {NO_PIZZA}
    /\ msgs \subseteq Messages
    /\ \A m \in msgs: m.type \in {"DecideOnPizza"}
    \* /\ \A m \in msgs:
    \*     IF m.type = "TellCoordinator" THEN
    \*         m.participant \in PARTICIPANTS
    \*     ELSE
    \*         TRUE
    \* /\ \A m \in msgs:
    \*     IF m.type = "TellCoordinator" THEN
    \*         m.pizza \in PIZZAS                                \* REQUIREMENT: \union {NO_PIZZA} - now missing <<<<<<<<<<<<<<<<<<<
    \*     ELSE
    \*         TRUE

(* the inital state *)
(* chosen
    Tom:    "Keine Pizza"
    Jerry:  "Keine Pizza"
    Alf:    "Keine Pizza"
 *)
Init ==
    /\ chosen = [p \in PARTICIPANTS |-> NO_PIZZA]           \* overview of all paticipants: who -> current choice of pizza
    /\ ordered = [p \in PARTICIPANTS |-> NO_PIZZA]          \* shopping list: who -> which pizza
    /\ msgs = {}                                            \* no messages send yet

(* send a message to ALL participants *)
Announce ==
    /\ msgs = {}
    /\ msgs' = msgs \union {[type |-> "DecideOnPizza"]}
    /\ UNCHANGED <<chosen, ordered>>

DecideOnPizza(participant) ==
    /\ [type |-> "DecideOnPizza"] \in msgs
    /\ \E pizza \in PIZZAS:
        /\ chosen' = [chosen EXCEPT ![participant] = pizza]
        /\ UNCHANGED <<ordered, msgs>>

(* the coordinator is told about the pizza *)
TellCoordinator(participant) ==
    /\ chosen[participant] /= NO_PIZZA                                      \* a pizza has to be chosen
    /\ ordered' = [ordered EXCEPT ![participant] = chosen[participant]]     \* add the pizza to the shopping list
    /\ UNCHANGED <<chosen, msgs>>

(* ConfirmAll -> OrderCorrect *)                            \* <<<<<<<<<<<<<<<<
OrderCorrect ==
    /\ [type |-> "DecideOnPizza"] \in msgs                  \* <<<<<<<<<<<<<<<<
    /\ \A p \in PARTICIPANTS:
        /\ ordered[p] /= NO_PIZZA                           \* <<<<<<<<<<<<<<<<
        /\ ordered[p] = chosen[p]
    /\ UNCHANGED <<chosen, ordered, msgs>>
    \* no explicit feedback loop needed here

(* every next state *)
Next ==
    \/ Announce
    \/ \E p \in PARTICIPANTS:
        \/ DecideOnPizza(p)
        \/ TellCoordinator(p)
    \/ OrderCorrect

Spec == Init /\ [][Next]_vars

====

remove Message
refine "Sync by ConfirmlAll" to "OrderCorrect"




Was haben wir bis hier erreicht?
\* 1. Wir haben eine abstrakte Beschreibung des Systems
\* 2. Wir haben eine Beschreibung des Verhaltens des Systems
\* 3. Wir haben eine Beschreibung der Invarianten
\* 4. Wir haben eine Beschreibung der Typen
\* 5. Wir haben eine Beschreibung der Initialisierung
\* 6. Wir haben eine Beschreibung der Nachrichten
\* 7. Wir haben eine Beschreibung der Aktionen
\* 8. Wir haben eine Beschreibung der nächsten Zustände





ABER:

Wir haben lediglich überprüft, dass etwas IMMER passieren KANN,

nicht, dass es irgendwann in der Zukunft tatsächlich passiert!






-coverage 1 -simulate num=1000,stats=basic
