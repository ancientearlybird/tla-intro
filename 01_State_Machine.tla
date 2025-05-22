---- MODULE 01_State_Machine ----
EXTENDS TLC

CONSTANTS PARTICIPANTS, PIZZAS, NO_PIZZA

VARIABLES chosen, ordered, msgs


vars == << chosen, ordered, msgs >>

(* all messages in the process *)
Messages ==
    [type: {"DecideOnPizza"}]                                               \* ask everyone to decide on a pizza
    \union
    [type: {"TellCoordinator"}, participant: PARTICIPANTS, pizza: PIZZAS ]  \* tell the coordinator which pizza was chosen

(* type checking *)
TypeOK ==
    /\ DOMAIN ordered = PARTICIPANTS
    /\ DOMAIN chosen = PARTICIPANTS
    /\ \A p \in PARTICIPANTS: 
        /\ ordered[p] \in PIZZAS \union {NO_PIZZA}
        /\ chosen[p] \in PIZZAS \union {NO_PIZZA}
    /\ msgs \subseteq Messages
    /\ \A m \in msgs: m.type \in {"DecideOnPizza", "TellCoordinator"}
    /\ \A m \in msgs:
        IF m.type = "TellCoordinator" THEN 
            m.participant \in PARTICIPANTS
        ELSE
            TRUE
    /\ \A m \in msgs:
        IF m.type = "TellCoordinator" THEN 
            m.pizza \in PIZZAS                                \* REQUIREMENT: \union {NO_PIZZA} - must there be a choice?
        ELSE
            TRUE

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

ConfirmAll ==
    /\ \A p \in PARTICIPANTS:
        /\ ordered[p] = chosen[p]
    /\ UNCHANGED <<chosen, ordered, msgs>>

(* every next state *)
Next ==
    \/ Announce
    \/ \E p \in PARTICIPANTS:
        \/ DecideOnPizza(p)
        \/ TellCoordinator(p)
    \/ ConfirmAll
    
    \* REFINE THE SPEC: no msgs sending here because it's called for each participant
    \* what is the most abstract view of the system?              

Spec == Init /\ [][Next]_vars

====



