---- MODULE 05_Decision ----
EXTENDS TLC, Integers

CONSTANTS PARTICIPANTS, PIZZAS, NO_PIZZA

VARIABLES chosen, ordered, msgs, choices


vars == << chosen, ordered, msgs, choices >>

(* the maximum number of choices a participant can make *)
max_number_of_choices == 3                                  \* <<<<<<<<<<<<<<<<

(* all participants *)

(* all messages in the process *)
Messages ==
    [type: {"DecideOnPizza"}]                               \* ask everyone to decide on a pizza

(* type checking *)
TypeOK ==
    /\ DOMAIN ordered = PARTICIPANTS
    /\ DOMAIN chosen = PARTICIPANTS
    /\ \A p \in PARTICIPANTS: 
        /\ ordered[p] \in PIZZAS \union {NO_PIZZA}
        /\ chosen[p] \in PIZZAS \union {NO_PIZZA}
    /\ msgs \subseteq Messages
    /\ \A m \in msgs: m.type \in {"DecideOnPizza"}
    /\ choices \in [PARTICIPANTS -> 0..max_number_of_choices] \* <<<<<<<<<<<<<<<<

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
    /\ choices = [p \in PARTICIPANTS |-> 0]                 \* <<<<<<<<<<<<<<<<

(* send a message to ALL participants *) 
Announce ==
    /\ msgs = {}
    /\ msgs' = msgs \union {[type |-> "DecideOnPizza"]}
    /\ UNCHANGED <<chosen, ordered, choices>>

DecideOnPizza(participant) ==
    /\ [type |-> "DecideOnPizza"] \in msgs
    /\ choices[participant] < max_number_of_choices         \* <<<<<<<<<<<<<<<<
    /\ \E pizza \in PIZZAS:
        /\ chosen' = [chosen EXCEPT ![participant] = pizza]
        /\ choices' = [choices EXCEPT ![participant] = choices[participant] + 1]        \* <<<<<<<<<<<<<<<<
        /\ UNCHANGED <<ordered, msgs>>

(* the coordinator is told about the pizza *)
TellCoordinator(participant) ==
    /\ chosen[participant] /= NO_PIZZA                                      \* a pizza has to be chosen
    /\ ordered' = [ordered EXCEPT ![participant] = chosen[participant]]     \* add the pizza to the shopping list
    /\ UNCHANGED <<chosen, msgs, choices>>

OrderCorrect(participant) ==                                \* <<<<<<<<<<<<<<<<
  \/ choices[participant] = max_number_of_choices
  \/ /\ choices[participant] < max_number_of_choices 
     /\ chosen[participant] = ordered[participant] 
     /\ chosen[participant] # NO_PIZZA

EventuallyCorrect ==                                        \* <<<<<<<<<<<<<<<<
    <>(\A p \in PARTICIPANTS: OrderCorrect(p))

(* every next state *)
Next ==
    \/ Announce
    \/ \E p \in PARTICIPANTS:
        \/ DecideOnPizza(p)
        \/ TellCoordinator(p)

Spec ==
    /\ Init 
    /\ [][Next]_vars
    /\ \A p \in PARTICIPANTS:
        /\ WF_vars(DecideOnPizza(p))
        /\ WF_vars(TellCoordinator(p))
    /\ WF_vars(Announce)                                    \* <<<<<<<<<<<<<<<< stuttering on initial state

ChoiceBounded ==                                            \* <<<<<<<<<<<<<<<<
    \A p \in DOMAIN choices: 
        /\ choices[p] >= 0
        /\ choices[p] <= max_number_of_choices

====




"Drei mal darfst du wählen."



