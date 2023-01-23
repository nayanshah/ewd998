---- MODULE EWD ----

EXTENDS Integers, TLC

CONSTANT NumNodes
VARIABLE
    NodeState,
    TerminationDetected,
    Network,
    Token

ATD == INSTANCE AT

vars == <<
    NodeState,
    TerminationDetected,
    Network,
    Token
    >>

Nodes == 1..NumNodes

TypeOK ==
    /\ NodeState \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetected \in {TRUE, FALSE}
    /\ Token \in Nodes

Init ==
    /\ NodeState = [node \in Nodes |-> TRUE]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE
    /\ Token = NumNodes

Terminated == 
    /\ \A node \in Nodes : NodeState[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

FinishWork(node) ==
    /\ Network[node] = 0
    /\ NodeState' = [NodeState EXCEPT ![node] = FALSE]
    /\ UNCHANGED << Network, Token, TerminationDetected >>

SendMessage(source) ==
    \E dest \in Nodes:
        /\ NodeState[source] = TRUE
        /\ Network' = [Network EXCEPT ![dest] = @ + 1]
        /\ UNCHANGED << NodeState, Token, TerminationDetected >>

ReceiveMessage(source) ==
    /\ Network[source] > 0
    /\ NodeState' = [NodeState EXCEPT ![source] = TRUE]
    /\ Network' = [Network EXCEPT ![source] = @ - 1]
    /\ UNCHANGED << Token, TerminationDetected >>

PassToken(source) ==
    /\ NodeState[source] = FALSE
    /\ Token = source
    /\ Token # 1
    /\ Token' = Token - 1
    /\ UNCHANGED << NodeState, Network, TerminationDetected >>

DetectTermination ==
    /\ Token = 1
    /\ NodeState[1] = FALSE
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED << NodeState, Token, Network >>

Next ==
    \E node \in Nodes:
        \/ FinishWork(node)
        \/ SendMessage(node)
        \/ ReceiveMessage(node)
        \/ PassToken(node)
        \/ DetectTermination

FiniteNetwork ==
    \A node \in Nodes : Network[node] <= 3

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

THEOREM Spec => ATD!Spec

ATDSpec == ATD!Spec

Correct ==
    /\ [](ATD!TypeOK)
    /\ [](TypeOK)
    /\ ATD!TerminationIsEventuallyDetected
    /\ ATD!TerminationDetectionIsStable
    /\ [](ATD!TerminatedDetectedIsCorrect)

====