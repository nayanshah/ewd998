---- MODULE AT ----

EXTENDS Integers, TLC

CONSTANT NumNodes
VARIABLE NodeState, TerminationDetected, Network

vars == <<NodeState, TerminationDetected, Network>>

Nodes == 1..NumNodes

TypeOK ==
    /\ NodeState \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]

Init ==
    /\ NodeState = [node \in Nodes |-> TRUE]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE

Terminated == 
    /\ \A node \in Nodes : NodeState[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

FinishWork(node) ==
    /\ NodeState[node] = TRUE
    /\ NodeState' = [NodeState EXCEPT ![node] = FALSE]
    /\ UNCHANGED << Network, TerminationDetected >>

SendMessage(source) ==
    \E dest \in Nodes:
        /\ NodeState[source] = TRUE
        /\ Network' = [Network EXCEPT ![dest] = @ + 1]
        /\ UNCHANGED << NodeState, TerminationDetected >>

ReceiveMessage(source) ==
    /\ Network[source] > 0
    /\ NodeState' = [NodeState EXCEPT ![source] = TRUE]
    /\ Network' = [Network EXCEPT ![source] = @ - 1]
    /\ UNCHANGED << TerminationDetected >>

DetectTermination ==
    /\ TerminationDetected' = Terminated
    /\ UNCHANGED << NodeState, Network >>

Next ==
    \E node \in Nodes:
        \/ FinishWork(node)
        \/ SendMessage(node)
        \/ ReceiveMessage(node)
        \/ DetectTermination

FiniteNetwork ==
    \A node \in Nodes : Network[node] <= 3


\* Properties

TerminationIsEventuallyDetected ==
    <>Terminated ~> TerminationDetected

TerminationDetectionIsStable ==
    [][TerminationDetected => TerminationDetected']_TerminationDetected

TerminatedDetectedIsCorrect ==
    TerminationDetected => Terminated

Spec ==
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_vars(Next)

====
