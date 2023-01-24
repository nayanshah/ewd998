---- MODULE EWD ----

EXTENDS Integers, TLC

CONSTANT NumNodes
VARIABLE
    NodeState,
    TerminationDetected,
    Network,
    Token, \* TokenHolder
    TokenValue,
    TokenColor,
    SendReceiveDiff,
    NodeColor

ATD == INSTANCE AT

vars == <<
    NodeState,
    TerminationDetected,
    Network,
    Token,
    TokenValue,
    TokenColor,
    SendReceiveDiff,
    NodeColor
    >>

Nodes == 1..NumNodes
Colors == {"Black", "White"}

TypeOK ==
    /\ NodeState \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetected \in {TRUE, FALSE}
    /\ Token \in Nodes
    /\ TokenValue \in Int
    /\ TokenColor \in Colors
    /\ SendReceiveDiff \in [Nodes -> Int]
    /\ NodeColor \in [Nodes -> Colors]

Init ==
    /\ NodeState = [node \in Nodes |-> TRUE]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE
    /\ Token = 1
    /\ TokenValue = 0
    /\ TokenColor = "Black"
    /\ SendReceiveDiff = [node \in Nodes |-> 0]
    /\ NodeColor = [node \in Nodes |-> "Black"]

Terminated == 
    /\ \A node \in Nodes : NodeState[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

FinishWork(node) ==
    /\ NodeState[node] = TRUE
    /\ NodeState' = [NodeState EXCEPT ![node] = FALSE]
    /\ UNCHANGED << Network, NodeColor, Token, TokenColor, TokenValue, SendReceiveDiff, TerminationDetected >>

SendMessage(source) ==
    \E dest \in Nodes:
        /\ source # dest
        /\ NodeState[source] = TRUE
        /\ Network' = [Network EXCEPT ![dest] = @ + 1]
        /\ SendReceiveDiff' = [SendReceiveDiff EXCEPT ![source] = @ + 1]
        /\ UNCHANGED << NodeState, NodeColor, Token, TokenColor, TokenValue, TerminationDetected >>

ReceiveMessage(source) ==
    /\ Network[source] > 0
    /\ NodeState' = [NodeState EXCEPT ![source] = TRUE]
    /\ Network' = [Network EXCEPT ![source] = @ - 1]
    /\ SendReceiveDiff' = [SendReceiveDiff EXCEPT ![source] = @ - 1]
    /\ NodeColor' = [NodeColor EXCEPT ![source] = "Black"]
    /\ UNCHANGED << Token, TokenColor, TokenValue, TerminationDetected >>

PassToken(source) ==
    /\ NodeState[source] = FALSE
    /\ Token = source
    /\ Token # 1
    /\ IF Token = NumNodes THEN Token' = 1 ELSE Token' = Token + 1
    /\ TokenValue' = TokenValue + SendReceiveDiff[source]
    /\ IF NodeColor[source] = "Black"
        THEN TokenColor' = "Black"
        ELSE UNCHANGED TokenColor 
    /\ NodeColor' = [NodeColor EXCEPT ![source] = "White"]
    /\ UNCHANGED << NodeState, Network, SendReceiveDiff, TerminationDetected >>

InitiateTermination ==
    /\ Token = 1
    /\ NodeState[1] = FALSE
    /\ \/ TokenValue + SendReceiveDiff[1] # 0
       \/ TokenColor = "Black"
       \/ NodeColor[1] = "Black"
    /\ Token' = Token + 1 \* NumNodes
    /\ TokenValue' = 0
    /\ TokenColor' = "White"
    /\ NodeColor' = [NodeColor EXCEPT ![1] = "White"]
    /\ UNCHANGED << NodeState, SendReceiveDiff, Network, TerminationDetected >>

DetectTermination ==
    /\ Token = 1
    /\ TokenValue + SendReceiveDiff[1] = 0
    /\ TokenColor = "White"
    /\ NodeState[1] = FALSE
    /\ NodeColor[1] = "White"
    /\ TerminationDetected' = TRUE
    /\ UNCHANGED << NodeState, NodeColor, Token, TokenColor, TokenValue, SendReceiveDiff, Network >>

Next ==
    \E node \in Nodes:
        \/ FinishWork(node)
        \/ SendMessage(node)
        \/ ReceiveMessage(node)
        \/ PassToken(node)
        \/ InitiateTermination
        \/ DetectTermination

FiniteNetwork ==
    \A node \in Nodes : Network[node] <= 3

FiniteMessages ==
    \A node \in Nodes : SendReceiveDiff[node] <= 2 

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    \* /\ \A node \in Nodes: WF_vars(ReceiveMessage(node))

Alias == [
    NodeState |-> NodeState,
    TerminationDetected |-> TerminationDetected,
    Network |-> Network,
    Token |-> Token,
    TokenValue |-> TokenValue,
    TokenColor |-> TokenColor,
    SendReceiveDiff |-> SendReceiveDiff,
    NodeColor |-> NodeColor,
    InitiateTermination |-> ENABLED(InitiateTermination),
    DetectTermination |-> ENABLED(DetectTermination),
    SendEnabled |-> [ 
        node \in Nodes |-> ENABLED (SendMessage(node))
    ], 
    ReceiveEnabled |-> [ 
        node \in Nodes |-> ENABLED (ReceiveMessage(node))
    ], 
    PassEnabled |-> [ 
        node \in Nodes |-> ENABLED (PassToken(node))
    ] 
]

THEOREM Spec => ATD!Spec

ATDSpec == ATD!Spec

Correct ==
    /\ [](ATD!TypeOK)
    /\ [](TypeOK)
    /\ ATD!TerminationIsEventuallyDetected
    /\ ATD!TerminationDetectionIsStable
    /\ [](ATD!TerminatedDetectedIsCorrect)

====