---- MODULE bintree ----
EXTENDS Naturals, Sequences, TLC

CONSTANT
    NodeId,
    Data

VARIABLES
    tree,
    mutexes,
    left,
    right,
    data

NodeType == [id: NodeId, left: NodeId, right: NodeId, data: Data]
MutexType == [locked: BOOLEAN]

Init ==
    /\ tree = <<>>
    /\ mutexes = [n \in NodeId |-> [locked |-> FALSE]]
    /\ left = [n \in NodeId |-> n]
    /\ right = [n \in NodeId |-> n]
    /\ data = [n \in NodeId |-> CHOOSE d \in Data : TRUE]

NodeInTree(node) == \E i \in 1..Len(tree): tree[i] = node
LeftProperLink(node) ==
    /\ left[node] \in NodeId
    /\ data[node] >= data[left[node]]
RightProperLink(node) ==
    /\ right[node] \in NodeId
    /\ data[node] < data[right[node]]
Sorted(node) == /\ LeftProperLink(node) /\ RightProperLink(node)

SortedInv == \A node \in NodeId: NodeInTree(node) => Sorted(node)

AcquireMutex(node) ==
    /\ ~mutexes[node].locked
    /\ mutexes' = [mutexes EXCEPT ![node].locked = TRUE]
    /\ UNCHANGED <<tree, left, right, data>>

ReleaseMutex(node) ==
    /\ mutexes[node].locked
    /\ mutexes' = [mutexes EXCEPT ![node].locked = FALSE]
    /\ UNCHANGED <<tree, left, right, data>>



Insert(pos, new) ==
    /\ AcquireMutex(pos)
    /\ AcquireMutex(new)
    /\ ~NodeInTree(new)
    /\ NodeInTree(pos)
    /\ IF data[new] < data[pos]
        THEN /\ \/ /\ left' = [new EXCEPT ![pos] = new]
        ELSE /\ right' = [new EXCEPT ![pos] = new]
    /\ ReleaseMutex(new)
    /\ ReleaseMutex(pos)
    /\ UNCHANGED  data

Next ==
    \/ \E pos \in NodeId, new \in NodeId: Insert(pos, new)
    \/ \E node \in NodeId: AcquireMutex(node) \/ ReleaseMutex(node)

Spec == Init /\ [][Next]_<<tree, mutexes, left, right, data>>

THEOREM  Spec => []<><<tree, mutexes, left, right, data>>_<<tree', mutexes', left', right', data'>>
=============================================================================
\* For model checking
NodeId == {1, 2, 3, 4, 5}
Data == {1, 2, 3, 4, 5}
Check = Spec /\ SortedInv
=============================================================================