module BinTree[Time]

open relation[Time]
open relation[Node]

sig Node {
    left : Node lone -> Time,
    right : Node lone -> Time
}

one sig BinTree {
    root : Node one -> Time,
    items : Node some -> Time
}

fun left_subtree[n : Node, t : Time] : set Node {
    n.^(left.t.*(right.t))
}

fun right_subtree[n : Node, t : Time] : set Node {
    n.^(right.t.*(left.t))
}

fun reachable[n : Node, t : Time] : set Node {
    left_subtree[n, t] + right_subtree[n, t]
}

fact {
    all t : Time | all n : BinTree.root.t | n in BinTree.items.t
    all t : Time | all n : Node | n.left.t != n.right.t or n.left.t = none
    all t : Time | all n : Node | n not in BinTree.items.t
        implies n.left.t = none and n.right.t = none
    all t : Time | all n : Node  {
        n.left.t != n
        n.right.t != n
    }
}

pred ordered[t : Time] {
    all n : Node | less[left_subtree[n, t], n]
    all n : Node | greater[right_subtree[n, t], n]
}

pred acyclic[now : Time] {
    all n : Node | n not in reachable[n, now]
}

pred tree_valid(now : Time) {
    all tree : BinTree {
        acyclic[now]
        ordered[now]
        all n : tree.items.now - tree.root.now | n in reachable[tree.root.now, now]
        all n : Node | n not in tree.items.now implies n not in reachable[tree.root.now, now]
    }
}

pred insert[now : Time] {
    let future = now.next {
        all tree : BinTree {
            tree.root.future = tree.root.now
        }
        some free : Node | {
            all t : BinTree | free not in t.items.now
        } implies {
            all tree : BinTree {
                tree.items.now + free = tree.items.future
                some pos : tree.items.now  {
                    all node : Node - pos {
                        node.left.future = node.left.now
                        node.right.future = node.right.now
                    }
                    { insert_left[now, pos, free] }
                    or
                    { insert_right[now, pos, free] }
                    ordered[future]
                }
            }
        } else {
            all node : Node {
                node.left.future = node.left.now
                node.right.future = node.right.now
            }
            all tree : BinTree | tree.items.future = tree.items.now
        }
    }
}

pred insert_left[now : Time, pos : Node, ins : Node] {
    less[ins, pos]
    pos.left.now = none
    let future = now.next {
        pos.left.future = ins
        pos.right.future = pos.right.now
    }
}

pred insert_right[now : Time, pos : Node, ins : Node] {
    greater[ins, pos]
    pos.right.now = none
    let future = now.next {
        pos.right.future = ins
        pos.left.future = pos.left.now
    }
}

example : run {
    all t : Time {
        tree_valid[t]
        #BinTree.items.t >= 4
    }
 } for 7

assert insertion_correct {
    all now : Time - last | let future = now.next | {
        tree_valid[now]
        insert[now]
    } implies tree_valid[future]
}

CheckInsert : check insertion_correct for 4 but exactly 2 Time