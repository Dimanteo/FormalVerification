module relations[exactly item]


private one sig Order {
  First: set item,
  Last: set item,
  Next: item -> item,
  Prev: item -> item
} {

  one First
  one Last
  First != Last
  no Last.Next
  no Next.First
  all i: item - Last {
    one i.Next
    Last in i.^Next
  }

  all disj i,j: item - Last |  i.Next != j.Next
  Prev = ~Next
}


fun next : item->item { Order.Next }
fun prev : item->item { Order.Prev }
fun first : one item { Order.First }
fun last : one item { Order.Last }

fun all_greater : item->item { ^this/next }
fun all_smaller : item->item { ^this/prev }
fun minimum(items : set item) : lone item { items - items.all_greater }
fun maximum(items : set item) : lone item { items - items.all_smaller }
pred less [lhs, rhs: item] { lhs in rhs.all_smaller }
pred greater [lhs, rhs: item] { lhs in rhs.all_greater }
pred less_or_equal [lhs, rhs: item] { lhs = rhs or less[lhs, rhs] }
pred greater_or_equal [lhs, rhs: item] { lhs = rhs or greater [lhs, rhs] }


assert module_is_correct {
  next.this/prev in iden 
  this/prev.next in iden
  item - first = first.all_greater
  item - last = last.all_smaller
  no first.all_smaller
  no last.all_greater
  all i : item | lone i.next
  all i : item | lone i.prev
  all i : item | i not in i.all_greater
  all i : item | i not in i.all_smaller
  all i : item | (i != first) implies (one i.prev)
  all i : item | (i != last) implies (one i.next)
  item = first.*next
  item = last.*prev
  all disj i,j:item | less[i, j] or less[j, i]
  no disj i,j:item | less[i, j] and greater[i, j]
  all disj i,j,k:item | less[i, j] and less[j, k] implies less[i, k]
  all disj i,j,k:item | greater[i, j] and greater[j, k] implies greater[i, k]
  all i,j:item | less_or_equal[i,j] and greater_or_equal[i,j] implies i=j
  all disj i,j,k:item | less[i, j] and less[j, k] implies minimum[i + j + k] = i 
  all disj i,j,k:item | less[i, j] and less[j, k] implies maximum[i + j + k] = k 
}

example: run {} for exactly 4 item

validate: check module_is_correct for 7