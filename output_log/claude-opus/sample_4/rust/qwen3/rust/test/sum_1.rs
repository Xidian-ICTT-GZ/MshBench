#[allow(dead_code)]
struct Node {
    value: i32,
    next: *mut Node,
}

#[allow(dead_code)]
struct Stack {
    head: *mut Node,
}

pred node(node: *mut Node, v: i32, next: *mut Node) =
    node != 0 &*& 
    malloc_block_Node(node) &*&
    (*node).value |-> v &*&
    (*node).next |-> next;

pred list(head: *mut Node, values: list<i32>) =
    head == 0 ? values == [] :
    exists<v: i32, tail: *mut Node, rest: list<i32>>(
        head != 0 &*&
        node(head, v, tail) &*&
        list(tail, rest) &*&
        values == cons(v, rest)
    );

lemma void list_distinct_nodes(list<heads: list<*mut Node>>, list<vals: list<i32>>)
    requires
        list_heads_disjoint(heads) &*&
        length(heads) == length(vals) &*&
        forall(i: int, 0 <= i && i < length(heads) ?
            list(nth(heads, i), nth(vals, i)) : true)
    ensures
        true;
{
    // This lemma can remain as is for possible reasoning.
}

#[requires(node != 0 &*& list(node, ?values) &*& malloc_block_Node(node))]
#[ensures(result == fold(values, 0, |acc: i32, x: i32| acc + x) &*& list(node, values))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    if node == 0 {
        0
    } else {
        open list(node, ?values);
        open node(node, ?v, ?next);
        int sum_tail = get_nodes_sum(next);
        // After recursive call, list(next, ?) is reestablished.

        // Reestablish node predicate and list predicate for current node.
        close node(node, v, next);
        close list(node, values);

        sum_tail + v
    }
}

#[requires(stack != 0 &*& malloc_block_Stack(stack) &*& (*stack).head |-> ?head &*& list(head, ?values))]
#[ensures(result == fold(values, 0, |acc: i32, x: i32| acc + x) &*& list((*stack).head, values))]
unsafe fn get_sum(stack: *mut Stack) -> i32 {
    get_nodes_sum((*stack).head)
}