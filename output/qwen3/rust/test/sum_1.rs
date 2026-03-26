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
    // This lemma is not needed for verification but may be useful for reasoning.
    // VeriFast can infer disjointness from malloc_block predicates.
}

#[requires(node != 0 &*& node(node, _, _))]
#[ensures(result == v + get_nodes_sum_result(next))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires
        node != 0 ? list(node, ?values) : true,
    ensures
        result == fold(values, 0, |acc: i32, x: i32| acc + x),
{
    let mut result = 0;

    if !node.is_null() {
        let next = (*node).next;
        let v = (*node).value;
        // Consume ownership of current node and recursively process next
        // We require that the list predicate holds for `node`, so we can split it
        // into current node and tail list.
        result = get_nodes_sum(next);
        result += v;
    }

    result
}

#[requires(stack != 0 &*& malloc_block_Stack(stack) &*& (*stack).head |-> ?head &*& list(head, ?values))]
#[ensures(result == fold(values, 0, |acc: i32, x: i32| acc + x))]
unsafe fn get_sum(stack: *mut Stack) -> i32
    requires
        stack != 0 ? list((*stack).head, ?values) : true,
    ensures
        result == fold(values, 0, |acc: i32, x: i32| acc + x),
{
    let result = get_nodes_sum((*stack).head);

    result
}