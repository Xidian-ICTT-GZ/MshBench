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

fixpoint int sum_list(list<i32> values) {
    switch(values) {
        case nil: return 0;
        case cons(h, t): return h + sum_list(t);
    }
}

pred list(head: *mut Node, values: list<i32>) =
    head == 0 ? values == [] :
    exists<v: i32, tail: *mut Node, rest: list<i32>>(
        head != 0 &*&
        node(head, v, tail) &*&
        list(tail, rest) &*&
        values == cons(v, rest)
    );

#[requires(node != 0)]
#[requires(list(node, ?values))]
#[ensures(list(node, values))]
#[ensures(result == sum_list(values))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    if node.is_null() {
        0
    } else {
        open list(node, values);
        // unpack list predicate
        reveal list;
        open list(node, values);
        assert node != 0;
        open node(node, ?v, ?next);
        open list(next, ?rest);

        // call recursively on next, which consumes list(next, rest)
        int result = get_nodes_sum(next);
        assert result == sum_list(rest);

        close list(next, rest);
        close node(node, v, next);
        close list(node, values);

        return result + v;
    }
}

#[requires(stack != 0)]
#[requires(malloc_block_Stack(stack))]
#[requires((*stack).head |-> ?head)]
#[requires(list(head, ?values))]
#[ensures(list(head, values))]
#[ensures(result == sum_list(values))]
unsafe fn get_sum(stack: *mut Stack) -> i32
{
    // open list predicate for stack->head to fulfill get_nodes_sum precondition
    open (*stack).head |-> ?head;
    open list(head, ?values);
    int result = get_nodes_sum(head);
    close list(head, values);
    return result;
}