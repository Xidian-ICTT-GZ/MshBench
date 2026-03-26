struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(node: *mut Node; vals: list<i32>) =
    node == std::ptr::null_mut() ?
        vals == nil
    :
        (*node).value |-> ?v &*& (*node).next |-> ?n &*& nodes(n; ?vs) &*& vals == cons(v, vs);

predicate stack(stack: *mut Stack; vals: list<i32>) =
    (*stack).head |-> ?h &*& nodes(h; vals);

fixpoint i32 sum_list(list<i32> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + sum_list(xs0);
    }
}

@*/

#[requires(nodes(node, ?vals))]
#[ensures(nodes(node, vals) &*& result == sum_list(vals))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, vals);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node, vals);
    } else {
        //@ open nodes(node, vals);
        //@ close nodes(node, vals);
    }

    result
}

impl Stack {
    #[requires(stack(stack, ?vals))]
    #[ensures(stack(stack, vals) &*& result == sum_list(vals))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        //@ open stack(stack, vals);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, vals);

        result
    }
}