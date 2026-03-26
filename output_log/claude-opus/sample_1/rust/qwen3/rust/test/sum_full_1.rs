#[allow(dead_code)]
struct Node {
    value: i32,
    next: *mut Node,
}

#[allow(dead_code)]
struct Stack {
    head: *mut Node,
}

/*@
pred node(p: *mut Node; v: i32, next: *mut Node) =
    (*p).value |-> v &*& (*p).next |-> next &*& struct_Node_padding(p);

pred lseg(p: *mut Node, end: *mut Node; sum: i32) =
    if p == end {
        sum == 0
    } else {
        node(p, ?v, ?next) &*& alloc_block_Node(p) &*& lseg(next, end, ?rest) &*& sum == v + rest
    };
@*/

/*@
lem_auto lseg_null_sum()
    req lseg(?p, 0 as *mut Node, ?sum) &*& p == 0 as *mut Node;
    ens lseg(p, 0 as *mut Node, sum) &*& sum == 0;
{
    open lseg(p, 0 as *mut Node, sum);
    close lseg(p, 0 as *mut Node, sum);
}
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req lseg(node, 0 as *mut Node, ?sum);
//@ ens lseg(node, 0 as *mut Node, sum) &*& result == sum;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open lseg(node, 0 as *mut Node, sum);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close lseg(node, 0 as *mut Node, sum);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req (*stack).head |-> ?head &*& lseg(head, 0 as *mut Node, ?sum);
    //@ ens (*stack).head |-> head &*& lseg(head, 0 as *mut Node, sum) &*& result == sum;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}